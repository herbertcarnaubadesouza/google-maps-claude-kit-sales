#!/usr/bin/env python3
"""Painel de prospecção (pt-BR) para o Google Maps Scraper Kit.

Servidor local, só biblioteca padrão. Serve o sistema em http://localhost:8090 e conversa com o
motor (docker compose) em http://localhost:8080. As buscas rodam UMA DE CADA VEZ numa fila,
de propósito: buscas paralelas contra o Google aumentam a chance de bloqueio.

Dados (tudo local, em painel/dados/):
  leads.json       base única de leads (CRM), chave = place_id do Google
  buscas/<id>.json cada busca, com os ids dos leads que ela trouxe
  config.json      modelos de mensagem do WhatsApp

    python3 painel/server.py
"""
import csv, hashlib, io, json, os, re, socket, sys, threading, time, unicodedata
import urllib.error, urllib.parse, urllib.request, uuid, webbrowser
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir, "scripts"))
import scrape as kit  # noqa: E402  (reaproveita req, grid, dedupe, extração de email/redes)

PORT = int(os.environ.get("PAINEL_PORT", "8090"))
DADOS = os.path.join(HERE, "dados")
DIR_BUSCAS = os.path.join(DADOS, "buscas")
ARQ_LEADS = os.path.join(DADOS, "leads.json")
ARQ_CONFIG = os.path.join(DADOS, "config.json")
os.makedirs(DIR_BUSCAS, exist_ok=True)
UA = kit.UA

TAMANHOS = {  # depth, grid, max_time (s)
    "rapida":   {"depth": 1,  "grid": 0, "max_time": 600},
    "padrao":   {"depth": 5,  "grid": 0, "max_time": 900},
    "completa": {"depth": 10, "grid": 0, "max_time": 1200},
    "cidade":   {"depth": 5,  "grid": 3, "max_time": 900},
}
STATUS_LEAD = ["novo", "contatado", "respondeu", "reuniao", "fechado", "descartado"]
NOME_STATUS = {"novo": "Novo", "contatado": "Contatado", "respondeu": "Respondeu",
               "reuniao": "Reunião marcada", "fechado": "Fechou negócio", "descartado": "Descartado"}
# campos que vêm do Google/site e podem ser atualizados quando o lead aparece de novo numa busca
CAMPOS_CONTATO = ("nome", "categoria", "telefone", "tel_digitos", "tel_tipo", "whatsapp", "whatsapp_origem",
                  "email", "site", "instagram", "facebook", "linkedin", "endereco", "bairro", "cidade", "uf",
                  "cep", "nota", "avaliacoes", "maps", "fechado")

CONFIG_PADRAO = {"templates": [
    {"id": "apresentacao", "nome": "Primeiro contato",
     "texto": "Olá, tudo bem? Encontrei a {nome} no Google Maps aqui em {cidade} e queria conversar rapidinho "
              "sobre uma ideia para trazer mais clientes para vocês. Posso te mandar?"},
    {"id": "sem_site", "nome": "Para quem não tem site",
     "texto": "Oi! Vi a {nome} no Google com ótimas avaliações, mas não encontrei um site de vocês. "
              "Trabalho justamente ajudando {categoria} de {cidade} a aparecer melhor na internet. Posso te mostrar um exemplo?"},
    {"id": "followup", "nome": "Retomar conversa",
     "texto": "Oi, tudo certo? Passando aqui para retomar nossa conversa sobre a {nome}. Conseguiu dar uma olhada?"},
], "padrao": "apresentacao", "auto_contatado": True}

lock = threading.RLock()
buscas = {}          # id -> busca
leads = {}           # id -> lead
config = {}
fila = []            # ids de buscas aguardando
fila_cond = threading.Condition(lock)


# ── Persistência ────────────────────────────────────────────────────────────────
def _grava(caminho, obj):
    tmp = caminho + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False)
    os.replace(tmp, caminho)

def salvar_busca(b):
    with lock:
        _grava(os.path.join(DIR_BUSCAS, f"{b['id']}.json"), b)

def salvar_leads():
    with lock:
        _grava(ARQ_LEADS, leads)

def salvar_config():
    with lock:
        _grava(ARQ_CONFIG, config)

def _le(caminho, padrao):
    try:
        with open(caminho, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return padrao

def carregar():
    leads.update(_le(ARQ_LEADS, {}))
    config.update(_le(ARQ_CONFIG, None) or json.loads(json.dumps(CONFIG_PADRAO)))
    for nome in os.listdir(DIR_BUSCAS):
        if nome.endswith(".json"):
            b = _le(os.path.join(DIR_BUSCAS, nome), None)
            if b:
                buscas[b["id"]] = b
    # migra o formato antigo (uma busca por arquivo em dados/, com os leads dentro)
    for nome in os.listdir(DADOS):
        caminho = os.path.join(DADOS, nome)
        if not nome.endswith(".json") or caminho in (ARQ_LEADS, ARQ_CONFIG):
            continue
        b = _le(caminho, None)
        if not b or "parametros" not in b:
            continue
        antigos = b.pop("leads", None) or []
        b["lead_ids"] = mesclar_leads(b, antigos)
        buscas[b["id"]] = b
        salvar_busca(b)
        os.remove(caminho)
    for b in buscas.values():
        if b.get("estado") in ("na_fila", "rodando"):  # servidor caiu no meio: recoloca na fila
            b["estado"], b["etapa"] = "na_fila", "Aguardando (retomada após reinício)"
            fila.append(b["id"])
    fila.sort(key=lambda i: buscas[i]["criado_em"])
    salvar_leads()


# ── Geografia ──────────────────────────────────────────────────────────────────
_municipios = None

def municipios():
    """Municípios do IBGE embutidos (painel/municipios.json): [{n, uf, lat, lon, ddd, cap}].
    Fonte: github.com/kelvins/municipios-brasileiros (códigos e coordenadas do IBGE)."""
    global _municipios
    if _municipios is None:
        with open(os.path.join(HERE, "municipios.json"), encoding="utf-8") as f:
            _municipios = json.load(f)
    return _municipios

def norm(s):
    return "".join(c for c in unicodedata.normalize("NFD", s or "") if not unicodedata.combining(c)).lower().strip()

def _municipio(cidade, uf):
    alvo = norm(cidade)
    return next((m for m in municipios() if m["uf"] == uf and norm(m["n"]) == alvo), None)

def geocodificar(local):
    """'Bairro, Cidade, UF' -> (lat, lon, bbox) restrito ao Brasil, via OpenStreetMap. None se falhar."""
    q = urllib.parse.urlencode({"format": "json", "limit": 1, "countrycodes": "br", "q": local})
    r = urllib.request.Request(f"https://nominatim.openstreetmap.org/search?{q}", headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(r, timeout=20) as resp:
            hits = json.loads(resp.read())
    except Exception:
        return None
    time.sleep(1)  # política do Nominatim: ~1 req/s
    if not hits:
        return None
    return hits[0]["lat"], hits[0]["lon"], hits[0].get("boundingbox")

def localizar(cidade, uf, bairro=""):
    """Centro da busca. Bairro: OpenStreetMap. Cidade: OpenStreetMap (traz os limites, usados no
    modo 'cidade inteira'), com o centro do IBGE como reserva se o OSM estiver fora do ar."""
    if bairro:
        geo = geocodificar(f"{bairro}, {cidade}, {uf}, Brasil")
        if geo:
            return geo
    geo = geocodificar(f"{cidade}, {uf}, Brasil")
    if geo:
        return geo
    m = _municipio(cidade, uf)
    if not m:
        return None
    d = 0.12  # ~13 km para cada lado: caixa aproximada quando não há limites do OSM
    return str(m["lat"]), str(m["lon"]), [m["lat"] - d, m["lat"] + d, m["lon"] - d, m["lon"] + d]


# ── Normalização brasileira ────────────────────────────────────────────────────
def telefone_br(bruto):
    """-> (digitos_com_55, tipo) onde tipo ∈ celular | fixo | 0800 | ''."""
    d = re.sub(r"\D", "", bruto or "")
    if d.startswith(("0800", "0300", "0500", "0900")):
        return d, "0800"
    if d.startswith("55") and len(d) in (12, 13):
        d = d[2:]
    if d.startswith("0") and len(d) in (11, 12):  # 0 + DDD (formato de operadora)
        d = d[1:]
    if len(d) == 11 and d[2] == "9":
        return "55" + d, "celular"
    if len(d) == 10:
        return "55" + d, ("celular" if d[2] in "6789" else "fixo")
    return d, ""

def formata_tel(d55):
    d = d55[2:] if d55.startswith("55") else d55
    if len(d) == 11:
        return f"({d[:2]}) {d[2:7]}-{d[7:]}"
    if len(d) == 10:
        return f"({d[:2]}) {d[2:6]}-{d[6:]}"
    return d55

WA_RE = re.compile(r"(?:wa\.me/|api\.whatsapp\.com/send/?\?phone=|whatsapp\.com/send/?\?phone=|web\.whatsapp\.com/send\?phone=)\+?(\d{10,13})", re.I)

def whatsapp_em(texto):
    for n in WA_RE.findall(texto or ""):
        d, tipo = telefone_br(n)
        if tipo in ("celular", "fixo"):
            return d
    return ""

def _json(s, padrao):
    try:
        return json.loads(s) if s else padrao
    except ValueError:
        return padrao

def id_lead(row):
    if row.get("place_id"):
        return row["place_id"]
    base = f"{row.get('title', '')}|{row.get('address', '')}"
    return "h" + hashlib.sha1(base.encode()).hexdigest()[:20]

def lead_de(row):
    """Linha bruta do motor -> lead enxuto em português."""
    tel_d, tipo = telefone_br(row.get("phone"))
    end = _json(row.get("complete_address"), {}) or {}
    endereco = row.get("address", "")
    titulo = row.get("title", "")
    if titulo and endereco.startswith(titulo + " - "):
        endereco = endereco[len(titulo) + 3:]
    cep = end.get("postal_code") or (re.search(r"\d{5}-?\d{3}", endereco) or [""])[0]
    uf = end.get("state", "")
    m = re.search(r"-\s*([A-Z]{2})\b", endereco)
    if m and (not uf or len(uf) != 2):
        uf = m.group(1)
    try:
        nota = float(row.get("review_rating") or 0)
    except ValueError:
        nota = 0.0
    try:
        avaliacoes = int(float(row.get("review_count") or 0))
    except ValueError:
        avaliacoes = 0
    wa = whatsapp_em(row.get("order_online", "")) or whatsapp_em(row.get("reservations", ""))
    origem = "maps" if wa else ""
    if not wa and tipo == "celular":
        wa, origem = tel_d, "telefone"
    st = (row.get("status") or "").lower()
    return {
        "id": id_lead(row),
        "nome": titulo,
        "categoria": row.get("category", ""),
        "telefone": formata_tel(tel_d) if tipo in ("celular", "fixo") else (row.get("phone") or ""),
        "tel_digitos": tel_d,
        "tel_tipo": tipo,
        "whatsapp": wa,
        "whatsapp_origem": origem,
        "email": row.get("emails", ""),
        "site": row.get("website", ""),
        "instagram": "", "facebook": "", "linkedin": "",
        "endereco": endereco,
        "bairro": end.get("borough", ""),
        "cidade": end.get("city", ""),
        "uf": uf,
        "cep": cep,
        "nota": nota,
        "avaliacoes": avaliacoes,
        "maps": row.get("link", ""),
        "fechado": "permanently" in st or "permanentemente" in st,
    }

def mesclar_leads(busca, novos):
    """Junta leads de uma busca na base. Lead que já existe: atualiza contato, mantém status,
    anotações e histórico. Devolve os ids na ordem da busca."""
    agora, ids = time.time(), []
    with lock:
        for n in novos:
            lid = n.get("id") or id_lead({"place_id": n.get("place_id"), "title": n.get("nome"), "address": n.get("endereco")})
            atual = leads.get(lid)
            if atual:
                for k in CAMPOS_CONTATO:
                    if n.get(k) not in (None, ""):
                        atual[k] = n[k]
                if busca["id"] not in atual["buscas"]:
                    atual["buscas"].append(busca["id"])
            else:
                lead = {k: n.get(k, "") for k in CAMPOS_CONTATO}
                lead.update(id=lid, status=n.get("status") or "novo", obs=n.get("obs", ""),
                            buscas=[busca["id"]], criado_em=agora, atualizado_em=agora, ultimo_contato=None,
                            nicho=", ".join(busca["parametros"]["nichos"]),
                            historico=[{"t": agora, "tipo": "criado",
                                        "txt": f"Encontrado na busca “{', '.join(busca['parametros']['nichos'])}”"}])
                if lead["obs"]:
                    lead["historico"].append({"t": agora, "tipo": "nota", "txt": lead["obs"]})
                leads[lid] = lead
            if lid not in ids:
                ids.append(lid)
    return ids


# ── Enriquecimento a partir do site (emails, WhatsApp, redes) ──────────────────
CONTATO_RE = re.compile(r"contato|fale|sobre|quem-somos|quem_somos|atendimento|contact|about", re.I)
CAMINHOS = ("/contato", "/fale-conosco", "/sobre", "/quem-somos", "/contact")

def links_contato(html, base):
    if not base.startswith(("http://", "https://")):
        base = "http://" + base
    host, out = kit._host(base), []
    for href, txt in kit.HREF_RE.findall(html or ""):
        if not CONTATO_RE.search(href + " " + txt):
            continue
        url = urllib.parse.urldefrag(urllib.parse.urljoin(base, href.strip()))[0]
        if url.startswith(("http://", "https://")) and kit._host(url) == host and url not in out:
            out.append(url)
    for p in CAMINHOS:
        url = urllib.parse.urljoin(base, p)
        if len(out) < 3 and url not in out:
            out.append(url)
    return out[:3]

def enriquecer(lead, redes):
    site = lead["site"]
    if not site or any(h in site for h in ("instagram.com", "facebook.com", "wa.me", "whatsapp.com", "linktr.ee")):
        # o "site" é na verdade uma rede social / link de WhatsApp: aproveita direto
        if "instagram.com" in site: lead["instagram"] = site
        elif "facebook.com" in site: lead["facebook"] = site
        wa = whatsapp_em(site)
        if wa: lead["whatsapp"], lead["whatsapp_origem"] = wa, "site"
        return
    home = kit._fetch_cached(site)
    if not home:
        return
    wa = whatsapp_em(home)
    if wa and (not lead["whatsapp"] or lead["whatsapp_origem"] == "telefone"):
        lead["whatsapp"], lead["whatsapp_origem"] = wa, "site"
    if redes:
        for k, v in kit._find_socials(home).items():
            lead[k] = lead[k] or v
    if not lead["email"]:
        achados = kit.extract_emails(home, site)
        if not achados:
            paginas = "".join(kit._fetch_html(u, timeout=8) for u in links_contato(home, site))
            achados = kit.extract_emails(paginas, site)
            if not lead["whatsapp"]:
                wa = whatsapp_em(paginas)
                if wa: lead["whatsapp"], lead["whatsapp_origem"] = wa, "site"
        lead["email"] = ", ".join(achados)


# ── Execução das buscas ────────────────────────────────────────────────────────
class Cancelada(Exception):
    pass

def atualizar(b, **kw):
    with lock:
        b.update(kw)
        b["atualizado_em"] = time.time()

def rodar_job(b, corpo, rotulo):
    _, raw = kit.req("POST", "/api/v1/jobs", corpo)
    jid = json.loads(raw).get("id")
    if not jid:
        raise RuntimeError("O motor não devolveu id do job.")
    with lock:
        b["jobs_motor"].append(jid)
    inicio = time.time()
    while True:
        if b.get("cancelar"):
            raise Cancelada()
        _, raw = kit.req("GET", f"/api/v1/jobs/{jid}")
        st = json.loads(raw).get("Status")
        atualizar(b, etapa=f"{rotulo} — {int(time.time() - inicio)}s")
        if st == "ok":
            break
        if st == "failed":
            raise RuntimeError("O Google recusou a busca (possível bloqueio temporário). Espere alguns minutos.")
        if time.time() - inicio > corpo["max_time"] + 300:
            raise RuntimeError("Tempo esgotado esperando o motor.")
        time.sleep(5)
    _, raw = kit.req("GET", f"/api/v1/jobs/{jid}/download")
    return list(csv.DictReader(io.StringIO(raw.decode("utf-8", "replace"))))

def executar(b):
    p = b["parametros"]
    t = TAMANHOS[p["tamanho"]]
    atualizar(b, estado="rodando", etapa="Localizando a cidade no mapa…", iniciado_em=time.time(), parcial=0)
    geo = localizar(p["cidade"], p["uf"], p.get("bairro"))
    if not geo:
        raise RuntimeError(f"Não encontrei \"{p['cidade']} - {p['uf']}\" no mapa.")
    lat, lon, bbox = geo
    onde = f"{p['bairro']}, {p['cidade']} - {p['uf']}" if p.get("bairro") else f"{p['cidade']} - {p['uf']}"
    corpo = {"name": f"painel:{b['id'][:8]}", "keywords": [f"{n} em {onde}" for n in p["nichos"]],
             "lang": "pt", "zoom": 15, "lat": str(lat), "lon": str(lon), "fast_mode": False,
             "radius": 3000 if p.get("bairro") else 10000,
             "depth": t["depth"], "email": True, "max_time": t["max_time"]}
    usa_grid = t["grid"] and bbox and not p.get("bairro")
    celulas = kit.grid_cells(bbox, t["grid"]) if usa_grid else [None]
    linhas = []
    for i, cel in enumerate(celulas, 1):
        rotulo = (f"Buscando no Google Maps — região {i}/{len(celulas)}" if len(celulas) > 1
                  else "Buscando no Google Maps")
        atualizar(b, progresso={"atual": i - 1, "total": len(celulas), "fase": "maps"})
        try:
            novas = rodar_job(b, dict(corpo, **cel) if cel else corpo, rotulo)
        except Cancelada:
            raise
        except Exception as e:
            if len(celulas) == 1:
                raise
            with lock:
                b["avisos"].append(f"Região {i} pulada: {e}")
            continue
        linhas = kit.dedupe(linhas + novas)
        atualizar(b, parcial=len(linhas))
    if usa_grid:
        linhas = [r for r in linhas if kit.in_bbox(r, bbox)]
    novos = [lead_de(r) for r in linhas]

    com_site = [l for l in novos if l["site"]]
    feitos = 0
    atualizar(b, etapa=f"Visitando sites atrás de e-mail e WhatsApp — 0/{len(com_site)}",
              progresso={"atual": 0, "total": len(com_site), "fase": "sites"})
    with ThreadPoolExecutor(max_workers=8) as ex:
        for _ in ex.map(lambda l: enriquecer(l, p.get("redes", True)), com_site):
            feitos += 1
            if b.get("cancelar"):
                raise Cancelada()
            atualizar(b, etapa=f"Visitando sites atrás de e-mail e WhatsApp — {feitos}/{len(com_site)}",
                      progresso={"atual": feitos, "total": len(com_site), "fase": "sites"})
    ids = mesclar_leads(b, novos)
    ja_tinha = sum(1 for i in ids if len(leads[i]["buscas"]) > 1)
    atualizar(b, lead_ids=ids, novos=len(ids) - ja_tinha, estado="concluida", etapa="Concluída",
              concluido_em=time.time(), progresso=None)
    salvar_leads()

def trabalhador():
    while True:
        with fila_cond:
            while not fila:
                fila_cond.wait()
            bid = fila.pop(0)
            b = buscas.get(bid)
        if not b or b.get("cancelar"):
            continue
        try:
            executar(b)
        except Cancelada:
            atualizar(b, estado="cancelada", etapa="Cancelada", progresso=None)
        except urllib.error.HTTPError as e:
            atualizar(b, estado="erro", progresso=None,
                      etapa=f"O motor recusou a busca (HTTP {e.code}: {e.read().decode(errors='replace')[:200]})")
        except urllib.error.URLError as e:
            atualizar(b, estado="erro", progresso=None,
                      etapa=f"Motor fora do ar ({e.reason}). Abra o Docker e rode: docker compose up -d")
        except Exception as e:
            atualizar(b, estado="erro", etapa=str(e), progresso=None)
        salvar_busca(b)


# ── Visões para a API ──────────────────────────────────────────────────────────
def resumo_busca(b):
    ls = [leads[i] for i in b.get("lead_ids", []) if i in leads]
    out = {k: b.get(k) for k in ("id", "parametros", "estado", "etapa", "progresso", "criado_em",
                                 "iniciado_em", "concluido_em", "avisos", "parcial", "novos")}
    out.update(total=len(ls),
               com_whatsapp=sum(1 for l in ls if l["whatsapp"]),
               com_email=sum(1 for l in ls if l["email"]),
               sem_site=sum(1 for l in ls if not l["site"]),
               posicao_fila=(fila.index(b["id"]) + 1) if b["id"] in fila else 0)
    return out

def lead_publico(l):
    return {k: v for k, v in l.items() if k != "historico"} | {"n_hist": len(l.get("historico", []))}

def painel_inicio():
    with lock:
        ls = list(leads.values())
        por_status = {s: 0 for s in STATUS_LEAD}
        for l in ls:
            por_status[l["status"]] = por_status.get(l["status"], 0) + 1
        def top(campo, n=8):
            c = {}
            for l in ls:
                if l.get(campo):
                    c[l[campo]] = c.get(l[campo], 0) + 1
            return sorted(c.items(), key=lambda x: -x[1])[:n]
        eventos = []
        for l in ls:
            for e in l.get("historico", []):
                if e["tipo"] != "criado":
                    eventos.append(e | {"lead": l["id"], "nome": l["nome"]})
        eventos.sort(key=lambda e: -e["t"])
        semana = time.time() - 7 * 86400
        return {
            "total": len(ls),
            "com_whatsapp": sum(1 for l in ls if l["whatsapp"]),
            "com_email": sum(1 for l in ls if l["email"]),
            "sem_site": sum(1 for l in ls if not l["site"]),
            "por_status": por_status,
            "contatos_semana": sum(1 for e in eventos if e["t"] >= semana and e["tipo"] == "whatsapp"),
            "novos_semana": sum(1 for l in ls if l["criado_em"] >= semana),
            "cidades": top("cidade"), "bairros": top("bairro"), "categorias": top("categoria"),
            "eventos": eventos[:12],
            "buscas_ativas": sum(1 for b in buscas.values() if b["estado"] in ("rodando", "na_fila")),
        }

def registrar(l, tipo, txt):
    agora = time.time()
    l.setdefault("historico", []).append({"t": agora, "tipo": tipo, "txt": txt})
    l["atualizado_em"] = agora
    if tipo == "whatsapp":
        l["ultimo_contato"] = agora

def motor_ok():
    try:
        kit.req("GET", "/api/v1/jobs")
        return True
    except Exception:
        return False


# ── HTTP ───────────────────────────────────────────────────────────────────────
class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _envia(self, code, corpo, tipo="application/json; charset=utf-8"):
        dados = corpo if isinstance(corpo, bytes) else json.dumps(corpo, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", tipo)
        self.send_header("Content-Length", str(len(dados)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(dados)

    def _corpo(self):
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n) or b"{}")

    def _rota(self):
        return urllib.parse.urlparse(self.path).path

    def do_GET(self):
        path = self._rota()
        if path in ("/", "/index.html"):
            with open(os.path.join(HERE, "index.html"), "rb") as f:
                return self._envia(200, f.read(), "text/html; charset=utf-8")
        if path == "/api/status":
            return self._envia(200, {"motor": motor_ok(), "fila": len(fila)})
        if path == "/api/municipios":
            return self._envia(200, [{k: m[k] for k in ("n", "uf", "ddd", "cap")} for m in municipios()])
        if path == "/api/inicio":
            return self._envia(200, painel_inicio())
        if path == "/api/config":
            return self._envia(200, config)
        if path == "/api/buscas":
            with lock:
                lista = sorted((resumo_busca(b) for b in buscas.values()), key=lambda x: -x["criado_em"])
            return self._envia(200, lista)
        m = re.fullmatch(r"/api/buscas/([\w-]+)", path)
        if m and m.group(1) in buscas:
            with lock:
                b = buscas[m.group(1)]
                return self._envia(200, resumo_busca(b) | {"lead_ids": b.get("lead_ids", [])})
        if path == "/api/leads":
            with lock:
                return self._envia(200, [lead_publico(l) for l in leads.values()])
        m = re.fullmatch(r"/api/leads/([\w-]+)", path)
        if m and m.group(1) in leads:
            with lock:
                return self._envia(200, leads[m.group(1)])
        self._envia(404, {"erro": "não encontrado"})

    def do_POST(self):
        path = self._rota()
        if path == "/api/buscas":
            d = self._corpo()
            nichos = [n.strip() for n in re.split(r"[\n,;]", d.get("nichos", "")) if n.strip()][:10]
            if not nichos or not d.get("cidade") or not d.get("uf"):
                return self._envia(400, {"erro": "Informe o nicho e a cidade."})
            if d.get("tamanho") not in TAMANHOS:
                d["tamanho"] = "padrao"
            bid = uuid.uuid4().hex
            b = {"id": bid, "criado_em": time.time(), "estado": "na_fila", "etapa": "Na fila",
                 "parametros": {"nichos": nichos, "cidade": d["cidade"].strip(), "uf": d["uf"].strip().upper(),
                                "bairro": (d.get("bairro") or "").strip(), "tamanho": d["tamanho"],
                                "redes": bool(d.get("redes", True))},
                 "jobs_motor": [], "avisos": [], "lead_ids": [], "progresso": None}
            with fila_cond:
                buscas[bid] = b
                fila.append(bid)
                fila_cond.notify()
            salvar_busca(b)
            return self._envia(201, resumo_busca(b))
        m = re.fullmatch(r"/api/buscas/([\w-]+)/(cancelar|repetir)", path)
        if m and m.group(1) in buscas:
            b = buscas[m.group(1)]
            with fila_cond:
                if m.group(2) == "cancelar":
                    b["cancelar"] = True
                    if b["id"] in fila:
                        fila.remove(b["id"])
                        b["estado"], b["etapa"] = "cancelada", "Cancelada"
                elif b["estado"] not in ("rodando", "na_fila"):
                    b.update(estado="na_fila", etapa="Na fila", cancelar=False, avisos=[], progresso=None)
                    fila.append(b["id"])
                    fila_cond.notify()
            salvar_busca(b)
            return self._envia(200, resumo_busca(b))
        m = re.fullmatch(r"/api/leads/([\w-]+)/evento", path)
        if m and m.group(1) in leads:
            d, l = self._corpo(), leads[m.group(1)]
            with lock:
                tipo = d.get("tipo") if d.get("tipo") in ("whatsapp", "ligacao", "email", "nota") else "nota"
                txt = str(d.get("txt") or "")[:2000]
                if tipo == "nota" and not txt.strip():
                    return self._envia(400, {"erro": "Escreva a anotação."})
                registrar(l, tipo, txt)
                if tipo in ("whatsapp", "ligacao", "email") and l["status"] == "novo" and config.get("auto_contatado", True):
                    l["status"] = "contatado"
                    registrar(l, "status", "Status: Contatado")
            salvar_leads()
            return self._envia(200, l)
        if path == "/api/leads/lote":
            d = self._corpo()
            if d.get("status") not in STATUS_LEAD:
                return self._envia(400, {"erro": "status inválido"})
            n = 0
            with lock:
                for lid in d.get("ids", []):
                    l = leads.get(lid)
                    if l and l["status"] != d["status"]:
                        l["status"] = d["status"]
                        registrar(l, "status", f"Status: {NOME_STATUS[d['status']]}")
                        n += 1
            salvar_leads()
            return self._envia(200, {"alterados": n})
        self._envia(404, {"erro": "não encontrado"})

    def do_PATCH(self):
        m = re.fullmatch(r"/api/leads/([\w-]+)", self._rota())
        if not m or m.group(1) not in leads:
            return self._envia(404, {"erro": "não encontrado"})
        d, l = self._corpo(), leads[m.group(1)]
        with lock:
            if d.get("status") in STATUS_LEAD and d["status"] != l["status"]:
                l["status"] = d["status"]
                registrar(l, "status", f"Status: {NOME_STATUS[d['status']]}")
            if "obs" in d:
                l["obs"] = str(d["obs"])[:2000]
                l["atualizado_em"] = time.time()
        salvar_leads()
        self._envia(200, l)

    def do_PUT(self):
        if self._rota() != "/api/config":
            return self._envia(404, {"erro": "não encontrado"})
        d = self._corpo()
        tpls = [{"id": str(t.get("id") or uuid.uuid4().hex[:8]), "nome": str(t.get("nome") or "Sem nome")[:80],
                 "texto": str(t.get("texto") or "")[:2000]} for t in d.get("templates", [])][:30]
        with lock:
            config["templates"] = tpls or CONFIG_PADRAO["templates"]
            ids = [t["id"] for t in config["templates"]]
            config["padrao"] = d.get("padrao") if d.get("padrao") in ids else ids[0]
            config["auto_contatado"] = bool(d.get("auto_contatado", True))
        salvar_config()
        self._envia(200, config)

    def do_DELETE(self):
        m = re.fullmatch(r"/api/buscas/([\w-]+)", self._rota())
        if not m or m.group(1) not in buscas:
            return self._envia(404, {"erro": "não encontrado"})
        manter_trabalhados = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("leads") != ["apagar"]
        with lock:
            b = buscas.pop(m.group(1))
            b["cancelar"] = True
            if b["id"] in fila:
                fila.remove(b["id"])
            for lid in b.get("lead_ids", []):
                l = leads.get(lid)
                if not l:
                    continue
                if b["id"] in l["buscas"]:
                    l["buscas"].remove(b["id"])
                trabalhado = l["status"] != "novo" or l.get("obs") or len(l.get("historico", [])) > 1
                if not l["buscas"] and not (manter_trabalhados and trabalhado):
                    del leads[lid]
        try:
            os.remove(os.path.join(DIR_BUSCAS, f"{b['id']}.json"))
        except OSError:
            pass
        salvar_leads()
        for jid in b.get("jobs_motor", []):
            try:
                kit.req("DELETE", f"/api/v1/jobs/{jid}")
            except Exception:
                pass
        self._envia(200, {"ok": True})


def main():
    carregar()
    threading.Thread(target=trabalhador, daemon=True).start()
    srv = ThreadingHTTPServer(("127.0.0.1", PORT), H)
    try:  # o navegador pode resolver "localhost" como ::1 (IPv6); continua só local
        class H6(ThreadingHTTPServer):
            address_family = socket.AF_INET6
        threading.Thread(target=H6(("::1", PORT), H).serve_forever, daemon=True).start()
    except OSError:
        pass
    url = f"http://localhost:{PORT}"
    print(f"Painel de prospecção rodando em {url}  (Ctrl+C para parar)")
    if not motor_ok():
        print("⚠  Motor fora do ar em", kit.BASE, "— abra o Docker e rode: docker compose up -d")
    if "--sem-navegador" not in sys.argv:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
