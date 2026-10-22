#!/bin/bash
# Dois cliques no Finder: liga o Docker, o motor de busca e o painel de prospecção.
cd "$(dirname "$0")"
if ! docker info >/dev/null 2>&1; then
  echo "Abrindo o Docker…"; open -a Docker
  until docker info >/dev/null 2>&1; do sleep 2; done
fi
docker compose up -d
exec python3 painel/server.py
