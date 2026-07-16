#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if rg -n \
  '^[[:space:]]*(axiom|axioms|sorry|admit)\b|:=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\b' \
  LeanRidgelet --glob '*.lean'
then
  echo 'assumption audit failed: source-level axiom or proof placeholder found' >&2
  exit 1
fi

lake build
lake env lean audit/Assumptions.lean

echo 'assumption audit passed'
