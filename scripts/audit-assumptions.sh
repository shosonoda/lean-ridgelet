#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# Source-level guard. Files listed here are the only ones allowed to contain a placeholder;
# which named declarations may use it is decided by `permittedSorryDeclarations` in
# `audit/Assumptions.lean`, checked below. Keep the two lists in sync.
sorry_files=(
  '!OverviewL2.lean'
  '!**/FS/Targets.lean'
)

globs=('--glob' '*.lean')
for f in "${sorry_files[@]}"; do
  globs+=('--glob' "$f")
done

if rg -n \
  '^[[:space:]]*(axiom|axioms|sorry|admit)\b|:=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\b' \
  LeanRidgelet "${globs[@]}"
then
  echo 'assumption audit failed: untracked source-level axiom or proof placeholder found' >&2
  exit 1
fi

lake build
lake env lean audit/Assumptions.lean

echo 'assumption audit passed'
