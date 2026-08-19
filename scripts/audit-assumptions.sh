#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# Source-level guard. Files listed here are the only ones allowed to contain a placeholder;
# which named declarations may use it is decided by `permittedSorryDeclarations` in
# `audit/Assumptions.lean`, checked below. Keep the two lists in sync.
source_files=()
while IFS= read -r -d '' path; do
  case "$path" in
    LeanRidgelet/OverviewL2.lean|LeanRidgelet/FS/Targets.lean|\
    LeanRidgelet/HA/QuadraticNonzero.lean)
      ;;
    *)
      source_files+=("$path")
      ;;
  esac
done < <(find LeanRidgelet -type f -name '*.lean' -print0)

if ((${#source_files[@]} > 0)) && grep -nHE \
  '^[[:space:]]*(axiom|axioms|sorry|admit)([^[:alnum:]_]|$)|:=[[:space:]]*(by[[:space:]]+)?(sorry|admit)([^[:alnum:]_]|$)' \
  "${source_files[@]}"
then
  echo 'assumption audit failed: untracked source-level axiom or proof placeholder found' >&2
  exit 1
fi

lake build
lake env lean audit/Assumptions.lean

echo 'assumption audit passed'
