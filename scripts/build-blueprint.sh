#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/build-blueprint.sh

Build the ten-chapter Verso Blueprint: the L2 theory, the L1 theory, and the Mathlib upstream
candidates. The development and public builds are the same document.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
  shift
done

lake build LeanRidgeletBlueprint.Assembly:olean
rm -rf _out/blueprint
lake lean LeanRidgeletBlueprintMain.lean -- \
  --run LeanRidgeletBlueprintMain.lean --output _out/blueprint

test -f _out/blueprint/html-multi/index.html
test -f _out/blueprint/html-multi/-verso-data/blueprint-manifest.json

chapters=(
  overview
  foundations
  fourier-dilation
  operators
  general-solution
  activations
  further-results
  overview-l1
  l1-theory
  to-mathlib
)

for chapter in "${chapters[@]}"; do
  test -f "_out/blueprint/html-multi/$chapter/index.html"
done

python3 scripts/postprocess-blueprint.py _out/blueprint

grep -q 'class="split-toc book"' \
  _out/blueprint/html-multi/index.html
grep -q 'bp_external_decl_implementation' \
  _out/blueprint/html-multi/foundations/index.html
