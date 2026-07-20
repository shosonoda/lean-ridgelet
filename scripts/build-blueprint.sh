#!/usr/bin/env bash

set -euo pipefail

mode=auto

usage() {
  cat <<'EOF'
Usage: scripts/build-blueprint.sh [--development|--public]

Build the development Blueprint with the L1 Overview, or the seven-chapter public Blueprint.
With no option, private-only directories select the development build; otherwise public mode is
used.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --development)
      mode=development
      ;;
    --public)
      mode=public
      ;;
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

if [[ "$mode" == auto ]]; then
  if [[ -d 00note && -d 00data ]]; then
    mode=development
  else
    mode=public
  fi
fi

if [[ "$mode" == development ]]; then
  assembly_target=LeanRidgeletBlueprint.Assembly:olean
  main_source=LeanRidgeletBlueprintMain.lean
else
  assembly_target=LeanRidgeletBlueprint.PublicAssembly:olean
  main_source=LeanRidgeletBlueprint/PublicMain.lean
fi

lake build "$assembly_target"
rm -rf _out/blueprint
lake lean "$main_source" -- \
  --run "$main_source" --output _out/blueprint

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
)

if [[ "$mode" == development ]]; then
  chapters+=(overview-l1)
fi

for chapter in "${chapters[@]}"; do
  test -f "_out/blueprint/html-multi/$chapter/index.html"
done

postprocess_args=(_out/blueprint)
if [[ "$mode" == public ]]; then
  postprocess_args+=(--exclude-l1)
fi
python3 scripts/postprocess-blueprint.py "${postprocess_args[@]}"

grep -q 'class="split-toc book"' \
  _out/blueprint/html-multi/index.html
grep -q 'bp_external_decl_implementation' \
  _out/blueprint/html-multi/foundations/index.html

if [[ "$mode" == public ]]; then
  test ! -e _out/blueprint/html-multi/overview-l1
  if rg -q 'overview-l1|L1 theory: ridgelet transforms with unbounded activations' \
    _out/blueprint/html-multi
  then
    echo 'development-only L1 Blueprint content entered the public output' >&2
    exit 1
  fi
fi
