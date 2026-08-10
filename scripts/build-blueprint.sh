#!/usr/bin/env bash

set -euo pipefail

mode=auto

usage() {
  cat <<'EOF'
Usage: scripts/build-blueprint.sh [--development|--public]

Build the Verso Blueprint: the L2 theory, the L1 theory, the two chapters of Mathlib upstream
candidates, and the two Fourier slice chapters, followed by the generated Dependency Graph and
Blueprint Summary chapters. Both modes currently build the same document — nothing is
development-only — and the two-mode machinery is kept so that a future manuscript can be developed
privately without rebuilding it. With no option, private-only directories select the development
build; otherwise public mode is used.
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
  overview-l1
  l1-theory
  to-mathlib
  to-mathlib-lie
  overview-fs
  fs-theory
)

chapters+=(Dependency-Graph Blueprint-Summary)

for chapter in "${chapters[@]}"; do
  test -f "_out/blueprint/html-multi/$chapter/index.html"
done

postprocess_args=(_out/blueprint)
if [[ "$mode" == public ]]; then
  postprocess_args+=(--exclude-fs)
fi
python3 scripts/postprocess-blueprint.py "${postprocess_args[@]}"

grep -q 'class="split-toc book"' \
  _out/blueprint/html-multi/index.html
grep -q 'bp_external_decl_implementation' \
  _out/blueprint/html-multi/foundations/index.html
grep -q 'bp_graph_legend' \
  _out/blueprint/html-multi/Dependency-Graph/index.html
grep -q 'bp_summary_grid' \
  _out/blueprint/html-multi/Blueprint-Summary/index.html

# Nothing is development-only at present, so the public output is checked to contain the same
# chapters as the development one rather than fewer. Should a manuscript be developed privately
# again, list its chapters in `postprocess-blueprint.py` as development-only and reinstate a check
# here that they are absent from the public output.
if [[ "$mode" == public ]]; then
  test -e _out/blueprint/html-multi/overview-fs
  test -e _out/blueprint/html-multi/fs-theory
fi
