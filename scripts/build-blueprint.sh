#!/usr/bin/env bash

set -euo pipefail

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
)

for chapter in "${chapters[@]}"; do
  test -f "_out/blueprint/html-multi/$chapter/index.html"
done

python3 scripts/postprocess-blueprint.py _out/blueprint

grep -q 'class="split-toc book"' \
  _out/blueprint/html-multi/index.html
grep -q 'bp_external_decl_implementation' \
  _out/blueprint/html-multi/foundations/index.html
