#!/usr/bin/env bash

set -euo pipefail

lake build \
  LeanRidgelet \
  LeanRidgeletBlueprint \
  LeanRidgeletBlueprint.Chapters.Foundations \
  LeanRidgeletBlueprint.Chapters.FourierDilation \
  LeanRidgeletBlueprint.Chapters.Operators \
  LeanRidgeletBlueprint.Chapters.GeneralSolution \
  LeanRidgeletBlueprint.Chapters.Activations \
  LeanRidgeletBlueprint.Chapters.FurtherResults
lake lean LeanRidgeletBlueprintMain.lean -- \
  --run LeanRidgeletBlueprintMain.lean --output _out/blueprint

test -f _out/blueprint/html-multi/index.html
test -f _out/blueprint/html-multi/-verso-data/blueprint-manifest.json

chapters=(
  foundations
  fourier-dilation
  operators
  general-solution
  activations
  further-results
)

for chapter in "${chapters[@]}"; do
  output="_out/blueprint/chapters/$chapter"
  lake lean LeanRidgeletBlueprintChaptersMain.lean -- \
    --run LeanRidgeletBlueprintChaptersMain.lean "$chapter" --output "$output"
  test -f "$output/html-multi/index.html"
  test -f "$output/html-multi/-verso-data/blueprint-manifest.json"
done
