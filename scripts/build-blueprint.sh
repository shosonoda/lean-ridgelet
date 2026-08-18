#!/usr/bin/env bash

set -euo pipefail

mode=auto
force=false

usage() {
  cat <<'EOF'
Usage: scripts/build-blueprint.sh [--development|--public] [--force]

Build the hierarchical Verso Blueprint: independent L2, L1, Fourier-slice, harmonic-analysis, and
ToMathlib subtrees followed by the generated Dependency Graph and Blueprint Summary. No subtree is
development-only at present, so both modes build the same document; the two assemblies stay separate
so that the next unstable subtree can be held back. With no option, private-only directories select
the development build; otherwise public mode is used.

The generated site and Lake-built generator are cached. Pass --force to regenerate the site even
when its mode-specific input fingerprint is unchanged.
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
    --force)
      force=true
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

if rg -n '^import LeanRidgelet$' LeanRidgeletBlueprint/Chapters; then
  echo 'Blueprint chapters must use theory-specific imports, not the LeanRidgelet umbrella' >&2
  exit 1
fi

mkdir -p _out/blueprint-cache
cache_root="_out/blueprint-cache/$mode"
active_root="_out/blueprint"
fingerprint_file="$cache_root/.build-fingerprint"

fingerprint_inputs() {
  printf '%s\n' "mode=$mode" 'blueprint-cache-format=2'
  for path in lean-toolchain lakefile.toml lake-manifest.json \
      scripts/build-blueprint.sh scripts/postprocess-blueprint.py \
      LeanRidgelet.lean LeanRidgeletBlueprint.lean LeanRidgeletBlueprintMain.lean; do
    if [[ -f "$path" ]]; then
      shasum -a 256 "$path"
    fi
  done
  while IFS= read -r path; do
    shasum -a 256 "$path"
  done < <(find LeanRidgelet LeanRidgeletBlueprint -type f -name '*.lean' | LC_ALL=C sort)
}

fingerprint="$(fingerprint_inputs | shasum -a 256 | awk '{print $1}')"

activate_cache() {
  rm -rf "$active_root"
  ln -s "blueprint-cache/$mode" "$active_root"
}

cached_fingerprint=
if [[ -f "$fingerprint_file" ]]; then
  IFS= read -r cached_fingerprint < "$fingerprint_file" || true
fi

if ! "$force" && [[ "$cached_fingerprint" == "$fingerprint" ]]; then
  echo "Reusing cached $mode Blueprint output."
  activate_cache
else
  lake build "$assembly_target"
  work_root="$(mktemp -d "_out/.blueprint-$mode.XXXXXX")"
  cleanup() {
    if [[ -n "${work_root:-}" && -e "$work_root" ]]; then
      rm -rf "$work_root"
    fi
  }
  trap cleanup EXIT
  lake lean "$main_source" -- \
    --run "$main_source" --output "$work_root"

  postprocess_args=("$work_root")
  if [[ "$mode" == public ]]; then
    postprocess_args+=(--published-only)
  fi
  python3 scripts/postprocess-blueprint.py "${postprocess_args[@]}"
  printf '%s\n' "$fingerprint" > "$work_root/.build-fingerprint"

  rm -rf "$cache_root"
  mv "$work_root" "$cache_root"
  work_root=
  activate_cache
fi

test -f _out/blueprint/html-multi/index.html
test -f _out/blueprint/html-multi/-verso-data/blueprint-manifest.json

pages=(
  l2
  l2/overview
  l2/foundations
  l2/fourier-dilation
  l2/operators
  l2/general-solution
  l2/activations
  l2/further-results
  l1
  l1/overview-l1
  l1/l1-theory
  fs
  fs/overview-fs
  fs/fs-theory
)

pages+=(
  ha
  ha/overview-ha
  ha/ha-representations
  ha/ha-affine
  ha/ha-architectures
)

pages+=(
  to-mathlib
  to-mathlib/measure-lp
  to-mathlib/radon-fourier
  to-mathlib/integral-fourier-tools
  to-mathlib/schwartz-convolution
  to-mathlib/finite-euclidean
  to-mathlib/representations
  to-mathlib/invariant-geometry
  to-mathlib/symmetric-spaces
  Dependency-Graph
  Blueprint-Summary
)

for page in "${pages[@]}"; do
  test -f "_out/blueprint/html-multi/$page/index.html"
done

grep -q 'class="split-toc book"' \
  _out/blueprint/html-multi/index.html
grep -q 'bp_external_decl_implementation' \
  _out/blueprint/html-multi/l2/foundations/index.html
grep -q 'bp_graph_legend' \
  _out/blueprint/html-multi/Dependency-Graph/index.html
grep -q 'bp_summary_grid' \
  _out/blueprint/html-multi/Blueprint-Summary/index.html

test -e _out/blueprint/html-multi/ha/overview-ha
test -e _out/blueprint/html-multi/ha/ha-representations
test -e _out/blueprint/html-multi/ha/ha-affine
test -e _out/blueprint/html-multi/ha/ha-architectures

if ! rg -q 'ha_main_reconstruction|ha_reconstruction_detail' \
    _out/blueprint/html-multi/Dependency-Graph/index.html \
    _out/blueprint/html-multi/Blueprint-Summary/index.html; then
  echo 'harmonic-analysis nodes are missing from the generated chapters' >&2
  exit 1
fi
