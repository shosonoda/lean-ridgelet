#!/usr/bin/env bash

set -euo pipefail

cd docbuild
# The cached marker can hide newly imported project modules even after their `docInfo` is updated.
# Keep the expensive dependency data, but always regenerate the project-level aggregate HTML.
rm -f .lake/build/doc-data/LeanRidgelet--library.docs_built{,.trace,.hash}
DOCGEN_SRC=file lake build LeanRidgelet:docs

test -f .lake/build/doc/index.html
test -f .lake/build/doc/LeanRidgelet/Overview.html
