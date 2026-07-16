#!/usr/bin/env bash

set -euo pipefail

cd docbuild
DOCGEN_SRC=file lake build LeanRidgelet:docs

test -f .lake/build/doc/index.html
