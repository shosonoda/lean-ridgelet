# Lean Ridgelet

<!-- BEGIN GENERATED BADGES -->
<p align="center"><a href="https://github.com/shosonoda/lean-ridgelet/actions/workflows/audit.yml"><img alt="Assumption audit" src="https://img.shields.io/github/actions/workflow/status/shosonoda/lean-ridgelet/audit.yml?branch=main&amp;label=assumption%20audit&amp;style=flat-square"></a> <a href="https://lean-lang.org/"><img alt="Lean 4.32.0" src="https://img.shields.io/badge/Lean-4.32.0-0f4c81.svg?style=flat-square"></a> <a href="https://arxiv.org/abs/2106.04770v2"><img alt="arXiv 2106.04770v2" src="https://img.shields.io/badge/arXiv-2106.04770v2-b31b1b.svg?style=flat-square"></a> <a href="LICENSE"><img alt="Apache 2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square"></a></p>
<!-- END GENERATED BADGES -->

Lean formalization of integral representations and ridgelet transforms. It covers the L1 and L2
theories for fully-connected networks, the Fourier-slice method across several architectures, and
the developing harmonic-analysis/Schur method. Each theory separates a publication-order roadmap
from implementation modules arranged by Lean dependency.

The Fourier-slice part reaches the networks on noncompact symmetric spaces, so the
upstream-candidate layer carries a Helgason--Fourier transform with the geometry as data, together
with the two concrete models it is instantiated at: the Poincaré ball model of real hyperbolic
space, and the manifold of positive definite matrices in the coordinates of Terras' power function.
Mathlib has neither model, and none of the group theory behind the transform, so the composite
distance and the constant enter as arguments and the inversion formula on each space is a definite
proposition rather than an axiom.

- [Verso Blueprint](https://shosonoda.github.io/lean-ridgelet/)
- [L1 theory (arXiv:1505.03654)](https://arxiv.org/abs/1505.03654)
- [L2 theory (arXiv:2106.04770v2)](https://arxiv.org/abs/2106.04770v2)
- [Fourier-slice method (arXiv:2402.15984)](https://arxiv.org/abs/2402.15984)
- [Harmonic-analysis/Schur method (arXiv:2405.13682)](https://arxiv.org/abs/2405.13682)

The public repository is a reproducible mirror of the private development repository. Private
development notes and local source PDFs are intentionally absent from this repository and its Git
history.

## Build the Lean project

The project uses Lean and Mathlib v4.32.0.

```bash
lake exe cache get
lake build
```

The Lean badge is generated from the version pinned in `lean-toolchain`. After changing that file,
refresh and check the generated badge block with:

```bash
python3 scripts/update-readme-badges.py
python3 scripts/update-readme-badges.py --check
```

Run the repository-wide audit for proof placeholders, kernel axioms, and proposition-valued fields
in project-defined structures and typeclasses with:

```bash
./scripts/audit-assumptions.sh
```

The `Assumption audit` badge reports the dedicated GitHub Actions workflow that runs this command.

## Build the documentation

Generate the Verso Blueprint with:

```bash
./scripts/build-blueprint.sh
```

The build is incremental. `LeanRidgeletBlueprint/Parts/` provides separate cached subtrees for
L2, L1, Fourier slice, and ToMathlib. Child pages use topic-specific imports, and ToMathlib is
split into eight independent analytic, geometric, and representation-theoretic pages. Lake can
therefore reuse unrelated page and subtree `.olean` files. The rendered site is cached under
`_out/blueprint-cache/`; an unchanged input fingerprint skips regeneration and postprocessing.
Use `./scripts/build-blueprint.sh --force` for a complete regeneration.

Preview the complete generated site through a local HTTP server:

```bash
python3 -m http.server 8000 --directory _out/blueprint
```

Then open <http://localhost:8000/html-multi/>. Verso's standard multi-page renderer preserves a
four-part hierarchy with twenty-three theory pages. Its nodes connect the informal statements to
their Lean declarations. A direct page URL is, for example,
<http://localhost:8000/html-multi/l2/foundations/>. Stop the server with `Ctrl-C`. Serving over
HTTP ensures that Blueprint preview data and browser modules are loaded correctly. The left
sidebar is Verso's generated table of contents: L2, L1, Fourier slice, and ToMathlib are the
top-level parts, with overview, detail, or topic pages nested beneath them. The development-only
harmonic-analysis part is not included in this mirror.

Two generated chapters follow them. <http://localhost:8000/html-multi/Dependency-Graph/> draws
every Blueprint node and its `(uses := ...)` edges, coloured by formalization status;
<http://localhost:8000/html-multi/Blueprint-Summary/> reports coverage counts, the most-used
statements, and the nodes that carry no Lean declaration yet. The graph page loads `d3` and
`d3-graphviz` from a CDN at view time and therefore needs network access in the browser.

Definition panels include the Lean implementation beginning at `:=` when the declaration belongs
to this project.

## Repository layout

- `LeanRidgelet/`: formal definitions and proofs
- `LeanRidgeletBlueprint/`: Verso Blueprint chapters
- `audit/`: machine-checked assumption audit
- `scripts/`: build and audit commands

Generated build and documentation trees are ignored by Git. GitHub Pages builds the Blueprint in
Actions and deploys it as an artifact.
