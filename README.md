# Lean Ridgelet

<!-- BEGIN GENERATED BADGES -->
<p align="center"><a href="https://github.com/shosonoda/lean-ridgelet/actions/workflows/audit.yml"><img alt="Assumption audit" src="https://img.shields.io/github/actions/workflow/status/shosonoda/lean-ridgelet/audit.yml?branch=main&amp;label=assumption%20audit&amp;style=flat-square"></a> <a href="https://lean-lang.org/"><img alt="Lean 4.32.0" src="https://img.shields.io/badge/Lean-4.32.0-0f4c81.svg?style=flat-square"></a> <a href="https://arxiv.org/abs/2106.04770v2"><img alt="arXiv 2106.04770v2" src="https://img.shields.io/badge/arXiv-2106.04770v2-b31b1b.svg?style=flat-square"></a> <a href="LICENSE"><img alt="Apache 2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square"></a></p>
<!-- END GENERATED BADGES -->

Lean formalization of integral representations of depth-2 fully-connected neural networks and
ridgelet transforms. The current focus is the L2 theory of ridgelet transforms, including the
unitary coordinate transform and its Fourier construction, synthesis and ridgelet operators,
general solutions, and standard activation functions.

- [Verso Blueprint](https://shosonoda.github.io/lean-ridgelet/)
- [L1 theory (arXiv:1505.03654)](https://arxiv.org/abs/1505.03654)
- [L2 theory (arXiv:2106.04770v2)](https://arxiv.org/abs/2106.04770v2)

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

Preview the complete generated site through a local HTTP server:

```bash
python3 -m http.server 8000 --directory _out/blueprint
```

Then open <http://localhost:8000/html-multi/>. Verso's standard multi-page renderer splits the
document into seven chapters whose nodes connect the informal statements to their Lean
declarations. A direct chapter URL is, for example,
<http://localhost:8000/html-multi/foundations/>. Stop the server with `Ctrl-C`. Serving over HTTP
ensures that Blueprint preview data and browser modules are loaded correctly.
The left sidebar is Verso's generated table of contents and links to all seven chapter pages.

Definition panels include the Lean implementation beginning at `:=` when the declaration belongs
to this project.

## Repository layout

- `LeanRidgelet/`: formal definitions and proofs
- `LeanRidgeletBlueprint/`: Verso Blueprint chapters
- `audit/`: machine-checked assumption audit
- `scripts/`: build and audit commands

Generated build and documentation trees are ignored by Git. GitHub Pages builds the Blueprint in
Actions and deploys it as an artifact.
