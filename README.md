# Lean Ridgelet

Lean formalization of integral representations of depth-2 fully-connected neural networks and
ridgelet transforms. The current focus is the L2 theory of ridgelet transforms, including its
Fourier--dilation coordinates, synthesis and ridgelet operators, general solution, and standard
activation functions.

- [Blueprint and API documentation](https://shosonoda.github.io/lean-ridgelet/)
- [L1 theory (arXiv:1505.03654)](https://arxiv.org/abs/1505.03654)
- [L2 theory source project](https://github.com/shosonoda/-draft-Ghosts)

The public repository is a reproducible mirror of the private development repository. Private
development notes and local source PDFs are intentionally absent from this repository and its Git
history.

## Build the Lean project

The project uses Lean and Mathlib v4.32.0.

```bash
lake exe cache get
lake build
```

Run the repository-wide audit for proof placeholders, kernel axioms, and proposition-valued fields
in project-defined structures and typeclasses with:

```bash
./scripts/audit-assumptions.sh
```

## Build the documentation

Generate the Verso Blueprint with:

```bash
./scripts/build-blueprint.sh
```

The entry page is `_out/blueprint/html-multi/index.html`. It links to six separately rendered
chapters whose nodes connect the informal statements to their Lean declarations.

Generate the doc-gen4 API documentation with:

```bash
./scripts/build-docs.sh
```

The API entry page is `docbuild/.lake/build/doc/index.html`. The first build generates documentation
for imported Mathlib modules as well as `LeanRidgelet`, so it can take several minutes.

## Repository layout

- `LeanRidgelet/`: formal definitions and proofs
- `LeanRidgeletBlueprint/`: Verso Blueprint chapters
- `audit/`: machine-checked assumption audit
- `docbuild/`: isolated doc-gen4 Lake project
- `scripts/`: build and audit commands

Generated build and documentation trees are ignored by Git. GitHub Pages builds them in Actions and
deploys them as an artifact, keeping hundreds of megabytes of imported API pages out of Git history.
