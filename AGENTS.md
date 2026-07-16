# Lean Ridgelet agent guide

This file applies to the whole repository. It is the stable entry point for resuming work in a new
thread, clone, or machine. Keep it short and operational; record changing details in the notes named
below instead of duplicating them here.

## Start here

1. Confirm that this is the private development repository, normally
   `shosonoda/lean-ridgelet-dev`. The public mirror is `shosonoda/lean-ridgelet`.
2. Read `00note/summary.md` for the current implementation state, outstanding `sorry`s, last
   verification results, and immediate next tasks.
3. Read the relevant part of `00note/plan.md` before changing mathematical scope, file structure,
   assumptions, Blueprint organization, or publication policy.
4. Read `README.md` for build, local documentation preview, assumption audit, and publication
   commands.
5. Inspect `git status --short` before editing. Preserve unrelated and user-owned changes. In
   particular, `00note/prompt.md` is an automatically accumulated user record; do not edit or stage
   it unless explicitly requested.

The public mirror intentionally omits `00note/` and `00data/`. When working from that repository,
use this file and `README.md`, then consult the private development repository before making a
change that depends on project history or source manuscripts.

## Mathematical sources of truth

- The current target is the depth-2 fully-connected L2 ridgelet theory, especially Chapters 2--5.
- In the private repository, `00data/ghost20260715.pdf` is authoritative for theorem statements,
  constants, ordering, and numbering.
- The LaTeX flow starts at `../-draft-Ghosts/main.tex`, `head.tex`, and the files included under
  `05journal/`. Use it to understand exposition and dependencies, but prefer the PDF if revisions
  disagree.
- The L1 reference is `00data/1505.03654v2.pdf` and its local source is
  `../arXiv-1505.03654v2`.

## Formalization policy

- Reuse Mathlib before introducing project-specific analytic infrastructure.
- Follow Mathlib naming and style conventions. Lean files use `UpperCamelCase`; theorem names use
  `snake_case`; definitions and data use `lowerCamelCase`.
- Do not encode an unproved analytic result as a structure field, typeclass field, or other strong
  assumption object.
- When a proof is not currently tractable, state the intended named theorem and use `sorry`. Keep
  every placeholder mechanically visible and update the exact allowlist in
  `audit/Assumptions.lean` only when the project deliberately accepts that named placeholder.
- Avoid `sorry` in definitions. Do not make unrelated declarations depend on an Overview
  placeholder merely to advance the build.
- Preserve the paper/Mathlib Fourier normalization distinction documented in `00note/plan.md`.
- Write operator application with explicit brackets in mathematical prose, for example
  `T[γ](x, ω)`, `S_σ[γ](x)`, and `R_q[f](x)`.

## Documentation policy

- Blueprint prose is English. Keep the numbered L2 results in publication order in
  `LeanRidgeletBlueprint/Chapters/Overview.lean`; organize later chapters by Lean dependency.
- Connect an informal node to an implemented declaration with strict `(lean := "...")` resolution.
  A node without a Lean declaration records future work and must not create a Lean assumption.
- The seven chapters form one standard Verso `Part` tree through
  `LeanRidgeletBlueprint/Assembly.lean`. Keep the standard `html-multi` page split, table of
  contents, chapter numbering, and previous/next navigation. Do not restore hand-written HTML
  navigation or seven independent Blueprint sites.
- `scripts/postprocess-blueprint.py` may expose project definition bodies and presentation fixes,
  but it must not synthesize the table of contents.
- After changing implementation status, theorem statements, or module organization, update the
  corresponding Blueprint nodes as part of the same task.

## Bootstrap and verification

On a fresh machine, install the Lean toolchain specified by `lean-toolchain`, then run:

```bash
lake update
lake exe cache get
lake build
```

Use the smallest relevant check while iterating. Before handing off a material Lean change, run:

```bash
./scripts/audit-assumptions.sh
```

For documentation changes, also run the relevant commands:

```bash
./scripts/build-blueprint.sh
./scripts/build-docs.sh
```

`build-docs.sh` can be expensive on a fresh machine. Do not discard a valid Mathlib or doc-gen4
cache without a demonstrated need. Always run `git diff --check` before committing.

## Keeping restart information current

- `00note/plan.md` is the development plan and records durable design decisions. Update it whenever
  the plan, milestones, assumptions policy, documentation architecture, or publication process
  changes.
- `00note/summary.md` is a replaceable snapshot of the repository. Update it after material work so
  its current files, theorem coverage, `sorry` count, verification results, and next tasks are true.
- Do not turn either file into a chronological work log. Git history carries history.
- If work stops with an external job in progress or a genuine blocker, record the exact command,
  URL/run identifier, completed checks, and remaining action in `00note/summary.md`.

## Private/public boundary

- Never publish `00note/`, `00data/`, PDFs, private prompts, or local manuscript clones.
- The public snapshot is controlled by the explicit allowlist in `scripts/publish-public.sh`, not by
  a broad copy with exclusions. Add a new public source path to that allowlist deliberately.
- Commit public-source changes in the private repository before running the publication script.
- In the private development repository, validate an existing build without publishing with:

```bash
./scripts/publish-public.sh --check --no-build
```

- Use `./scripts/publish-public.sh` only when publication is in scope. It writes to the sibling
  public clone and pushes its `main` branch.
- Keep GitHub Actions tuning and long-running log analysis separate from mathematical
  formalization work; use a lightweight model for that operational task when available.
