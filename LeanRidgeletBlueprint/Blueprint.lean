import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lean Ridgelet Blueprint" =>

This Blueprint connects the mathematical development of integral-representation neural networks
and ridgelet transforms with the declarations in `LeanRidgelet`. The first chapter lists the
numbered results in the general-first 2026-07-18 manuscript publication order; the following
chapters trace the dependency structure of the Lean development and use the current notation.
The final chapter maps the L1 theory of arXiv:1505.03654v2 — the weak ridgelet transform,
admissible pairs, and the universality of networks with unbounded activations — onto its
overview declarations.

The mathematical text follows the paper notation. In Lean, the opt-in scope
`LeanRidgelet.Paper` provides the space names `𝓐`, `𝓗`, and `𝓖`, together with `S[σ]`, `R[h]`,
`R[f; ρ]`, `L[σ]`, `𝐓`, `𝐓⁻`, the postfix Fourier notation `f♯`, and the Japanese-bracket
notations. These are notation aliases for the linked declarations, not a second API. Historical
identifiers such as `FiberSpace`, `fiberSynthesis`, and `fiberRidgelet` remain visible in the Lean
panels where they denote the coefficient space, the pointwise lift $`\widetilde L`, and the
simple-tensor map $`J_h`, respectively.

A node without an associated Lean declaration records work that remains to be formalized; it does
not introduce an assumption into the Lean development. The L1 chapter describes a parallel,
actively developed formalization, so its prose records the intended theorem boundary without
using proof completion as a measure of the chapter's mathematical coverage.
