import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lean Ridgelet Blueprint" =>

This Blueprint connects the mathematical development of integral-representation neural networks
and ridgelet transforms with the declarations in `LeanRidgelet`. Each theory gets one *overview*
chapter, which lists the manuscript's definitions and numbered results in publication order with
a link to the declaration carrying each — the place to check what is formalized — followed by
*detail* chapters that trace the dependency structure of the Lean development and use the current
notation. The first chapter is the overview of arXiv:2106.04770v2, in its general-first
publication order.

The mathematical text follows the manuscript notation. In Lean, the opt-in scope
`LeanRidgelet.Notation` provides the space names `𝓐`, `𝓗`, `𝓖`, and `𝕐`, together with `S[σ]`,
`R[h]`, `R[f; ρ]`, `L[σ]`, `𝐓`, `𝐓⁻`, `𝓡[s; ψ]`, `𝓡†[s; η]`, `K[m; ψ, Fη]`, `Λ^m`, the postfix
Fourier notation `f♯`, and the Japanese-bracket notations. These are notation aliases for the linked declarations, not a second API. Historical
identifiers such as `FiberSpace`, `fiberSynthesis`, and `fiberRidgelet` remain visible in the Lean
panels where they denote the coefficient space, the pointwise lift $`\widetilde L`, and the
simple-tensor map $`J_h`, respectively.

A node without an associated Lean declaration records work that remains to be formalized; it does
not introduce an assumption into the Lean development.
