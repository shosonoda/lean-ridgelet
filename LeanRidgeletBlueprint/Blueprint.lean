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
overview declarations. A node without an associated Lean declaration records work that remains
to be formalized; it does not introduce an assumption into the Lean development.
