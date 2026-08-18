import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Fourier slice method" =>
%%%
file := "fs"
%%%

The architecture-independent derivation by the Fourier slice theorem. The overview follows
arXiv:2402.15984, while the detail section exposes the reusable Lean dependency chain.
