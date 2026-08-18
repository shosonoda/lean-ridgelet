import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Mathlib upstream candidates" =>
%%%
file := "to-mathlib"
%%%

This chapter collects the general-purpose results developed for the ridgelet formalization and
staged for upstreaming to Mathlib. They import only Mathlib and carry no dependence on the
ridgelet theories.

The sections are separate Lean modules and cache boundaries: `Lp` and measure transport; Radon
and Fourier transforms; supporting integral and Fourier tools; Schwartz space and convolution;
finite Fourier and Euclidean geometry; unitary representations and topological groups; invariant
geometry and integration; and symmetric spaces with the Helgason--Fourier transform. A change in
one independent topic therefore leaves the unrelated Blueprint section objects reusable.

A survey of the pinned Mathlib version confirmed the principal gaps represented here. Mathlib has
no Radon or `d`-plane transform, Fourier slice theorem, Hilbert transform, general Young
convolution inequality on `Lp`, or matrix polar integration formula. The child sections state the
precise generality and proof strategy of each upstream candidate.
