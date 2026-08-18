/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Defs

/-!
# The Harish-Chandra `c`-function and the Plancherel density

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

The density of the Helgason--Fourier inversion formula is `|W|^{-1}|c(λ)|^{-2}`, where `|W|` is the
order of the Weyl group and `c` is Harish-Chandra's function. Two things about it have to be kept
apart, and this file is arranged so that they are.

*The `c`-function is an integral, not a formula.* Its definition is
`c(λ) = ∫_{N̄} e^{-(iλ+ϱ)(H(n̄))} dn̄`, and the Gindikin--Karpelevich product of Gamma factors
(Helgason, *Groups and Geometric Analysis*, Ch. IV, Thm 6.14) is a *theorem* about that integral.
Taking the integral as the definition is what keeps the normalization honest: the measure `dn̄` is
visible, and the constant of the inversion formula then has to come out of a proof rather than be
copied from a book. Copying is a real hazard here — Helgason normalizes `c` so that `c(-iϱ) = 1` in
the introduction of *Groups and Geometric Analysis* but writes the inversion formula of
*Geometric Analysis on Symmetric Spaces*, Ch. III, Thm 1.3 against a measure `dλ` on `𝔞*` that is
not Lebesgue measure, and the two conventions differ by a power of `π`.

*Only `|c(λ)|^{-2}` ever appears.* The inversion formula uses the modulus, and on the real form
`𝔞*` the modulus is computed from the reflection `c(-λ) = conj(c(λ))`, so `|c(λ)|^2 = c(λ)c(-λ)`.
That identity is recorded here as a lemma taking the reflection as a hypothesis, since the
reflection itself is a property of the integral in each model.

## Main definitions

* `SymmetricSpace.cFunctionIntegral`: `c(λ) = ∫_{N̄} e^{-(iλ+ϱ)(H(n̄))} dn̄`.
* `SymmetricSpace.plancherelDensity`: `κ(λ) = (|W| ‖c(λ)‖²)^{-1}`, the density of the inversion
  formula.

## Main results

* `SymmetricSpace.mul_neg_eq_normSq_of_conj`: `c(λ)c(-λ) = ‖c(λ)‖²` under the reflection
  `c(-λ) = conj(c(λ))`.
* `SymmetricSpace.plancherelDensity_pos`: the density is positive where `c` does not vanish.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace SymmetricSpace

/-! ## The Plancherel density

Only the modulus of the `c`-function ever enters the inversion formula, and the modulus needs no
structure on `𝔞*` at all, so this part is stated for a bare type. -/

section Density

variable {E : Type*}

/-- The density `κ(λ) = (|W| ‖c(λ)‖²)^{-1}` of the Helgason--Fourier inversion formula
(Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. III, Thm 1.3), built from the order `W` of
the Weyl group and the `c`-function.

The two ingredients are kept as separate arguments because the split between them is a convention:
`|W|` can be absorbed into `c`, and different sources do. What is invariant is the product. -/
def plancherelDensity (W : ℝ) (c : E → ℂ) (lam : E) : ℝ := (W * ‖c lam‖ ^ 2)⁻¹

theorem plancherelDensity_eq (W : ℝ) (c : E → ℂ) (lam : E) :
    plancherelDensity W c lam = (W * ‖c lam‖ ^ 2)⁻¹ := rfl

/-- The density is positive wherever the `c`-function does not vanish. Its zeros and poles are what
the Paley--Wiener theory of the transform is about; positivity away from them is all the inversion
formula needs in order to be read as a measure. -/
theorem plancherelDensity_pos {W : ℝ} (hW : 0 < W) (c : E → ℂ) {lam : E} (hc : c lam ≠ 0) :
    0 < plancherelDensity W c lam := by
  have : 0 < ‖c lam‖ ^ 2 := by positivity
  exact inv_pos.2 (mul_pos hW this)

/-- Changing the `c`-function without changing its modulus does not change the density. This is the
precise sense in which the phase convention for `c` is free — and, read the other way, the reason a
discrepancy in a power of `π` between two sources cannot be a phase convention but must be a
normalization of the measures. -/
theorem plancherelDensity_congr (W : ℝ) (c c' : E → ℂ) (lam : E) (h : ‖c' lam‖ = ‖c lam‖) :
    plancherelDensity W c' lam = plancherelDensity W c lam := by
  rw [plancherelDensity, plancherelDensity, h]

end Density

/-! ## The `c`-function -/

section CFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Harish-Chandra's `c`-function**, `c(λ) = ∫_{N̄} e^{-(iλ+ϱ)(H(n̄))} dn̄`, where `H` is the
`𝔞`-component of the Iwasawa decomposition on the opposite nilpotent group `N̄`.

The integrand is `horosphericalCharacter (-ϱ) (-λ)`, the character of the exponent `-(iλ+ϱ)`. Both
`H` and the measure `dn̄` are data; fixing them is what fixes the normalization of the whole
inversion formula, so they are arguments rather than a global convention. -/
def cFunctionIntegral {Y : Type*} [MeasurableSpace Y] (nbar : Measure Y) (H : Y → E)
    (rho lam : E) : ℂ :=
  ∫ n : Y, horosphericalCharacter (-rho) (-lam) (H n) ∂nbar

omit [InnerProductSpace ℝ E] in
/-- On the real form `𝔞*` the `c`-function satisfies `c(-λ) = conj(c(λ))`, and then its squared
modulus is the product `c(λ)c(-λ)`. The reflection is a property of the defining integral in each
model, so it enters as a hypothesis. -/
theorem mul_neg_eq_normSq_of_conj (c : E → ℂ) (lam : E) (h : c (-lam) = conj (c lam)) :
    c lam * c (-lam) = ((‖c lam‖ ^ 2 : ℝ) : ℂ) := by
  rw [h, Complex.mul_conj']
  norm_cast

end CFunction

end SymmetricSpace

end

end
