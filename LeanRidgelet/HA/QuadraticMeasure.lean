/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Quadratic

/-!
# The parameter measure of the quadratic-form example

This file carries the measure-theoretic layer of Section 7 of arXiv:2405.13682.  It does for
quadratic parameters what the second half of `LeanRidgelet.HA.Affine` does for ridge parameters.
The affine group acts on `LeanRidgelet.QuadraticParameter E` through the linear equivalence
`LeanRidgelet.quadraticParameterLinearEquiv`, so an additive Haar measure on the parameter space is
strongly quasi-invariant with a constant Radon--Nikodym cocycle, namely the absolute determinant of
that equivalence.  Feeding the cocycle to the generic quasi-invariant construction produces a
unitary representation of the affine group on the scalar `L²` of the parameter space.

The whole file rests on the abstract determinant of the parameter action.  Its value is never
computed; only multiplicativity along the group law and non-vanishing, which is automatic because
the action is by linear equivalences, are used.

## Main results

* `LeanRidgelet.quadraticParameterJacobian`: the constant Radon--Nikodym density of the inverse
  parameter action, with its normalization `LeanRidgelet.quadraticParameterJacobian_one`, its
  cocycle law `LeanRidgelet.quadraticParameterJacobian_cocycle`, and its non-vanishing
  `LeanRidgelet.quadraticParameterJacobian_ne_zero`.
* `LeanRidgelet.quadraticParameter_group_map_eq_withDensity`: an additive Haar measure on the
  quadratic parameter space is strongly quasi-invariant with that density.
* `LeanRidgelet.quadraticParameterLpUnitaryRepresentation`: the resulting
  Radon--Nikodym-corrected unitary representation of the affine group on parameter `L²`.

## Deviations from the article

The article writes the parameter measure through the explicit Jacobian of the coordinate change,
whose symmetric block is a power of the determinant of the linear part.  Here the density is the
absolute determinant of the parameter equivalence itself, exactly as in the ridge case, where
`LeanRidgelet.affineParameterJacobian` is the absolute determinant of
`LeanRidgelet.affineParameterLinearEquiv` rewritten through
`LeanRidgelet.det_affineParameterLinearEquiv`.  The block factorization of the article is recorded
as `LeanRidgelet.quadraticParameterJacobian_eq_blocks`, but the explicit value of the congruence
determinant is not needed anywhere.

As in the ridge case, the article uses invariant-measure notation, whereas an additive Haar measure
on the quadratic parameter space is not invariant under a general parameter action.  The constant
Radon--Nikodym density is therefore carried explicitly.

The data and parameter densities do not balance here, and this is the reason the file stops at the
parameter representation.  The generic quasi-invariant synthesis and ridgelet identities of
`LeanRidgelet.HA.BochnerIntertwining` require the parameter density to be the reciprocal of the
data density, and the ridge case satisfies that exactly: the ridge parameter action has determinant
`(det L)⁻¹` against the data determinant `det L`.  For quadratic parameters the determinant carries
the extra congruence factor of `LeanRidgelet.quadraticParameterJacobian_eq_blocks`, whose classical
value is `(det L)^{-(m+1)}`, so the two densities differ by a positive character of the affine
group.  A synthesis or ridgelet identity for this feature therefore intertwines the parameter
representation with a character-twisted data action rather than with the data representation
itself.  The twist does *not* cancel in the composite of synthesis with ridgelet: both halves pick
up the same factor, so the composite carries its square, and
`LeanRidgelet.character_eq_one_of_balance_of_mul_self_eq_one` shows that a square equal to one
forces the character to be one, that is, exact balance.  The composite is therefore not a commutant
element of the data representation for *this* measure, and the reconstruction argument does not
apply to it.  The repair is carried out in `LeanRidgelet.HA.QuadraticRelativeMeasure`: replacing the
additive Haar measure by the relatively invariant measure with weight a power of the determinant of
the symmetric coefficient restores exact balance, at the price of a measure that is only σ-finite
rather than locally finite.  Nothing downstream needs local finiteness, so the price is not real.

The quadratic parameter space is a product whose first factor is a submodule coerced to a type, and
it gets no global measurable structure here.  The measurable and Borel structures of the data space
and of the symmetric block are instead instance hypotheses of the declarations that need them, so
that a later file remains free to choose them; the product structure is then supplied by
`Prod.instMeasurableSpace` and `Prod.borelSpace`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The identity of the affine group acts on quadratic parameters by the identity.  This is the
group action law `one_smul` read back through `LeanRidgelet.quadraticParameter_smul_def`. -/
theorem quadraticParameterLinearEquiv_one :
    quadraticParameterLinearEquiv (1 : E ≃ᵃ[ℝ] E) =
      LinearEquiv.refl ℝ (QuadraticParameter E) :=
  LinearEquiv.ext fun ξ ↦ one_smul (E ≃ᵃ[ℝ] E) ξ

/-- The parameter action is multiplicative.  This is the group action law `mul_smul` read back
through `LeanRidgelet.quadraticParameter_smul_def`; no block computation is needed. -/
theorem quadraticParameterLinearEquiv_mul (g h : E ≃ᵃ[ℝ] E) :
    (quadraticParameterLinearEquiv (g * h) :
        QuadraticParameter E →ₗ[ℝ] QuadraticParameter E) =
      (quadraticParameterLinearEquiv g :
          QuadraticParameter E →ₗ[ℝ] QuadraticParameter E).comp
        (quadraticParameterLinearEquiv h :
          QuadraticParameter E →ₗ[ℝ] QuadraticParameter E) :=
  LinearMap.ext fun ξ ↦ mul_smul g h ξ

/-- The inverse affine group element acts by the inverse parameter equivalence. -/
theorem quadraticParameterLinearEquiv_inv (g : E ≃ᵃ[ℝ] E) :
    quadraticParameterLinearEquiv g⁻¹ = (quadraticParameterLinearEquiv g).symm := by
  refine LinearEquiv.ext fun ξ ↦ ?_
  apply (quadraticParameterLinearEquiv g).injective
  rw [(quadraticParameterLinearEquiv g).apply_symm_apply]
  change g • (g⁻¹ • ξ) = ξ
  exact smul_inv_smul g ξ

/-- The constant Radon--Nikodym density for the inverse quadratic parameter action.  It is the
absolute determinant of the parameter equivalence, left unevaluated. -/
def quadraticParameterJacobian (g : E ≃ᵃ[ℝ] E) : QuadraticParameter E → ℝ≥0 :=
  fun _ ↦ ‖LinearMap.det
    (quadraticParameterLinearEquiv g : QuadraticParameter E →ₗ[ℝ] QuadraticParameter E)‖₊

/-- The parameter Jacobian is normalized at the identity. -/
@[simp]
theorem quadraticParameterJacobian_one (ξ : QuadraticParameter E) :
    quadraticParameterJacobian (1 : E ≃ᵃ[ℝ] E) ξ = 1 := by
  simp only [quadraticParameterJacobian]
  rw [quadraticParameterLinearEquiv_one]
  simp

/-- The parameter Jacobian obeys the Radon--Nikodym cocycle law. -/
theorem quadraticParameterJacobian_cocycle (g h : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticParameterJacobian (g * h) ξ =
      quadraticParameterJacobian g (h • ξ) * quadraticParameterJacobian h ξ := by
  simp only [quadraticParameterJacobian]
  rw [quadraticParameterLinearEquiv_mul, LinearMap.det_comp, nnnorm_mul]

/-- The parameter Jacobian is everywhere nonzero, because the parameter action is by linear
equivalences and the determinant of a linear equivalence is a unit. -/
theorem quadraticParameterJacobian_ne_zero (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticParameterJacobian g ξ ≠ 0 := by
  simp only [quadraticParameterJacobian, ne_eq, nnnorm_eq_zero]
  exact (quadraticParameterLinearEquiv g).isUnit_det'.ne_zero

/-- The block form of the parameter Jacobian: the absolute determinant of the symmetric congruence
block times the reciprocal absolute determinant of the linear part.  The second factor is the ridge
parameter Jacobian, so the quadratic density differs from the ridge one exactly by the congruence
block.  Nothing below uses this identity; it records the article's factorization. -/
theorem quadraticParameterJacobian_eq_blocks (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticParameterJacobian g ξ =
      ‖LinearMap.det
          ((quadraticCongr g.linear.symm) :
            QuadraticSymmetric E →ₗ[ℝ] QuadraticSymmetric E)‖₊ *
        ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ := by
  simp only [quadraticParameterJacobian]
  rw [det_quadraticParameterLinearEquiv, nnnorm_mul, nnnorm_inv]

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- The quadratic parameter action is measurable, being linear on a finite-dimensional space. -/
theorem quadraticParameter_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable fun ξ : QuadraticParameter E ↦ g • ξ :=
  (quadraticParameterLinearEquiv g : QuadraticParameter E →ₗ[ℝ] QuadraticParameter E)
    |>.continuous_of_finiteDimensional.measurable

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The constant parameter Jacobian is measurable. -/
theorem quadraticParameterJacobian_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (quadraticParameterJacobian g) := measurable_const

/-- Pushforward of parameter Haar measure by the inverse parameter equivalence. -/
theorem quadraticParameter_map_eq_withDensity (ν : Measure (QuadraticParameter E))
    [ν.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    ν.map (quadraticParameterLinearEquiv g).symm =
      ν.withDensity (fun ξ ↦ (quadraticParameterJacobian g ξ : ℝ≥0∞)) := by
  have h := Measure.map_affineEquiv_symm_addHaar_eq_withDensity ν
    (quadraticParameterLinearEquiv g).toAffineEquiv
  have hfun : ⇑(quadraticParameterLinearEquiv g).toAffineEquiv.symm =
      ⇑(quadraticParameterLinearEquiv g).symm := rfl
  rw [hfun] at h
  simpa [LinearEquiv.toAffineEquiv, quadraticParameterJacobian] using h

/-- The parameter pushforward formula expressed through the affine-group action instance.  This is
the strong quasi-invariance hypothesis of the generic `L²` construction. -/
theorem quadraticParameter_group_map_eq_withDensity (ν : Measure (QuadraticParameter E))
    [ν.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    ν.map (fun ξ ↦ g⁻¹ • ξ) =
      ν.withDensity (fun ξ ↦ (quadraticParameterJacobian g ξ : ℝ≥0∞)) := by
  change ν.map (quadraticParameterLinearEquiv g⁻¹) = _
  rw [quadraticParameterLinearEquiv_inv]
  exact quadraticParameter_map_eq_withDensity ν g

/-- The Radon--Nikodym-corrected quadratic parameter representation on scalar `L²`. -/
noncomputable def quadraticParameterLpUnitaryRepresentation
    (ν : Measure (QuadraticParameter E)) [ν.IsAddHaarMeasure] [SigmaFinite ν] :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp ℂ 2 ν) :=
  quasiInvariantLpUnitaryRepresentation quadraticParameterJacobian
    quadraticParameter_measurable (quadraticParameter_group_map_eq_withDensity ν)
    quadraticParameterJacobian_measurable quadraticParameterJacobian_ne_zero
    quadraticParameterJacobian_one quadraticParameterJacobian_cocycle

end Measure

end LeanRidgelet
