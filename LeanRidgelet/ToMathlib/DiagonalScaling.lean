/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinatewise scaling of `ℝ^k`

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib has the one-dimensional change of variables `x ↦ c * x`
(`MeasureTheory.integral_comp_mul_left`) and, at the level of measures, the rescaling of an
additive Haar measure by an arbitrary linear map
(`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`). What is missing is the integral
form of the simultaneous change of variables in all `k` coordinates at once,
$$`\int_{\mathbb R^k}G(w_1d_1,\ldots,w_kd_k)\,\mathrm d\boldsymbol d
   =\Bigl(\prod_i|w_i|\Bigr)^{-1}\int_{\mathbb R^k}G(\boldsymbol y)\,\mathrm d\boldsymbol y,`
which is what a `k`-fold scale parameter produces — for instance the diagonal factor of a singular
value decomposition, where the `k` singular values are scaled against the `k` coordinates of a
frequency.

The proof is the composite of the two facts above: the diagonal map is a linear equivalence when no
`w i` vanishes, its determinant is `∏ w i`, and the Haar rescaling then transports the integral.

## Main definitions and results

* `MeasureTheory.diagScale`: the coordinatewise scaling `d ↦ (w i * d i)ᵢ` of `ℝ^k` as a linear map,
  and `MeasureTheory.diagScaleEquiv`: the same as a linear equivalence when no coordinate of `w`
  vanishes.
* `MeasureTheory.det_diagScale`: its determinant is `∏ w i`.
* `MeasureTheory.integral_comp_diagScale`: **the change of variables.** No hypothesis on the
  integrand: both sides are junk values simultaneously, the map being a measurable equivalence.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Coordinatewise scaling of `ℝ^k`: the diagonal linear map with entries `w`. -/
def diagScale (w : Fin k → ℝ) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun d := WithLp.toLp 2 fun i => w i * d i
  map_add' d d' := by
    ext i
    simp [mul_add]
  map_smul' c d := by
    ext i
    simp [mul_left_comm]

@[simp] theorem diagScale_apply (w : Fin k → ℝ) (d : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    diagScale w d i = w i * d i := rfl

/-- The determinant of a coordinatewise scaling is the product of its entries. -/
theorem det_diagScale (w : Fin k → ℝ) : LinearMap.det (diagScale w) = ∏ i, w i := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis]
  have : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (diagScale w) = Matrix.diagonal w := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    · rw [if_neg hij]
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, hij]
  rw [this, Matrix.det_diagonal]

/-- Coordinatewise scaling as a linear equivalence, available when no coordinate vanishes. -/
def diagScaleEquiv {w : Fin k → ℝ} (hw : ∀ i, w i ≠ 0) :
    EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) where
  __ := diagScale w
  invFun v := WithLp.toLp 2 fun i => (w i)⁻¹ * v i
  left_inv d := by
    ext i
    simp [inv_mul_cancel_left₀ (hw i)]
  right_inv v := by
    ext i
    simp [mul_inv_cancel_left₀ (hw i)]

/-- Coordinatewise scaling as a measurable equivalence. -/
def diagScaleMeasurableEquiv {w : Fin k → ℝ} (hw : ∀ i, w i ≠ 0) :
    EuclideanSpace ℝ (Fin k) ≃ᵐ EuclideanSpace ℝ (Fin k) :=
  (diagScaleEquiv hw).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp] theorem coe_diagScaleMeasurableEquiv {w : Fin k → ℝ} (hw : ∀ i, w i ≠ 0)
    (d : EuclideanSpace ℝ (Fin k)) : diagScaleMeasurableEquiv hw d = diagScale w d := rfl

/-- **The coordinatewise change of variables.** Scaling the `k` coordinates by `w` divides the
integral by `∏ |w i|`. There is no hypothesis on the integrand: the change of variables is along a
measurable equivalence, so both sides are junk values simultaneously. -/
theorem integral_comp_diagScale {w : Fin k → ℝ} (hw : ∀ i, w i ≠ 0)
    (G' : EuclideanSpace ℝ (Fin k) → G) :
    (∫ d : EuclideanSpace ℝ (Fin k), G' (diagScale w d))
      = (∏ i, |w i|)⁻¹ • ∫ y : EuclideanSpace ℝ (Fin k), G' y := by
  have hdet : LinearMap.det (diagScale (k := k) w) = ∏ i, w i := det_diagScale w
  have hne : LinearMap.det (diagScale (k := k) w) ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hw i
  have habs : |(∏ i, w i)⁻¹| = (∏ i, |w i|)⁻¹ := by
    rw [abs_inv, Finset.abs_prod]
  have hmap : Measure.map (diagScaleMeasurableEquiv hw)
      (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = ENNReal.ofReal ((∏ i, |w i|)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) hne
    rw [hdet, habs] at h
    exact h
  have hpos : (0 : ℝ) ≤ (∏ i, |w i|)⁻¹ :=
    inv_nonneg.2 (Finset.prod_nonneg fun i _ => abs_nonneg _)
  calc (∫ d : EuclideanSpace ℝ (Fin k), G' (diagScale w d))
      = ∫ y : EuclideanSpace ℝ (Fin k), G' y
          ∂(Measure.map (diagScaleMeasurableEquiv hw)
            (volume : Measure (EuclideanSpace ℝ (Fin k)))) :=
        (integral_map_equiv (diagScaleMeasurableEquiv hw) G').symm
    _ = (∏ i, |w i|)⁻¹ • ∫ y : EuclideanSpace ℝ (Fin k), G' y := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]

end MeasureTheory
