/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.AffineHaar
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The nonzero orbit of the general linear group

This file records the elementary orbit geometry used by the Mackey analysis of affine groups.
On a finite-dimensional real inner-product space, the general linear group acts transitively on
the nonzero vectors. The same is true for the contragredient action
`L ↦ L⁻ᵀ = L.symm.adjoint`.

The proofs are independent of ridgelet transforms and are intended as Mathlib upstream
candidates. A reflection maps a vector to a suitable rescaling of the target vector, and a final
nonzero scalar equivalence corrects its norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace LinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The general linear group of a finite-dimensional real inner-product space acts transitively
on its nonzero vectors. -/
theorem exists_apply_eq_of_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ L : E ≃ₗ[ℝ] E, L x = y := by
  let c : ℝ := ‖x‖ / ‖y‖
  have hc_pos : 0 < c := div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  let z : E := c • y
  have hz_norm : ‖x‖ = ‖z‖ := by
    change ‖x‖ = ‖c • y‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]
  let R : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (x - z))ᗮ
  have hR : R x = z := Submodule.reflection_sub hz_norm
  let d : ℝ := ‖y‖ / ‖x‖
  have hd : d ≠ 0 := div_ne_zero (norm_ne_zero_iff.mpr hy) (norm_ne_zero_iff.mpr hx)
  let S : E ≃ₗ[ℝ] E := LinearEquiv.smulOfUnit (Units.mk0 d hd)
  refine ⟨R.toLinearEquiv.trans S, ?_⟩
  rw [LinearEquiv.trans_apply]
  change S (R x) = y
  rw [hR]
  change d • (c • y) = y
  rw [smul_smul]
  have hdc : d * c = 1 := by
    dsimp [d, c]
    field_simp
  rw [hdc, one_smul]

/-- Taking the adjoint twice returns the original finite-dimensional linear equivalence. -/
@[simp]
theorem adjoint_adjoint (L : E ≃ₗ[ℝ] E) : L.adjoint.adjoint = L := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (LinearMap.adjoint_adjoint (L : E →ₗ[ℝ] E)) x

/-- The contragredient operation `L ↦ L⁻ᵀ`, as an automorphism homomorphism of the general
linear group. -/
def contragredientHom : (E ≃ₗ[ℝ] E) →* (E ≃ₗ[ℝ] E) where
  toFun L := L.symm.adjoint
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply ext_inner_left ℝ
    intro z
    change ⟪z, ((1 : E ≃ₗ[ℝ] E).symm : E →ₗ[ℝ] E).adjoint x⟫_ℝ = ⟪z, x⟫_ℝ
    rw [LinearMap.adjoint_inner_right]
    rfl
  map_mul' L M := by
    apply LinearEquiv.ext
    intro x
    apply ext_inner_left ℝ
    intro z
    change ⟪z, ((L * M).symm : E →ₗ[ℝ] E).adjoint x⟫_ℝ =
      ⟪z, (L.symm : E →ₗ[ℝ] E).adjoint ((M.symm : E →ₗ[ℝ] E).adjoint x)⟫_ℝ
    rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right,
      LinearMap.adjoint_inner_right]
    rfl

@[simp]
theorem contragredientHom_apply (L : E ≃ₗ[ℝ] E) :
    contragredientHom L = L.symm.adjoint := rfl

/-- The contragredient automorphisms `L⁻ᵀ` also act transitively on nonzero vectors. This is
the orbit calculation used on the Fourier side of the affine quasi-regular representation. -/
theorem exists_symm_adjoint_apply_eq_of_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ L : E ≃ₗ[ℝ] E, L.symm.adjoint x = y := by
  obtain ⟨A, hA⟩ := exists_apply_eq_of_ne_zero hx hy
  refine ⟨A.symm.adjoint, ?_⟩
  rw [adjoint_symm, adjoint_adjoint]
  exact hA

end LinearEquiv

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The nonzero vectors form a conull set for every additive Haar measure on a nontrivial
finite-dimensional real normed space. -/
theorem setOf_ne_zero_ae_eq_univ (mu : Measure E) [mu.IsAddHaarMeasure] :
    {x : E | x ≠ 0} =ᵐ[mu] Set.univ := by
  rw [ae_eq_univ]
  simpa only [Set.compl_setOf, not_ne_iff, Set.setOf_eq_eq_singleton] using
    (measure_singleton (μ := mu) (0 : E))

end MeasureTheory
