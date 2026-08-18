/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bochner integration against a quasi-invariant measure

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

## Main results

* `MeasureTheory.integral_eq_integral_smul_comp_smul_of_map_eq_withDensity` is the Bochner
  change-of-variables formula associated with a group action whose inverse pushforward is a
  density multiple of the original measure.
* `NNReal.smul_inv_sqrt_smul` records the square-root cancellation used by unitary
  Radon--Nikodym multipliers.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory

variable {G X E : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Bochner change-of-variables formula for a quasi-invariant measure. The hypothesis says
that pushforward by `x ↦ g⁻¹ • x` has density `jacobian g` with respect to `μ`; the conclusion
moves the action from the measure to the integrand and inserts that density as a real scalar. -/
theorem integral_eq_integral_smul_comp_smul_of_map_eq_withDensity (μ : Measure X)
    (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity (fun x ↦ (jacobian g x : ℝ≥0∞)))
    (h_jacobian : ∀ g : G, Measurable (jacobian g)) (g : G) (F : X → E) :
    ∫ x, F x ∂μ = ∫ x, jacobian g x • F (g • x) ∂μ := by
  let e : X ≃ᵐ X :=
    { toEquiv :=
        { toFun := fun x ↦ g⁻¹ • x
          invFun := fun x ↦ g • x
          left_inv := fun x ↦ smul_inv_smul g x
          right_inv := fun x ↦ inv_smul_smul g x }
      measurable_toFun := h_measurable g⁻¹
      measurable_invFun := h_measurable g }
  calc
    ∫ x, F x ∂μ = ∫ x, F (e.symm x) ∂μ.map e := by
      rw [integral_map_equiv]
      simp only [e.symm_apply_apply]
    _ = ∫ x, F (e.symm x) ∂μ.withDensity (fun x ↦ (jacobian g x : ℝ≥0∞)) := by
      rw [show μ.map e = μ.withDensity (fun x ↦ (jacobian g x : ℝ≥0∞)) by
        simpa [e] using h_map g]
    _ = ∫ x, jacobian g x • F (e.symm x) ∂μ := by
      exact integral_withDensity_eq_integral_smul (h_jacobian g) _
    _ = ∫ x, jacobian g x • F (g • x) ∂μ := by rfl

end MeasureTheory

namespace NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by a nonzero nonnegative real cancels one inverse square-root factor. -/
theorem smul_inv_sqrt_smul (j : ℝ≥0) (hj : j ≠ 0) (y : E) :
    j • (((j.sqrt : ℂ)⁻¹) • y) = (j.sqrt : ℂ) • y := by
  rw [NNReal.smul_def,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E)]
  rw [smul_smul]
  congr 1
  have hs : (j.sqrt : ℂ) ≠ 0 := by
    exact_mod_cast (show j.sqrt ≠ 0 by simpa using hj)
  have hjc : ((j : ℝ) : ℂ) = (j.sqrt : ℂ) ^ 2 := by
    norm_cast
    exact (NNReal.sq_sqrt j).symm
  change ((j : ℝ) : ℂ) * (j.sqrt : ℂ)⁻¹ = (j.sqrt : ℂ)
  rw [hjc, pow_two, mul_assoc, mul_inv_cancel₀ hs, mul_one]

end NNReal
