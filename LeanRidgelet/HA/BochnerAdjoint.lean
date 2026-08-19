/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanRidgelet.HA.BochnerIntertwining

/-!
# The synthesis integral is the adjoint of the ridgelet transform

`LeanRidgelet.HA.AdjointReconstruction` gets a nonzero reconstruction constant by taking the machine
to be the adjoint of the ridgelet transform.  That is the coorbit argument, and it is abstract: it
says nothing about the machine being an integral against a feature.  This file supplies the missing
identification, and it is exactly the *common-feature* case.

For a single feature `φ`, the Bochner synthesis integral against `φ` and the Bochner ridgelet
transform against `φ` are adjoint to each other.  The computation is one line of Fubini:

`⟪M γ, f⟫ = ∫∫ conj (γ ξ) conj (φ x ξ) f x = ⟪γ, R f⟫`,

the left-hand side integrating the parameter first and the right-hand side the data first.  So the
abstract adjoint of the previous file *is* the network's own synthesis integral, provided the
synthesis feature is the analysis feature.  With a different synthesis feature the two are not
adjoint, which is the precise sense in which the coorbit route reconstructs with the network whose
activation is the analysis feature rather than one fixed in advance.

## Main results

* `LeanRidgelet.bochnerSynthesis_eq_adjoint_bochnerRidgelet`: bounded realizations of the two
  Bochner integrals against the same feature are adjoint operators.

## What is assumed

That the two operators realize the two integrals pointwise almost everywhere -- the standing
convention of this development for the analytic input -- and one Fubini hypothesis: the doubly
indexed integrand is integrable for the product measure.  Both measures are `s`-finite, as
Tonelli needs.  Nothing is assumed about the feature beyond what those hypotheses say.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace LeanRidgelet

/-- **The synthesis integral is the adjoint of the ridgelet transform, for a common feature.**  If a
bounded operator realizes the Bochner synthesis integral against a feature and another realizes the
Bochner ridgelet transform against the *same* feature, the first is the adjoint of the second.

The proof pairs each side against arbitrary vectors and exchanges the order of integration: both
pairings are the double integral of `conj (γ ξ) conj (φ x ξ) f x`, one taken parameter-first and the
other data-first. -/
theorem bochnerSynthesis_eq_adjoint_bochnerRidgelet {X Ξ : Type*} [MeasurableSpace X]
    [MeasurableSpace Ξ] (μ : Measure X) [SFinite μ] (ν : Measure Ξ) [SFinite ν] (φ : X → Ξ → ℂ)
    (M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (hM : ∀ γ : Lp ℂ 2 ν, (M γ : X → ℂ) =ᵐ[μ] bochnerSynthesis ν φ (γ : Ξ → ℂ))
    (hR : ∀ f : Lp ℂ 2 μ, (R f : Ξ → ℂ) =ᵐ[ν] bochnerRidgelet μ φ (f : X → ℂ))
    (hfub : ∀ (γ : Lp ℂ 2 ν) (f : Lp ℂ 2 μ), Integrable
      (Function.uncurry fun (x : X) (ξ : Ξ) ↦
        conj ((γ : Ξ → ℂ) ξ) * (conj (φ x ξ) * (f : X → ℂ) x)) (μ.prod ν)) :
    M = ContinuousLinearMap.adjoint R := by
  refine (ContinuousLinearMap.eq_adjoint_iff M R).2 fun γ f ↦ ?_
  rw [L2.inner_def, L2.inner_def]
  have hleft : ∀ᵐ x ∂μ, ⟪(M γ : X → ℂ) x, (f : X → ℂ) x⟫_ℂ =
      ∫ ξ, conj ((γ : Ξ → ℂ) ξ) * (conj (φ x ξ) * (f : X → ℂ) x) ∂ν := by
    filter_upwards [hM γ] with x hx
    rw [hx, RCLike.inner_apply', bochnerSynthesis]
    simp only [smul_eq_mul]
    rw [← integral_conj, ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by
      simp only [map_mul, mul_assoc])
  have hright : ∀ᵐ ξ ∂ν, ⟪(γ : Ξ → ℂ) ξ, (R f : Ξ → ℂ) ξ⟫_ℂ =
      ∫ x, conj ((γ : Ξ → ℂ) ξ) * (conj (φ x ξ) * (f : X → ℂ) x) ∂μ := by
    filter_upwards [hR f] with ξ hξ
    rw [hξ, RCLike.inner_apply', bochnerRidgelet, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply'])
  rw [integral_congr_ae hleft, integral_congr_ae hright]
  exact MeasureTheory.integral_integral_swap (hfub γ f)

end LeanRidgelet
