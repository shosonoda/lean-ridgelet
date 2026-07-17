/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.FiberSynthesis
public import LeanRidgelet.Space.Duality

/-!
# Synthesis in unitary coordinates

This file specializes the abstract pointwise lift to the activation and coefficient Hilbert
spaces. Because `ParameterSpace` is currently the transported coordinate model, the unitary
coordinate transform `T` is definitionally the identity here and `networkSynthesis` is the
coordinate realization of the manuscript factorization `S = \widetilde L_σ T`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- Synthesis as a continuous bilinear operator in activation and unitary coordinates. -/
def networkSynthesisMap (m : ℕ) [NeZero m] (s t : ℝ) :
    ActivationSpace s t →L[ℂ] ParameterSpace m s t →L[ℂ] TargetSpace m :=
  (activationFiberDualMap m s t).compLpL₂ 2 volume

/-- Synthesis associated with an activation coordinate in the transported `T`-coordinate model. -/
def networkSynthesis (m : ℕ) [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) :
    ParameterSpace m s t →L[ℂ] TargetSpace m :=
  networkSynthesisMap m s t σ

theorem networkSynthesis_eq_fiberSynthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    networkSynthesis m s t σ = fiberSynthesis volume (activationFiberFunctional m s t σ) :=
  rfl

/-- Pointwise coordinate form `S[γ](x) = L_σ[T[γ](x, ·)]`, with `T = I` in this model. -/
theorem networkSynthesis_apply_ae (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ (γ x) := by
  exact fiberSynthesis_apply_ae volume (activationFiberFunctional m s t σ) γ

/-- The concrete operator-norm estimate for synthesis. -/
theorem norm_networkSynthesis_le (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    ‖networkSynthesis m s t σ‖ ≤ (2 * Real.pi) ^ (m - 1) * ‖σ‖ := by
  calc
    ‖networkSynthesis m s t σ‖ ≤ ‖activationFiberFunctional m s t σ‖ :=
      ContinuousLinearMap.norm_compLpL_le _
    _ ≤ (2 * Real.pi) ^ (m - 1) * ‖σ‖ :=
      norm_activationFiberFunctional_le m s t σ

/-- The concrete synthesis estimate evaluated at a parameter distribution. -/
theorem norm_networkSynthesis_apply_le (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    ‖networkSynthesis m s t σ γ‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ * ‖γ‖ := by
  calc
    ‖networkSynthesis m s t σ γ‖ ≤ ‖networkSynthesis m s t σ‖ * ‖γ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((2 * Real.pi) ^ (m - 1) * ‖σ‖) * ‖γ‖ := by
      gcongr
      exact norm_networkSynthesis_le m s t σ

end LeanRidgelet
