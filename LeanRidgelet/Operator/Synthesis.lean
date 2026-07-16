/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.FiberSynthesis
public import LeanRidgelet.Space.Duality

/-!
# Synthesis in Fourier--dilation coordinates

This file specializes the abstract pointwise fiber synthesis to the activation and parameter
Hilbert spaces. It gives the coordinate form of the integral representation operator in
Theorem 1, equations (15)--(16), of the L2 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- Synthesis as a continuous bilinear operator in activation and parameter coordinates. -/
def networkSynthesisMap (m : ℕ) [NeZero m] (s t : ℝ) :
    ActivationSpace s t →L[ℂ] ParameterSpace m s t →L[ℂ] TargetSpace m :=
  (activationFiberDualMap m s t).compLpL₂ 2 volume

/-- Theorem 1, equation (15): synthesis associated with an activation coordinate. -/
def networkSynthesis (m : ℕ) [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) :
    ParameterSpace m s t →L[ℂ] TargetSpace m :=
  networkSynthesisMap m s t σ

theorem networkSynthesis_eq_fiberSynthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    networkSynthesis m s t σ = fiberSynthesis volume (activationFiberFunctional m s t σ) :=
  rfl

/-- Pointwise coordinate form of equation (15). -/
theorem networkSynthesis_apply_ae (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ (γ x) := by
  exact fiberSynthesis_apply_ae volume (activationFiberFunctional m s t σ) γ

/-- The operator-norm estimate in Theorem 1. -/
theorem norm_networkSynthesis_le (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    ‖networkSynthesis m s t σ‖ ≤ (2 * Real.pi) ^ (m - 1) * ‖σ‖ := by
  calc
    ‖networkSynthesis m s t σ‖ ≤ ‖activationFiberFunctional m s t σ‖ :=
      ContinuousLinearMap.norm_compLpL_le _
    _ ≤ (2 * Real.pi) ^ (m - 1) * ‖σ‖ :=
      norm_activationFiberFunctional_le m s t σ

/-- Equation (16), evaluated at a parameter distribution. -/
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
