/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Activation.ReLU
public import LeanRidgelet.Operator.Ridgelet

/-!
# Rectified-linear-unit synthesis and ridgelet operators

This file specializes the coordinate operator theory to the rectified linear unit in `A_{0,t}`
for `3 / 2 < t`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate InnerProduct

namespace LeanRidgelet

/-- Network synthesis for the rectified-linear-unit activation. -/
def reluSynthesis (m : ℕ) [NeZero m] (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    ParameterSpace m 0 t →L[ℂ] TargetSpace m :=
  networkSynthesis m 0 t (reluActivation t ht)

theorem surjective_reluSynthesis (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    Function.Surjective (reluSynthesis m t ht) :=
  surjective_networkSynthesis m 0 t (reluActivation_ne_zero t ht)

/-- The rectified-linear-unit Riesz representer `h_σ`. -/
def reluRieszRepresenter (m : ℕ) [NeZero m] (t : ℝ) (ht : (3 : ℝ) / 2 < t) :
    FiberSpace m 0 t :=
  activationRieszRepresenter m 0 t (reluActivation t ht)

@[simp]
theorem inner_reluRieszRepresenter (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) (h : FiberSpace m 0 t) :
    inner ℂ (reluRieszRepresenter m t ht) h =
      activationFiberFunctional m 0 t (reluActivation t ht) h :=
  inner_activationRieszRepresenter m 0 t (reluActivation t ht) h

theorem adjoint_reluSynthesis (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    (reluSynthesis m t ht)† = ridgeletOperator m 0 t (reluRieszRepresenter m t ht) :=
  adjoint_networkSynthesis m 0 t (reluActivation t ht)

/-- The positive rectified-linear-unit reconstruction constant. -/
def reluNormalization (m : ℕ) [NeZero m] (t : ℝ) (ht : (3 : ℝ) / 2 < t) : ℝ :=
  activationNormalization m 0 t (reluActivation t ht)

theorem reluNormalization_pos (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    0 < reluNormalization m t ht :=
  activationNormalization_pos m 0 t (reluActivation_ne_zero t ht)

/-- The normalized minimum-norm rectified-linear-unit ridgelet solution. -/
def normalizedReLURightInverse (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    TargetSpace m →L[ℂ] ParameterSpace m 0 t :=
  normalizedNetworkRightInverse m 0 t (reluActivation t ht)

theorem normalizedReLURightInverse_rightInverse (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) :
    Function.RightInverse (normalizedReLURightInverse m t ht) (reluSynthesis m t ht) :=
  normalizedNetworkRightInverse_rightInverse m 0 t (reluActivation_ne_zero t ht)

theorem reluSolution_iff_kernel_translate (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) (f : TargetSpace m) (γ : ParameterSpace m 0 t) :
    reluSynthesis m t ht γ = f ↔
      γ - normalizedReLURightInverse m t ht f ∈
        LinearMap.ker (reluSynthesis m t ht).toLinearMap :=
  networkSolution_iff_kernel_translate m 0 t (reluActivation_ne_zero t ht) f γ

theorem normalizedReLURightInverse_unique_minimal (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (3 : ℝ) / 2 < t) (f : TargetSpace m) :
    ∀ γ : ParameterSpace m 0 t,
      reluSynthesis m t ht γ = f →
      ‖normalizedReLURightInverse m t ht f‖ ≤ ‖γ‖ ∧
        (‖normalizedReLURightInverse m t ht f‖ = ‖γ‖ →
          normalizedReLURightInverse m t ht f = γ) :=
  normalizedNetworkRightInverse_unique_minimal m 0 t (reluActivation_ne_zero t ht) f

end LeanRidgelet
