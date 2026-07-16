/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Activation.Tanh
public import LeanRidgelet.Operator.Ridgelet

/-!
# Hyperbolic-tangent synthesis and ridgelet operators

This file specializes the coordinate operator theory to the hyperbolic tangent in `A_{0,t}` for
`1 / 2 < t`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate InnerProduct

namespace LeanRidgelet

/-- Network synthesis for the hyperbolic-tangent activation. -/
def tanhSynthesis (m : ℕ) [NeZero m] (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    ParameterSpace m 0 t →L[ℂ] TargetSpace m :=
  networkSynthesis m 0 t (tanhActivation t ht)

theorem surjective_tanhSynthesis (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    Function.Surjective (tanhSynthesis m t ht) :=
  surjective_networkSynthesis m 0 t (tanhActivation_ne_zero t ht)

/-- The Riesz-dual hyperbolic-tangent fiber. -/
def tanhRieszRepresenter (m : ℕ) [NeZero m] (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    FiberSpace m 0 t :=
  activationRieszRepresenter m 0 t (tanhActivation t ht)

@[simp]
theorem inner_tanhRieszRepresenter (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) (q : FiberSpace m 0 t) :
    inner ℂ (tanhRieszRepresenter m t ht) q =
      activationFiberFunctional m 0 t (tanhActivation t ht) q :=
  inner_activationRieszRepresenter m 0 t (tanhActivation t ht) q

theorem adjoint_tanhSynthesis (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    (tanhSynthesis m t ht)† = ridgeletOperator m 0 t (tanhRieszRepresenter m t ht) :=
  adjoint_networkSynthesis m 0 t (tanhActivation t ht)

/-- The positive hyperbolic-tangent reconstruction constant. -/
def tanhNormalization (m : ℕ) [NeZero m] (t : ℝ) (ht : (1 : ℝ) / 2 < t) : ℝ :=
  activationNormalization m 0 t (tanhActivation t ht)

theorem tanhNormalization_pos (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    0 < tanhNormalization m t ht :=
  activationNormalization_pos m 0 t (tanhActivation_ne_zero t ht)

/-- The normalized minimum-norm hyperbolic-tangent ridgelet solution. -/
def normalizedTanhRightInverse (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    TargetSpace m →L[ℂ] ParameterSpace m 0 t :=
  normalizedNetworkRightInverse m 0 t (tanhActivation t ht)

theorem normalizedTanhRightInverse_rightInverse (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    Function.RightInverse (normalizedTanhRightInverse m t ht) (tanhSynthesis m t ht) :=
  normalizedNetworkRightInverse_rightInverse m 0 t (tanhActivation_ne_zero t ht)

theorem tanhSolution_iff_kernel_translate (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) (f : TargetSpace m) (γ : ParameterSpace m 0 t) :
    tanhSynthesis m t ht γ = f ↔
      γ - normalizedTanhRightInverse m t ht f ∈
        LinearMap.ker (tanhSynthesis m t ht).toLinearMap :=
  networkSolution_iff_kernel_translate m 0 t (tanhActivation_ne_zero t ht) f γ

theorem normalizedTanhRightInverse_unique_minimal (m : ℕ) [NeZero m] (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) (f : TargetSpace m) :
    ∀ γ : ParameterSpace m 0 t,
      tanhSynthesis m t ht γ = f →
      ‖normalizedTanhRightInverse m t ht f‖ ≤ ‖γ‖ ∧
        (‖normalizedTanhRightInverse m t ht f‖ = ‖γ‖ →
          normalizedTanhRightInverse m t ht f = γ) :=
  normalizedNetworkRightInverse_unique_minimal m 0 t (tanhActivation_ne_zero t ht) f

end LeanRidgelet
