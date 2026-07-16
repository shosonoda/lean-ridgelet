/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Activation.Gaussian
public import LeanRidgelet.Operator.Ridgelet

/-!
# Gaussian synthesis and ridgelet operators

This file specializes the coordinate operator theory to the standard Gaussian activation at
`(s,t)=(0,0)`, the first model case in Chapter 5.
-/

@[expose] public section

noncomputable section

namespace LeanRidgelet

/-- Network synthesis for the standard Gaussian activation. -/
def gaussianSynthesis (m : ℕ) [NeZero m] :
    ParameterSpace m 0 0 →L[ℂ] TargetSpace m :=
  networkSynthesis m 0 0 gaussianActivation

theorem surjective_gaussianSynthesis (m : ℕ) [NeZero m] :
    Function.Surjective (gaussianSynthesis m) :=
  surjective_networkSynthesis m 0 0 gaussianActivation_ne_zero

/-- The Riesz-dual Gaussian fiber. -/
def gaussianRieszRepresenter (m : ℕ) [NeZero m] : FiberSpace m 0 0 :=
  activationRieszRepresenter m 0 0 gaussianActivation

@[simp]
theorem inner_gaussianRieszRepresenter (m : ℕ) [NeZero m] (q : FiberSpace m 0 0) :
    inner ℂ (gaussianRieszRepresenter m) q =
      activationFiberFunctional m 0 0 gaussianActivation q :=
  inner_activationRieszRepresenter m 0 0 gaussianActivation q

/-- The positive Gaussian reconstruction constant. -/
def gaussianNormalization (m : ℕ) [NeZero m] : ℝ :=
  activationNormalization m 0 0 gaussianActivation

theorem gaussianNormalization_pos (m : ℕ) [NeZero m] :
    0 < gaussianNormalization m :=
  activationNormalization_pos m 0 0 gaussianActivation_ne_zero

/-- The normalized minimum-norm Gaussian ridgelet solution. -/
def normalizedGaussianRightInverse (m : ℕ) [NeZero m] :
    TargetSpace m →L[ℂ] ParameterSpace m 0 0 :=
  normalizedNetworkRightInverse m 0 0 gaussianActivation

theorem normalizedGaussianRightInverse_rightInverse (m : ℕ) [NeZero m] :
    Function.RightInverse (normalizedGaussianRightInverse m) (gaussianSynthesis m) :=
  normalizedNetworkRightInverse_rightInverse m 0 0 gaussianActivation_ne_zero

end LeanRidgelet
