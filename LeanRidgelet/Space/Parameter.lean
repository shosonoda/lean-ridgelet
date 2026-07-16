/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Fiber

/-!
# Parameter Hilbert space

This file defines the Fourier--dilation coordinate model of the parameter space from Section 2.3
of the L2 manuscript. Equation (12) identifies the parameter Hilbert space with the Bochner space
`L²(ℝᵐ; H_{s,t})`. Its realization as a distribution on parameter space and the nontrivial
Fourier--dilation transform are deferred to the concrete analytic layer.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- The coordinate model `L²(ℝᵐ; H_{s,t})` of the parameter space in equation (12). -/
abbrev ParameterSpace (m : ℕ) [NeZero m] (s t : ℝ) :=
  BochnerL2 (InputSpace m) (FiberSpace m s t) volume

/-- Equation (12), with the parameter space defined by transport to its Bochner `L²` model. -/
def parameterCoordinateEquiv (m : ℕ) [NeZero m] (s t : ℝ) :
    ParameterSpace m s t ≃ₗᵢ[ℂ] BochnerL2 (InputSpace m) (FiberSpace m s t) volume :=
  LinearIsometryEquiv.refl ℂ _

@[simp]
theorem parameterCoordinateEquiv_apply (m : ℕ) [NeZero m] (s t : ℝ)
    (γ : ParameterSpace m s t) : parameterCoordinateEquiv m s t γ = γ :=
  rfl

end LeanRidgelet
