/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Fiber

/-!
# Parameter Hilbert space

This file defines the transported unitary-coordinate model of the parameter space
of the L2 manuscript. The unitary transform identifies the parameter Hilbert space with the
Bochner space `L²(ℝᵐ; H_{s,t})`. Its realization as a distribution on parameter space and the
nontrivial concrete Fourier construction of the unitary transform is deferred to the analytic
layer.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- The coordinate model `L²(ℝᵐ; H_{s,t})` of the parameter Hilbert space. -/
abbrev ParameterSpace (m : ℕ) [NeZero m] (s t : ℝ) :=
  BochnerL2 (InputSpace m) (FiberSpace m s t) volume

/-- The parameter-space unitary, with the source defined by transport to its Bochner `L²` model. -/
def parameterCoordinateEquiv (m : ℕ) [NeZero m] (s t : ℝ) :
    ParameterSpace m s t ≃ₗᵢ[ℂ] BochnerL2 (InputSpace m) (FiberSpace m s t) volume :=
  LinearIsometryEquiv.refl ℂ _

@[simp]
theorem parameterCoordinateEquiv_apply (m : ℕ) [NeZero m] (s t : ℝ)
    (γ : ParameterSpace m s t) : parameterCoordinateEquiv m s t γ = γ :=
  rfl

end LeanRidgelet
