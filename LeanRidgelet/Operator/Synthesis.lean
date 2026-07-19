/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.UnitarySynthesis
public import LeanRidgelet.Space.Duality
public import LeanRidgelet.Transform.FourierDilation

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

/-- The concrete synthesis is the specialization of the abstract unitary factorization to the
transported coordinate model `T = I`. -/
theorem networkSynthesis_eq_unitarySynthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    networkSynthesis m s t σ =
      unitarySynthesis volume (parameterCoordinateEquiv m s t)
        (activationFiberFunctional m s t σ) := by
  ext γ
  rfl

/-- Pointwise coordinate form `S[γ](x) = L_σ[T[γ](x, ·)]`, with `T = I` in this model. -/
theorem networkSynthesis_apply_ae (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ (γ x) := by
  exact fiberSynthesis_apply_ae volume (activationFiberFunctional m s t σ) γ

/-- Pointwise manuscript factorization `S[γ](x) = L_σ[T[γ](x, ·)]`.

Although the transported coordinate model makes `T` definitionally the identity, this theorem
keeps the unitary transform explicit and is therefore the interface used by the concrete Fourier
construction. -/
theorem networkSynthesis_apply_fourierDilation_ae (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ
        (fourierDilationTransform m s t γ x) := by
  simpa [fourierDilationTransform, parameterCoordinateEquiv_apply] using
    networkSynthesis_apply_ae m s t σ γ

/-- On the Schwartz compatibility domain, synthesis is represented by the concrete
Fourier--dilation core.  This is the Hilbert-space formula (29) before expanding the activation
functional into its weighted Fourier pairing. -/
theorem networkSynthesis_parameterSchwartzRealization_apply_ae
    {m : ℕ} [NeZero m] (s t : ℝ) (σ : ActivationSpace s t)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    networkSynthesis m s t σ (parameterSchwartzRealization s t γ hγ) =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ
        (fourierDilationTransformFiber s t γ x) := by
  filter_upwards
    [networkSynthesis_apply_fourierDilation_ae m s t σ
      (parameterSchwartzRealization s t γ hγ),
    fourierDilationTransform_parameterSchwartzRealization_apply_ae s t γ hγ]
    with x hS hT
  rw [hS, hT]

/-- Weighted-Fourier pairing form of synthesis on the Schwartz compatibility domain. -/
theorem networkSynthesis_parameterSchwartzRealization_fourierPairing_ae
    {m : ℕ} [NeZero m] (s t : ℝ) (σ : ActivationSpace s t)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    networkSynthesis m s t σ (parameterSchwartzRealization s t γ hγ) =ᵐ[volume]
      fun x ↦ (2 * Real.pi : ℂ) ^ (m - 1) *
        inner ℂ (star σ)
          (fiberDualCoordinateCoreValue s t
            (fourierDilationTransformFiberCore s t γ x)) := by
  filter_upwards
    [networkSynthesis_parameterSchwartzRealization_apply_ae s t σ γ hγ]
    with x hx
  rw [hx]
  exact activationFiberFunctional_coe m s t σ
    (fourierDilationTransformFiberCore s t γ x)

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
