/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Space.Duality

/-!
# Activation spectrum and classical realization

The Hilbert coordinate of `A_{s,t}` used by the operator layer is the manuscript isometry
coordinate `⟨ω⟩^s ⟨∂ω⟩^{-t}[σ♯]` of equation (7); the spectrum `σ♯` and the classical
activation `σ = 𝓕⁻¹_paper[σ♯]` are reconstructed from it in `LeanRidgelet.Space.Activation`.
This file proves that the bounded activation functional acts on the Schwartz fiber core by the
distributional pairing `L_σ[h] = (2π)^{m-1} σ♯[h]` of the manuscript definition (10).  This is
the bridge used by the classical-integral agreement theorems.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ComplexConjugate FourierTransform InnerProductSpace SchwartzMap

namespace LeanRidgelet

open Fourier

/-- The activation spectrum acts on a Schwartz coefficient vector by the weighted dual pairing.
This identity is the content of the manuscript's self-adjoint rewrite of `∫ h σ♯`. -/
theorem activationSpectrum_apply (s t : ℝ) (σ : ActivationSpace s t)
    (h : SchwartzMap ℝ ℂ) :
    activationSpectrum s t σ h =
      inner ℂ (star σ) (fiberDualCoordinateCoreValue s t h) := by
  unfold activationSpectrum paperBesselPotential
  simp only [ContinuousLinearMap.comp_apply]
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply]
  rw [fourier_smulLeft_fourierInv_of_even (hasTemperateGrowth_paperBesselSymbol t)
    (paperBesselSymbol_neg t) h]
  unfold temperedWeightMultiplier
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  rw [show SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s))
        (SchwartzMap.fourierMultiplierCLM ℂ (paperBesselSymbol t) h) =
      fiberDualSchwartzCoordinate s t h from rfl]
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star σ,
    (memLp_fiberDualCoordinateFn s t h).coeFn_toLp] with ω hstar hdual
  rw [RCLike.inner_apply]
  rw [show fiberDualCoordinateCoreValue s t h ω = fiberDualCoordinateFn s t h ω from hdual]
  rw [show ((star σ : ActivationSpace s t) : ℝ → ℂ) ω = star (σ ω) from hstar]
  rw [starRingEnd_apply, star_star]
  have hpoint : (fiberDualSchwartzCoordinate s t h) ω = fiberDualCoordinateFn s t h ω := by
    unfold fiberDualSchwartzCoordinate
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight (-s))]
    simp [fiberDualCoordinateFn, temperedWeight, smul_eq_mul]
  rw [hpoint]
  ring

/-- On the Schwartz fiber core, the activation functional is `(2π)^{m-1}` times the
distributional action of the manuscript spectrum `σ♯`.  This proves the Blueprint formula
`L_σ[h] = (2π)^{m-1} ∫ h(ω) σ♯(ω) dω` for the transported coordinate model. -/
theorem activationFiberFunctional_eq_spectrum (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberCore m s t) :
    activationFiberFunctional m s t σ (h : FiberSpace m s t) =
      (2 * Real.pi : ℂ) ^ (m - 1) *
        activationSpectrum s t σ (FiberCore.toSchwartz h) := by
  rw [activationFiberFunctional_coe, activationSpectrum_apply]
  rfl

/-- The activation functional acts by pairing with the paper Fourier transform of the realized
classical activation. -/
theorem activationFiberFunctional_eq_realization (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberCore m s t) :
    activationFiberFunctional m s t σ (h : FiberSpace m s t) =
      (2 * Real.pi : ℂ) ^ (m - 1) *
        activationRealization s t σ (paperFourierSchwartz (FiberCore.toSchwartz h)) := by
  rw [activationFiberFunctional_eq_spectrum,
    ← paperFourierDistribution_activationRealization,
    paperFourierDistribution_apply]

end LeanRidgelet
