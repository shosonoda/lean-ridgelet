/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Basic
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Activation Hilbert space

This file begins the formalization of Section 2.1 and Proposition 1 of the L2 manuscript. The
activation space is represented by its `L²(ℝ)` coordinate under the isometric isomorphism (7).
Its realization as a tempered distribution is reconstructed using a Bessel potential and
multiplication by a Japanese-bracket weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

namespace LeanRidgelet

/-- The Japanese bracket to the power `r`: `⟨x⟩^r = (1 + ‖x‖²)^(r / 2)`. -/
def japaneseBracketPow {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (r / 2)

theorem japaneseBracketPow_pos {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) :
    0 < japaneseBracketPow r x := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem japaneseBracketPow_add {E : Type*} [NormedAddCommGroup E]
    (r u : ℝ) (x : E) :
    japaneseBracketPow (r + u) x = japaneseBracketPow r x * japaneseBracketPow u x := by
  unfold japaneseBracketPow
  rw [show (r + u) / 2 = r / 2 + u / 2 by ring]
  exact Real.rpow_add (by positivity) _ _

theorem japaneseBracketPow_sq {E : Type*} [NormedAddCommGroup E] (r : ℝ) (x : E) :
    japaneseBracketPow r x ^ 2 = japaneseBracketPow (2 * r) x := by
  rw [pow_two, ← japaneseBracketPow_add]
  congr 1
  ring

@[simp]
theorem japaneseBracketPow_zero {E : Type*} [NormedAddCommGroup E] (x : E) :
    japaneseBracketPow 0 x = 1 := by
  simp [japaneseBracketPow]

/-- The complex-valued Japanese-bracket multiplier used on tempered distributions. -/
def temperedWeight (r : ℝ) (x : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow r x)

@[simp]
theorem temperedWeight_mul_neg (r : ℝ) : temperedWeight r * temperedWeight (-r) = 1 := by
  funext x
  simp only [Pi.mul_apply, Pi.one_apply, temperedWeight, ← Complex.ofReal_mul]
  rw [← japaneseBracketPow_add]
  simp

@[fun_prop]
theorem hasTemperateGrowth_temperedWeight (r : ℝ) :
    Function.HasTemperateGrowth (temperedWeight r) := by
  unfold temperedWeight japaneseBracketPow
  fun_prop

/-- Multiplication of a tempered distribution by `⟨x⟩^r`. -/
def temperedWeightMultiplier (r : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.smulLeftCLM ℂ (temperedWeight r)

/-- The Bessel symbol in Mathlib frequency coordinates for the paper's Fourier convention. -/
def paperBesselSymbol (r : ℝ) (ξ : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow r ((2 * Real.pi) * ξ))

@[simp]
theorem paperBesselSymbol_neg_mul (r : ℝ) :
    paperBesselSymbol (-r) * paperBesselSymbol r = 1 := by
  funext ξ
  simp only [Pi.mul_apply, Pi.one_apply, paperBesselSymbol, ← Complex.ofReal_mul]
  rw [← japaneseBracketPow_add]
  simp

@[fun_prop]
theorem hasTemperateGrowth_paperBesselSymbol (r : ℝ) :
    Function.HasTemperateGrowth (paperBesselSymbol r) := by
  unfold paperBesselSymbol japaneseBracketPow
  exact (Function.Complex.hasTemperateGrowth_ofReal).comp <|
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (r / 2)).comp (by fun_prop)

/-- The Bessel potential for the paper convention `exp (-i x · ξ)`.

Mathlib uses a `2π` Fourier character, hence the rescaled symbol `⟨2πξ⟩^r`. -/
def paperBesselPotential (r : ℝ) :
    TemperedDistribution ℝ ℂ →L[ℂ] TemperedDistribution ℝ ℂ :=
  TemperedDistribution.fourierMultiplierCLM ℂ (paperBesselSymbol r)

/-- Membership in the paper-normalized Sobolev space `H^s(ℝ)`. -/
def MemPaperSobolev (s : ℝ) (σ : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ f : L2 ℝ volume, paperBesselPotential s σ = f

/-- Membership in the real-domain description `⟨·⟩^t H^s(ℝ)` of the activation space. -/
def MemActivationSpace (s t : ℝ) (σ : TemperedDistribution ℝ ℂ) : Prop :=
  MemPaperSobolev s (temperedWeightMultiplier (-t) σ)

/-- The Hilbert coordinate model of the activation space `A_{s,t}`. -/
abbrev ActivationSpace (_s _t : ℝ) := L2 ℝ volume

/-- The activation-space isometry in the transported `L²` coordinate model. -/
def activationCoordinateEquiv (s t : ℝ) : ActivationSpace s t ≃ₗᵢ[ℂ] L2 ℝ volume :=
  LinearIsometryEquiv.refl ℂ (L2 ℝ volume)

/-- Realize an activation coordinate as an element of `⟨·⟩^t H^s(ℝ) ⊆ 𝓢'(ℝ)`. -/
def activationDistribution (s t : ℝ) :
    ActivationSpace s t →L[ℂ] TemperedDistribution ℝ ℂ :=
  temperedWeightMultiplier t ∘L
    paperBesselPotential (-s) ∘L
      Lp.toTemperedDistributionCLM ℂ volume 2

/-- Applying the inverse weights recovers the original `L²` coordinate as a distribution. -/
theorem paperBesselPotential_temperedWeightMultiplier_activationDistribution
    (s t : ℝ) (σ : ActivationSpace s t) :
    paperBesselPotential s
        (temperedWeightMultiplier (-t) (activationDistribution s t σ)) =
      Lp.toTemperedDistributionCLM ℂ volume 2 σ := by
  unfold activationDistribution paperBesselPotential temperedWeightMultiplier
  simp only [ContinuousLinearMap.comp_apply]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_temperedWeight t) (hasTemperateGrowth_temperedWeight (-t))]
  rw [temperedWeight_mul_neg]
  have hone (f : TemperedDistribution ℝ ℂ) :
      TemperedDistribution.smulLeftCLM ℂ (1 : ℝ → ℂ) f = f := by
    change TemperedDistribution.smulLeftCLM ℂ (fun _ : ℝ ↦ 1) f = f
    simp
  rw [hone]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_paperBesselSymbol (-s)) (hasTemperateGrowth_paperBesselSymbol s)]
  rw [paperBesselSymbol_neg_mul]
  change TemperedDistribution.fourierMultiplierCLM ℂ (fun _ : ℝ ↦ 1)
    (Lp.toTemperedDistributionCLM ℂ volume 2 σ) = _
  rw [TemperedDistribution.fourierMultiplierCLM_const]
  simp

/-- The concrete realization of every activation coordinate belongs to `A_{s,t}`. -/
theorem memActivationSpace_activationDistribution (s t : ℝ) (σ : ActivationSpace s t) :
    MemActivationSpace s t (activationDistribution s t σ) := by
  exact ⟨σ, paperBesselPotential_temperedWeightMultiplier_activationDistribution s t σ⟩

/-- The activation-space isometry gives unique `L²` coordinates for realized activations. -/
theorem activationDistribution_injective (s t : ℝ) :
    Function.Injective (activationDistribution s t) := by
  intro σ τ hστ
  have hdist : Lp.toTemperedDistributionCLM ℂ volume 2 σ =
      Lp.toTemperedDistributionCLM ℂ volume 2 τ := by
    rw [← paperBesselPotential_temperedWeightMultiplier_activationDistribution s t σ,
      ← paperBesselPotential_temperedWeightMultiplier_activationDistribution s t τ, hστ]
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  exact hdist

end LeanRidgelet
