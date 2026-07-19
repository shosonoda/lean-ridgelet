/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex, Claude
-/
module

public import LeanRidgelet.Space.Duality

/-!
# Ridgelet distributions reconstructed from coefficient vectors

A completed coefficient vector `h ∈ H_{s,t}` is realized as a tempered distribution by undoing
its weighted Bessel coordinate, and the manuscript ridgelet distribution `ρ` with spectrum
`ρ♯ = |ω|^m conj h` is reconstructed continuously and conjugate-linearly through the square-root
dilation-Jacobian pairing.  On the dense Schwartz core these constructions agree with the
pointwise formulas.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal FourierTransform InnerProductSpace SchwartzMap

namespace LeanRidgelet

open Fourier

/-- Realize a completed coefficient vector as a tempered distribution by undoing its weighted
Bessel coordinate.  This is the distributional realization needed before constructing the
manuscript ridgelet function `ρ` from its coefficient vector `hρ`. -/
def fiberDistribution (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →L[ℂ] TemperedDistribution ℝ ℂ :=
  paperBesselPotential (-t) ∘L
    temperedWeightMultiplier s ∘L
      Lp.toTemperedDistributionCLM ℂ volume 2 ∘L
        fiberDualCoordinate m s t

/-- On the dense Schwartz core, the completed coefficient-distribution realization recovers the
original Schwartz function as a tempered distribution. -/
theorem fiberDistribution_coe (m : ℕ) [NeZero m] (s t : ℝ) (h : FiberCore m s t) :
    fiberDistribution m s t (h : FiberSpace m s t) =
      SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume (FiberCore.toSchwartz h) := by
  unfold fiberDistribution
  simp only [ContinuousLinearMap.comp_apply, fiberDualCoordinate_coe]
  rw [show fiberDualCoordinateCore m s t h =
      (fiberDualSchwartzCoordinate s t (FiberCore.toSchwartz h)).toLp 2 volume by
    exact fiberDualCoordinateCoreValue_eq_toLp s t (FiberCore.toSchwartz h)]
  change paperBesselPotential (-t)
      (temperedWeightMultiplier s
        (((fiberDualSchwartzCoordinate s t (FiberCore.toSchwartz h)).toLp 2 volume :
          L2 ℝ volume) : TemperedDistribution ℝ ℂ)) = _
  rw [Lp.toTemperedDistribution_toLp_eq]
  rw [temperedWeightMultiplier_toTemperedDistributionCLM]
  unfold fiberDualSchwartzCoordinate
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_temperedWeight s)
    (hasTemperateGrowth_temperedWeight (-s))]
  rw [temperedWeight_mul_neg]
  change paperBesselPotential (-t)
      (SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume
        (SchwartzMap.smulLeftCLM ℂ (fun _ : ℝ ↦ (1 : ℂ))
          (schwartzBesselPotential t (FiberCore.toSchwartz h)))) = _
  rw [SchwartzMap.smulLeftCLM_const]
  simp only [one_smul, ContinuousLinearMap.id_apply]
  unfold paperBesselPotential schwartzBesselPotential
  rw [TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (hasTemperateGrowth_paperBesselSymbol (-t))]
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_paperBesselSymbol (-t))
    (hasTemperateGrowth_paperBesselSymbol t)]
  rw [paperBesselSymbol_neg_mul]
  change SchwartzMap.toTemperedDistributionCLM ℝ ℂ volume
      (SchwartzMap.fourierMultiplierCLM ℂ (fun _ : ℝ ↦ 1)
        (FiberCore.toSchwartz h)) = _
  rw [SchwartzMap.fourierMultiplierCLM_const]
  simp

/-- The manuscript spectrum `ρ♯ = |ω|ᵐ conj h` associated with a Schwartz coefficient vector. -/
def ridgeletSpectrumCoreFn (m : ℕ) (h : SchwartzMap ℝ ℂ) (ω : ℝ) : ℂ :=
  ((|ω| ^ m : ℝ) : ℂ) * conj (h ω)

/-- The core ridgelet spectrum is square-integrable, despite the possible nonsmoothness of
`|ω|ᵐ` at the origin. -/
theorem memLp_ridgeletSpectrumCoreFn (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    MemLp (ridgeletSpectrumCoreFn m h) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by
    unfold ridgeletSpectrumCoreFn
    fun_prop)).2
  convert integrable_norm_sq_mul_abs_pow (2 * m) h using 1
  funext ω
  unfold ridgeletSpectrumCoreFn
  rw [norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (abs_nonneg ω) m)]
  ring

/-- The `L²` realization of the manuscript spectrum of a Schwartz coefficient vector. -/
def ridgeletSpectrumCoreL2 (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_ridgeletSpectrumCoreFn m h).toLp (ridgeletSpectrumCoreFn m h)

/-- The spectrum `ρ♯ = |ω|ᵐ conj h`, embedded as a tempered distribution. -/
def ridgeletSpectrumCore (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistributionCLM ℂ volume 2 (ridgeletSpectrumCoreL2 m h)

/-- Evaluation of the core ridgelet spectrum on a Schwartz test function. -/
theorem ridgeletSpectrumCore_apply (m : ℕ) (h φ : SchwartzMap ℝ ℂ) :
    ridgeletSpectrumCore m h φ =
      ∫ ω : ℝ, φ ω * (((|ω| ^ m : ℝ) : ℂ) * conj (h ω)) := by
  rw [show ridgeletSpectrumCore m h φ =
      ∫ ω : ℝ, φ ω * ridgeletSpectrumCoreL2 m h ω by
    exact Lp.toTemperedDistribution_apply (ridgeletSpectrumCoreL2 m h) φ]
  apply integral_congr_ae
  filter_upwards [(memLp_ridgeletSpectrumCoreFn m h).coeFn_toLp] with ω hω
  change φ ω *
      ((memLp_ridgeletSpectrumCoreFn m h).toLp
        (ridgeletSpectrumCoreFn m h)) ω = _
  rw [hω]
  rfl

/-- The ridgelet function reconstructed from a Schwartz coefficient vector by the manuscript
inverse Fourier transform. -/
def ridgeletFunctionCore (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  paperFourierInvDistribution (ridgeletSpectrumCore m h)

/-- The reconstructed core ridgelet function has manuscript spectrum
`ρ♯ = |ω|ᵐ conj h`. -/
theorem paperFourierDistribution_ridgeletFunctionCore
    (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    paperFourierDistribution (ridgeletFunctionCore m h) = ridgeletSpectrumCore m h :=
  paperFourierDistribution_paperFourierInvDistribution _

/-! ### Reconstruction from a completed coefficient vector -/

/-- The manuscript spectrum `ρ♯ = |ω|ᵐ conj h` for a completed coefficient vector.

The formula is realized through the `L²` pairing of square-root weighted coordinates.  This avoids
the invalid intermediate operation of multiplying an arbitrary tempered distribution by the
nonsmooth function `|ω|ᵐ` in odd dimensions.  The dependence on `h` is conjugate-linear, as in the
manuscript formula. -/
def ridgeletSpectrum (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →SL[starRingEnd ℂ] TemperedDistribution ℝ ℂ where
  toFun h := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (SchwartzMap ℝ ℂ) ℂ
      ((innerSL ℂ (fiberBaseCoordinate m s t h)).comp
        (fiberBaseCoordinateSchwartz m))
  map_add' h r := by
    ext φ
    change inner ℂ
        (fiberBaseCoordinate m s t (h + r))
        (fiberBaseCoordinateSchwartz m φ) =
      inner ℂ (fiberBaseCoordinate m s t h) (fiberBaseCoordinateSchwartz m φ) +
        inner ℂ (fiberBaseCoordinate m s t r) (fiberBaseCoordinateSchwartz m φ)
    rw [map_add, inner_add_left]
  map_smul' c h := by
    ext φ
    simp
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro φ
    exact (innerSLFlip ℂ (fiberBaseCoordinateSchwartz m φ)).continuous.comp
      (fiberBaseCoordinate m s t).continuous

/-- Evaluation of the completed ridgelet spectrum is the weighted `L²` pairing. -/
theorem ridgeletSpectrum_apply (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) (φ : SchwartzMap ℝ ℂ) :
    ridgeletSpectrum m s t h φ =
      inner ℂ (fiberBaseCoordinate m s t h) (fiberBaseCoordinateSchwartz m φ) := rfl

/-- The completed spectrum agrees with the pointwise `|ω|ᵐ conj h` formula on the dense Schwartz
core. -/
theorem ridgeletSpectrum_coe (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    ridgeletSpectrum m s t (h : FiberSpace m s t) =
      ridgeletSpectrumCore m (FiberCore.toSchwartz h) := by
  ext φ
  rw [ridgeletSpectrum_apply, fiberBaseCoordinate_coe, ridgeletSpectrumCore_apply]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (memLp_fiberBaseCoordinateFn m (FiberCore.toSchwartz h)).coeFn_toLp,
    (memLp_fiberBaseCoordinateFn m φ).coeFn_toLp] with ω hh hφ
  rw [show fiberBaseCoordinateCore m s t h ω =
      fiberBaseCoordinateFn m (FiberCore.toSchwartz h) ω by exact hh]
  rw [show fiberBaseCoordinateSchwartz m φ ω = fiberBaseCoordinateFn m φ ω by exact hφ]
  unfold fiberBaseCoordinateFn
  rw [RCLike.inner_apply]
  rw [map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  have hsqrt :
      ((Real.sqrt (|ω| ^ m) : ℂ) * (Real.sqrt (|ω| ^ m) : ℂ)) =
        ((|ω| ^ m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (pow_nonneg (abs_nonneg ω) m)]
  calc
    _ = φ ω * (starRingEnd ℂ) (FiberCore.toSchwartz h ω) *
          ((Real.sqrt (|ω| ^ m) : ℂ) * (Real.sqrt (|ω| ^ m) : ℂ)) := by ring
    _ = φ ω * (starRingEnd ℂ) (FiberCore.toSchwartz h ω) *
        ((|ω| ^ m : ℝ) : ℂ) := by rw [hsqrt]
    _ = φ ω * (((|ω| ^ m : ℝ) : ℂ) *
        (starRingEnd ℂ) (FiberCore.toSchwartz h ω)) := by ring

/-- Reconstruct the ridgelet function `ρ` from a completed coefficient vector `h` by applying the
manuscript inverse Fourier transform to `ρ♯`. -/
def ridgeletFunction (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →SL[starRingEnd ℂ] TemperedDistribution ℝ ℂ where
  toFun h := paperFourierInvDistribution (ridgeletSpectrum m s t h)
  map_add' h r := by simp
  map_smul' c h := by simp
  cont := paperFourierInvDistribution.continuous.comp (ridgeletSpectrum m s t).continuous

/-- Reconstruction from a completed coefficient vector agrees with the Schwartz-core formula. -/
theorem ridgeletFunction_coe (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    ridgeletFunction m s t (h : FiberSpace m s t) =
      ridgeletFunctionCore m (FiberCore.toSchwartz h) := by
  change paperFourierInvDistribution
      (ridgeletSpectrum m s t (h : FiberSpace m s t)) =
    paperFourierInvDistribution (ridgeletSpectrumCore m (FiberCore.toSchwartz h))
  rw [ridgeletSpectrum_coe]

/-- The reconstructed completed ridgelet function has spectrum `ρ♯`. -/
theorem paperFourierDistribution_ridgeletFunction
    (m : ℕ) [NeZero m] (s t : ℝ) (h : FiberSpace m s t) :
    paperFourierDistribution (ridgeletFunction m s t h) = ridgeletSpectrum m s t h :=
  paperFourierDistribution_paperFourierInvDistribution _

end LeanRidgelet
