/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Reconstruction
public import LeanRidgelet.L1.StructureTheorem
public import LeanRidgelet.L1.TruncatedPower
public import LeanRidgelet.ToMathlib.GaussianSchwartz

/-!
# L1 theory: an explicit admissible ridgelet function, and ReLU universality

## Main results

* `LeanRidgelet.bumpRidgelet`: an **explicit ridgelet function**, the inverse Fourier transform
  of a smooth bump supported in `(5π/2, 7π/2)` in the angular frequency `ω = 2πξ` — that is,
  in `Metric.ball (3/2) (1/4)` in Mathlib's frequency variable `ξ`, which is the variable the
  inverse transform integrates over.
* `LeanRidgelet.isAdmissiblePair_bumpRidgelet`, `LeanRidgelet.integral_pow_mul_bumpRidgelet`:
  it is admissible against every truncated power, and all of its moments vanish — it is a
  Lizorkin test function.
* `LeanRidgelet.l1_truncatedPower_admissible_exists`: for every dimension `m` and degree `k`
  there is an integrable ridgelet function, with weighted integrability and vanishing moments
  of every order, admissible against `z₊^k`.
* `LeanRidgelet.l1_relu_network_universal_approximation`: **universality of ReLU networks**,
  by feeding the explicit pair at `k = 1` into the reconstruction formula.
* `LeanRidgelet.l1_truncatedPower_isAdmissiblePair_of_window`: the article's construction
  `ψ = Λ^m w^{(ℓ+k+1)}` for an arbitrary Schwartz window `w`, and
  `LeanRidgelet.l1_truncatedPower_admissible`: **the article's own Gaussian witness**, through
  the angular Fourier transform of the Gaussian
  `LeanRidgelet.angularFourier1D_gaussianWindow`.

## Deviations from the article

The explicit witness `bumpRidgelet` is used for the universality corollary rather than the
article's `ψ = Λ^m G^{(ℓ+k+1)}`: because its spectrum is compactly supported *away from the
origin*, the admissibility integrand is a nonzero constant times a nonnegative continuous
compactly supported density on the positive half-line, so integrability and `K ≠ 0` come
together, and all of its moments vanish. The article's Gaussian witness is proved separately
(`l1_truncatedPower_admissible`), using the `L¹` bound for the Hilbert transform of a Schwartz
function with vanishing integral and the Gaussian Schwartz function of
`LeanRidgelet.ToMathlib.GaussianSchwartz`.

`l1_relu_network_universal_approximation` inherits the first-moment hypothesis from the amended
reconstruction formula with the ReLU growth degree `k = 1`. The Dirac-delta and sigmoid
examples of Section 6 are deferred with the distributional pass.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

open Metric Set

/-! ## A smooth spectrum supported away from the origin -/

/-- A smooth bump on the frequency line, supported in the ball of radius `1/4` around `3/2`
and equal to `1` at `3/2`. -/
def spectrumBumpFn : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The frequency bump as a complex-valued Schwartz function. -/
def spectrumBump : SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap
    (f := fun ξ : ℝ => ((spectrumBumpFn ξ : ℝ) : ℂ))
    (spectrumBumpFn.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp spectrumBumpFn.contDiff)

theorem coe_spectrumBump (ξ : ℝ) : spectrumBump ξ = ((spectrumBumpFn ξ : ℝ) : ℂ) := rfl

theorem support_spectrumBumpFn : Function.support ⇑spectrumBumpFn = ball (3 / 2 : ℝ) (1 / 4) :=
  spectrumBumpFn.support_eq

theorem spectrumBumpFn_nonneg (ξ : ℝ) : 0 ≤ spectrumBumpFn ξ := spectrumBumpFn.nonneg

theorem spectrumBumpFn_eq_zero {ξ : ℝ} (hξ : ξ ∉ ball (3 / 2 : ℝ) (1 / 4)) :
    spectrumBumpFn ξ = 0 := by
  by_contra h
  exact hξ (support_spectrumBumpFn ▸ h)

theorem spectrumBumpFn_center : spectrumBumpFn (3 / 2 : ℝ) = 1 :=
  spectrumBumpFn.one_of_mem_closedBall (by simp [spectrumBumpFn])

/-- The explicit ridgelet function of the universality theorem: the inverse Fourier transform of
the frequency bump. Its spectrum is smooth, compactly supported and supported away from the
origin, which makes it admissible against every truncated power and gives it vanishing moments
of every order. -/
def bumpRidgeletSchwartz : SchwartzMap ℝ ℂ := 𝓕⁻ spectrumBump

def bumpRidgelet : ℝ → ℂ := ⇑bumpRidgeletSchwartz

theorem integrable_bumpRidgelet : Integrable bumpRidgelet volume :=
  SchwartzMap.integrable bumpRidgeletSchwartz

theorem fourier_bumpRidgelet : 𝓕 bumpRidgelet = ⇑spectrumBump := by
  have hFint : Integrable (𝓕 (⇑spectrumBump)) volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  rw [bumpRidgelet, bumpRidgeletSchwartz, SchwartzMap.fourierInv_coe]
  exact spectrumBump.continuous.fourier_fourierInv_eq (SchwartzMap.integrable _) hFint

theorem angularFourier1D_bumpRidgelet (ζ : ℝ) :
    angularFourier1D bumpRidgelet ζ = ((spectrumBumpFn ((2 * Real.pi)⁻¹ * ζ) : ℝ) : ℂ) := by
  rw [angularFourier1D, Fourier.angularFourierIntegralInner_eq_fourier, fourier_bumpRidgelet,
    smul_eq_mul, coe_spectrumBump]

/-! ## Admissibility against the truncated powers -/

/-- The real density of the admissibility integral of the pair `(bumpRidgelet, z₊^k)`. -/
def bumpAdmissibilityDensity (m k : ℕ) : ℝ → ℝ :=
  fun ζ => spectrumBumpFn ((2 * Real.pi)⁻¹ * ζ) / (ζ ^ (k + 1) * |ζ| ^ m)

theorem bumpAdmissibilityDensity_eq_zero_of_lt (m k : ℕ) {ζ : ℝ}
    (hζ : |ζ - 3 * Real.pi| ≥ Real.pi / 2) : bumpAdmissibilityDensity m k ζ = 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hout : ((2 * Real.pi)⁻¹ * ζ) ∉ ball (3 / 2 : ℝ) (1 / 4) := by
    simp only [mem_ball, Real.dist_eq, not_lt]
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have hrw : |(2 * Real.pi)⁻¹ * ζ - 3 / 2| = (2 * Real.pi)⁻¹ * |ζ - 3 * Real.pi| := by
      have hid : (2 * Real.pi)⁻¹ * ζ - 3 / 2 = (2 * Real.pi)⁻¹ * (ζ - 3 * Real.pi) := by
        field_simp
      rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    rw [hrw]
    calc (1 : ℝ) / 4 = (2 * Real.pi)⁻¹ * (Real.pi / 2) := by field_simp; ring
      _ ≤ (2 * Real.pi)⁻¹ * |ζ - 3 * Real.pi| := by
          exact mul_le_mul_of_nonneg_left hζ (by positivity)
  rw [bumpAdmissibilityDensity, spectrumBumpFn_eq_zero hout, zero_div]

theorem bumpAdmissibilityDensity_nonneg (m k : ℕ) (ζ : ℝ) :
    0 ≤ bumpAdmissibilityDensity m k ζ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases le_or_gt (Real.pi / 2) |ζ - 3 * Real.pi| with h | h
  · rw [bumpAdmissibilityDensity_eq_zero_of_lt m k h]
  · have hζpos : 0 < ζ := by
      rw [abs_lt] at h
      linarith [h.1]
    rw [bumpAdmissibilityDensity]
    have : (0 : ℝ) < ζ ^ (k + 1) * |ζ| ^ m := by
      have h1 : (0 : ℝ) < ζ ^ (k + 1) := pow_pos hζpos _
      have h2 : (0 : ℝ) < |ζ| ^ m := pow_pos (abs_pos.mpr hζpos.ne') m
      positivity
    exact div_nonneg (spectrumBumpFn_nonneg _) this.le

theorem continuous_bumpAdmissibilityDensity (m k : ℕ) :
    Continuous (bumpAdmissibilityDensity m k) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [continuous_iff_continuousAt]
  intro ζ
  rcases eq_or_ne ζ 0 with rfl | hζ
  · have hloc : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)] bumpAdmissibilityDensity m k := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < Real.pi)] with z hz
      refine (bumpAdmissibilityDensity_eq_zero_of_lt m k ?_).symm
      rw [mem_ball, Real.dist_eq, sub_zero] at hz
      rw [ge_iff_le, le_abs]
      right
      rw [abs_lt] at hz
      linarith [hz.2]
    exact (continuousAt_const (y := (0 : ℝ))).congr hloc
  · refine ContinuousAt.div ?_ ?_ ?_
    · exact (spectrumBumpFn.continuous.comp (by fun_prop)).continuousAt
    · exact (by fun_prop : Continuous fun z : ℝ => z ^ (k + 1) * |z| ^ m).continuousAt
    · have h1 : ζ ^ (k + 1) ≠ 0 := pow_ne_zero _ hζ
      have h2 : |ζ| ^ m ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hζ)
      exact mul_ne_zero h1 h2

theorem hasCompactSupport_bumpAdmissibilityDensity (m k : ℕ) :
    HasCompactSupport (bumpAdmissibilityDensity m k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (3 * Real.pi) (Real.pi / 2)) fun z hz => ?_
  refine bumpAdmissibilityDensity_eq_zero_of_lt m k ?_
  rw [mem_closedBall, Real.dist_eq, not_le] at hz
  exact hz.le

theorem integrable_bumpAdmissibilityDensity (m k : ℕ) :
    Integrable (bumpAdmissibilityDensity m k) volume :=
  (continuous_bumpAdmissibilityDensity m k).integrable_of_hasCompactSupport
    (hasCompactSupport_bumpAdmissibilityDensity m k)

theorem bumpAdmissibilityDensity_center_pos (m k : ℕ) :
    0 < bumpAdmissibilityDensity m k (3 * Real.pi) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcenter : (2 * Real.pi)⁻¹ * (3 * Real.pi) = 3 / 2 := by
    field_simp
  rw [bumpAdmissibilityDensity, hcenter, spectrumBumpFn_center,
    abs_of_pos (by positivity : (0 : ℝ) < 3 * Real.pi)]
  positivity

theorem integral_bumpAdmissibilityDensity_pos (m k : ℕ) :
    0 < ∫ ζ : ℝ, bumpAdmissibilityDensity m k ζ := by
  rw [integral_pos_iff_support_of_nonneg (bumpAdmissibilityDensity_nonneg m k)
    (integrable_bumpAdmissibilityDensity m k)]
  have hpos := bumpAdmissibilityDensity_center_pos m k
  have hcont : ContinuousAt (bumpAdmissibilityDensity m k) (3 * Real.pi) :=
    (continuous_bumpAdmissibilityDensity m k).continuousAt
  have hev : ∀ᶠ z in 𝓝 (3 * Real.pi), 0 < bumpAdmissibilityDensity m k z :=
    hcont.eventually (eventually_gt_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hsub : ball (3 * Real.pi) δ ⊆ Function.support (bumpAdmissibilityDensity m k) := by
    intro z hz
    exact ne_of_gt (hball (by simpa [Real.dist_eq, mem_ball] using hz))
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_ball]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- The admissibility integrand of the pair `(bumpRidgelet, z₊^k)` is a fixed nonzero constant
times the real density `bumpAdmissibilityDensity`. -/
theorem admissibilityIntegrand_bumpRidgelet (m k : ℕ) (ζ : ℝ) :
    conj (angularFourier1D bumpRidgelet ζ) * truncatedPowerFourier k ζ / ((|ζ| ^ m : ℝ) : ℂ)
      = ((Nat.factorial k : ℂ) / Complex.I ^ (k + 1)) *
          ((bumpAdmissibilityDensity m k ζ : ℝ) : ℂ) := by
  rw [angularFourier1D_bumpRidgelet, truncatedPowerFourier, bumpAdmissibilityDensity,
    Complex.conj_ofReal]
  rcases eq_or_ne ζ 0 with rfl | hζ
  · have hb : spectrumBumpFn ((2 * Real.pi)⁻¹ * (0 : ℝ)) = 0 := by
      refine spectrumBumpFn_eq_zero ?_
      simp only [mul_zero, mem_ball, Real.dist_eq, zero_sub, abs_neg]
      norm_num
    rw [hb]
    simp
  · have hIζ : (Complex.I * (ζ : ℂ)) ^ (k + 1) ≠ 0 := by
      refine pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero ?_)
      exact Complex.ofReal_ne_zero.mpr hζ
    have habs : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (abs_ne_zero.mpr hζ))
    have hζC : ((ζ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hζ
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
      mul_pow]
    field_simp

theorem integrableOn_admissibilityIntegrand_bumpRidgelet (m k : ℕ) :
    IntegrableOn
      (fun ζ => conj (angularFourier1D bumpRidgelet ζ) * truncatedPowerFourier k ζ /
        ((|ζ| ^ m : ℝ) : ℂ)) {(0 : ℝ)}ᶜ volume := by
  have h : Integrable (fun ζ : ℝ => ((Nat.factorial k : ℂ) / Complex.I ^ (k + 1)) *
      ((bumpAdmissibilityDensity m k ζ : ℝ) : ℂ)) volume :=
    ((integrable_bumpAdmissibilityDensity m k).ofReal (𝕜 := ℂ)).const_mul _
  refine (h.integrableOn).congr_fun (fun ζ _ => ?_) (measurableSet_singleton (0 : ℝ)).compl
  exact (admissibilityIntegrand_bumpRidgelet m k ζ).symm

theorem admissibilityConstant_bumpRidgelet_ne_zero (m k : ℕ) :
    admissibilityConstant m bumpRidgelet (truncatedPowerFourier k) ≠ 0 := by
  have hint : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D bumpRidgelet ζ) *
      truncatedPowerFourier k ζ / ((|ζ| ^ m : ℝ) : ℂ))
      = ((Nat.factorial k : ℂ) / Complex.I ^ (k + 1)) *
        ((∫ ζ : ℝ, bumpAdmissibilityDensity m k ζ : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun (measurableSet_singleton (0 : ℝ)).compl
      (fun ζ _ => admissibilityIntegrand_bumpRidgelet m k ζ)]
    rw [integral_const_mul, ← integral_complex_ofReal, restrict_compl_singleton 0]
  rw [admissibilityConstant, hint]
  refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
  · exact pow_ne_zero _ (by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
      (pow_ne_zero _ Complex.I_ne_zero)
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (integral_bumpAdmissibilityDensity_pos m k))

/-- **The explicit ridgelet function is admissible against every truncated power.** -/
theorem isAdmissiblePair_bumpRidgelet (m k : ℕ) :
    IsAdmissiblePair m bumpRidgelet (truncatedPower k) (truncatedPowerFourier k) :=
  ⟨integrable_bumpRidgelet, l1_truncatedPower_hasFourierAwayFromOrigin k,
    integrableOn_admissibilityIntegrand_bumpRidgelet m k,
    admissibilityConstant_bumpRidgelet_ne_zero m k⟩

/-! ## Vanishing moments, and universality of ReLU networks -/

theorem tsupport_spectrumBump : tsupport ⇑spectrumBump ⊆ {(0 : ℝ)}ᶜ := by
  have hsupp : Function.support ⇑spectrumBump = ball (3 / 2 : ℝ) (1 / 4) := by
    rw [← support_spectrumBumpFn]
    ext ξ
    simp only [Function.mem_support, ne_eq, coe_spectrumBump, Complex.ofReal_eq_zero]
  have hclos : tsupport ⇑spectrumBump ⊆ closedBall (3 / 2 : ℝ) (1 / 4) := by
    rw [tsupport, hsupp]
    exact closure_ball_subset_closedBall
  intro ξ hξ
  have h := hclos hξ
  rw [mem_closedBall, Real.dist_eq] at h
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h0
  rw [h0] at h
  norm_num at h

/-- The explicit ridgelet function has vanishing moments of every order: its spectrum is
supported away from the origin. -/
theorem integral_pow_mul_bumpRidgelet (n : ℕ) : (∫ s : ℝ, (s : ℂ) ^ n * bumpRidgelet s) = 0 := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hzero := integral_pow_mul_angularFourier1D_eq_zero spectrumBump tsupport_spectrumBump n
  have hval : ∀ s : ℝ,
      bumpRidgelet s = angularFourier1D (⇑spectrumBump) (-(2 * Real.pi) * s) := by
    intro s
    rw [angularFourier1D, Fourier.angularFourierIntegralInner_eq_fourier, smul_eq_mul,
      show (2 * Real.pi)⁻¹ * (-(2 * Real.pi) * s) = -s from by field_simp,
      bumpRidgelet, bumpRidgeletSchwartz, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg]
  set g : ℝ → ℂ := fun ζ => (ζ : ℂ) ^ n * angularFourier1D (⇑spectrumBump) ζ with hg_def
  have hsub : (∫ s : ℝ, g (-(2 * Real.pi) * s)) = |(-(2 * Real.pi))⁻¹| • ∫ ζ : ℝ, g ζ :=
    MeasureTheory.Measure.integral_comp_mul_left g (-(2 * Real.pi))
  rw [hzero, smul_zero] at hsub
  have hrel : ∀ s : ℝ, (s : ℂ) ^ n * bumpRidgelet s
      = (((-(2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ n * g (-(2 * Real.pi) * s) := by
    intro s
    have hne : ((-(2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      simp only [ne_eq, neg_eq_zero]
      positivity
    have hscal : (((-(2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ n * (((-(2 * Real.pi) * s : ℝ) : ℂ)) ^ n
        = (s : ℂ) ^ n := by
      rw [Complex.ofReal_mul, mul_pow, ← mul_assoc, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero n hne), one_mul]
    rw [hval s, hg_def]
    simp only []
    calc (s : ℂ) ^ n * angularFourier1D (⇑spectrumBump) (-(2 * Real.pi) * s)
        = ((((-(2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ n * (((-(2 * Real.pi) * s : ℝ) : ℂ)) ^ n) *
            angularFourier1D (⇑spectrumBump) (-(2 * Real.pi) * s) := by rw [hscal]
      _ = (((-(2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ n *
            ((((-(2 * Real.pi) * s : ℝ) : ℂ)) ^ n *
              angularFourier1D (⇑spectrumBump) (-(2 * Real.pi) * s)) := by ring
  rw [show (∫ s : ℝ, (s : ℂ) ^ n * bumpRidgelet s)
      = ∫ s : ℝ, (((-(2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ n * g (-(2 * Real.pi) * s) from
    integral_congr_ae (Filter.Eventually.of_forall hrel), integral_const_mul, hsub, mul_zero]

theorem integrable_weight_bumpRidgelet (k : ℕ) :
    Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖bumpRidgelet s‖) volume :=
  integrable_one_add_abs_pow_mul_schwartz bumpRidgeletSchwartz k

/-- The explicit ridgelet function is a **Lizorkin test function**: all of its moments vanish,
because its spectrum is supported away from the origin. -/
theorem bumpRidgeletSchwartz_mem_lizorkinSpace : bumpRidgeletSchwartz ∈ LizorkinSpace :=
  fun n => integral_pow_mul_bumpRidgelet n

/-- **Section 6.2 in general form**: for any Schwartz window `w`, the truncated power `z₊^k` is
admissible with the filtered ridgelet function `ψ = Λ^m w^{(ℓ+k+1)}` as soon as the `ℓ`-th
moment of `conj (ŵ)` is nonzero.

The admissibility density collapses to a constant multiple of `ζ^ℓ conj (ŵ (ζ))`: the factor
`|ζ|^m` of `(Λ^m w^{(ℓ+k+1)})^` cancels the `|ζ|^{-m}` of the density
(`l1_isAdmissiblePair_lambdaOperatorPow`), the factor `(iζ)^{ℓ+k+1}` of the `(ℓ+k+1)`-st
derivative (`angularFourier1D_iteratedDeriv`) cancels the pole `k!/(iζ)^{k+1}` of the
Gel'fand--Shilov data of `z₊^k` down to `ζ^ℓ`, and the surviving constant
`(-1)^{ℓ+k+1} i^ℓ k!` is nonzero. This is the whole mechanism of the manuscript's construction,
with the window left free. -/
theorem l1_truncatedPower_isAdmissiblePair_of_window (m : ℕ) [NeZero m] (k ℓ : ℕ)
    (w : SchwartzMap ℝ ℂ)
    (hne : (∫ ζ in {(0 : ℝ)}ᶜ, (ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑w) ζ)) ≠ 0) :
    IsAdmissiblePair m (lambdaOperatorPow m (iteratedDeriv (ℓ + k + 1) (⇑w)))
      (truncatedPower k) (truncatedPowerFourier k) := by
  set φ : SchwartzMap ℝ ℂ := (⇑(SchwartzMap.derivCLM ℂ ℂ))^[ℓ + k + 1] w with hφ_def
  have hφ : ⇑φ = iteratedDeriv (ℓ + k + 1) (⇑w) := coe_iterate_schwartz_derivCLM _ w
  set c : ℂ := (-1 : ℂ) ^ (ℓ + k + 1) * Complex.I ^ ℓ * (k.factorial : ℂ) with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ Complex.I_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  have hval : ∀ ζ : ℝ, ζ ≠ 0 →
      conj (angularFourier1D (⇑φ) ζ) * truncatedPowerFourier k ζ
        = c * ((ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑w) ζ)) := by
    intro ζ hζ
    have hζ' : (ζ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hζ
    rw [hφ, angularFourier1D_iteratedDeriv, map_mul, map_pow, map_mul, Complex.conj_I,
      Complex.conj_ofReal, truncatedPowerFourier, hc_def]
    field_simp
    ring
  have hmom : Integrable (fun ζ : ℝ => (ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑w) ζ)) volume := by
    have h := (Fourier.angularFourierSchwartz w).integrable_pow_mul volume ℓ
    refine h.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (Complex.continuous_ofReal.pow ℓ).aestronglyMeasurable
      · rw [angularFourier1D_coe_schwartz]
        exact (RCLike.continuous_conj.comp
          (Fourier.angularFourierSchwartz w).continuous).aestronglyMeasurable
    · rw [norm_mul, norm_pow, Complex.norm_real, RCLike.norm_conj, angularFourier1D_coe_schwartz]
  rw [← hφ]
  refine (l1_isAdmissiblePair_lambdaOperatorPow m φ
    (l1_truncatedPower_hasFourierAwayFromOrigin k)).2 ⟨?_, ?_⟩
  · refine (hmom.const_mul c).integrableOn.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ
    exact (hval ζ (by simpa using hζ)).symm
  · have hI : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D (⇑φ) ζ) * truncatedPowerFourier k ζ)
        = c * ∫ ζ in {(0 : ℝ)}ᶜ, (ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑w) ζ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ
      exact hval ζ (by simpa using hζ)
    rw [hI]
    exact mul_ne_zero hc hne

/-! ## The manuscript's Gaussian witness -/

/-- The Gaussian window of Section 6.2 is the Schwartz Gaussian. -/
theorem coe_gaussianSchwartz : ⇑Real.gaussianSchwartz = gaussianWindow := rfl

/-- **The angular Fourier transform of the Gaussian**: `Ĝ(ζ) = √(2π) e^{-ζ²/2}`, positive at
every frequency. In the article convention no `2π` rescaling of the frequency is needed, so this
is Mathlib's `fourierIntegral_gaussian` with `b = 1/2` and `t = -ζ`. -/
theorem angularFourier1D_gaussianWindow (ζ : ℝ) :
    angularFourier1D gaussianWindow ζ
      = ((Real.sqrt (2 * Real.pi) * Real.exp (-ζ ^ 2 / 2) : ℝ) : ℂ) := by
  have hb : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) hb ((-ζ : ℝ) : ℂ)
  rw [angularFourier1D_apply]
  have hint : (∫ z : ℝ, Complex.exp (-Complex.I * ((z * ζ : ℝ) : ℂ)) * gaussianWindow z)
      = ∫ z : ℝ, Complex.exp (Complex.I * ((-ζ : ℝ) : ℂ) * (z : ℂ)) *
          Complex.exp (-(1 / 2 : ℂ) * (z : ℂ) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    have hfac1 : Complex.exp (-Complex.I * ((z * ζ : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((-ζ : ℝ) : ℂ) * (z : ℂ)) := by
      congr 1
      push_cast
      ring
    have hfac2 : gaussianWindow z = Complex.exp (-(1 / 2 : ℂ) * (z : ℂ) ^ 2) := by
      simp only [gaussianWindow]
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hfac1, hfac2]
  rw [hint, h]
  have hconst : ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    have h1 : ((Real.pi : ℂ) / (1 / 2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  have hexpo : Complex.exp (-((-ζ : ℝ) : ℂ) ^ 2 / (4 * (1 / 2 : ℂ)))
      = ((Real.exp (-ζ ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hconst, hexpo, ← Complex.ofReal_mul]

/-- Section 6.2: the truncated power `z₊^k` is admissible with the Gaussian-derivative ridgelet
function `ψ = Λ^m G^{(ℓ+k+1)}` for every even `ℓ`.

**Deviations from the article.** The filter is the standard Lambda operator (`lambdaOperatorPow`)
rather than the article's `eq:bp`; for odd `m` the constructed `ψ` leaves the Schwartz class, so
`IsAdmissiblePair` asks only for its integrability (paper gap memo, 2026-07-19). -/
theorem l1_truncatedPower_admissible (m : ℕ) [NeZero m] (k ℓ : ℕ) (hℓ : Even ℓ) :
    IsAdmissiblePair m
      (lambdaOperatorPow m (iteratedDeriv (ℓ + k + 1) gaussianWindow))
      (truncatedPower k) (truncatedPowerFourier k) := by
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set f : ℝ → ℝ := fun ζ => ζ ^ ℓ * (Real.sqrt (2 * Real.pi) * Real.exp (-ζ ^ 2 / 2)) with hf_def
  have hfval : ∀ ζ : ℝ, f ζ = ζ ^ ℓ * (Real.sqrt (2 * Real.pi) * Real.exp (-ζ ^ 2 / 2)) :=
    fun ζ => rfl
  have hfnonneg : 0 ≤ f := by
    intro ζ
    have := hℓ.pow_nonneg ζ
    have h2 : (0 : ℝ) < Real.exp (-ζ ^ 2 / 2) := Real.exp_pos _
    positivity
  have hfint : Integrable f volume := by
    have h := (Real.gaussianSchwartz.integrable_pow_mul volume ℓ).const_mul
      (Real.sqrt (2 * Real.pi))
    refine h.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · exact (by fun_prop : Continuous f).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg ζ), hfval ζ]
      have hz : ‖ζ‖ ^ ℓ = |ζ| ^ ℓ := by rw [Real.norm_eq_abs]
      have hg : ‖Real.gaussianSchwartz ζ‖ = Real.exp (-ζ ^ 2 / 2) := by
        rw [Real.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      have hpow : ζ ^ ℓ = |ζ| ^ ℓ := (hℓ.pow_abs ζ).symm
      rw [hz, hg, hpow]
      exact le_of_eq (by ring)
  have hfpos : 0 < ∫ ζ : ℝ, f ζ := by
    rw [integral_pos_iff_support_of_nonneg hfnonneg hfint]
    have hsub : Set.Ioi (1 : ℝ) ⊆ Function.support f := by
      intro ζ hζ
      have hζ1 : (1 : ℝ) < ζ := hζ
      have hp : (0 : ℝ) < ζ ^ ℓ := pow_pos (by linarith) ℓ
      have : f ζ ≠ 0 := by
        rw [hf_def]
        positivity
      exact this
    calc (0 : ENNReal) < volume (Set.Ioi (1 : ℝ)) := by simp
      _ ≤ volume (Function.support f) := measure_mono hsub
  have hne : (∫ ζ in {(0 : ℝ)}ᶜ,
      (ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑Real.gaussianSchwartz) ζ)) ≠ 0 := by
    have hval : ∀ ζ : ℝ, (ζ : ℂ) ^ ℓ * conj (angularFourier1D (⇑Real.gaussianSchwartz) ζ)
        = ((f ζ : ℝ) : ℂ) := by
      intro ζ
      rw [coe_gaussianSchwartz, angularFourier1D_gaussianWindow, Complex.conj_ofReal,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_complex_ofReal,
      restrict_compl_singleton]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hfpos)
  have h := l1_truncatedPower_isAdmissiblePair_of_window m k ℓ Real.gaussianSchwartz hne
  rwa [coe_gaussianSchwartz] at h

/-- **Admissibility of the truncated powers** (Section 6.1--6.2), in the form the function-level
development proves: for every dimension `m` and every degree `k` there is an integrable ridgelet
function with `k`-weighted integrability and vanishing moments of every order which is admissible
against `z₊^k`. The witness is `bumpRidgelet`; see the section header for why the manuscript's
`ψ = Λ^m G^{(ℓ+k+1)}` (`l1_truncatedPower_admissible`) is not the witness used here. -/
theorem l1_truncatedPower_admissible_exists (m k : ℕ) :
    ∃ ψ : ℝ → ℂ, Integrable ψ volume ∧
      Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume ∧
      (∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0) ∧
      IsAdmissiblePair m ψ (truncatedPower k) (truncatedPowerFourier k) :=
  ⟨bumpRidgelet, integrable_bumpRidgelet, integrable_weight_bumpRidgelet k,
    fun j _ => integral_pow_mul_bumpRidgelet j, isAdmissiblePair_bumpRidgelet m k⟩

theorem norm_truncatedPower_one_le (z : ℝ) :
    ‖truncatedPower 1 z‖ ≤ 1 * (1 + |z|) ^ 1 := by
  rw [truncatedPower, one_mul, pow_one]
  by_cases hz : 0 < z
  · rw [if_pos hz, Complex.norm_real, Real.norm_eq_abs, pow_one]
    linarith [le_abs_self z, abs_nonneg z]
  · rw [if_neg hz, norm_zero]
    positivity

/-- Headline corollary of the L1 theory: neural networks with the unbounded ReLU activation are
universal approximators. For every `f ∈ L¹(ℝ^m)` with a finite first moment and
`f̂ ∈ L¹(ℝ^m)` there exist an integrable ridgelet function `ψ` and a nonzero constant `K`
such that the network `x ↦ ∫ R_ψ f (a, b) relu (⟪a, x⟫ - b) ‖a‖⁻¹ da db` reconstructs `K f`.

**Amendment to the article (author decision 2026-07-22).** The first-moment hypothesis on
`f` is inherited from the amended `l1_reconstruction_formula` with the ReLU growth degree
`k = 1`; it is necessary at function level and vacuous in the deferred distributional
pass. -/
theorem l1_relu_network_universal_approximation (m : ℕ) [NeZero m]
    {f : InputSpace m → ℂ} (hf : Integrable f volume)
    (hf1 : Integrable (fun y : InputSpace m => (1 + ‖y‖) * ‖f y‖) volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume) :
    ∃ (ψ : ℝ → ℂ) (K : ℂ), Integrable ψ volume ∧ K ≠ 0 ∧
      ∀ᵐ x ∂(volume : Measure (InputSpace m)),
        Filter.Tendsto
          (fun q : ℝ × ℝ =>
            truncatedDualRidgeletTransform m 1 (truncatedPower 1)
              (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
          ridgeletTruncationFilter (𝓝 (K * f x)) := by
  refine ⟨bumpRidgelet, admissibilityConstant m bumpRidgelet (truncatedPowerFourier 1),
    integrable_bumpRidgelet, admissibilityConstant_bumpRidgelet_ne_zero m 1, ?_⟩
  have hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ 1 * ‖f y‖) volume := by
    simpa [pow_one] using hf1
  exact (l1_reconstruction_formula m 1 (isAdmissiblePair_bumpRidgelet m 1)
    norm_truncatedPower_one_le (integrable_weight_bumpRidgelet 1)
    (fun j _ => integral_pow_mul_bumpRidgelet j) hf hfk hfhat).1

end LeanRidgelet
