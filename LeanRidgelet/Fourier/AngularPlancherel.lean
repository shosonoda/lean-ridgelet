/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.Convention
public import LeanRidgelet.ToMathlib.FourierPlancherel

/-!
# Plancherel's theorem for the angular Fourier integral on `L¹ ∩ L²`

The Schwartz-level Plancherel identity for the angular-frequency Fourier convention lives in
`LeanRidgelet.Fourier.Convention` (`angular_plancherel_schwartz_inner`). This file extends it to
`L¹ ∩ L²` on an arbitrary finite-dimensional real inner product space by rescaling the
`L¹ ∩ L²` Plancherel theorem for the Mathlib `2π` convention
(`MeasureTheory.Integrable.integral_norm_fourier_sq` in
`LeanRidgelet.ToMathlib.FourierPlancherel`):

`∫ ξ, ‖f♯ ξ‖² dξ = (2π)^dim V ⬝ ∫ x, ‖f x‖² dx`.

The `lintegral` and `MemLp` forms are provided as well; they drive the fiberwise `L²` theory of
the L1 ridgelet transform (`thm:parseval`, `thm:L2`).
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ComplexConjugate ENNReal

namespace LeanRidgelet.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The angular Fourier integral is the Mathlib Fourier integral read at the rescaled
frequency, function-level form of `angularFourierIntegralInner_eq_mathlib`. -/
theorem angularFourierIntegralInner_eq_fourier (f : V → ℂ) (ξ : V) :
    angularFourierIntegralInner f ξ = 𝓕 f ((2 * Real.pi)⁻¹ • ξ) :=
  angularFourierIntegralInner_eq_mathlib f ξ

/-- **Plancherel's theorem on `L¹ ∩ L²`** for the angular Fourier integral, `lintegral` form:
`∫⁻ ‖f♯ ξ‖ₑ² dξ = (2π)^dim V ⬝ ∫⁻ ‖f x‖ₑ² dx`. -/
theorem lintegral_enorm_angularFourierIntegralInner_sq {f : V → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    ∫⁻ ξ, ‖angularFourierIntegralInner f ξ‖ₑ ^ 2 ∂(volume : Measure V)
      = ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ V) *
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(volume : Measure V) := by
  have hπ : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
  have hFc : Continuous (𝓕 f : V → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hGm : Measurable fun w : V => ‖(𝓕 f : V → ℂ) w‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp hFc.enorm).measurable
  have hconst : ENNReal.ofReal |(((2 * Real.pi)⁻¹ : ℝ) ^ Module.finrank ℝ V)⁻¹|
      = ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ V) := by
    congr 1
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  calc ∫⁻ ξ, ‖angularFourierIntegralInner f ξ‖ₑ ^ 2 ∂(volume : Measure V)
      = ∫⁻ ξ, ‖(𝓕 f : V → ℂ) (((2 * Real.pi)⁻¹ : ℝ) • ξ)‖ₑ ^ 2 ∂(volume : Measure V) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [angularFourierIntegralInner_eq_fourier]
    _ = ∫⁻ w, ‖(𝓕 f : V → ℂ) w‖ₑ ^ 2
          ∂(Measure.map ((((2 * Real.pi)⁻¹ : ℝ)) • ·) (volume : Measure V)) :=
        (lintegral_map hGm (measurable_const_smul _)).symm
    _ = ENNReal.ofReal |(((2 * Real.pi)⁻¹ : ℝ) ^ Module.finrank ℝ V)⁻¹| *
          ∫⁻ w, ‖(𝓕 f : V → ℂ) w‖ₑ ^ 2 ∂(volume : Measure V) := by
        rw [Measure.map_addHaar_smul (volume : Measure V) hπ, lintegral_smul_measure,
          smul_eq_mul]
    _ = ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ V) *
          ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(volume : Measure V) := by
        rw [hconst, hf.lintegral_enorm_fourier_sq h2]

/-- The angular Fourier integral of an integrable function is continuous. -/
theorem continuous_angularFourierIntegralInner {f : V → ℂ} (hf : Integrable f volume) :
    Continuous (angularFourierIntegralInner f) := by
  have hFc : Continuous (𝓕 f : V → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have heq : angularFourierIntegralInner f
      = fun ξ => (𝓕 f : V → ℂ) (((2 * Real.pi)⁻¹ : ℝ) • ξ) :=
    funext fun ξ => angularFourierIntegralInner_eq_fourier f ξ
  rw [heq]
  exact hFc.comp (continuous_const_smul _)

/-- On `L¹ ∩ L²`, the angular Fourier integral is square-integrable. -/
theorem memLp_two_angularFourierIntegralInner {f : V → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    MemLp (angularFourierIntegralInner f) 2 volume := by
  have hc : Continuous (angularFourierIntegralInner f) :=
    continuous_angularFourierIntegralInner hf
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hrw : ∀ v : V → ℂ, eLpNorm v 2 volume
      = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂(volume : Measure V)) ^ ((1 : ℝ) / 2) := by
    intro v
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    norm_num [ENNReal.rpow_natCast]
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(volume : Measure V)) ≠ ∞ := by
    have h := h2.eLpNorm_lt_top
    rw [hrw] at h
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact absurd h (lt_irrefl _)
  have hlt : (∫⁻ ξ, ‖angularFourierIntegralInner f ξ‖ₑ ^ 2 ∂(volume : Measure V)) ≠ ∞ := by
    rw [lintegral_enorm_angularFourierIntegralInner_sq hf h2]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin)).ne
  rw [hrw]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt

/-- **Plancherel's theorem on `L¹ ∩ L²`** for the angular Fourier integral:
`∫ ‖f♯ ξ‖² dξ = (2π)^dim V ⬝ ∫ ‖f x‖² dx`. -/
theorem integral_norm_angularFourierIntegralInner_sq {f : V → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    ∫ ξ, ‖angularFourierIntegralInner f ξ‖ ^ 2 ∂(volume : Measure V)
      = (2 * Real.pi) ^ Module.finrank ℝ V * ∫ x, ‖f x‖ ^ 2 ∂(volume : Measure V) := by
  rw [MeasureTheory.integral_norm_sq_eq_toReal_lintegral
      (memLp_two_angularFourierIntegralInner hf h2).aestronglyMeasurable,
    MeasureTheory.integral_norm_sq_eq_toReal_lintegral h2.aestronglyMeasurable,
    lintegral_enorm_angularFourierIntegralInner_sq hf h2,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The angular inverse Fourier integral is the `(2π)^dim V`-rescaled Mathlib inverse
transform of the Mathlib transform: `∫ ξ, f♯(ξ) e^{i⟨ξ,x⟩} dξ = (2π)^d ⋅ 𝓕⁻(𝓕 f)(x)`.
Together with the Fourier inversion theorems this computes the angular inverse integral of
the spectral data of an integrable function. -/
theorem integral_angularFourierIntegralInner_mul_exp (f : V → ℂ) (x : V) :
    (∫ ξ, angularFourierIntegralInner f ξ *
        Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
      = (((2 * Real.pi) ^ Module.finrank ℝ V : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) x := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcov := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure V))
    (fun w : V => 𝓕 f w * Complex.exp (Complex.I *
      ((2 * Real.pi * inner ℝ w x : ℝ) : ℂ))) ((2 * Real.pi)⁻¹)
  have hleft : (∫ ξ : V, (fun w : V => 𝓕 f w * Complex.exp (Complex.I *
      ((2 * Real.pi * inner ℝ w x : ℝ) : ℂ))) (((2 * Real.pi)⁻¹ : ℝ) • ξ))
      = ∫ ξ, angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [← angularFourierIntegralInner_eq_fourier]
    congr 3
    rw [real_inner_smul_left]
    field_simp
  have hF : (∫ w : V, 𝓕 f w * Complex.exp (Complex.I *
      ((2 * Real.pi * inner ℝ w x : ℝ) : ℂ))) = 𝓕⁻ (𝓕 f) x := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [smul_eq_mul, mul_comm]
    congr 1
    ring
  rw [hleft, hF] at hcov
  rw [hcov, Complex.real_smul]
  congr 2
  rw [abs_inv, abs_pow, abs_inv, abs_of_pos hπ, inv_pow, inv_inv]

/-- **Parseval's relation on `L¹ ∩ L²`** for the angular Fourier integral:
`∫ f♯(ξ) conj (g♯(ξ)) dξ = (2π)^dim V ⋅ ∫ f(x) conj (g(x)) dx`. -/
theorem integral_angularFourierIntegralInner_mul_conj {f g : V → ℂ}
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (∫ ξ, angularFourierIntegralInner f ξ * conj (angularFourierIntegralInner g ξ))
      = (((2 * Real.pi) ^ Module.finrank ℝ V : ℝ) : ℂ) * ∫ x, f x * conj (g x) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcov := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure V))
    (fun w : V => 𝓕 f w * conj (𝓕 g w)) ((2 * Real.pi)⁻¹)
  have hleft : (∫ ξ : V, (fun w : V => 𝓕 f w * conj (𝓕 g w))
      (((2 * Real.pi)⁻¹ : ℝ) • ξ))
      = ∫ ξ, angularFourierIntegralInner f ξ * conj (angularFourierIntegralInner g ξ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [← angularFourierIntegralInner_eq_fourier, ← angularFourierIntegralInner_eq_fourier]
  have habs : |(((2 * Real.pi)⁻¹ : ℝ) ^ Module.finrank ℝ V)⁻¹|
      = (2 * Real.pi) ^ Module.finrank ℝ V := by
    rw [abs_inv, abs_pow, abs_inv, abs_of_pos hπ, inv_pow, inv_inv]
  rw [hleft, habs] at hcov
  rw [hcov, hf1.integral_fourier_mul_conj_fourier hf2 hg1 hg2, Complex.real_smul]

end LeanRidgelet.Fourier