/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.ReconstructionSection
public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.ToMathlib.FourierInversion

/-!
# L1 theory: the reconstruction formula (steps T5--T6)

The truncated reconstruction is rewritten as a spectral pairing against the admissibility
density `u(ζ) = conj (ψ̂ ζ) Fη(ζ) / |ζ|^m` and the truncation limit is taken.

## Main results

* `LeanRidgelet.truncatedSpectralWindow_eq`: the spectral window
  `G_{x,ε,δ}(ζ) = ∫_{|ζ|ε ≤ ‖ξ‖ ≤ |ζ|δ} f̂(ξ) e^{i⟨ξ,x⟩} dξ` is the `|ζ|^m`-rescaled spectral
  factor.
* `LeanRidgelet.truncatedDualRidgeletTransform_eq_spectral_pairing`: **step T5**,
  `R†_η[R_ψ f](x; ε, δ) = (2π)⁻¹ ∫_{ζ ≠ 0} u(ζ) G_{x,ε,δ}(ζ) dζ`.
* `LeanRidgelet.tendsto_truncatedDualRidgeletTransform`: **step T6**, the truncation limit
  along the filter `(𝓝[>] 0) ×ˢ atTop`.
* `LeanRidgelet.l1_reconstruction_formula`: `thm:formula`, `R†_η R_ψ f = K_{ψ,η} f` in the
  truncation limit, almost everywhere and at every continuity point of `f`.

## Deviations from the article

`l1_reconstruction_formula` is the amended function-level statement (author decision
2026-07-22): the growth degree `k` of the activation is explicit and matched by `k`-th moments
of `ψ` and of `f`, and `ψ` is required to have `k` vanishing moments — the condition in the
article's own remark after `thm:eq.ac`. All three hypotheses are vacuous in the deferred
distributional pass.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The spectral window and the spectral pairing (step T5) -/

/-- The spectral window `G_{x,ε,δ}(ζ) = ∫_{|ζ|ε ≤ ‖ξ‖ ≤ |ζ|δ} f̂(ξ) e^{i⟨ξ,x⟩} dξ`
(step T5): the inverse Fourier integral of the signal truncated to the dilated annulus. -/
def truncatedSpectralWindow (m : ℕ) (f : InputSpace m → ℂ) (x : InputSpace m)
    (ε δ : ℝ) (ζ : ℝ) : ℂ :=
  ∫ ξ in scaleAnnulus m (|ζ| * ε) (|ζ| * δ),
    Fourier.angularFourierIntegralInner f ξ *
      Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))

/-- Dilation identity (step T5): the spectral window is the `|ζ|^m`-rescaled spectral factor,
`G_{x,ε,δ}(ζ) = |ζ|^m ⋅ H_{x,ε,δ}(ζ)`, by the change of variables `ξ = ζ • a`. -/
theorem truncatedSpectralWindow_eq (m : ℕ) (f : InputSpace m → ℂ) (x : InputSpace m)
    (ε δ : ℝ) {ζ : ℝ} (hζ : ζ ≠ 0) :
    truncatedSpectralWindow m f x ε δ ζ
      = ((|ζ| ^ m : ℝ) : ℂ) * truncatedSpectralFactor m f x ε δ ζ := by
  have hζ' : (0 : ℝ) < |ζ| := abs_pos.mpr hζ
  have hpow : (0 : ℝ) < |ζ| ^ m := by positivity
  have hmeas := measurableSet_scaleAnnulus m (|ζ| * ε) (|ζ| * δ)
  set g : InputSpace m → ℂ := fun ξ => Fourier.angularFourierIntegralInner f ξ *
    Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) with hg_def
  have hmem : ∀ a : InputSpace m,
      ζ • a ∈ scaleAnnulus m (|ζ| * ε) (|ζ| * δ) ↔ a ∈ scaleAnnulus m ε δ := by
    intro a
    simp only [scaleAnnulus, Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨le_of_mul_le_mul_left h1 hζ', le_of_mul_le_mul_left h2 hζ'⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_le_mul_of_nonneg_left h1 hζ'.le, mul_le_mul_of_nonneg_left h2 hζ'.le⟩
  have hcov := MeasureTheory.Measure.integral_comp_smul
    (μ := (volume : Measure (InputSpace m)))
    ((scaleAnnulus m (|ζ| * ε) (|ζ| * δ)).indicator g) ζ
  have hleft : (∫ a : InputSpace m,
      (scaleAnnulus m (|ζ| * ε) (|ζ| * δ)).indicator g (ζ • a))
      = truncatedSpectralFactor m f x ε δ ζ := by
    have hind : ∀ a : InputSpace m,
        (scaleAnnulus m (|ζ| * ε) (|ζ| * δ)).indicator g (ζ • a)
          = (scaleAnnulus m ε δ).indicator (fun a' => g (ζ • a')) a := by
      intro a
      by_cases ha : a ∈ scaleAnnulus m ε δ
      · rw [Set.indicator_of_mem ((hmem a).mpr ha), Set.indicator_of_mem ha]
      · rw [Set.indicator_of_notMem (fun h => ha ((hmem a).mp h)),
          Set.indicator_of_notMem ha]
    rw [integral_congr_ae (Filter.Eventually.of_forall hind),
      integral_indicator (measurableSet_scaleAnnulus m ε δ)]
    rw [truncatedSpectralFactor]
    refine setIntegral_congr_ae (measurableSet_scaleAnnulus m ε δ) ?_
    refine Filter.Eventually.of_forall fun a _ => ?_
    rw [hg_def]
    simp only []
    rw [real_inner_smul_left]
  rw [hleft, integral_indicator hmeas] at hcov
  have habs : |((ζ : ℝ) ^ Module.finrank ℝ (InputSpace m))⁻¹| = (|ζ| ^ m)⁻¹ := by
    rw [show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin,
      abs_inv, abs_pow]
  rw [habs] at hcov
  rw [hcov, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow.ne']
  norm_num
  rfl

/-- The reconstruction section is integrable (step T2). -/
theorem integrable_truncatedReconstructionSection (m k : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (x : InputSpace m) (ε δ : ℝ) :
    Integrable (truncatedReconstructionSection m ψ f x ε δ) volume := by
  refine (integrable_weight_truncatedReconstructionSection m k hf hfk hψm hψk x ε δ).mono'
    (aestronglyMeasurable_truncatedReconstructionSection m hf hψm x ε δ)
    (Filter.Eventually.of_forall fun r => ?_)
  have h1 : (1 : ℝ) ≤ (1 + |r|) ^ k :=
    one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg r))
  nlinarith [norm_nonneg (truncatedReconstructionSection m ψ f x ε δ r)]

/-- Absolute convergence of the spectral pairing (step T5): the admissibility density
`u(ζ) = conj(ψ̂ ζ) Fη ζ / |ζ|^m` and the dilation bound on the spectral factor dominate the
pairing integrand of the extension theorem, `‖Fη(ζ) Ξ̂(-ζ)‖ ≤ ‖u(ζ)‖ ⋅ ‖f̂‖₁`. -/
theorem integrableOn_fourierData_truncatedReconstructionSection (m k : ℕ)
    {ψ Fη : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (hFηm : AEStronglyMeasurable Fη ((volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ))
    (hKint : IntegrableOn
      (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      {(0 : ℝ)}ᶜ volume)
    (x : InputSpace m) (ε δ : ℝ) :
    IntegrableOn (fun ζ : ℝ => Fη ζ *
      angularFourier1D (truncatedReconstructionSection m ψ f x ε δ) (-ζ))
      {(0 : ℝ)}ᶜ volume := by
  have hΞhatc : Continuous
      (angularFourier1D (truncatedReconstructionSection m ψ f x ε δ)) :=
    Fourier.continuous_angularFourierIntegralInner
      (integrable_truncatedReconstructionSection m k hf hfk hψm hψk x ε δ)
  have hCf0 : (0 : ℝ) ≤ ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ :=
    integral_nonneg fun ξ => norm_nonneg _
  refine ((hKint.norm.mul_const
    (∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖)).mono' ?_ ?_)
  · exact hFηm.mul ((hΞhatc.comp continuous_neg).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem ((measurableSet_singleton (0 : ℝ)).compl)] with ζ hζ
    have hζ0 : ζ ≠ 0 := by simpa using hζ
    have habs : (0 : ℝ) < |ζ| ^ m := by
      have := abs_pos.mpr hζ0
      positivity
    have hT2c := angularFourier1D_truncatedReconstructionSection m k hf hfk hψm hψk
      x ε δ (-ζ)
    rw [neg_neg] at hT2c
    rw [norm_mul, hT2c, norm_mul, RCLike.norm_conj]
    have hu : ‖conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ)‖
        = ‖angularFourier1D ψ ζ‖ * ‖Fη ζ‖ / |ζ| ^ m := by
      rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos habs]
    have hH := norm_truncatedSpectralFactor_le_of_ne m hfhat x ε δ hζ0
    calc ‖Fη ζ‖ * (‖angularFourier1D ψ ζ‖ * ‖truncatedSpectralFactor m f x ε δ ζ‖)
        ≤ ‖Fη ζ‖ * (‖angularFourier1D ψ ζ‖ *
            (|ζ|⁻¹ ^ m * ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖)) := by
          gcongr
      _ = ‖angularFourier1D ψ ζ‖ * ‖Fη ζ‖ / |ζ| ^ m *
            ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := by
          rw [inv_pow]
          ring
      _ = ‖conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ)‖ *
            ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := by
          rw [hu]

/-- The spectral pairing identity (step T5): against the Fourier data of the activation, the
reconstruction section pairs into the admissibility density and the spectral window,
`∫_{ζ≠0} Fη(ζ) Ξ̂(-ζ) dζ = ∫_{ζ≠0} u(ζ) G_{x,ε,δ}(ζ) dζ`. -/
theorem setIntegral_fourierData_truncatedReconstructionSection (m k : ℕ)
    {ψ Fη : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (x : InputSpace m) (ε δ : ℝ) :
    (∫ ζ in {(0 : ℝ)}ᶜ, Fη ζ *
        angularFourier1D (truncatedReconstructionSection m ψ f x ε δ) (-ζ))
      = ∫ ζ in {(0 : ℝ)}ᶜ,
          conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
            truncatedSpectralWindow m f x ε δ ζ := by
  refine setIntegral_congr_ae (measurableSet_singleton (0 : ℝ)).compl ?_
  refine Filter.Eventually.of_forall fun ζ hζ => ?_
  have hζ0 : ζ ≠ 0 := by simpa using hζ
  have habs : (|ζ| ^ m : ℝ) ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hζ0)
  have hcast : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr habs
  have hT2c := angularFourier1D_truncatedReconstructionSection m k hf hfk hψm hψk
    x ε δ (-ζ)
  rw [neg_neg] at hT2c
  rw [hT2c, truncatedSpectralWindow_eq m f x ε δ hζ0]
  field_simp

/-- **Steps T1–T5 combined**: under matched growth and moments and an absolutely convergent
admissibility density, the truncated reconstruction is the spectral pairing
`R†_η[R_ψ f](x; ε, δ) = (2π)⁻¹ ∫_{ζ≠0} u(ζ) G_{x,ε,δ}(ζ) dζ` of the admissibility density
`u(ζ) = conj(ψ̂ ζ) Fη ζ / |ζ|^m` against the spectral window. -/
theorem truncatedDualRidgeletTransform_eq_spectral_pairing (m k : ℕ)
    {ψ η Fη : ℝ → ℂ} {f : InputSpace m → ℂ} {Cη : ℝ}
    (hη : HasFourierAwayFromOrigin η Fη)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (hKint : IntegrableOn
      (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      {(0 : ℝ)}ᶜ volume)
    (x : InputSpace m) {ε δ : ℝ} (hε : 0 < ε) :
    truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ x
      = (2 * Real.pi)⁻¹ * ∫ ζ in {(0 : ℝ)}ᶜ,
          conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
            truncatedSpectralWindow m f x ε δ ζ := by
  have hηm : AEStronglyMeasurable η volume := hη.1.aestronglyMeasurable
  have hFηm : AEStronglyMeasurable Fη ((volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ) :=
    hη.2.2.1.aestronglyMeasurable
  rw [truncatedDualRidgeletTransform_eq_section_pairing m k hf hfk hψm hηm hψk hηk x hε]
  rw [hasFourierAwayFromOrigin_pairing_extension k hη hηk
    (aestronglyMeasurable_truncatedReconstructionSection m hf hψm x ε δ)
    (integrable_weight_truncatedReconstructionSection m k hf hfk hψm hψk x ε δ)
    (fun j hj => integral_pow_mul_truncatedReconstructionSection_eq_zero m k hf hfk hψm
      hψk hψvm x ε δ hj)
    (integrableOn_fourierData_truncatedReconstructionSection m k hf hfk hψm hψk hfhat
      hFηm hKint x ε δ)]
  congr 1
  exact setIntegral_fourierData_truncatedReconstructionSection m k hf hfk hψm hψk x ε δ

/-! ## The truncation limit and Fourier inversion (step T6) -/

/-- Uniform bound of the spectral window by the spectral mass (step T6):
`‖G_{x,ε,δ}(ζ)‖ ≤ ‖f̂‖₁` for all scales and truncations. -/
theorem norm_truncatedSpectralWindow_le (m : ℕ) {f : InputSpace m → ℂ}
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (x : InputSpace m) (ε δ ζ : ℝ) :
    ‖truncatedSpectralWindow m f x ε δ ζ‖
      ≤ ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := by
  rw [truncatedSpectralWindow]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have h1 : (∫ ξ in scaleAnnulus m (|ζ| * ε) (|ζ| * δ),
      ‖Fourier.angularFourierIntegralInner f ξ *
        Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))‖)
      = ∫ ξ in scaleAnnulus m (|ζ| * ε) (|ζ| * δ),
        ‖Fourier.angularFourierIntegralInner f ξ‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  rw [h1]
  exact setIntegral_le_integral hfhat.norm
    (Filter.Eventually.of_forall fun ξ => norm_nonneg _)

/-- The spectral factor is continuous in the frequency (step T6). -/
theorem continuous_truncatedSpectralFactor (m : ℕ) {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (x : InputSpace m) (ε δ : ℝ) :
    Continuous (truncatedSpectralFactor m f x ε δ) := by
  have hfhatc := Fourier.continuous_angularFourierIntegralInner hf
  have hbound : ∀ ξ : InputSpace m,
      ‖Fourier.angularFourierIntegralInner f ξ‖ ≤ ∫ y, ‖f y‖ := by
    intro ξ
    rw [Fourier.angularFourierIntegralInner]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
    simp only []
    rw [norm_mul, Complex.norm_exp]
    have hre : (-Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, one_mul]
  haveI : IsFiniteMeasure ((volume : Measure (InputSpace m)).restrict
      (scaleAnnulus m ε δ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_scaleAnnulus_lt_top m ε δ
  refine MeasureTheory.continuous_of_dominated
    (bound := fun _ : InputSpace m => ∫ y, ‖f y‖) ?_ ?_ ?_ ?_
  · intro ζ
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (hfhatc.comp ?_) ?_
    · exact (by fun_prop : Continuous fun a : InputSpace m => ζ • a)
    · exact Complex.continuous_exp.comp (by fun_prop :
        Continuous fun a : InputSpace m => Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ))
  · intro ζ
    refine Filter.Eventually.of_forall fun a => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
    exact hbound _
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun a => ?_
    refine Continuous.mul (hfhatc.comp ?_) ?_
    · exact (by fun_prop : Continuous fun ζ : ℝ => ζ • a)
    · exact Complex.continuous_exp.comp (by fun_prop :
        Continuous fun ζ : ℝ => Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ))

/-- Pointwise truncation limit of the spectral window (step T6): at every nonzero frequency
the window converges to the full inverse spectral integral along the truncation filter. -/
theorem tendsto_truncatedSpectralWindow (m : ℕ) [NeZero m] {f : InputSpace m → ℂ}
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (x : InputSpace m) {ζ : ℝ} (hζ : ζ ≠ 0) :
    Filter.Tendsto (fun q : ℝ × ℝ => truncatedSpectralWindow m f x q.1 q.2 ζ)
      ridgeletTruncationFilter
      (𝓝 (∫ ξ, Fourier.angularFourierIntegralInner f ξ *
        Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))) := by
  classical
  haveI : Filter.IsCountablyGenerated ridgeletTruncationFilter := by
    unfold ridgeletTruncationFilter
    infer_instance
  have hζ' : (0 : ℝ) < |ζ| := abs_pos.mpr hζ
  set g : InputSpace m → ℂ := fun ξ => Fourier.angularFourierIntegralInner f ξ *
    Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) with hg_def
  have hgm : AEStronglyMeasurable g volume := by
    refine hfhat.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact Complex.continuous_exp.comp (by fun_prop :
      Continuous fun ξ : InputSpace m => Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))
  have hae : ∀ᵐ ξ : InputSpace m ∂volume, ξ ≠ 0 := by
    refine mem_ae_iff.mpr ?_
    rw [show {ξ : InputSpace m | ξ ≠ 0}ᶜ = {(0 : InputSpace m)} from by ext ξ; simp]
    exact measure_singleton 0
  have hind : ∀ q : ℝ × ℝ,
      (∫ ξ, (scaleAnnulus m (|ζ| * q.1) (|ζ| * q.2)).indicator g ξ)
        = truncatedSpectralWindow m f x q.1 q.2 ζ := fun q =>
    integral_indicator (measurableSet_scaleAnnulus _ _ _)
  refine Filter.Tendsto.congr hind
    (tendsto_integral_filter_of_dominated_convergence
      (fun ξ => ‖Fourier.angularFourierIntegralInner f ξ‖) ?_ ?_ hfhat.norm ?_)
  · refine Filter.Eventually.of_forall fun q => ?_
    exact hgm.indicator (measurableSet_scaleAnnulus _ _ _)
  · refine Filter.Eventually.of_forall fun q => ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    refine le_trans (norm_indicator_le_norm_self _ _) ?_
    rw [hg_def]
    simp only []
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  · filter_upwards [hae] with ξ hξ0
    have hc : (0 : ℝ) < ‖ξ‖ / |ζ| := div_pos (norm_pos_iff.mpr hξ0) hζ'
    have h1 : ∀ᶠ ε' in 𝓝[>] (0 : ℝ), ε' < ‖ξ‖ / |ζ| :=
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const hc
    have h2 : ∀ᶠ δ' in (Filter.atTop : Filter ℝ), ‖ξ‖ / |ζ| ≤ δ' :=
      Filter.eventually_ge_atTop _
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    unfold ridgeletTruncationFilter
    refine Filter.eventually_of_mem (Filter.prod_mem_prod h1 h2) ?_
    intro q hq
    have hmem : ξ ∈ scaleAnnulus m (|ζ| * q.1) (|ζ| * q.2) := by
      refine ⟨?_, ?_⟩
      · have := hq.1
        rw [Set.mem_setOf_eq] at this
        nlinarith [(lt_div_iff₀ hζ').mp this]
      · have := hq.2
        rw [Set.mem_setOf_eq] at this
        nlinarith [(div_le_iff₀ hζ').mp this]
    exact (Set.indicator_of_mem hmem g).symm

set_option maxHeartbeats 400000 in
-- The proof is a single long dominated-convergence assembly over the truncation filter.
/-- **Step T6, truncation limit**: the truncated reconstruction converges along the
truncation filter to the admissibility constant times the normalized inverse spectral
integral. -/
theorem tendsto_truncatedDualRidgeletTransform (m k : ℕ) [NeZero m]
    {ψ η Fη : ℝ → ℂ} {f : InputSpace m → ℂ} {Cη : ℝ}
    (hη : HasFourierAwayFromOrigin η Fη)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (hKint : IntegrableOn (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ /
      ((|ζ| ^ m : ℝ) : ℂ)) {(0 : ℝ)}ᶜ volume)
    (x : InputSpace m) :
    Filter.Tendsto (fun q : ℝ × ℝ => truncatedDualRidgeletTransform m 1 η
        (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
      ridgeletTruncationFilter
      (𝓝 (admissibilityConstant m ψ Fη * ((((2 * Real.pi) ^ m : ℝ) : ℂ))⁻¹ *
        ∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))) := by
  classical
  haveI : Filter.IsCountablyGenerated ridgeletTruncationFilter := by
    unfold ridgeletTruncationFilter
    infer_instance
  -- the dominated-convergence limit of the spectral pairing
  have hDCT : Filter.Tendsto (fun q : ℝ × ℝ => ∫ ζ in {(0 : ℝ)}ᶜ,
      conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
        truncatedSpectralWindow m f x q.1 q.2 ζ) ridgeletTruncationFilter
      (𝓝 (∫ ζ in {(0 : ℝ)}ᶜ,
        conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
          ∫ ξ, Fourier.angularFourierIntegralInner f ξ *
            Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ζ => ‖conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ)‖ *
        ∫ ξ', ‖Fourier.angularFourierIntegralInner f ξ'‖) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun q => ?_
      have hcont : Continuous fun ζ : ℝ => ((|ζ| ^ m : ℝ) : ℂ) *
          truncatedSpectralFactor m f x q.1 q.2 ζ := by
        refine Continuous.mul ?_ (continuous_truncatedSpectralFactor m hf x q.1 q.2)
        fun_prop
      refine AEStronglyMeasurable.congr
        (hKint.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ
      have hζ0 : ζ ≠ 0 := by simpa using hζ
      simp only [Pi.mul_apply]
      rw [truncatedSpectralWindow_eq m f x q.1 q.2 hζ0]
    · refine Filter.Eventually.of_forall fun q => ?_
      refine Filter.Eventually.of_forall fun ζ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_truncatedSpectralWindow_le m hfhat x q.1 q.2 ζ) (norm_nonneg _)
    · exact hKint.norm.mul_const _
    · filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ
      have hζ0 : ζ ≠ 0 := by simpa using hζ
      exact (tendsto_truncatedSpectralWindow m hfhat x hζ0).const_mul _
  -- transfer along the T5 identity, eventually in the truncation
  have hev : ∀ᶠ q : ℝ × ℝ in ridgeletTruncationFilter, (0 : ℝ) < q.1 := by
    unfold ridgeletTruncationFilter
    refine Filter.eventually_of_mem
      (Filter.prod_mem_prod self_mem_nhdsWithin Filter.univ_mem) ?_
    intro q hq
    exact hq.1
  have htend := hDCT.const_mul ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)
  have heq : (fun q : ℝ × ℝ => ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ in {(0 : ℝ)}ᶜ,
      conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
        truncatedSpectralWindow m f x q.1 q.2 ζ)
      =ᶠ[ridgeletTruncationFilter] fun q : ℝ × ℝ =>
        truncatedDualRidgeletTransform m 1 η
          (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x := by
    filter_upwards [hev] with q hq
    exact (truncatedDualRidgeletTransform_eq_spectral_pairing m k hη hηk hψm hψk hψvm
      hf hfk hfhat hKint x hq).symm
  have hfinal := htend.congr' heq
  -- identify the limit constant
  have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne m))
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
  have hlimit : ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ in {(0 : ℝ)}ᶜ,
      conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) *
        ∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))
      = admissibilityConstant m ψ Fη * ((((2 * Real.pi) ^ m : ℝ) : ℂ))⁻¹ *
        ∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) := by
    rw [integral_mul_const, admissibilityConstant]
    have hpowm : (((2 * Real.pi) ^ m : ℝ) : ℂ)
        = ((2 : ℂ) * (Real.pi : ℂ)) ^ (m - 1) * ((2 : ℂ) * (Real.pi : ℂ)) := by
      push_cast
      rw [← pow_succ, hm1]
    rw [hpowm]
    have h2πC : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    push_cast
    field_simp
  rw [hlimit] at hfinal
  exact hfinal

/-- The truncation limit is the inverse Fourier integral, almost everywhere: for `f ∈ L¹`
with `f̂ ∈ L¹`, `∫ f̂(ξ) e^{i⟨ξ,x⟩} dξ = (2π)^m f(x)` at almost every `x`. -/
theorem ae_integral_angularFourier_mul_exp (m : ℕ) {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume) :
    ∀ᵐ x ∂(volume : Measure (InputSpace m)),
      (∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x := by
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h𝓕 : Integrable (𝓕 f) (volume : Measure (InputSpace m)) := by
    have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure (InputSpace m))
      (Fourier.angularFourierIntegralInner f) hne).mpr hfhat
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [Fourier.angularFourierIntegralInner_eq_fourier]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  filter_upwards [hf.fourierInv_fourier_ae_eq h𝓕] with x hx
  rw [Fourier.integral_angularFourierIntegralInner_mul_exp f x,
    show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin, hx]

/-- The truncation limit is the inverse Fourier integral at continuity points. -/
theorem integral_angularFourier_mul_exp_of_continuousAt (m : ℕ) {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    {x : InputSpace m} (hx : ContinuousAt f x) :
    (∫ ξ, Fourier.angularFourierIntegralInner f ξ *
        Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
      = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x := by
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h𝓕 : Integrable (𝓕 f) (volume : Measure (InputSpace m)) := by
    have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure (InputSpace m))
      (Fourier.angularFourierIntegralInner f) hne).mpr hfhat
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [Fourier.angularFourierIntegralInner_eq_fourier]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [Fourier.integral_angularFourierIntegralInner_mul_exp f x,
    show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin,
    hf.fourierInv_fourier_eq h𝓕 hx]

/-- Theorem 5.6 (`thm:formula`), the reconstruction formula, in the amended function-level
form: for an admissible pair `(ψ, η)` whose activation has polynomial growth of degree `k`,
a ridgelet function with finite `k`-th moment and `k` vanishing moments, and `f ∈ L¹(ℝ^m)`
with finite `k`-th moment and `f̂ ∈ L¹(ℝ^m)`, the truncated dual ridgelet transform of
`R_ψ f` converges to `K_{ψ,η} f (x)` at almost every `x` and at every continuity point of
`f`.

**Amendment to the article (author decision 2026-07-22).** The article states the theorem
for `(ψ, η) ∈ 𝒮(ℝ) × 𝒮₀'(ℝ)` with a distributional pairing. At function level the added
hypotheses are necessary: for growth degree `k ≥ 1` there are `f ∈ L¹` with `f̂ ∈ L¹`
(Gaussian bumps of weight `2⁻ⁿ` at distance `4ⁿ`) whose truncated reconstruction integrand
is not Bochner integrable, and without vanishing moments the function-level pairing sees the
polynomial part of `η`, which the Lizorkin quotient hides (the article's remark after
`thm:eq.ac` imposes the same vanishing moments). All three added hypotheses are vacuous in
the deferred distributional pass. -/
theorem l1_reconstruction_formula (m k : ℕ) [NeZero m]
    {ψ η Fη : ℝ → ℂ} {f : InputSpace m → ℂ} {Cη : ℝ}
    (hadm : IsAdmissiblePair m ψ η Fη)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume) :
    (∀ᵐ x ∂(volume : Measure (InputSpace m)),
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          truncatedDualRidgeletTransform m 1 η
            (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
        ridgeletTruncationFilter (𝓝 (admissibilityConstant m ψ Fη * f x))) ∧
    ∀ x, ContinuousAt f x →
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          truncatedDualRidgeletTransform m 1 η
            (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
        ridgeletTruncationFilter (𝓝 (admissibilityConstant m ψ Fη * f x)) := by
  obtain ⟨hψint, hη, hKint, -⟩ := hadm
  have hψm : AEStronglyMeasurable ψ volume := hψint.aestronglyMeasurable
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpowC : (((2 * Real.pi) ^ m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hcore := fun x => tendsto_truncatedDualRidgeletTransform m k hη hηk hψm hψk
    hψvm hf hfk hfhat hKint x
  have hclean : ∀ x : InputSpace m,
      (∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x →
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          truncatedDualRidgeletTransform m 1 η
            (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
        ridgeletTruncationFilter (𝓝 (admissibilityConstant m ψ Fη * f x)) := by
    intro x hx
    have h := hcore x
    have hlim : admissibilityConstant m ψ Fη * ((((2 * Real.pi) ^ m : ℝ) : ℂ))⁻¹ *
        (∫ ξ, Fourier.angularFourierIntegralInner f ξ *
          Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        = admissibilityConstant m ψ Fη * f x := by
      rw [hx]
      field_simp
    rw [hlim] at h
    exact h
  constructor
  · filter_upwards [ae_integral_angularFourier_mul_exp m hf hfhat] with x hx
    exact hclean x hx
  · intro x hxc
    exact hclean x (integral_angularFourier_mul_exp_of_continuousAt m hf hfhat hxc)

end LeanRidgelet
