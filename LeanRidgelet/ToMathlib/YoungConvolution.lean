/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Young's convolution inequality for `L¹ ⋆ L^p`

Mathlib (as of the pinned version) has neither Young's convolution inequality nor the continuous
Minkowski integral inequality. This file proves the special case needed by the ridgelet theory:
on a measurable additive commutative group with an invariant σ-finite measure, the convolution of
an `L¹` function with an `L^p` function is in `L^p` for `1 ≤ p`, with
`‖f ⋆ g‖_p ≤ ‖f‖₁ ‖g‖_p`.

The proof avoids the Minkowski integral inequality by the classical Hölder splitting
`‖f t‖ ‖g (x - t)‖ = ‖f t‖^{1/q} ⋅ (‖f t‖^{1/p} ‖g (x - t)‖)`, the two-function Hölder
inequality `ENNReal.lintegral_mul_le_Lp_mul_Lq`, Tonelli's theorem, and translation invariance.

These lemmas are stated for scalar-valued functions and are candidates for upstreaming to
Mathlib in bilinear-map generality.

## Main results

* `MeasureTheory.eLpNorm_convolution_le`: `‖f ⋆ g‖_p ≤ ‖f‖₁ ‖g‖_p` for `1 ≤ p ≤ ∞`, with no
  integrability hypotheses (both sides may be infinite).
* `MeasureTheory.Integrable.convolution_memLp`: membership form for `f ∈ L¹`, `g ∈ L^p`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

section EnormBound

variable {G : Type*} [MeasurableSpace G] [Sub G] {μ : Measure G}

/-- The convolution integral is dominated by the `lintegral` of the pointwise product of
extended norms. -/
theorem enorm_integral_mul_sub_le (f g : G → ℂ) (x : G) :
    ‖∫ t, f t * g (x - t) ∂μ‖ₑ ≤ ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
  simp_rw [enorm_mul]

end EnormBound

section RightInvariant

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]

/-- Tonelli's theorem combined with translation invariance: the iterated `lintegral` of a
convolution-shaped product of nonnegative functions factors into the product of the total
integrals. -/
theorem lintegral_lintegral_mul_comp_sub (F K : G → ℝ≥0∞)
    (hF : AEMeasurable F μ) (hK : AEMeasurable K μ) :
    ∫⁻ x, ∫⁻ t, F t * K (x - t) ∂μ ∂μ = (∫⁻ t, F t ∂μ) * ∫⁻ y, K y ∂μ := by
  have hprod : AEMeasurable (Function.uncurry fun x t => F t * K (x - t)) (μ.prod μ) := by
    refine AEMeasurable.mul ?_ ?_
    · exact hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    · exact hK.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant μ μ)
  calc ∫⁻ x, ∫⁻ t, F t * K (x - t) ∂μ ∂μ
      = ∫⁻ t, ∫⁻ x, F t * K (x - t) ∂μ ∂μ := lintegral_lintegral_swap hprod
    _ = ∫⁻ t, F t * ∫⁻ y, K y ∂μ ∂μ := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [lintegral_sub_right_eq_self (fun y => F t * K y) t,
          lintegral_const_mul'' (F t) hK]
    _ = (∫⁻ t, F t ∂μ) * ∫⁻ y, K y ∂μ := lintegral_mul_const'' _ hF

end RightInvariant

section Young

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsAddRightInvariant]
  [μ.IsNegInvariant]

/-- **Young's convolution inequality**, `L¹ ⋆ L^p` case, `eLpNorm` form: for `1 ≤ p`,
`‖f ⋆ g‖_p ≤ ‖f‖₁ ‖g‖_p`. Neither side is assumed finite. -/
theorem eLpNorm_convolution_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => ∫ t, f t * g (x - t) ∂μ) p μ ≤ eLpNorm f 1 μ * eLpNorm g p μ := by
  have hFm : AEMeasurable (fun t => ‖f t‖ₑ) μ := hf.enorm
  have hGm : AEMeasurable (fun t => ‖g t‖ₑ) μ := hg.enorm
  have hGx : ∀ x : G, AEMeasurable (fun t => ‖g (x - t)‖ₑ) μ := fun x =>
    hGm.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  -- the case `p = ∞`
  by_cases hptop : p = ∞
  · subst hptop
    rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x => ?_)
    refine (enorm_integral_mul_sub_le f g x).trans ?_
    have hae : ∀ᵐ t ∂μ, ‖g (x - t)‖ₑ ≤ eLpNormEssSup g μ :=
      (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae
        (ae_le_eLpNormEssSup (f := g) (μ := μ))
    calc ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
        ≤ ∫⁻ t, ‖f t‖ₑ * eLpNormEssSup g μ ∂μ :=
          lintegral_mono_ae (hae.mono fun t ht => mul_le_mul' le_rfl ht)
      _ = (∫⁻ t, ‖f t‖ₑ ∂μ) * eLpNormEssSup g μ := lintegral_mul_const'' _ hFm
      _ = eLpNorm f 1 μ * eLpNorm g ∞ μ := by
          rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_exponent_top]
  -- the case `p = 1`
  by_cases hp1 : p = 1
  · subst hp1
    simp only [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ x, ‖∫ t, f t * g (x - t) ∂μ‖ₑ ∂μ
        ≤ ∫⁻ x, ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ ∂μ :=
          lintegral_mono fun x => enorm_integral_mul_sub_le f g x
      _ = (∫⁻ t, ‖f t‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂μ :=
          lintegral_lintegral_mul_comp_sub _ _ hFm hGm
  -- the case `1 < p < ∞`: degenerate values of the right-hand side first
  by_cases hf0 : f =ᵐ[μ] 0
  · have hconv : ∀ x : G, (∫ t, f t * g (x - t) ∂μ) = 0 := fun x => by
      rw [← integral_zero G ℂ (μ := μ)]
      refine integral_congr_ae ?_
      filter_upwards [hf0] with t ht
      rw [ht]
      simp
    calc eLpNorm (fun x => ∫ t, f t * g (x - t) ∂μ) p μ
        = eLpNorm (fun _ : G => (0 : ℂ)) p μ := by
          refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => hconv x)
      _ = 0 := eLpNorm_zero
      _ ≤ _ := bot_le
  by_cases hg0 : g =ᵐ[μ] 0
  · have hconv : ∀ x : G, (∫ t, f t * g (x - t) ∂μ) = 0 := fun x => by
      rw [← integral_zero G ℂ (μ := μ)]
      refine integral_congr_ae ?_
      have hgx : ∀ᵐ t ∂μ, g (x - t) = 0 :=
        (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae hg0
      filter_upwards [hgx] with t ht
      rw [ht]
      simp
    calc eLpNorm (fun x => ∫ t, f t * g (x - t) ∂μ) p μ
        = eLpNorm (fun _ : G => (0 : ℂ)) p μ := by
          refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => hconv x)
      _ = 0 := eLpNorm_zero
      _ ≤ _ := bot_le
  have hfne : eLpNorm f 1 μ ≠ 0 := by
    rw [Ne, eLpNorm_eq_zero_iff hf one_ne_zero]
    exact hf0
  have hgne : eLpNorm g p μ ≠ 0 := by
    rw [Ne, eLpNorm_eq_zero_iff hg hp0]
    exact hg0
  by_cases hftop : eLpNorm f 1 μ = ∞
  · rw [hftop, ENNReal.top_mul hgne]
    exact le_top
  by_cases hgtop : eLpNorm g p μ = ∞
  · rw [hgtop, ENNReal.mul_top hfne]
    exact le_top
  -- the main case: `1 < p < ∞` with finite nonzero right-hand side
  have hp1lt : 1 < p := lt_of_le_of_ne hp fun h => hp1 h.symm
  have hpr1 : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).mpr hp1lt
    simpa using this
  set pr : ℝ := p.toReal with hpr_def
  have hpr0 : 0 < pr := lt_trans one_pos hpr1
  have hpq : pr.HolderConjugate (Real.conjExponent pr) :=
    Real.HolderConjugate.conjExponent hpr1
  set qr : ℝ := Real.conjExponent pr with hqr_def
  have hqr1 : 1 < qr := (Real.holderConjugate_iff.mp hpq.symm).1
  have hqr0 : 0 < qr := lt_trans one_pos hqr1
  have hsum : 1 / qr + 1 / pr = 1 := by
    have h := (Real.holderConjugate_iff.mp hpq).2
    rw [one_div, one_div, add_comm]
    exact h
  set A : ℝ≥0∞ := ∫⁻ t, ‖f t‖ₑ ∂μ with hA_def
  set B : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ pr ∂μ with hB_def
  have hA_eq : eLpNorm f 1 μ = A := eLpNorm_one_eq_lintegral_enorm
  have hB_eq : eLpNorm g p μ = B ^ (1 / pr) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  have hAtop : A ≠ ∞ := hA_eq ▸ hftop
  -- pointwise Hölder bound in the inner variable
  have hkey : ∀ x : G, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ) ≤
      A ^ (1 / qr) * (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr ∂μ) ^ (1 / pr) := by
    intro x
    have hφm : AEMeasurable (fun t => ‖f t‖ₑ ^ (1 / qr)) μ := hFm.pow_const _
    have hψm : AEMeasurable (fun t => ‖f t‖ₑ ^ (1 / pr) * ‖g (x - t)‖ₑ) μ :=
      (hFm.pow_const _).mul (hGx x)
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm hφm hψm
    calc ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ
        = ∫⁻ t, ((fun t => ‖f t‖ₑ ^ (1 / qr)) *
            fun t => ‖f t‖ₑ ^ (1 / pr) * ‖g (x - t)‖ₑ) t ∂μ := by
          refine lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [Pi.mul_apply]
          rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
            hsum, ENNReal.rpow_one]
      _ ≤ (∫⁻ t, (‖f t‖ₑ ^ (1 / qr)) ^ qr ∂μ) ^ (1 / qr) *
            (∫⁻ t, (‖f t‖ₑ ^ (1 / pr) * ‖g (x - t)‖ₑ) ^ pr ∂μ) ^ (1 / pr) := hHolder
      _ = A ^ (1 / qr) * (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr ∂μ) ^ (1 / pr) := by
          congr 1
          · congr 1
            refine lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            beta_reduce
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hqr0),
              ENNReal.rpow_one]
          · congr 1
            refine lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            beta_reduce
            rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hpr0), ← ENNReal.rpow_mul,
              one_div, inv_mul_cancel₀ (ne_of_gt hpr0), ENNReal.rpow_one]
  -- integrate the `pr`-th power and factor by Tonelli and translation invariance
  have hmain : (∫⁻ x, ‖∫ t, f t * g (x - t) ∂μ‖ₑ ^ pr ∂μ) ≤ A ^ (pr / qr) * (A * B) := by
    have hApow : A ^ ((1 : ℝ) / qr) ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hAtop
    calc ∫⁻ x, ‖∫ t, f t * g (x - t) ∂μ‖ₑ ^ pr ∂μ
        ≤ ∫⁻ x, (A ^ (1 / qr) *
            (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr ∂μ) ^ (1 / pr)) ^ pr ∂μ := by
          refine lintegral_mono fun x => ?_
          refine ENNReal.rpow_le_rpow ?_ (le_of_lt hpr0)
          exact (enorm_integral_mul_sub_le f g x).trans (hkey x)
      _ = ∫⁻ x, A ^ (pr / qr) * ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr ∂μ ∂μ := by
          refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          beta_reduce
          have h1 : (1 / qr) * pr = pr / qr := by ring
          have h2 : (1 / pr) * pr = 1 := by field_simp
          rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hpr0), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, h1, h2, ENNReal.rpow_one]
      _ = A ^ (pr / qr) * ∫⁻ x, ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr ∂μ ∂μ := by
          refine lintegral_const_mul'' _ ?_
          -- measurability of the inner integral
          have hprod : AEMeasurable
              (Function.uncurry fun x t => ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ pr) (μ.prod μ) := by
            refine AEMeasurable.mul ?_ ?_
            · exact hFm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
            · exact (hGm.pow_const pr).comp_quasiMeasurePreserving
                (quasiMeasurePreserving_sub_of_right_invariant μ μ)
          exact hprod.lintegral_prod_right'
      _ = A ^ (pr / qr) * (A * B) := by
          rw [lintegral_lintegral_mul_comp_sub _ _ hFm (hGm.pow_const pr)]
  -- conclude by taking the `1/pr`-th power
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hA_eq, hB_eq, ← hpr_def]
  calc (∫⁻ x, ‖∫ t, f t * g (x - t) ∂μ‖ₑ ^ pr ∂μ) ^ (1 / pr)
      ≤ (A ^ (pr / qr) * (A * B)) ^ (1 / pr) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = A * B ^ (1 / pr) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
        congr 2
        field_simp
        have hexp : (pr + qr) / (pr * qr) = 1 := by
          rw [div_eq_one_iff_eq (by positivity)]
          field_simp at hsum
          ring_nf at hsum ⊢
          linarith [hsum]
        rw [hexp, ENNReal.rpow_one]

/-- **Young's convolution inequality**, membership form: the convolution of an integrable
function with an `L^p` function lies in `L^p` for `1 ≤ p`. -/
theorem Integrable.convolution_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : G → ℂ}
    (hf : Integrable f μ) (hg : MemLp g p μ) :
    MemLp (fun x => ∫ t, f t * g (x - t) ∂μ) p μ := by
  refine ⟨?_, ?_⟩
  · have h := hf.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      hg.aestronglyMeasurable
    have h2 := h.integral_prod_right'
    simpa only [ContinuousLinearMap.mul_apply'] using h2
  · refine lt_of_le_of_lt
      (eLpNorm_convolution_le hp hf.aestronglyMeasurable hg.aestronglyMeasurable) ?_
    exact ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hf).2 hg.2

end Young

end MeasureTheory
