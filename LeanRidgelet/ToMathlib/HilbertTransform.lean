/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.DirichletIntegral
public import LeanRidgelet.ToMathlib.FourierPlancherel
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Hilbert transform and its Fourier symbol

This file is a Mathlib upstream candidate; apart from the Dirichlet integral of
`LeanRidgelet.ToMathlib.DirichletIntegral` (also an upstream candidate) it has no dependencies on
the rest of the `LeanRidgelet` project.

Mathlib has no Hilbert transform. This file defines the principal-value Hilbert transform in the
classical normalization
$$`\mathscr H g(x)=\frac1\pi\,\mathrm{p.v.}\!\int\frac{g(t)}{x-t}\,dt`
(so that $`\mathscr H^2=-1`) and identifies its **Fourier symbol** on Schwartz functions:
$$`\mathscr H g=\mathcal F^{-1}\big[-i\,\mathrm{sign}(\xi)\,\mathcal Fg\big].`
The symbol is homogeneous of degree `0`, so the statement is the same in every normalization of
the Fourier transform; it is proved here in Mathlib's convention
`𝓕 g ξ = ∫ e^{-2πi x ξ} g x dx`.

## Main results

* `MeasureTheory.pvHilbertTransform`: the principal-value Hilbert transform, as a
  junk-valued limit of truncated integrals.
* `MeasureTheory.setIntegral_hilbert_eq_Ioi`: the truncated integral as the absolutely convergent
  integral of the odd difference quotient `(g(x - s) - g(x + s))/s` over `(ε, ∞)`.
* `MeasureTheory.intervalIntegral_hilbert_eq_fourier`: the doubly truncated integral on the
  Fourier side, where the truncated kernel contributes the partial Dirichlet integral
  `∫_ε^R sin(2πsξ)/s ds` — the step that needs the outer cut-off `R`, since the Hilbert kernel is
  not integrable at infinity and Fubini would otherwise fail.
* `MeasureTheory.setIntegral_hilbert_eq_fourier_tail`: the `ε`-truncated integral on the Fourier
  side, with the Dirichlet tail as symbol, after `R → ∞` (dominated convergence against the
  uniform bound on the partial Dirichlet integrals).
* `MeasureTheory.pvHilbertTransform_schwartz` (**the Fourier symbol of the Hilbert transform**):
  for a Schwartz function `f`, `𝓗 f (x) = ∫ (-i sign ξ) 𝓕f(ξ) e^{2πi x ξ} dξ`, by a second
  dominated-convergence pass driven by the Dirichlet integral `∫_0^∞ sin u/u du = π/2`. In
  particular the principal-value limit exists at every point.
* `MeasureTheory.pvHilbertTransform_schwartz_eq_fourierInv`: the same statement written with
  Mathlib's inverse Fourier integral `𝓕⁻`.
* `MeasureTheory.pvHilbertTransform_schwartz_eq_oddIntegral`: the principal value as an
  absolutely convergent integral of the odd difference quotient over `(0, ∞)`.
* `MeasureTheory.coord_mul_pvHilbertTransform` (**the commutator identity**):
  `x 𝓗g(x) = 𝓗(t g(t))(x) + π⁻¹ ∫ g`.
* `MeasureTheory.memLp_two_pvHilbertTransform`: `𝓗 g` is square-integrable, the symbol being
  unimodular.
* `MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero`: **`𝓗 g` is integrable when
  `∫ g = 0`.** In general `𝓗 g` decays only like `1/x`; the vanishing integral removes the
  leading term. The commutator identity turns this into a statement about two `L²` functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology FourierTransform RealInnerProductSpace

namespace MeasureTheory

/-- The principal-value Hilbert transform in the classical normalization
`𝓗 g (x) = (1/π) p.v. ∫ g t / (x - t) dt`. -/
def pvHilbertTransform (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    (1 / (Real.pi : ℂ)) * ∫ t in {t : ℝ | ε < |x - t|}, g t / ((x : ℂ) - (t : ℂ))

/-- A rescaled and translated Schwartz function is integrable. -/
theorem integrable_schwartz_comp_affine (f : SchwartzMap ℝ ℂ) (x c : ℝ) (hc : c ≠ 0) :
    Integrable (fun s : ℝ => f (x + c * s)) volume := by
  have h := f.integrable (μ := (volume : Measure ℝ))
  have h1 : Integrable (fun s : ℝ => f (c * s)) volume :=
    (integrable_comp_mul_left_iff (g := fun y : ℝ => f y) hc).mpr h
  have h2 := h1.comp_add_right (x / c)
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only []
  rw [mul_add, mul_div_cancel₀ _ hc, add_comm]

/-- Outside a ball the Hilbert kernel applied to a Schwartz function is integrable. -/
theorem integrableOn_schwartz_div_abs_gt (f : SchwartzMap ℝ ℂ) (x c : ℝ) (hc : c ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    IntegrableOn (fun s : ℝ => f (x + c * s) / (s : ℂ)) {s : ℝ | ε < |s|} volume := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ => f (x + c * s) / (s : ℂ)) volume := by
    have h1 : Measurable fun s : ℝ => (f (x + c * s) : ℂ) :=
      (f.continuous.comp (by fun_prop)).measurable
    exact (h1.div Complex.measurable_ofReal).aestronglyMeasurable
  have hmeasS : MeasurableSet {s : ℝ | ε < |s|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  refine Integrable.mono' (g := fun s : ℝ => ε⁻¹ * ‖f (x + c * s)‖) ?_ hmeas.restrict ?_
  · exact ((integrable_schwartz_comp_affine f x c hc).norm.const_mul ε⁻¹).integrableOn
  · refine (ae_restrict_iff' hmeasS).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < |s| := lt_trans hε hs
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hs0]
    calc ‖f (x + c * s)‖ = ε⁻¹ * ‖f (x + c * s)‖ * ε := by field_simp
      _ ≤ ε⁻¹ * ‖f (x + c * s)‖ * |s| :=
          mul_le_mul_of_nonneg_left (le_of_lt hs) (by positivity)

/-- The truncated Hilbert integral as the integral of the odd difference quotient. -/
theorem setIntegral_hilbert_eq_Ioi (f : SchwartzMap ℝ ℂ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in {t : ℝ | ε < |x - t|}, f t / ((x : ℂ) - (t : ℂ)))
      = ∫ s in Ioi ε, (f (x - s) - f (x + s)) / (s : ℂ) := by
  have hmeasS : MeasurableSet {s : ℝ | ε < |s|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hφ : MeasurePreserving (fun t : ℝ => x - t) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hemb : MeasurableEmbedding (fun t : ℝ => x - t) :=
    (Homeomorph.subLeft x).measurableEmbedding
  -- integrability of the two rays
  have hintS : IntegrableOn (fun s : ℝ => f (x - s) / (s : ℂ)) {s : ℝ | ε < |s|} volume := by
    have h := integrableOn_schwartz_div_abs_gt f x (-1) (by norm_num) hε
    refine h.congr_fun (fun s _ => ?_) hmeasS
    simp only []
    rw [show x + (-1 : ℝ) * s = x - s from by ring]
  have hint1 : IntegrableOn (fun s : ℝ => f (x - s) / (s : ℂ)) (Ioi ε) volume := by
    refine hintS.mono_set fun s hs => ?_
    have : ε < s := hs
    simp only [Set.mem_setOf_eq]
    rw [abs_of_pos (lt_trans hε this)]
    exact this
  have hintIio : IntegrableOn (fun s : ℝ => f (x - s) / (s : ℂ)) (Iio (-ε)) volume := by
    refine hintS.mono_set fun s hs => ?_
    have : s < -ε := hs
    simp only [Set.mem_setOf_eq]
    rw [abs_of_neg (by linarith)]
    linarith
  have hint2 : IntegrableOn (fun s : ℝ => f (x + s) / (s : ℂ)) (Ioi ε) volume := by
    have h := integrableOn_schwartz_div_abs_gt f x 1 (by norm_num) hε
    refine (h.mono_set fun s hs => ?_).congr_fun (fun s _ => ?_) measurableSet_Ioi
    · have : ε < s := hs
      simp only [Set.mem_setOf_eq]
      rw [abs_of_pos (lt_trans hε this)]
      exact this
    · simp only []
      rw [show x + (1 : ℝ) * s = x + s from by ring]
  -- pass to the variable `s = x - t`
  have hstep1 : (∫ t in {t : ℝ | ε < |x - t|}, f t / ((x : ℂ) - (t : ℂ)))
      = ∫ s in {s : ℝ | ε < |s|}, f (x - s) / (s : ℂ) := by
    have hpre : (fun t : ℝ => x - t) ⁻¹' {s : ℝ | ε < |s|} = {t : ℝ | ε < |x - t|} := by
      ext t
      simp
    have h := hφ.setIntegral_preimage_emb hemb
      (fun s : ℝ => f (x - s) / (s : ℂ)) {s : ℝ | ε < |s|}
    rw [hpre] at h
    refine Eq.trans ?_ h
    refine setIntegral_congr_fun
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).abs).measurableSet
      fun t _ => ?_
    push_cast
    ring_nf
  rw [hstep1]
  -- split into the two rays and reflect the negative one
  have hsplit : {s : ℝ | ε < |s|} = Iio (-ε) ∪ Ioi ε := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs]
      constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · linarith
        · exact h
    · rw [abs_of_neg hs]
      constructor
      · exact fun h => Or.inl (by linarith)
      · rintro (h | h)
        · linarith
        · linarith
  have hneg : (∫ s in Iio (-ε), f (x - s) / (s : ℂ))
      = -∫ s in Ioi ε, f (x + s) / (s : ℂ) := by
    have h : (∫ s in Iio (-ε), f (x - s) / (s : ℂ))
        = ∫ s in Ioi ε, f (x + s) / ((-s : ℝ) : ℂ) := by
      have hcomp := integral_comp_neg_Ioi ε (fun s : ℝ => f (x - s) / (s : ℂ))
      rw [← integral_Iic_eq_integral_Iio, ← hcomp]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      push_cast
      ring_nf
    rw [h, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast
    ring
  have hunion : (∫ s in {s : ℝ | ε < |s|}, f (x - s) / (s : ℂ))
      = (∫ s in Iio (-ε), f (x - s) / (s : ℂ)) + ∫ s in Ioi ε, f (x - s) / (s : ℂ) := by
    rw [hsplit]
    refine setIntegral_union ?_ measurableSet_Ioi hintIio hint1
    rw [Set.disjoint_left]
    intro s hs hs'
    have h1 : s < -ε := hs
    have h2 : ε < s := hs'
    linarith
  rw [hunion, hneg,
    show (-∫ s in Ioi ε, f (x + s) / (s : ℂ)) + ∫ s in Ioi ε, f (x - s) / (s : ℂ)
      = (∫ s in Ioi ε, f (x - s) / (s : ℂ)) - ∫ s in Ioi ε, f (x + s) / (s : ℂ) from by ring,
    ← integral_sub hint1 hint2]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [div_sub_div_same]


theorem inner_real_eq_mul (v w : ℝ) : (inner ℝ v w : ℝ) = v * w := by
  simp [RCLike.inner_apply, mul_comm]

/-- `e^{-ia} - e^{ia} = -2i sin a`. -/
theorem exp_neg_sub_exp_eq (a : ℝ) :
    Complex.exp (((-a : ℝ) : ℂ) * Complex.I) - Complex.exp (((a : ℝ) : ℂ) * Complex.I)
      = -2 * Complex.I * ((Real.sin a : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
    Complex.sin_neg, ← Complex.ofReal_sin]
  ring

/-- Fourier inversion for a Schwartz function, in exponential form. -/
theorem schwartz_eq_integral_fourier (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    (f y : ℂ) = ∫ ξ : ℝ, Complex.exp (((2 * π * (y * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ := by
  have hf𝓕 : Integrable (𝓕 (⇑f)) volume := by
    have h := (𝓕 f).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourier_coe] at h
  have h := congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf𝓕) y
  rw [fourierInv_eq'] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only []
  rw [smul_eq_mul, inner_real_eq_mul, mul_comm ξ y]

/-- The truncated Hilbert integral of a Schwartz function on the Fourier side: the truncated
kernel contributes the partial Dirichlet integral. -/
theorem intervalIntegral_hilbert_eq_fourier (f : SchwartzMap ℝ ℂ) (x : ℝ) {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ s in ε..R, (f (x - s) - f (x + s)) / (s : ℂ))
      = ∫ ξ : ℝ, (-2 * Complex.I *
            ((∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
  classical
  have hf𝓕 : Integrable (𝓕 (⇑f)) volume := by
    have h := (𝓕 f).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourier_coe] at h
  set G : ℝ → ℝ → ℂ := fun s ξ =>
    (-2 * Complex.I * ((Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
      (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) with hG_def
  -- the difference quotient as a `ξ`-integral
  have hquot : ∀ s : ℝ, s ≠ 0 → (f (x - s) - f (x + s)) / (s : ℂ) = ∫ ξ : ℝ, G s ξ := by
    intro s hs
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    have hint1 : Integrable (fun ξ : ℝ =>
        Complex.exp (((2 * π * ((x - s) * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) volume := by
      refine hf𝓕.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
      · refine AEStronglyMeasurable.mul ?_ hf𝓕.aestronglyMeasurable
        exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hint2 : Integrable (fun ξ : ℝ =>
        Complex.exp (((2 * π * ((x + s) * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) volume := by
      refine hf𝓕.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
      · refine AEStronglyMeasurable.mul ?_ hf𝓕.aestronglyMeasurable
        exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [schwartz_eq_integral_fourier f (x - s), schwartz_eq_integral_fourier f (x + s),
      ← integral_sub hint1 hint2, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hG_def]
    have hsplit : ∀ y : ℝ,
        Complex.exp (((2 * π * (y * ξ) : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((2 * π * ((y - x) * ξ) : ℝ) : ℂ) * Complex.I) := by
      intro y
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit (x - s), hsplit (x + s)]
    have h1 : ((x - s - x : ℝ)) = -s := by ring
    have h2 : ((x + s - x : ℝ)) = s := by ring
    rw [h1, h2]
    have hE : Complex.exp (((-(2 * π * (s * ξ)) : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((2 * π * (s * ξ) : ℝ) : ℂ) * Complex.I)
        = -2 * Complex.I * ((Real.sin (2 * π * (s * ξ)) : ℝ) : ℂ) :=
      exp_neg_sub_exp_eq _
    have hs1 : ((2 * π * (-s * ξ) : ℝ) : ℂ) = ((-(2 * π * (s * ξ)) : ℝ) : ℂ) := by
      push_cast; ring
    have hcast : ((Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)
        = ((Real.sin (2 * π * (s * ξ)) : ℝ) : ℂ) / ((s : ℝ) : ℂ) := by
      rw [show s * (2 * π * ξ) = 2 * π * (s * ξ) from by ring, Complex.ofReal_div]
    rw [hs1, hcast,
      show -2 * Complex.I * (((Real.sin (2 * π * (s * ξ)) : ℝ) : ℂ) / ((s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ)
        = (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ *
            (-2 * Complex.I * ((Real.sin (2 * π * (s * ξ)) : ℝ) : ℂ))) / ((s : ℝ) : ℂ) from by
        ring]
    congr 1
    linear_combination (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) *
      𝓕 (⇑f) ξ) * hE
  -- integrability of the joint kernel
  have hGaesm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioc ε R)).prod (volume : Measure ℝ)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine AEStronglyMeasurable.const_mul ?_ _
      refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
      exact (Real.measurable_sin.comp (by fun_prop)).div (by fun_prop)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · exact hf𝓕.aestronglyMeasurable.comp_snd
  have hGint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc ε R)).prod (volume : Measure ℝ)) := by
    haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc ε R)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact measure_Ioc_lt_top
    have hmeasure : ((volume : Measure ℝ).restrict (Ioc ε R)).prod (volume : Measure ℝ)
        = ((volume : Measure ℝ).prod volume).restrict ((Ioc ε R) ×ˢ (Set.univ : Set ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    refine Integrable.mono' (g := fun p : ℝ × ℝ => (2 / ε) * ‖𝓕 (⇑f) p.2‖) ?_ hGaesm ?_
    · exact (hf𝓕.norm.const_mul (2 / ε)).comp_snd _
    · rw [hmeasure]
      refine (ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)).mpr ?_
      refine Filter.Eventually.of_forall fun p hp => ?_
      have hs : ε < p.1 := (Set.mem_prod.mp hp).1.1
      have hs0 : 0 < p.1 := lt_trans hε hs
      have hnorm : ‖Function.uncurry G p‖
          = 2 * |Real.sin (p.1 * (2 * π * p.2)) / p.1| * ‖𝓕 (⇑f) p.2‖ := by
        simp only [hG_def, Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_I, Complex.norm_ofNat]
        ring
      rw [hnorm]
      have hsin : |Real.sin (p.1 * (2 * π * p.2)) / p.1| ≤ ε⁻¹ := by
        rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
        calc |Real.sin (p.1 * (2 * π * p.2))| ≤ 1 := Real.abs_sin_le_one _
          _ = ε⁻¹ * ε := by field_simp
          _ ≤ ε⁻¹ * p.1 := mul_le_mul_of_nonneg_left hs.le (by positivity)
      calc 2 * |Real.sin (p.1 * (2 * π * p.2)) / p.1| * ‖𝓕 (⇑f) p.2‖
          ≤ 2 * ε⁻¹ * ‖𝓕 (⇑f) p.2‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hsin (by norm_num)
        _ = (2 / ε) * ‖𝓕 (⇑f) p.2‖ := by rw [div_eq_mul_inv]
  -- Fubini
  have hswap := integral_integral_swap hGint
  rw [intervalIntegral.integral_of_le hεR]
  have hleft : (∫ s in Ioc ε R, (f (x - s) - f (x + s)) / (s : ℂ))
      = ∫ s in Ioc ε R, ∫ ξ : ℝ, G s ξ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact hquot s (ne_of_gt (lt_trans hε hs.1))
  rw [hleft, hswap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [hG_def]
  calc (∫ s in Ioc ε R, -2 * Complex.I * ((Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ) *
        (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))
      = (∫ s in Ioc ε R, -2 * Complex.I * ((Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) :=
        integral_mul_const _ _
    _ = (-2 * Complex.I * ((∫ s in Ioc ε R, Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
        rw [integral_const_mul, integral_complex_ofReal]
    _ = (-2 * Complex.I * ((∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
        rw [intervalIntegral.integral_of_le hεR]


/-- The truncated Dirichlet kernel converges to the Dirichlet tail as the outer cut-off grows. -/
theorem tendsto_partial_dirichlet_atTop {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    Filter.Tendsto (fun R : ℝ => ∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s) atTop
      (𝓝 (Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|))) := by
  rcases eq_or_ne ξ 0 with hξ | hξ
  · subst hξ
    simp only [mul_zero, Real.sign_zero, zero_mul]
    refine Filter.Tendsto.congr (fun R => ?_) tendsto_const_nhds
    simp
  · have hω : (2 * π * ξ) ≠ 0 := by
      have : (0 : ℝ) < 2 * π := by positivity
      exact mul_ne_zero this.ne' hξ
    have habs : (0 : ℝ) < |2 * π * ξ| := abs_pos.mpr hω
    have hscale : Filter.Tendsto (fun R : ℝ => R * |2 * π * ξ|) atTop atTop :=
      Filter.Tendsto.atTop_mul_const habs Filter.tendsto_id
    have hinner : Filter.Tendsto
        (fun R : ℝ => ∫ u in (ε * |2 * π * ξ|)..(R * |2 * π * ξ|), Real.sin u / u) atTop
        (𝓝 (sinDivTail (ε * |2 * π * ξ|))) :=
      (tendsto_intervalIntegral_sin_div_atTop_left _).comp hscale
    have hmul := hinner.const_mul (Real.sign (2 * π * ξ))
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ε] with R hR
    exact (intervalIntegral_sin_mul_div_eq (2 * π * ξ) hω ε R hε hR).symm

/-- Uniform bound on the truncated Dirichlet kernel. -/
theorem abs_partial_dirichlet_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : ℝ) :
    |∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s| ≤ 3 := by
  rcases eq_or_ne ξ 0 with hξ | hξ
  · subst hξ
    simp only [mul_zero, zero_mul, Real.sin_zero, zero_div]
    simp
  · have hω : (2 * π * ξ) ≠ 0 := by
      have : (0 : ℝ) < 2 * π := by positivity
      exact mul_ne_zero this.ne' hξ
    have habs : (0 : ℝ) < |2 * π * ξ| := abs_pos.mpr hω
    rw [intervalIntegral_sin_mul_div_eq (2 * π * ξ) hω ε R hε hεR, abs_mul]
    have hsign : |Real.sign (2 * π * ξ)| = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero _ hω with h | h <;> rw [h] <;> simp
    rw [hsign, one_mul]
    refine abs_intervalIntegral_sin_div_le (by positivity) ?_
    exact mul_le_mul_of_nonneg_right hεR habs.le

/-- The Fourier representation of the `ε`-truncated Hilbert integral of a Schwartz function. -/
theorem setIntegral_hilbert_eq_fourier_tail (f : SchwartzMap ℝ ℂ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in {t : ℝ | ε < |x - t|}, f t / ((x : ℂ) - (t : ℂ)))
      = ∫ ξ : ℝ, (-2 * Complex.I *
            ((Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
  classical
  have hf𝓕 : Integrable (𝓕 (⇑f)) volume := by
    have h := (𝓕 f).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourier_coe] at h
  haveI : Filter.IsCountablyGenerated (atTop : Filter ℝ) := by infer_instance
  -- the left-hand side is the limit of the truncated interval integrals
  have hintdiff : IntegrableOn (fun s : ℝ => (f (x - s) - f (x + s)) / (s : ℂ)) (Ioi ε) volume := by
    have h1 : IntegrableOn (fun s : ℝ => f (x - s) / (s : ℂ)) (Ioi ε) volume := by
      have h := integrableOn_schwartz_div_abs_gt f x (-1) (by norm_num) hε
      refine (h.mono_set fun s hs => ?_).congr_fun (fun s _ => ?_) measurableSet_Ioi
      · have : ε < s := hs
        simp only [Set.mem_setOf_eq]
        rw [abs_of_pos (lt_trans hε this)]
        exact this
      · simp only []
        rw [show x + (-1 : ℝ) * s = x - s from by ring]
    have h2 : IntegrableOn (fun s : ℝ => f (x + s) / (s : ℂ)) (Ioi ε) volume := by
      have h := integrableOn_schwartz_div_abs_gt f x 1 (by norm_num) hε
      refine (h.mono_set fun s hs => ?_).congr_fun (fun s _ => ?_) measurableSet_Ioi
      · have : ε < s := hs
        simp only [Set.mem_setOf_eq]
        rw [abs_of_pos (lt_trans hε this)]
        exact this
      · simp only []
        rw [show x + (1 : ℝ) * s = x + s from by ring]
    refine (h1.sub h2).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [div_sub_div_same]
  have hleft : Filter.Tendsto
      (fun R : ℝ => ∫ s in ε..R, (f (x - s) - f (x + s)) / (s : ℂ)) atTop
      (𝓝 (∫ s in Ioi ε, (f (x - s) - f (x + s)) / (s : ℂ))) :=
    intervalIntegral_tendsto_integral_Ioi ε hintdiff Filter.tendsto_id
  -- the right-hand side is the limit of the truncated Fourier integrals
  have hright : Filter.Tendsto
      (fun R : ℝ => ∫ ξ : ℝ, (-2 * Complex.I *
            ((∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ)) atTop
      (𝓝 (∫ ξ : ℝ, (-2 * Complex.I *
            ((Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun ξ : ℝ => 6 * ‖𝓕 (⇑f) ξ‖) ?_ ?_ (hf𝓕.norm.const_mul 6) ?_
    · filter_upwards [Filter.eventually_ge_atTop ε] with R hR
      refine AEStronglyMeasurable.mul (AEStronglyMeasurable.const_mul ?_ _) ?_
      · -- measurability of the parametric Dirichlet kernel
        have hker : AEStronglyMeasurable
            (fun p : ℝ × ℝ => Real.sin (p.2 * (2 * π * p.1)) / p.2)
            ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioc ε R))) := by
          have h1 : Measurable fun p : ℝ × ℝ => Real.sin (p.2 * (2 * π * p.1)) :=
            Real.measurable_sin.comp (by fun_prop)
          exact (h1.div measurable_snd).aestronglyMeasurable
        have h := hker.integral_prod_right'
        refine (Complex.continuous_ofReal.comp_aestronglyMeasurable h).congr ?_
        refine Filter.Eventually.of_forall fun ξ => ?_
        simp only []
        rw [intervalIntegral.integral_of_le hR]
      · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
          hf𝓕.aestronglyMeasurable
    · filter_upwards [Filter.eventually_ge_atTop ε] with R hR
      refine Filter.Eventually.of_forall fun ξ => ?_
      have hnorm : ‖(-2 * Complex.I *
            ((∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ)‖
          = 2 * |∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s| * ‖𝓕 (⇑f) ξ‖ := by
        simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, norm_neg, Complex.norm_I, Complex.norm_ofNat]
        ring
      rw [hnorm]
      calc 2 * |∫ s in ε..R, Real.sin (s * (2 * π * ξ)) / s| * ‖𝓕 (⇑f) ξ‖
          ≤ 2 * 3 * ‖𝓕 (⇑f) ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (abs_partial_dirichlet_le hε hR ξ) (by norm_num)
        _ = 6 * ‖𝓕 (⇑f) ξ‖ := by ring
    · refine Filter.Eventually.of_forall fun ξ => ?_
      refine Filter.Tendsto.mul_const _ ?_
      refine Filter.Tendsto.const_mul _ ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_partial_dirichlet_atTop hε ξ)
  -- identify the two limits
  rw [setIntegral_hilbert_eq_Ioi f x hε]
  refine tendsto_nhds_unique hleft ?_
  refine hright.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ε] with R hR
  exact (intervalIntegral_hilbert_eq_fourier f x hε hR).symm


theorem measurable_real_sign : Measurable Real.sign := by
  have hrw : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := rfl
  rw [hrw]
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

theorem sign_two_pi_mul (ξ : ℝ) : Real.sign (2 * π * ξ) = Real.sign ξ := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (by nlinarith [Real.pi_pos])]
  · subst h
    simp
  · rw [Real.sign_of_pos h, Real.sign_of_pos (by positivity)]

/-- **The Fourier symbol of the Hilbert transform**: on Schwartz functions the principal-value
Hilbert transform is the Fourier multiplier `-i sign ξ`. -/
theorem pvHilbertTransform_schwartz (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    pvHilbertTransform (⇑f) x
      = ∫ ξ : ℝ, (-Complex.I * ((Real.sign ξ : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
  classical
  have hf𝓕 : Integrable (𝓕 (⇑f)) volume := by
    have h := (𝓕 f).integrable (μ := (volume : Measure ℝ))
    rwa [SchwartzMap.fourier_coe] at h
  have hπ : (0 : ℝ) < π := Real.pi_pos
  haveI : Filter.IsCountablyGenerated (𝓝[>] (0 : ℝ)) := by infer_instance
  -- the limit of the Fourier-side expressions as the inner cut-off shrinks
  have hdct : Filter.Tendsto
      (fun ε : ℝ => ∫ ξ : ℝ, (-2 * Complex.I *
            ((Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ξ : ℝ, (-2 * Complex.I *
            ((Real.sign (2 * π * ξ) * (π / 2) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun ξ : ℝ => 6 * ‖𝓕 (⇑f) ξ‖) ?_ ?_ (hf𝓕.norm.const_mul 6) ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      refine AEStronglyMeasurable.mul (AEStronglyMeasurable.const_mul ?_ _) ?_
      · refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_)
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact (measurable_real_sign.comp (by fun_prop)).aestronglyMeasurable
        · exact (continuous_sinDivTail.measurable.comp (by fun_prop)).aestronglyMeasurable
      · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
          hf𝓕.aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => ?_
      have hε0 : (0 : ℝ) < ε := hε
      refine Filter.Eventually.of_forall fun ξ => ?_
      have hnorm : ‖(-2 * Complex.I *
              ((Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|) : ℝ) : ℂ)) *
            (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ)‖
          = 2 * |Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|)| * ‖𝓕 (⇑f) ξ‖ := by
        simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, norm_neg, Complex.norm_I, Complex.norm_ofNat, abs_mul]
        ring
      rw [hnorm]
      have hb : |Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|)| ≤ 3 := by
        rw [abs_mul]
        rcases eq_or_ne (2 * π * ξ) 0 with h | h
        · rw [h, Real.sign_zero]
          simp
        · have hsign : |Real.sign (2 * π * ξ)| = 1 := by
            rcases Real.sign_apply_eq_of_ne_zero _ h with h' | h' <;> rw [h'] <;> simp
          rw [hsign, one_mul]
          exact abs_sinDivTail_le (by positivity)
      calc 2 * |Real.sign (2 * π * ξ) * sinDivTail (ε * |2 * π * ξ|)| * ‖𝓕 (⇑f) ξ‖
          ≤ 2 * 3 * ‖𝓕 (⇑f) ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = 6 * ‖𝓕 (⇑f) ξ‖ := by ring
    · refine Filter.Eventually.of_forall fun ξ => ?_
      refine Filter.Tendsto.mul_const _ (Filter.Tendsto.const_mul _ ?_)
      refine (Complex.continuous_ofReal.tendsto _).comp ?_
      refine Filter.Tendsto.const_mul _ ?_
      rcases eq_or_ne (2 * π * ξ) 0 with h | h
      · rw [h]
        simp only [abs_zero, mul_zero, sinDivTail, intervalIntegral.integral_same, sub_zero]
        exact tendsto_const_nhds
      · have habs : (0 : ℝ) < |2 * π * ξ| := abs_pos.mpr h
        have hscale : Filter.Tendsto (fun ε : ℝ => ε * |2 * π * ξ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h1 : Filter.Tendsto (fun ε : ℝ => ε * |2 * π * ξ|) (𝓝 (0 : ℝ)) (𝓝 0) := by
            have hc : Continuous fun ε : ℝ => ε * |2 * π * ξ| := by fun_prop
            have := hc.tendsto (0 : ℝ)
            simpa using this
          exact h1.mono_left nhdsWithin_le_nhds
        exact tendsto_sinDivTail_nhds_zero.comp hscale
  -- the truncated Hilbert integrals agree with the Fourier-side expressions
  have hcongr : Filter.Tendsto
      (fun ε : ℝ => ∫ t in {t : ℝ | ε < |x - t|}, f t / ((x : ℂ) - (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ξ : ℝ, (-2 * Complex.I * ((Real.sign (2 * π * ξ) * (π / 2) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))) := by
    refine hdct.congr' ?_
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => ?_
    exact (setIntegral_hilbert_eq_fourier_tail f x hε).symm
  -- multiply by the normalization and identify the symbol
  have hconst : (1 / (π : ℂ)) *
        (∫ ξ : ℝ, (-2 * Complex.I * ((Real.sign (2 * π * ξ) * (π / 2) : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ))
      = ∫ ξ : ℝ, (-Complex.I * ((Real.sign ξ : ℝ) : ℂ)) *
          (Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [sign_two_pi_mul]
    have hπC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
    push_cast
    field_simp
  have hfinal := hcongr.const_mul (1 / (π : ℂ))
  rw [hconst] at hfinal
  exact hfinal.limUnder_eq

/-- **The Fourier symbol of the Hilbert transform**, in terms of Mathlib's inverse Fourier
integral: `𝓗 f = 𝓕⁻ (-i sign ⬝ 𝓕 f)` for every Schwartz function `f`. -/
theorem pvHilbertTransform_schwartz_eq_fourierInv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    pvHilbertTransform (⇑f) x
      = 𝓕⁻ (fun ξ => -Complex.I * ((Real.sign ξ : ℝ) : ℂ) * 𝓕 (⇑f) ξ) x := by
  rw [pvHilbertTransform_schwartz f x, fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only []
  rw [smul_eq_mul, inner_real_eq_mul, mul_comm ξ x]
  ring

/-! ## Integrability of the Hilbert transform of a Schwartz function with vanishing integral

The Hilbert transform of a Schwartz function is only `O(1/x)` in general, hence not integrable.
If the integral of the function vanishes the decay improves and `𝓗 g` becomes integrable. The
proof is the commutator identity `x 𝓗g(x) = 𝓗(t g(t))(x) + π⁻¹ ∫ g`, which follows from the
pointwise identity `x g(t)/(x - t) = t g(t)/(x - t) + g(t)`: with `∫ g = 0` it says that `x 𝓗g`
is again the Hilbert transform of a Schwartz function, so both `𝓗g` and `x 𝓗g` are
square-integrable, and `𝓗g = x⁻¹ ⬝ (x 𝓗g)` is integrable away from the origin by
Cauchy--Schwarz.
-/

/-- The odd difference quotient of a Schwartz function is integrable on the positive half-line:
near `0` it is bounded by twice the Lipschitz constant, and at infinity by the function itself. -/
theorem integrableOn_schwartz_oddDiff (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    IntegrableOn (fun s : ℝ => (f (x - s) - f (x + s)) / (s : ℂ)) (Ioi (0 : ℝ)) volume := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y : ℝ, ‖deriv (⇑f) y‖ ≤ C := by
    obtain ⟨C, -, hC⟩ := (SchwartzMap.derivCLM ℂ ℂ f).decay 0 0
    exact ⟨C, fun y => by simpa using hC y⟩
  have hlip : ∀ a b : ℝ, ‖f a - f b‖ ≤ C * |a - b| := by
    intro a b
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ⇑f)
      (fun y _ => f.differentiableAt) (fun y _ => hC y) convex_univ
      (Set.mem_univ b) (Set.mem_univ a)
    simpa [Real.norm_eq_abs] using h
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (f (x - s) - f (x + s)) / (s : ℂ)) volume := by
    have h1 : Measurable fun s : ℝ => (f (x - s) - f (x + s) : ℂ) :=
      ((f.continuous.comp (by fun_prop)).sub (f.continuous.comp (by fun_prop))).measurable
    exact (h1.div Complex.measurable_ofReal).aestronglyMeasurable
  have hnear : IntegrableOn (fun s : ℝ => (f (x - s) - f (x + s)) / (s : ℂ))
      (Ioc (0 : ℝ) 1) volume := by
    refine Measure.integrableOn_of_bounded (M := 2 * C) (by simp) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have habs : |(x - s) - (x + s)| = 2 * s := by
      rw [show (x - s) - (x + s) = -(2 * s) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_le_iff₀ hs0]
    calc ‖f (x - s) - f (x + s)‖ ≤ C * |(x - s) - (x + s)| := hlip _ _
      _ = 2 * C * s := by rw [habs]; ring
  have hgl : Integrable (fun s : ℝ => f (x - s)) volume := by
    refine (integrable_schwartz_comp_affine f x (-1) (by norm_num)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [neg_one_mul, ← sub_eq_add_neg]
  have hgr : Integrable (fun s : ℝ => f (x + s)) volume := by
    refine (integrable_schwartz_comp_affine f x 1 (by norm_num)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [one_mul]
  have hfar : IntegrableOn (fun s : ℝ => (f (x - s) - f (x + s)) / (s : ℂ))
      (Ioi (1 : ℝ)) volume := by
    refine Integrable.mono' (hgl.norm.add hgr.norm).integrableOn hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    calc ‖f (x - s) - f (x + s)‖ / s ≤ ‖f (x - s) - f (x + s)‖ / 1 := by gcongr
      _ ≤ ‖f (x - s)‖ + ‖f (x + s)‖ := by
          rw [div_one]
          exact norm_sub_le _ _
  rw [show Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact hnear.union hfar

/-- **The principal value of the Hilbert transform of a Schwartz function is an absolutely
convergent integral** of the odd difference quotient over the positive half-line. -/
theorem pvHilbertTransform_schwartz_eq_oddIntegral (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    pvHilbertTransform (⇑f) x
      = (1 / (Real.pi : ℂ)) * ∫ s in Ioi (0 : ℝ), (f (x - s) - f (x + s)) / (s : ℂ) := by
  set F : ℝ → ℂ := fun s => (f (x - s) - f (x + s)) / (s : ℂ) with hF_def
  have hFm : AEStronglyMeasurable F volume := by
    have h1 : Measurable fun s : ℝ => (f (x - s) - f (x + s) : ℂ) :=
      ((f.continuous.comp (by fun_prop)).sub (f.continuous.comp (by fun_prop))).measurable
    exact (h1.div Complex.measurable_ofReal).aestronglyMeasurable
  have hFint : IntegrableOn F (Ioi (0 : ℝ)) volume := integrableOn_schwartz_oddDiff f x
  have htend : Filter.Tendsto (fun ε : ℝ => ∫ s in Ioi ε, F s) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ s in Ioi (0 : ℝ), F s)) := by
    simp_rw [← integral_indicator measurableSet_Ioi]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => ‖(Ioi (0 : ℝ)).indicator F s‖) ?_ ?_ ?_ ?_
    · filter_upwards with ε
      exact hFm.indicator measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards with s
      by_cases h : ε < s
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 h),
          Set.indicator_of_mem (Set.mem_Ioi.2 (lt_trans hε h))]
      · rw [Set.indicator_of_notMem (by simpa using h)]
        simp
    · exact ((integrable_indicator_iff measurableSet_Ioi).2 hFint).norm
    · filter_upwards with s
      by_cases h : (0 : ℝ) < s
      · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds h)] with ε hεs
        rw [Set.indicator_of_mem (Set.mem_Ioi.2 h), Set.indicator_of_mem (Set.mem_Ioi.2 hεs)]
      · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Set.indicator_of_notMem (by simpa using h),
          Set.indicator_of_notMem (fun hm => h (lt_trans hε (Set.mem_Ioi.1 hm)))]
  refine Filter.Tendsto.limUnder_eq ?_
  refine (htend.const_mul (1 / (Real.pi : ℂ))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [setIntegral_hilbert_eq_Ioi f x hε]

/-- **The commutator identity for the Hilbert transform**: multiplying by the coordinate turns
`𝓗 g` into the Hilbert transform of `t g(t)`, up to the total mass of `g`. It is the pointwise
identity `x g(t)/(x - t) = t g(t)/(x - t) + g(t)`. -/
theorem coord_mul_pvHilbertTransform (g h : SchwartzMap ℝ ℂ)
    (hgh : ∀ t : ℝ, h t = (t : ℂ) * g t) (x : ℝ) :
    (x : ℂ) * pvHilbertTransform (⇑g) x
      = pvHilbertTransform (⇑h) x + (1 / (Real.pi : ℂ)) * ∫ t : ℝ, g t := by
  have hgI : IntegrableOn (fun s : ℝ => (g (x - s) - g (x + s)) / (s : ℂ)) (Ioi (0 : ℝ)) volume :=
    integrableOn_schwartz_oddDiff g x
  have hhI : IntegrableOn (fun s : ℝ => (h (x - s) - h (x + s)) / (s : ℂ)) (Ioi (0 : ℝ)) volume :=
    integrableOn_schwartz_oddDiff h x
  have hgl : Integrable (fun s : ℝ => g (x - s)) volume := by
    refine (integrable_schwartz_comp_affine g x (-1) (by norm_num)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [neg_one_mul, ← sub_eq_add_neg]
  have hgr : Integrable (fun s : ℝ => g (x + s)) volume := by
    refine (integrable_schwartz_comp_affine g x 1 (by norm_num)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [one_mul]
  have hmass : ((∫ s in Ioi (0 : ℝ), g (x - s)) + ∫ s in Ioi (0 : ℝ), g (x + s))
      = ∫ t : ℝ, g t := by
    have h1 : (∫ s in Ioi (0 : ℝ), g (x + s)) = ∫ t in Ioi x, g t := by
      have hmp : MeasurePreserving (fun s : ℝ => x + s) volume volume :=
        measurePreserving_add_left volume x
      have hpre : (fun s : ℝ => x + s) ⁻¹' Ioi x = Ioi (0 : ℝ) := by
        ext s; simp
      have hh := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft x) (⇑g) (Ioi x)
      rwa [hpre] at hh
    have h2 : (∫ s in Ioi (0 : ℝ), g (x - s)) = ∫ t in Iio x, g t := by
      have hmp : MeasurePreserving (fun s : ℝ => x - s) volume volume :=
        Measure.measurePreserving_sub_left volume x
      have hpre : (fun s : ℝ => x - s) ⁻¹' Iio x = Ioi (0 : ℝ) := by
        ext s; simp
      have hh := hmp.setIntegral_preimage_emb (measurableEmbedding_subLeft x) (⇑g) (Iio x)
      rwa [hpre] at hh
    rw [h1, h2, ← integral_Ici_eq_integral_Ioi,
      intervalIntegral.integral_Iio_add_Ici (SchwartzMap.integrable g).integrableOn
        (SchwartzMap.integrable g).integrableOn]
  rw [pvHilbertTransform_schwartz_eq_oddIntegral, pvHilbertTransform_schwartz_eq_oddIntegral,
    ← mul_assoc, mul_comm ((x : ℂ)) (1 / (Real.pi : ℂ)), mul_assoc, ← mul_add]
  congr 1
  rw [← integral_const_mul, ← hmass, ← integral_add hgl.integrableOn hgr.integrableOn,
    ← sub_eq_iff_eq_add', ← integral_sub (hgI.const_mul _) hhI]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  rw [hgh, hgh]
  push_cast
  field_simp
  ring

/-- Multiplication by the coordinate as an endomorphism of Schwartz space, `g ↦ (t ↦ g t ⬝ t)`. -/
def coordMulSchwartz (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) Complex.ofRealCLM.hasTemperateGrowth g

@[simp]
theorem coordMulSchwartz_apply (g : SchwartzMap ℝ ℂ) (t : ℝ) :
    coordMulSchwartz g t = g t * (t : ℂ) := rfl

/-- **The Hilbert transform of a Schwartz function is square-integrable.** On the Fourier side it
is multiplication by the unimodular symbol `-i sign ξ`, so Plancherel applies. -/
theorem memLp_two_pvHilbertTransform (f : SchwartzMap ℝ ℂ) :
    MemLp (pvHilbertTransform (⇑f)) 2 volume := by
  set F : ℝ → ℂ := fun ξ => -Complex.I * ((Real.sign ξ : ℝ) : ℂ) * 𝓕 (⇑f) ξ with hF_def
  have hFhat : Integrable (𝓕 (⇑f)) volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  have hFhat2 : MemLp (𝓕 (⇑f)) 2 volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.memLp _ 2 _
  have hsign : ∀ ξ : ℝ, |Real.sign ξ| ≤ 1 := by
    intro ξ
    rcases lt_trichotomy ξ 0 with h | h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [h, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have hFm : AEStronglyMeasurable F volume := by
    refine AEStronglyMeasurable.mul ?_ hFhat.aestronglyMeasurable
    exact (measurable_const.mul (Complex.measurable_ofReal.comp
      measurable_real_sign)).aestronglyMeasurable
  have hbound : ∀ ξ : ℝ, ‖F ξ‖ ≤ ‖𝓕 (⇑f) ξ‖ := by
    intro ξ
    rw [hF_def]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hsign ξ)
  have hFint : Integrable F volume :=
    hFhat.norm.mono' hFm (Filter.Eventually.of_forall fun ξ => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound ξ)
  have hF2 : MemLp F 2 volume :=
    hFhat2.mono hFm (Filter.Eventually.of_forall hbound)
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume := Measure.measurePreserving_neg _
  have hFnint : Integrable (fun x : ℝ => F (-x)) volume := hFint.comp_neg
  have hFn2 : MemLp (fun x : ℝ => F (-x)) 2 volume := hF2.comp_measurePreserving hneg
  have hrep : pvHilbertTransform (⇑f) = 𝓕 (fun x : ℝ => F (-x)) := by
    funext x
    rw [pvHilbertTransform_schwartz_eq_fourierInv f x, fourierInv_eq_fourier_comp_neg]
  rw [hrep]
  exact hFnint.memLp_fourier hFn2

/-- **The Hilbert transform of a Schwartz function with vanishing integral is integrable.**

The Hilbert transform of a Schwartz function is only `O(1/x)` in general; the hypothesis
`∫ g = 0` kills the leading term and improves the decay to `O(1/x²)`. The proof does not estimate
the decay directly: by `coord_mul_pvHilbertTransform` the function `x ↦ x 𝓗g(x)` is again the
Hilbert transform of a Schwartz function, hence square-integrable, and away from the origin
`‖𝓗g x‖ = |x|⁻¹ ‖x 𝓗g x‖ ≤ (1 + x²)⁻¹ + ‖x 𝓗g x‖²` by the arithmetic--geometric mean
inequality. -/
theorem integrable_pvHilbertTransform_of_integral_eq_zero (g : SchwartzMap ℝ ℂ)
    (hg : (∫ t : ℝ, g t) = 0) : Integrable (pvHilbertTransform (⇑g)) volume := by
  have h2g : MemLp (pvHilbertTransform (⇑g)) 2 volume := memLp_two_pvHilbertTransform g
  have hmeas : AEStronglyMeasurable (pvHilbertTransform (⇑g)) volume := h2g.aestronglyMeasurable
  have hcomm : ∀ x : ℝ, pvHilbertTransform (⇑(coordMulSchwartz g)) x
      = (x : ℂ) * pvHilbertTransform (⇑g) x := by
    intro x
    rw [coord_mul_pvHilbertTransform g (coordMulSchwartz g)
      (fun t => by rw [coordMulSchwartz_apply]; ring) x, hg, mul_zero, add_zero]
  have h2c : MemLp (fun x : ℝ => (x : ℂ) * pvHilbertTransform (⇑g) x) 2 volume :=
    (memLp_two_pvHilbertTransform (coordMulSchwartz g)).ae_eq
      (Filter.Eventually.of_forall hcomm)
  -- near the origin: a square-integrable function on a set of finite measure is integrable
  have hnear : IntegrableOn (pvHilbertTransform (⇑g)) (Icc (-1 : ℝ) 1) volume := by
    haveI : Fact (volume (Icc (-1 : ℝ) 1) < ⊤) := ⟨by simp⟩
    exact (h2g.restrict _).integrable one_le_two
  -- away from the origin: the arithmetic--geometric mean inequality
  have hset : MeasurableSet {x : ℝ | 1 < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hsq : Integrable (fun x : ℝ => ‖(x : ℂ) * pvHilbertTransform (⇑g) x‖ ^ 2) volume :=
    h2c.norm.integrable_sq
  have hfar : IntegrableOn (pvHilbertTransform (⇑g)) {x : ℝ | 1 < |x|} volume := by
    refine Integrable.mono' (integrable_inv_one_add_sq.add hsq).integrableOn hmeas.restrict ?_
    filter_upwards [ae_restrict_mem hset] with x hx
    simp only [Pi.add_apply]
    have hx1 : (1 : ℝ) < |x| := hx
    have hx0 : (0 : ℝ) < |x| := lt_trans one_pos hx1
    set b : ℝ := ‖(x : ℂ) * pvHilbertTransform (⇑g) x‖ with hb_def
    have hab : |x|⁻¹ * b = ‖pvHilbertTransform (⇑g) x‖ := by
      rw [hb_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hx0), one_mul]
    have hx2 : (1 : ℝ) ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hxpos : (0 : ℝ) < x ^ 2 := lt_of_lt_of_le one_pos hx2
    have hone : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hinv : (|x|⁻¹) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [inv_pow, sq_abs]
      calc (x ^ 2)⁻¹ = 1 / x ^ 2 := by rw [one_div]
        _ ≤ 2 / (1 + x ^ 2) := by
            rw [div_le_div_iff₀ hxpos hone]
            linarith
        _ = 2 * (1 + x ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    calc ‖pvHilbertTransform (⇑g) x‖ = |x|⁻¹ * b := hab.symm
      _ ≤ ((|x|⁻¹) ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (|x|⁻¹ - b)]
      _ ≤ (1 + x ^ 2)⁻¹ + b ^ 2 := by nlinarith [sq_nonneg b]
  rw [← integrableOn_univ, show (Set.univ : Set ℝ) = Icc (-1 : ℝ) 1 ∪ {x : ℝ | 1 < |x|} from ?_]
  · exact hnear.union hfar
  · ext x
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ x⟩
    rcases le_or_gt |x| 1 with h | h
    · exact Or.inl (abs_le.1 h)
    · exact Or.inr h

end MeasureTheory

