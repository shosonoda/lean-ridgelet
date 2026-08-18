/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import LeanRidgelet.ToMathlib.LpIndicator
public import LeanRidgelet.ToMathlib.LpUnimodular

/-!
# Fourier-character multipliers on `L²`

The Fourier characters of a finite-dimensional real inner-product space, restricted along a
measurable embedding, generate the scalar Borel multiplication algebra on `L²`.  Consequently, a
bounded operator commuting with every character multiplier commutes with every measurable-set
indicator projection.

The final statement is the concrete multiplier form of the spectral-projection commutant
criterion used in Folland's Theorem 4.44.  It deliberately avoids introducing a general
projection-valued-measure structure.  Density of finite character sums in `L²` of an arbitrary
finite measure follows from uniqueness of finite measures from their characteristic functions
(`MeasureTheory.ext_of_integral_char_eq`).  A weighted-measure argument then gives simultaneous
approximation on two `L²` vectors, after which finite character sums pass through the bounded
operator.
-/

@[expose] public section

noncomputable section

open scoped ENNReal InnerProductSpace
open Complex ComplexConjugate

namespace MeasureTheory

variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure X}

/-- The `L²(μ)` seminorm of a pointwise product is the seminorm of the first factor for the
measure weighted by the squared norm of the second factor. -/
theorem eLpNorm_mul_eq_eLpNorm_withDensity_enorm_sq (u f : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ u x * f x) 2 μ =
      eLpNorm u 2 (μ.withDensity fun x ↦ ‖f x‖ₑ ^ (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (hf.enorm.pow_const 2) (hu.enorm.pow_const 2)]
  apply lintegral_congr_ae
  filter_upwards with x
  simp only [Pi.mul_apply, enorm_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2)]
  ac_rfl

/-- The Fourier character on `V`, pulled back along a map `j : X → V`.  The sign and the
`2π` normalization agree with Mathlib's Fourier transform. -/
def fourierCharacterMultiplierPhase (j : X → V) (b : V) (x : X) : ℂ :=
  Real.fourierChar (-⟪b, j x⟫_ℝ)

/-- A measurable pullback of a Fourier character is strongly measurable. -/
theorem fourierCharacterMultiplierPhase_aestronglyMeasurable (j : X → V)
    (hj : Measurable j) (b : V) :
    AEStronglyMeasurable (fourierCharacterMultiplierPhase j b) μ := by
  have hinner : AEStronglyMeasurable (fun x ↦ -⟪b, j x⟫_ℝ) μ :=
    (AEStronglyMeasurable.inner aestronglyMeasurable_const hj.aestronglyMeasurable).neg
  exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp_aestronglyMeasurable
    hinner

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Pulled-back Fourier characters are pointwise unimodular. -/
theorem fourierCharacterMultiplierPhase_norm_one (j : X → V) (b : V) :
    ∀ᵐ x ∂μ, ‖fourierCharacterMultiplierPhase j b x‖ = 1 := by
  filter_upwards with x
  exact Circle.norm_coe _

/-- Multiplication by a pulled-back Fourier character, bundled as a unitary `L²` operator. -/
noncomputable def fourierCharacterLpMultiplier (j : X → V) (hj : Measurable j) (b : V) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  unimodularMultiplierLinearIsometryEquiv (fourierCharacterMultiplierPhase j b)
    (fourierCharacterMultiplierPhase_aestronglyMeasurable (μ := μ) j hj b)
    (fourierCharacterMultiplierPhase_norm_one (μ := μ) j b)

/-- The bundled Fourier-character multiplier has its defining pointwise representative. -/
theorem fourierCharacterLpMultiplier_apply_ae (j : X → V) (hj : Measurable j) (b : V)
    (f : Lp ℂ 2 μ) :
    fourierCharacterLpMultiplier (μ := μ) j hj b f =ᵐ[μ]
      fun x ↦ fourierCharacterMultiplierPhase j b x * f x := by
  exact unimodularMultiplierLinearIsometryEquiv_apply_ae _ _ _ f

/-- A real integrable density on a finite-dimensional real inner-product space is almost
everywhere zero if all of its Fourier-character integrals vanish. -/
theorem integrable_real_eq_zero_of_integral_fourierChar_inner
    {ν : Measure V} [IsFiniteMeasure ν]
    (r : V → ℝ) (hrm : Measurable r) (hr : Integrable r ν)
    (hzero : ∀ b : V,
      ∫ x, (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) * (r x : ℂ) ∂ν = 0) :
    r =ᵐ[ν] 0 := by
  let νp : Measure V := ν.withDensity fun x ↦ ENNReal.ofReal (r x)
  let νn : Measure V := ν.withDensity fun x ↦ ENNReal.ofReal (-r x)
  letI : IsFiniteMeasure νp := isFiniteMeasure_withDensity_ofReal hr.hasFiniteIntegral
  letI : IsFiniteMeasure νn := isFiniteMeasure_withDensity_ofReal hr.neg.hasFiniteIntegral
  have hmeasure : νp = νn := by
    have hinner : Continuous (fun p : V × V ↦ (innerₗ V p.1) p.2) := by
      simpa only [innerₗ_apply_apply] using
        (continuous_inner : Continuous (fun p : V × V ↦ ⟪p.1, p.2⟫_ℝ))
    refine ext_of_integral_char_eq Real.continuous_fourierChar Real.fourierChar_ne_one
      (L := innerₗ V)
      (fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩)
      hinner ?_
    intro b
    have hchar_meas : AEStronglyMeasurable
        (fun x : V ↦ (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)) ν := by
      fun_prop
    have hchar_norm : ∀ᵐ x : V ∂ν,
        ‖(Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)‖ ≤ 1 := by
      filter_upwards with x
      simp
    have hpint : Integrable
        (fun x : V ↦ ((max (r x) 0 : ℝ) : ℂ) *
          (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)) ν :=
      hr.pos_part.ofReal.mul_bdd hchar_meas hchar_norm
    have hnint : Integrable
        (fun x : V ↦ ((max (-r x) 0 : ℝ) : ℂ) *
          (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)) ν :=
      hr.neg_part.ofReal.mul_bdd hchar_meas hchar_norm
    apply sub_eq_zero.mp
    calc
      (∫ x, (BoundedContinuousFunction.char Real.continuous_fourierChar hinner b x) ∂νp) -
          ∫ x, (BoundedContinuousFunction.char Real.continuous_fourierChar hinner b x) ∂νn =
          (∫ x, (ENNReal.ofReal (r x)).toReal •
              (BoundedContinuousFunction.char Real.continuous_fourierChar hinner b x) ∂ν) -
            ∫ x, (ENNReal.ofReal (-r x)).toReal •
              (BoundedContinuousFunction.char Real.continuous_fourierChar hinner b x) ∂ν := by
        rw [show νp = ν.withDensity (fun x ↦ ENNReal.ofReal (r x)) from rfl,
          show νn = ν.withDensity (fun x ↦ ENNReal.ofReal (-r x)) from rfl,
          integral_withDensity_eq_integral_toReal_smul hrm.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
          integral_withDensity_eq_integral_toReal_smul
            (f := fun x ↦ ENNReal.ofReal (-r x)) hrm.neg.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      _ = (∫ x, ((max (r x) 0 : ℝ) : ℂ) *
              (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) ∂ν) -
            ∫ x, ((max (-r x) 0 : ℝ) : ℂ) *
              (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) ∂ν := by
        congr 1
      _ = ∫ x, (((max (r x) 0 : ℝ) : ℂ) *
              (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) -
            ((max (-r x) 0 : ℝ) : ℂ) *
              (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)) ∂ν := by
        rw [integral_sub hpint hnint]
      _ = ∫ x, (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) * (r x : ℂ) ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
        ring
      _ = 0 := hzero b
  have hdensity : (fun x ↦ ENNReal.ofReal (r x)) =ᵐ[ν]
      fun x ↦ ENNReal.ofReal (-r x) :=
    (withDensity_eq_iff_of_sigmaFinite (μ := ν)
      (f := fun x ↦ ENNReal.ofReal (r x)) (g := fun x ↦ ENNReal.ofReal (-r x))
      hrm.ennreal_ofReal.aemeasurable hrm.neg.ennreal_ofReal.aemeasurable).mp hmeasure
  filter_upwards [hdensity] with x hx
  change r x = 0
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpzero : ENNReal.ofReal (r x) = 0 := ENNReal.ofReal_eq_zero.mpr hneg.le
    have hnpos : ENNReal.ofReal (-r x) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (neg_pos.mpr hneg)).ne'
    exact hnpos (hx ▸ hpzero)
  · have hppos : ENNReal.ofReal (r x) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
    have hnzero : ENNReal.ofReal (-r x) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hpos.le)
    exact hppos (hx.trans hnzero)

/-- A complex integrable density on a finite-dimensional real inner-product space is almost
everywhere zero if all of its Fourier-character integrals vanish. -/
theorem integrable_complex_eq_zero_of_integral_fourierChar_inner
    {ν : Measure V} [IsFiniteMeasure ν]
    (f : V → ℂ) (hfm : Measurable f) (hf : Integrable f ν)
    (hzero : ∀ b : V,
      ∫ x, (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) * f x ∂ν = 0) :
    f =ᵐ[ν] 0 := by
  let χ : V → V → ℂ := fun b x ↦ (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ)
  have hχ_meas (b : V) : AEStronglyMeasurable (χ b) ν := by
    dsimp only [χ]
    fun_prop
  have hχ_norm (b : V) : ∀ᵐ x : V ∂ν, ‖χ b x‖ ≤ 1 := by
    filter_upwards with x
    simp [χ]
  have hχ_top (b : V) : MemLp (χ b) ∞ ν :=
    memLp_top_of_bound (hχ_meas b) 1 (hχ_norm b)
  have hχ_mul_f (b : V) : Integrable (fun x ↦ χ b x * f x) ν :=
    hf.mul_of_top_right (hχ_top b)
  have hχ_conj_mul_f (b : V) : Integrable (fun x ↦ conj (χ b x * f x)) ν :=
    (LinearIsometryEquiv.integrable_comp_iff (@RCLike.conjLIE ℂ _) (μ := ν)).2
      (hχ_mul_f b)
  have hχ_neg (b : V) : ∀ x, χ (-b) x = conj (χ b x) := by
    intro x
    simp only [χ, inner_neg_right, Real.fourierChar.map_neg_eq_inv,
      Circle.coe_inv_eq_conj]
  have hzero_re (b : V) :
      ∫ x, χ b x * ((f x).re : ℂ) ∂ν = 0 := by
    have hzb : ∫ x, χ b x * f x ∂ν = 0 := by simpa only [χ] using hzero b
    have hznb : ∫ x, χ (-b) x * f x ∂ν = 0 := by simpa only [χ] using hzero (-b)
    calc
      ∫ x, χ b x * ((f x).re : ℂ) ∂ν =
          ∫ x, (χ b x * f x + conj (χ (-b) x * f x)) / 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hχ_neg]
        simp only [map_mul, Complex.conj_conj]
        rw [Complex.re_eq_add_conj]
        ring
      _ = ((∫ x, χ b x * f x ∂ν) +
            ∫ x, conj (χ (-b) x * f x) ∂ν) / 2 := by
        rw [integral_div, integral_add (hχ_mul_f b) (hχ_conj_mul_f (-b))]
      _ = ((∫ x, χ b x * f x ∂ν) +
            conj (∫ x, χ (-b) x * f x ∂ν)) / 2 := by
        rw [integral_conj]
      _ = 0 := by simp [hzb, hznb]
  have hzero_im (b : V) :
      ∫ x, χ b x * ((f x).im : ℂ) ∂ν = 0 := by
    have hzb : ∫ x, χ b x * f x ∂ν = 0 := by simpa only [χ] using hzero b
    have hznb : ∫ x, χ (-b) x * f x ∂ν = 0 := by simpa only [χ] using hzero (-b)
    calc
      ∫ x, χ b x * ((f x).im : ℂ) ∂ν =
          ∫ x, (χ b x * f x - conj (χ (-b) x * f x)) / (2 * Complex.I) ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hχ_neg]
        simp only [map_mul, Complex.conj_conj]
        rw [Complex.im_eq_sub_conj]
        ring
      _ = ((∫ x, χ b x * f x ∂ν) -
            ∫ x, conj (χ (-b) x * f x) ∂ν) / (2 * Complex.I) := by
        rw [integral_div, integral_sub (hχ_mul_f b) (hχ_conj_mul_f (-b))]
      _ = ((∫ x, χ b x * f x ∂ν) -
            conj (∫ x, χ (-b) x * f x ∂ν)) / (2 * Complex.I) := by
        rw [integral_conj]
      _ = 0 := by simp [hzb, hznb]
  have hre : (fun x ↦ (f x).re) =ᵐ[ν] 0 :=
    integrable_real_eq_zero_of_integral_fourierChar_inner (fun x ↦ (f x).re)
      (Complex.continuous_re.measurable.comp hfm) hf.re hzero_re
  have him : (fun x ↦ (f x).im) =ᵐ[ν] 0 :=
    integrable_real_eq_zero_of_integral_fourierChar_inner (fun x ↦ (f x).im)
      (Complex.continuous_im.measurable.comp hfm) hf.im hzero_im
  filter_upwards [hre, him] with x hxre hxim
  apply Complex.ext
  · simpa using hxre
  · simpa using hxim

private noncomputable def fourierCharacterPhaseLp (ν : Measure V) [IsFiniteMeasure ν]
    (b : V) : Lp ℂ 2 ν :=
  let hphase : MemLp (fourierCharacterMultiplierPhase (V := V) id b) 2 ν :=
    MemLp.of_bound
      (fourierCharacterMultiplierPhase_aestronglyMeasurable
        (μ := ν) id measurable_id b) 1
      ((fourierCharacterMultiplierPhase_norm_one (μ := ν) id b).mono
        fun _ hx ↦ hx.le)
  hphase.toLp (fourierCharacterMultiplierPhase id b)

private theorem fourierCharacterPhaseLp_apply_ae (ν : Measure V) [IsFiniteMeasure ν]
    (b : V) :
    fourierCharacterPhaseLp ν b =ᵐ[ν] fourierCharacterMultiplierPhase id b := by
  unfold fourierCharacterPhaseLp
  exact MemLp.coeFn_toLp _

private theorem fourierCharacterPhaseLp_span_dense
    {ν : Measure V} [IsFiniteMeasure ν] :
    (Submodule.span ℂ (Set.range (fourierCharacterPhaseLp ν))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hforth
  let fm : V → ℂ := (Lp.aestronglyMeasurable f).mk f
  have hfm : Measurable fm := (Lp.aestronglyMeasurable f).measurable_mk
  have hfint : Integrable (fun x ↦ f x) ν :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num))
  have hfmint : Integrable fm ν :=
    hfint.congr (Lp.aestronglyMeasurable f).ae_eq_mk
  have hzero (b : V) :
      ∫ x, (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) * fm x ∂ν = 0 := by
    have hinner : ⟪fourierCharacterPhaseLp ν b, f⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self b)) hforth
    rw [L2.inner_def] at hinner
    calc
      ∫ x, (Real.fourierChar (⟪x, b⟫_ℝ) : ℂ) * fm x ∂ν =
          ∫ x, ⟪fourierCharacterPhaseLp ν b x, f x⟫_ℂ ∂ν := by
        apply integral_congr_ae
        filter_upwards [fourierCharacterPhaseLp_apply_ae ν b,
          (Lp.aestronglyMeasurable f).ae_eq_mk] with x hphase hfx
        rw [hphase]
        change _ * (Lp.aestronglyMeasurable f).mk f x = _
        rw [← hfx]
        simp only [RCLike.inner_apply', fourierCharacterMultiplierPhase, id_eq,
          Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj,
          Complex.conj_conj, real_inner_comm]
      _ = 0 := hinner
  have hfmzero : fm =ᵐ[ν] 0 :=
    integrable_complex_eq_zero_of_integral_fourierChar_inner fm hfm hfmint hzero
  apply (Lp.eq_zero_iff_ae_eq_zero).2
  exact (Lp.aestronglyMeasurable f).ae_eq_mk.trans hfmzero

/-- On a finite measure over `V`, finite complex linear combinations of Fourier characters
approximate every measurable indicator in `L²` seminorm.

This is the analytic density input to the multiplier form of Folland's Theorem 4.44.  The proof
identifies the orthogonal complement of the character span with integrable densities whose
characteristic function vanishes, applies `MeasureTheory.ext_of_integral_char_eq` to the positive
and negative parts of the real and imaginary components, and then uses
`Submodule.topologicalClosure_eq_top_iff`. -/
theorem exists_fourierCharacter_finset_approx_indicator_eLpNorm
    {ν : Measure V} [IsFiniteMeasure ν]
    (s : Set V) (hs : MeasurableSet s) {epsilon : ℝ≥0∞} (hepsilon : epsilon ≠ 0) :
    ∃ (t : Finset V) (c : V → ℂ),
      eLpNorm
        (fun x ↦ (∑ b ∈ t, c b * fourierCharacterMultiplierPhase id b x) -
          s.indicator (fun _ ↦ 1) x) 2 ν < epsilon := by
  by_cases hepsilon_top : epsilon = ∞
  · refine ⟨∅, 0, ?_⟩
    rw [hepsilon_top]
    have hmem : MemLp
        (fun x : V ↦ (0 : ℂ) - s.indicator (fun _ ↦ 1) x) 2 ν :=
      (memLp_const (0 : ℂ)).sub
        (memLp_indicator_const 2 hs (1 : ℂ) (Or.inr (measure_ne_top ν s)))
    simpa using hmem.eLpNorm_lt_top
  have hepsilon_real : 0 < epsilon.toReal :=
    ENNReal.toReal_pos hepsilon hepsilon_top
  let u : Lp ℂ 2 ν :=
    indicatorConstLp 2 hs (measure_ne_top ν s) (1 : ℂ)
  let K : Submodule ℂ (Lp ℂ 2 ν) :=
    Submodule.span ℂ (Set.range (fourierCharacterPhaseLp ν))
  have hu : u ∈ K.topologicalClosure := by
    rw [show K.topologicalClosure = ⊤ by
      exact fourierCharacterPhaseLp_span_dense (ν := ν)]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hu
  obtain ⟨v, hvK, huv⟩ := hu epsilon.toReal hepsilon_real
  obtain ⟨a, ha⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hvK
  have hav : (∑ b ∈ a.support, a b • fourierCharacterPhaseLp ν b) = v := by
    simpa only [Finsupp.sum] using ha
  refine ⟨a.support, fun b ↦ a b, ?_⟩
  have hpoint :
      (fun x ↦ (∑ b ∈ a.support,
          (a b : ℂ) * fourierCharacterMultiplierPhase id b x) -
        s.indicator (fun _ ↦ (1 : ℂ)) x) =ᵐ[ν]
        fun x ↦ (v - u) x := by
    have hsum := Lp.coeFn_finsetSum a.support
      (fun b ↦ a b • fourierCharacterPhaseLp ν b)
    have hsmul : ∀ b ∈ a.support, ∀ᵐ x ∂ν,
        (a b • fourierCharacterPhaseLp ν b) x =
          a b * fourierCharacterPhaseLp ν b x := fun b _ ↦ by
      exact (Lp.coeFn_smul (a b) (fourierCharacterPhaseLp ν b)).mono fun x hx ↦ by
        simpa only [Pi.smul_apply, smul_eq_mul] using hx
    have hsmul_all := eventually_finset_ball.2 hsmul
    have hphase : ∀ b ∈ a.support, ∀ᵐ x ∂ν,
        fourierCharacterPhaseLp ν b x =
          fourierCharacterMultiplierPhase id b x := fun b _ ↦
      fourierCharacterPhaseLp_apply_ae ν b
    have hphase_all := eventually_finset_ball.2 hphase
    have hu_ae := @indicatorConstLp_coeFn V ℂ _ 2 ν _ s hs
      (measure_ne_top ν s) (1 : ℂ)
    have hsub := Lp.coeFn_sub v u
    filter_upwards [hsum, hsmul_all, hphase_all, hu_ae, hsub] with
      x hsumx hsmulx hphasex hux hsubx
    rw [hav] at hsumx
    rw [hsubx]
    simp only [Pi.sub_apply]
    rw [hsumx, hux]
    simp only [Finset.sum_apply]
    apply congrArg (fun z : ℂ ↦ z - s.indicator (fun _ ↦ (1 : ℂ)) x)
    apply Finset.sum_congr rfl
    intro b hb
    rw [hsmulx b hb, hphasex b hb]
  rw [eLpNorm_congr_ae hpoint]
  have hnorm : ‖v - u‖ < epsilon.toReal := by
    simpa only [dist_eq_norm, norm_sub_rev] using huv
  rw [Lp.norm_def] at hnorm
  exact (ENNReal.toReal_lt_toReal (Lp.eLpNorm_ne_top (v - u)) hepsilon_top).mp hnorm

/-- A measurable indicator can be approximated simultaneously on two `L²` vectors by one finite
complex linear combination of pulled-back Fourier-character multipliers.

The proof pushes the finite measure weighted by the squared norms of `f` and `g` through `j`,
applies `exists_fourierCharacter_finset_approx_indicator_eLpNorm`, and pulls the approximation
back.  The simultaneous form is what allows the same polynomial to approximate both `f` and
`T f`. -/
theorem exists_finsetSum_fourierCharacterLpMultiplier_approx_indicatorLp
    (j : X → V) (hj : MeasurableEmbedding j) (f g : Lp ℂ 2 μ)
    (s : Set X) (hs : MeasurableSet s) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (t : Finset V) (c : V → ℂ),
      ‖(∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) f -
        indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f‖ < epsilon ∧
      ‖(∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) g -
        indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs g‖ < epsilon := by
  let wf : X → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ (2 : ℝ)
  let wg : X → ℝ≥0∞ := fun x ↦ ‖g x‖ₑ ^ (2 : ℝ)
  let w : X → ℝ≥0∞ := fun x ↦ wf x + wg x
  have hwf : AEMeasurable wf μ := (Lp.aestronglyMeasurable f).enorm.pow_const 2
  have hwf_top : (∫⁻ x, wf x ∂μ) ≠ ∞ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp f).2).ne
  have hwg_top : (∫⁻ x, wg x ∂μ) ≠ ∞ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp g).2).ne
  have hw_top : (∫⁻ x, w x ∂μ) ≠ ∞ := by
    change (∫⁻ x, wf x + wg x ∂μ) ≠ ∞
    rw [lintegral_add_left' hwf]
    exact ENNReal.add_ne_top.mpr ⟨hwf_top, hwg_top⟩
  let ρ : Measure X := μ.withDensity w
  let ν : Measure V := Measure.map j ρ
  letI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity hw_top
  letI : IsFiniteMeasure ν := by
    dsimp only [ν]
    infer_instance
  obtain ⟨t, c, happrox⟩ :=
    exists_fourierCharacter_finset_approx_indicator_eLpNorm (ν := ν) (j '' s)
      (hj.measurableSet_image' hs) (ENNReal.ofReal_ne_zero_iff.mpr hepsilon)
  let q : V → ℂ := fun x ↦ ∑ b ∈ t, c b * fourierCharacterMultiplierPhase id b x
  let e : X → ℂ := fun x ↦ q (j x) - s.indicator (fun _ ↦ 1) x
  have hindicator (x : X) :
      (j '' s).indicator (fun _ ↦ (1 : ℂ)) (j x) = s.indicator (fun _ ↦ 1) x := by
    by_cases hx : x ∈ s
    · have hjxs : j x ∈ j '' s := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hjxs, Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]
      rw [Set.indicator_of_notMem]
      rintro ⟨y, hy, hjyx⟩
      exact hx (hj.injective hjyx ▸ hy)
  have he_approx : eLpNorm e 2 ρ < ENNReal.ofReal epsilon := by
    calc
      eLpNorm e 2 ρ = eLpNorm (fun x ↦
          q x - (j '' s).indicator (fun _ ↦ (1 : ℂ)) x) 2 ν := by
        rw [show ν = Measure.map j ρ from rfl, hj.eLpNorm_map_measure]
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by simp only [Function.comp_apply, e, hindicator]
      _ < ENNReal.ofReal epsilon := by simpa only [q] using happrox
  have h_wf_le_w : μ.withDensity wf ≤ ρ := by
    exact withDensity_mono (Filter.Eventually.of_forall fun _ ↦ le_add_right le_rfl)
  have h_wg_le_w : μ.withDensity wg ≤ ρ := by
    exact withDensity_mono (Filter.Eventually.of_forall fun _ ↦ le_add_left le_rfl)
  have he_meas : AEStronglyMeasurable e μ := by
    have hq : AEStronglyMeasurable
        (fun x ↦ ∑ b ∈ t, c b * fourierCharacterMultiplierPhase j b x) μ := by
      have hsum := Finset.aestronglyMeasurable_sum t fun b _ ↦
        (fourierCharacterMultiplierPhase_aestronglyMeasurable
          (μ := μ) j hj.measurable b).const_mul (c b)
      exact hsum.congr (Filter.Eventually.of_forall fun x ↦ by
        simp only [Finset.sum_apply])
    have hq_eq : (fun x ↦ q (j x)) =
        fun x ↦ ∑ b ∈ t, c b * fourierCharacterMultiplierPhase j b x := by
      funext x
      simp only [q, fourierCharacterMultiplierPhase, id_eq]
    have hq_comp : AEStronglyMeasurable (fun x ↦ q (j x)) μ :=
      hq.congr (Filter.Eventually.of_forall fun x ↦ (congrFun hq_eq x).symm)
    exact hq_comp.sub (aestronglyMeasurable_const.indicator hs)
  have hef : eLpNorm (fun x ↦ e x * f x) 2 μ < ENNReal.ofReal epsilon := by
    rw [eLpNorm_mul_eq_eLpNorm_withDensity_enorm_sq e f he_meas
      (Lp.aestronglyMeasurable f)]
    exact (eLpNorm_mono_measure e h_wf_le_w).trans_lt he_approx
  have heg : eLpNorm (fun x ↦ e x * g x) 2 μ < ENNReal.ofReal epsilon := by
    rw [eLpNorm_mul_eq_eLpNorm_withDensity_enorm_sq e g he_meas
      (Lp.aestronglyMeasurable g)]
    exact (eLpNorm_mono_measure e h_wg_le_w).trans_lt he_approx
  have hnorm (u : Lp ℂ 2 μ)
      (heu : eLpNorm (fun x ↦ e x * u x) 2 μ < ENNReal.ofReal epsilon) :
      ‖(∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) u -
        indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs u‖ < epsilon := by
    have heq : eLpNorm
        (↑↑((∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) u -
        indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs u)) 2 μ =
          eLpNorm (fun x ↦ e x * u x) 2 μ := by
      apply eLpNorm_congr_ae
      have hsum := Lp.coeFn_finsetSum t fun b ↦
        c b • fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u
      have hmult : ∀ b ∈ t, ∀ᵐ x ∂μ,
          fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u x =
            fourierCharacterMultiplierPhase j b x * u x := fun b _ ↦
        fourierCharacterLpMultiplier_apply_ae j hj.measurable b u
      have hmult_all := eventually_finset_ball.2 hmult
      have hsmul : ∀ b ∈ t, ∀ᵐ x ∂μ,
          (c b • fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u) x =
            c b * fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u x := fun b _ ↦ by
        exact (Lp.coeFn_smul (c b)
          (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u)).mono fun x hx ↦ by
            simpa only [Pi.smul_apply, smul_eq_mul] using hx
      have hsmul_all := eventually_finset_ball.2 hsmul
      have hind := indicatorLp_apply_ae (p := (2 : ℝ≥0∞)) (μ := μ)
        (E := ℂ) (𝕜 := ℂ) s hs u
      have hsub := Lp.coeFn_sub
        ((∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) u)
        (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs u)
      filter_upwards [hsum, hmult_all, hsmul_all, hind, hsub] with x hsumx hmultx hsmulx hindx hsubx
      rw [hsubx]
      change _ - (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ)
        (E := ℂ) (𝕜 := ℂ) s hs u) x = e x * u x
      rw [hindx]
      simp only [Finset.sum_apply] at hsumx
      rw [show ((∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j
        hj.measurable b : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) u : Lp ℂ 2 μ) =
          ∑ b ∈ t, c b • fourierCharacterLpMultiplier (μ := μ) j hj.measurable b u by simp,
        hsumx]
      rw [Finset.sum_congr rfl fun b hb ↦ hsmulx b hb]
      rw [Finset.sum_congr rfl fun b hb ↦ congrArg (c b * ·) (hmultx b hb)]
      simp only [e, q, fourierCharacterMultiplierPhase, id_eq]
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx]
        rw [sub_mul, one_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro b hb
        ring
      · simp only [Set.indicator_of_notMem hx, sub_zero, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        ring
    rw [Lp.norm_def, heq, ← ENNReal.toReal_ofReal hepsilon.le]
    exact (ENNReal.toReal_lt_toReal heu.ne_top ENNReal.ofReal_ne_top).2 heu
  exact ⟨t, c, hnorm f hef, hnorm g heg⟩

/-- Commutation with individual Fourier-character multipliers extends to every finite complex
linear combination of them. -/
theorem ContinuousLinearMap.commutes_finsetSum_fourierCharacterLpMultiplier
    (j : X → V) (hj : Measurable j) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hchar : ∀ b : V,
      T.comp (fourierCharacterLpMultiplier (μ := μ) j hj b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =
        (fourierCharacterLpMultiplier (μ := μ) j hj b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).comp T)
    (s : Finset V) (c : V → ℂ) :
    T.comp (∑ b ∈ s, c b • (fourierCharacterLpMultiplier (μ := μ) j hj b :
        Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) =
      (∑ b ∈ s, c b • (fourierCharacterLpMultiplier (μ := μ) j hj b :
        Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).comp T := by
  change Commute T (∑ b ∈ s, c b • (fourierCharacterLpMultiplier (μ := μ) j hj b :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
  refine Commute.sum_right s _ T fun b _ ↦ ?_
  exact (show Commute T (fourierCharacterLpMultiplier (μ := μ) j hj b :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) from hchar b).smul_right (c b)

/-- A bounded operator commuting with every pulled-back Fourier-character multiplier commutes
with every measurable indicator projection.

This is the minimal `L²` multiplier consequence of the spectral-projection commutant criterion:
the measurable embedding ensures that the restricted characters generate the measurable
structure on `X`.  No general projection-valued-measure object is needed. -/
theorem ContinuousLinearMap.commutes_indicatorLp_of_commutes_fourierCharacter
    (j : X → V) (hj : MeasurableEmbedding j) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hchar : ∀ b : V,
      T.comp (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =
        (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
          Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).comp T)
    (s : Set X) (hs : MeasurableSet s) :
    T.comp (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs) =
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs).comp T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply]
  apply eq_of_forall_dist_le
  intro epsilon hepsilon
  have hden_pos : 0 < ‖T‖ + 1 := by positivity
  have hdelta_pos : 0 < epsilon / (‖T‖ + 1) := div_pos hepsilon hden_pos
  obtain ⟨t, c, hf, hTf⟩ :=
    exists_finsetSum_fourierCharacterLpMultiplier_approx_indicatorLp
      j hj f (T f) s hs hdelta_pos
  let A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    ∑ b ∈ t, c b • (fourierCharacterLpMultiplier (μ := μ) j hj.measurable b :
      Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
  have hcomm := ContinuousLinearMap.commutes_finsetSum_fourierCharacterLpMultiplier
    j hj.measurable T hchar t c
  have hpoint : T (A f) = A (T f) := by
    exact DFunLike.congr_fun hcomm f
  have hf_dist : dist
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f) (A f) <
        epsilon / (‖T‖ + 1) := by
    simpa only [A, dist_eq_norm, norm_sub_rev] using hf
  have hTf_dist : dist (A (T f))
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) <
        epsilon / (‖T‖ + 1) := by
    simpa only [A, dist_eq_norm] using hTf
  have hbound : dist
      (T (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f))
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) <
        ‖T‖ * (epsilon / (‖T‖ + 1)) + epsilon / (‖T‖ + 1) := by
    calc
      dist
          (T (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f))
          (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) ≤
          dist
              (T (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f))
              (T (A f)) +
            dist (T (A f))
              (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) :=
        dist_triangle _ _ _
      _ = dist
              (T (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f))
              (T (A f)) +
            dist (A (T f))
              (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) := by
        rw [hpoint]
      _ ≤ ‖T‖ * dist
              (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f) (A f) +
            dist (A (T f))
              (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs (T f)) := by
        gcongr
        exact T.dist_le_opNorm _ _
      _ < ‖T‖ * (epsilon / (‖T‖ + 1)) + epsilon / (‖T‖ + 1) := by
        exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hf_dist.le (norm_nonneg T)) hTf_dist
  have hsum :
      ‖T‖ * (epsilon / (‖T‖ + 1)) + epsilon / (‖T‖ + 1) = epsilon := by
    field_simp
  exact (hbound.trans_eq hsum).le

end MeasureTheory
