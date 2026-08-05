/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Balancing
public import LeanRidgelet.L1.Plancherel
public import LeanRidgelet.L1.ReconstructionSection
public import LeanRidgelet.ToMathlib.L2Duality

/-!
# L1 theory: reconstruction in `L²` (`thm:formula.L2`)

The compatibility statement between the L1 and L2 reconstructions on `L¹ ∩ L²`: for normalized
self-admissible `ψ`, `η` with `K_{ψ,η} = 1`, the truncated reconstruction converges to `f` in
`L²(ℝ^m)`.

## Main results

* `LeanRidgelet.setIntegral_annulus_ridgeletTransform_mul_conj`: **truncated duality**, the
  identity `thm:dual` applied to the annulus-truncated data `1_A R_ψ f`.
* `LeanRidgelet.eLpNorm_truncatedDualRidgeletTransform_sub_le`: the **error bound**
  `‖R†_η[R_ψ f](·; ε, δ) - f‖₂ ≤ ‖R_ψ f‖_{L²(Aᶜ)}`, obtained by subtracting Parseval's relation
  and testing against an exhausting sequence of balls with the `L²` duality criterion of
  `LeanRidgelet.ToMathlib.L2Duality`; no a priori `L²`-membership of the truncated
  reconstruction is needed.
* `LeanRidgelet.tendsto_setIntegral_compl_annulus_norm_sq`: the **vanishing tail**.
* `LeanRidgelet.l1_reconstruction_formula_L2`: `thm:formula.L2`.

## Standing hypotheses

As in `LeanRidgelet.L1.Plancherel`, on which this rests, both `ψ` and `η` are integrable,
continuous and bounded, so this Euclidean form of the `L²` reconstruction does not cover the
unbounded activations of Section 6 of the article; in weighted Sobolev coordinates the L2 theory
does (see the standing-hypotheses note of `LeanRidgelet.L1.Plancherel`).

## Deviations from the article

The article assumes admissible decomposability and then opens its proof with "assume without
loss of generality that `(ψ, ψ)` and `(η, η)` are self-admissible". That reduction needs the
equivalence-invariance of the composite `R†_η R_ψ`, a distributional statement absent from the
function-level development, so self-admissibility of both members is taken as a hypothesis —
exactly as in the amended Parseval relation on which the proof rests. The general `f ∈ L²`
case follows from the bounded extension `thm:L2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The annulus-truncated data -/

/-- The scale annulus `ε ≤ ‖a‖ ≤ δ` of the parameter space is measurable. -/
theorem measurableSet_annulusParameter (m : ℕ) (ε δ : ℝ) :
    MeasurableSet {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} := by
  have h : {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}
      = (scaleAnnulus m ε δ) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [scaleAnnulus, Set.mem_prod]
  rw [h]
  exact (measurableSet_scaleAnnulus m ε δ).prod MeasurableSet.univ

/-- The `L¹` norm of the ridgelet transform in the bias variable is bounded by
`‖f‖₁ ‖ψ‖₁ ‖a‖^s`. -/
theorem integral_norm_euclideanRidgeletTransform_bias_le (m : ℕ) (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume) (a : InputSpace m) :
    ∫ b, ‖euclideanRidgeletTransform m s ψ f (a, b)‖ ≤
      (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖) * ‖a‖ ^ s := by
  have hker := integrable_ridgelet_bias_kernel hf hψ a
  have hrs : (0 : ℝ) ≤ ‖a‖ ^ s := Real.rpow_nonneg (norm_nonneg _) s
  have hpt : ∀ b : ℝ, ‖euclideanRidgeletTransform m s ψ f (a, b)‖
      ≤ (∫ x, ‖f x * conj (ψ (inner ℝ a x - b))‖) * ‖a‖ ^ s := by
    intro b
    have hsplit : euclideanRidgeletTransform m s ψ f (a, b)
        = (∫ x, f x * conj (ψ (inner ℝ a x - b))) * ((‖a‖ ^ s : ℝ) : ℂ) := by
      unfold euclideanRidgeletTransform
      rw [← integral_mul_const]
    rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrs]
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hrs
  have hint1 : Integrable (fun b => ‖euclideanRidgeletTransform m s ψ f (a, b)‖) volume :=
    (integrable_euclideanRidgeletTransform_bias m s hf hψ a).norm
  have hint2 : Integrable
      (fun b => (∫ x, ‖f x * conj (ψ (inner ℝ a x - b))‖) * ‖a‖ ^ s) volume :=
    (hker.norm.integral_prod_left).mul_const (‖a‖ ^ s)
  calc ∫ b, ‖euclideanRidgeletTransform m s ψ f (a, b)‖
      ≤ ∫ b, (∫ x, ‖f x * conj (ψ (inner ℝ a x - b))‖) * ‖a‖ ^ s :=
        integral_mono hint1 hint2 hpt
    _ = (∫ b, ∫ x, ‖f x * conj (ψ (inner ℝ a x - b))‖) * ‖a‖ ^ s := integral_mul_const _ _
    _ = (∫ x, ∫ b, ‖f x * conj (ψ (inner ℝ a x - b))‖) * ‖a‖ ^ s := by
        rw [integral_integral_swap hker.norm]
    _ = (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖) * ‖a‖ ^ s := by
        have h2 : ∀ x : InputSpace m, (∫ b, ‖f x * conj (ψ (inner ℝ a x - b))‖)
            = ‖f x‖ * ∫ z, ‖ψ z‖ := by
          intro x
          have h1 : ∀ b : ℝ, ‖f x * conj (ψ (inner ℝ a x - b))‖
              = ‖f x‖ * ‖ψ (inner ℝ a x - b)‖ := by
            intro b
            rw [norm_mul, RCLike.norm_conj]
          simp only [h1]
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun z => ‖ψ z‖) volume (inner ℝ a x)
        rw [show (∫ x, ∫ b, ‖f x * conj (ψ (inner ℝ a x - b))‖)
            = ∫ x, ‖f x‖ * ∫ z, ‖ψ z‖ from
          integral_congr_ae (Filter.Eventually.of_forall h2), integral_mul_const]

/-- With a positive inner truncation radius the truncated ridgelet data has an integrable
weighted form, the hypothesis of the duality identity `l1_dualRidgeletTransform_pairing`. -/
theorem integrable_weight_indicator_euclideanRidgeletTransform (m : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume) (hψc : Continuous ψ)
    {ε δ : ℝ} (hε : 0 < ε) :
    Integrable (fun q : RidgeletParameterSpace m =>
      Set.indicator {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}
        (euclideanRidgeletTransform m 1 ψ f) q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume := by
  classical
  set A : Set (RidgeletParameterSpace m) := {p | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} with hA_def
  have hAmeas : MeasurableSet A := by
    rw [hA_def]
    exact measurableSet_annulusParameter m ε δ
  set F : RidgeletParameterSpace m → ℂ := fun q =>
    Set.indicator A (euclideanRidgeletTransform m 1 ψ f) q * ((‖q.1‖ : ℝ) : ℂ)⁻¹ with hF_def
  have hw : Measurable fun q : RidgeletParameterSpace m => ((‖q.1‖ : ℝ) : ℂ)⁻¹ :=
    (measurable_fst.norm.complex_ofReal).inv
  have hFaesm : AEStronglyMeasurable F (volume : Measure (RidgeletParameterSpace m)) :=
    ((aestronglyMeasurable_euclideanRidgeletTransform m 1 hf hψc).indicator hAmeas).mul
      hw.aestronglyMeasurable
  -- the fiberwise data
  have hmemA : ∀ (a : InputSpace m) (b : ℝ),
      ((a, b) ∈ A) ↔ (ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ) := by
    intro a b
    simp [hA_def]
  have hfiber : ∀ a : InputSpace m, Integrable (fun b => F (a, b)) volume := by
    intro a
    by_cases ha : ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ
    · have hcongr : ∀ b : ℝ, F (a, b)
          = euclideanRidgeletTransform m 1 ψ f (a, b) * ((‖a‖ : ℝ) : ℂ)⁻¹ := by
        intro b
        rw [hF_def]
        simp only []
        rw [Set.indicator_of_mem ((hmemA a b).mpr ha)]
      refine ((integrable_euclideanRidgeletTransform_bias m 1 hf hψ a).mul_const
        (((‖a‖ : ℝ) : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun b => ?_)
      exact (hcongr b).symm
    · have hcongr : ∀ b : ℝ, F (a, b) = 0 := by
        intro b
        rw [hF_def]
        simp only []
        rw [Set.indicator_of_notMem (by simpa [hmemA a b] using ha), zero_mul]
      exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun b => (hcongr b).symm)
  -- the fiberwise `L¹` bound
  have hbound : ∀ a : InputSpace m, (∫ b, ‖F (a, b)‖)
      ≤ Set.indicator {a : InputSpace m | ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ}
          (fun _ => (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖)) a := by
    intro a
    by_cases ha : ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ
    · have ha0 : ‖a‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hε ha.1)
      have hcongr : ∀ b : ℝ, ‖F (a, b)‖
          = ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ * ‖a‖⁻¹ := by
        intro b
        rw [hF_def]
        simp only []
        rw [Set.indicator_of_mem ((hmemA a b).mpr ha), norm_mul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
      rw [Set.indicator_of_mem (by simpa using ha)]
      calc (∫ b, ‖F (a, b)‖)
          = (∫ b, ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ * ‖a‖⁻¹) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
            exact hcongr b
        _ = (∫ b, ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖) * ‖a‖⁻¹ :=
            integral_mul_const _ _
        _ ≤ ((∫ x, ‖f x‖) * (∫ z, ‖ψ z‖) * ‖a‖ ^ (1 : ℝ)) * ‖a‖⁻¹ :=
            mul_le_mul_of_nonneg_right
              (integral_norm_euclideanRidgeletTransform_bias_le m 1 hf hψ a) (by positivity)
        _ = (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖) := by
            rw [Real.rpow_one, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
    · have hcongr : ∀ b : ℝ, ‖F (a, b)‖ = 0 := by
        intro b
        rw [hF_def]
        simp only []
        rw [Set.indicator_of_notMem (by simpa [hmemA a b] using ha), zero_mul, norm_zero]
      rw [Set.indicator_of_notMem (by simpa using ha)]
      simp only [hcongr, integral_zero]
      exact le_rfl
  -- assemble through Fubini
  rw [Measure.volume_eq_prod] at hFaesm ⊢
  rw [integrable_prod_iff hFaesm]
  refine ⟨Filter.Eventually.of_forall hfiber, ?_⟩
  have hdom : Integrable (Set.indicator {a : InputSpace m | ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ}
      (fun _ => (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖))) (volume : Measure (InputSpace m)) := by
    refine (MeasureTheory.integrableOn_const (C := (∫ x, ‖f x‖) * (∫ z, ‖ψ z‖))
      ?_).integrable_indicator (measurableSet_scaleAnnulus m ε δ)
    exact (volume_scaleAnnulus_lt_top m ε δ).ne
  refine hdom.mono' hFaesm.norm.integral_prod_right' (Filter.Eventually.of_forall fun a => ?_)
  have hnn : (0 : ℝ) ≤ ∫ b, ‖F (a, b)‖ :=
    integral_nonneg fun b => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hbound a

/-- The truncated dual ridgelet transform of weighted-integrable data against a bounded
activation is uniformly bounded in the input variable. -/
theorem norm_truncatedDualRidgeletTransform_le (m : ℕ) {η : ℝ → ℂ} {Cη : ℝ}
    {T : RidgeletParameterSpace m → ℂ} {ε δ : ℝ}
    (hTm : AEStronglyMeasurable T (volume : Measure (RidgeletParameterSpace m)))
    (hT : Integrable (fun q : RidgeletParameterSpace m => T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume)
    (hηc : Continuous η) (hηb : ∀ z, ‖η z‖ ≤ Cη) (x : InputSpace m) :
    ‖truncatedDualRidgeletTransform m 1 η T ε δ x‖
      ≤ Cη * ∫ q, ‖T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹‖ := by
  have hCη : (0 : ℝ) ≤ Cη := le_trans (norm_nonneg _) (hηb 0)
  set K : RidgeletParameterSpace m → ℂ := fun p =>
    T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ (1 : ℝ) : ℝ) : ℂ)⁻¹ with hK_def
  have hbd : ∀ p : RidgeletParameterSpace m,
      ‖K p‖ ≤ Cη * ‖T p * ((‖p.1‖ : ℝ) : ℂ)⁻¹‖ := by
    intro p
    rw [hK_def]
    simp only []
    rw [Real.rpow_one, norm_mul, norm_mul, norm_mul]
    calc ‖T p‖ * ‖η (inner ℝ p.1 x - p.2)‖ * ‖((‖p.1‖ : ℝ) : ℂ)⁻¹‖
        ≤ ‖T p‖ * Cη * ‖((‖p.1‖ : ℝ) : ℂ)⁻¹‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hηb _) (norm_nonneg _)) (norm_nonneg _)
      _ = Cη * (‖T p‖ * ‖((‖p.1‖ : ℝ) : ℂ)⁻¹‖) := by ring
  have hKaesm : AEStronglyMeasurable K (volume : Measure (RidgeletParameterSpace m)) := by
    refine AEStronglyMeasurable.mul (hTm.mul ?_) ?_
    · exact (hηc.comp ((Continuous.inner continuous_fst continuous_const).sub
        continuous_snd)).aestronglyMeasurable
    · exact ((measurable_fst.norm.pow measurable_const).complex_ofReal.inv).aestronglyMeasurable
  have hKint : Integrable K (volume : Measure (RidgeletParameterSpace m)) :=
    (hT.norm.const_mul Cη).mono' hKaesm (Filter.Eventually.of_forall hbd)
  have hAmeas : MeasurableSet {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} :=
    measurableSet_annulusParameter m ε δ
  calc ‖truncatedDualRidgeletTransform m 1 η T ε δ x‖
      = ‖∫ p in {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}, K p‖ := rfl
    _ ≤ ∫ p in {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}, ‖K p‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p in {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ},
          Cη * ‖T p * ((‖p.1‖ : ℝ) : ℂ)⁻¹‖ :=
        setIntegral_mono_on hKint.norm.integrableOn (hT.norm.const_mul Cη).integrableOn hAmeas
          (fun p _ => hbd p)
    _ ≤ ∫ p, Cη * ‖T p * ((‖p.1‖ : ℝ) : ℂ)⁻¹‖ :=
        setIntegral_le_integral (hT.norm.const_mul Cη)
          (Filter.Eventually.of_forall fun p => by positivity)
    _ = Cη * ∫ q, ‖T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹‖ := integral_const_mul _ _

/-- The truncated dual ridgelet transform of measurable data against a continuous activation is
almost-everywhere strongly measurable in the input variable. -/
theorem aestronglyMeasurable_truncatedDualRidgeletTransform (m : ℕ) {η : ℝ → ℂ}
    {T : RidgeletParameterSpace m → ℂ} {ε δ : ℝ}
    (hTm : AEStronglyMeasurable T (volume : Measure (RidgeletParameterSpace m)))
    (hηc : Continuous η) :
    AEStronglyMeasurable (truncatedDualRidgeletTransform m 1 η T ε δ)
      (volume : Measure (InputSpace m)) := by
  have hKaesm : AEStronglyMeasurable
      (fun z : InputSpace m × RidgeletParameterSpace m =>
        T z.2 * η (inner ℝ z.2.1 z.1 - z.2.2) * ((‖z.2.1‖ ^ (1 : ℝ) : ℝ) : ℂ)⁻¹)
      ((volume : Measure (InputSpace m)).prod
        ((volume : Measure (RidgeletParameterSpace m)).restrict
          {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ})) := by
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul hTm.restrict.comp_snd ?_) ?_
    · exact (hηc.comp ((Continuous.inner continuous_snd.fst continuous_fst).sub
        continuous_snd.snd)).aestronglyMeasurable
    · exact ((measurable_snd.fst.norm.pow measurable_const).complex_ofReal.inv).aestronglyMeasurable
  exact hKaesm.integral_prod_right'

/-! ## Truncated duality, the error bound and the vanishing tail -/

/-- **The truncated duality identity**: the pairing of the ridgelet transform of `f` against the
ridgelet transform of `g` over the scale annulus `ε ≤ ‖a‖ ≤ δ` is the pairing of the truncated
reconstruction of `f` against `g`. -/
theorem setIntegral_annulus_ridgeletTransform_mul_conj (m : ℕ) [NeZero m]
    {ψ η : ℝ → ℂ} {f g : InputSpace m → ℂ} {ε δ : ℝ} (hε : 0 < ε)
    (hf : Integrable f volume) (hψ : Integrable ψ volume) (hψc : Continuous ψ)
    (hg : Integrable g volume) (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C) :
    ∫ q in {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ},
        euclideanRidgeletTransform m 1 ψ f q *
          conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m
      = ∫ x, truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ x *
          conj (g x) := by
  classical
  set A : Set (RidgeletParameterSpace m) := {p | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} with hA_def
  have hAmeas : MeasurableSet A := by
    rw [hA_def]
    exact measurableSet_annulusParameter m ε δ
  set T : RidgeletParameterSpace m → ℂ :=
    Set.indicator A (euclideanRidgeletTransform m 1 ψ f) with hT_def
  have hT : Integrable (fun q : RidgeletParameterSpace m =>
      T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume :=
    integrable_weight_indicator_euclideanRidgeletTransform m hf hψ hψc hε
  have hpair := l1_dualRidgeletTransform_pairing m hg hηc hηb hT
  -- the dual transform of the truncated data is the truncated dual transform
  have hdual : euclideanDualRidgeletTransform m 1 η T
      = truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ := by
    funext x
    unfold euclideanDualRidgeletTransform truncatedDualRidgeletTransform
    rw [← integral_indicator hAmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hT_def]
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul, zero_mul]
  -- conjugate the duality identity and identify the truncated pairing
  have hconj := congrArg (starRingEnd ℂ) hpair
  rw [← integral_conj, ← integral_conj] at hconj
  calc ∫ q in A, euclideanRidgeletTransform m 1 ψ f q *
        conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m
      = ∫ q, conj (euclideanRidgeletTransform m 1 η g q * conj (T q))
          ∂ridgeletParameterMeasure m := by
        rw [← integral_indicator hAmeas]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [hT_def]
        by_cases hp : p ∈ A
        · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, map_mul, RCLike.conj_conj]
          ring
        · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, map_zero, map_mul, map_zero,
            mul_zero]
    _ = ∫ x, conj (g x * conj (euclideanDualRidgeletTransform m 1 η T x)) := hconj
    _ = ∫ x, truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ x *
          conj (g x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [map_mul, RCLike.conj_conj, hdual]
        ring

/-- **Reconstruction error bound in `L²`**: for normalized self-admissible `ψ` and `η` paired
with `K_{ψ,η} = 1`, the truncated reconstruction error is bounded by the energy of the ridgelet
transform outside the scale annulus. -/
theorem eLpNorm_truncatedDualRidgeletTransform_sub_le (m : ℕ) [NeZero m]
    {ψ η : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hψself : IsSelfAdmissible m ψ)
    (hKψ : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hηself : IsSelfAdmissible m η)
    (hKη : admissibilityConstant m η (angularFourier1D η) = 1)
    (hK : admissibilityConstant m ψ (angularFourier1D η) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    {ε δ : ℝ} (hε : 0 < ε) :
    eLpNorm (fun x => truncatedDualRidgeletTransform m 1 η
        (euclideanRidgeletTransform m 1 ψ f) ε δ x - f x) 2 volume
      ≤ ENNReal.ofReal (Real.sqrt (∫ q in {p : RidgeletParameterSpace m |
          ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}ᶜ,
          ‖euclideanRidgeletTransform m 1 ψ f q‖ ^ 2 ∂ridgeletParameterMeasure m)) := by
  classical
  obtain ⟨Cψ, hψC⟩ := hψb
  obtain ⟨Cη, hηC⟩ := hηb
  have hψint : Integrable ψ volume := hψself.1
  have hηint : Integrable η volume := hηself.1
  set A : Set (RidgeletParameterSpace m) := {p | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} with hA_def
  have hAmeas : MeasurableSet A := by
    rw [hA_def]
    exact measurableSet_annulusParameter m ε δ
  set R : RidgeletParameterSpace m → ℂ := euclideanRidgeletTransform m 1 ψ f with hR_def
  set I : InputSpace m → ℂ := truncatedDualRidgeletTransform m 1 η R ε δ with hI_def
  set M : ℝ := Real.sqrt (∫ q in Aᶜ, ‖R q‖ ^ 2 ∂ridgeletParameterMeasure m) with hM_def
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hRmem : MemLp R 2 (ridgeletParameterMeasure m) :=
    memLp_two_euclideanRidgeletTransform m hψself hKψ hψc ⟨Cψ, hψC⟩ hf1 hf2
  -- the truncated transform sees only the indicator data
  have hTaesm : AEStronglyMeasurable (Set.indicator A R)
      (volume : Measure (RidgeletParameterSpace m)) :=
    (aestronglyMeasurable_euclideanRidgeletTransform m 1 hf1 hψc).indicator hAmeas
  have hTint : Integrable (fun q : RidgeletParameterSpace m =>
      Set.indicator A R q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume :=
    integrable_weight_indicator_euclideanRidgeletTransform m hf1 hψint hψc hε
  have hIeq : I = truncatedDualRidgeletTransform m 1 η (Set.indicator A R) ε δ := by
    funext x
    rw [hI_def]
    unfold truncatedDualRidgeletTransform
    refine setIntegral_congr_fun hAmeas fun p hp => ?_
    rw [Set.indicator_of_mem hp]
  -- boundedness and measurability of the truncated reconstruction
  set CI : ℝ := Cη * ∫ q, ‖Set.indicator A R q * ((‖q.1‖ : ℝ) : ℂ)⁻¹‖ with hCI_def
  have hIbd : ∀ x, ‖I x‖ ≤ CI := by
    intro x
    rw [hIeq, hCI_def]
    exact norm_truncatedDualRidgeletTransform_le m hTaesm hTint hηc hηC x
  have hIaesm : AEStronglyMeasurable I (volume : Measure (InputSpace m)) := by
    rw [hIeq]
    exact aestronglyMeasurable_truncatedDualRidgeletTransform m hTaesm hηc
  set h : InputSpace m → ℂ := fun x => I x - f x with hh_def
  -- the duality bound against square-integrable test functions
  have hweak : ∀ g : InputSpace m → ℂ, Integrable g volume → MemLp g 2 volume →
      ‖∫ x, h x * conj (g x)‖ ≤ M * Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
    intro g hg1 hg2
    set S : RidgeletParameterSpace m → ℂ := euclideanRidgeletTransform m 1 η g with hS_def
    have hSmem : MemLp S 2 (ridgeletParameterMeasure m) :=
      memLp_two_euclideanRidgeletTransform m hηself hKη hηc ⟨Cη, hηC⟩ hg1 hg2
    have hprod : Integrable (fun q => R q * conj (S q)) (ridgeletParameterMeasure m) :=
      hRmem.integrable_mul_conj hSmem
    have hpars : (∫ q, R q * conj (S q) ∂ridgeletParameterMeasure m) = ∫ x, f x * conj (g x) :=
      l1_parseval_relation m hψself hKψ hηself hKη hK hψc ⟨Cψ, hψC⟩ hηc ⟨Cη, hηC⟩
        hf1 hf2 hg1 hg2
    have htrunc : (∫ q in A, R q * conj (S q) ∂ridgeletParameterMeasure m)
        = ∫ x, I x * conj (g x) :=
      setIntegral_annulus_ridgeletTransform_mul_conj m hε hf1 hψint hψc hg1 hηc ⟨Cη, hηC⟩
    have hsplit : (∫ q in A, R q * conj (S q) ∂ridgeletParameterMeasure m)
        + ∫ q in Aᶜ, R q * conj (S q) ∂ridgeletParameterMeasure m
        = ∫ q, R q * conj (S q) ∂ridgeletParameterMeasure m :=
      integral_add_compl hAmeas hprod
    have hfg : Integrable (fun x => f x * conj (g x)) volume := hf2.integrable_mul_conj hg2
    have hIg : Integrable (fun x => I x * conj (g x)) volume := by
      refine (hg1.norm.const_mul CI).mono'
        (hIaesm.mul (RCLike.continuous_conj.comp_aestronglyMeasurable hg1.aestronglyMeasurable))
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_right (hIbd x) (norm_nonneg _)
    have herr : (∫ x, h x * conj (g x))
        = -∫ q in Aᶜ, R q * conj (S q) ∂ridgeletParameterMeasure m := by
      have hstep : (∫ x, h x * conj (g x))
          = (∫ x, I x * conj (g x)) - ∫ x, f x * conj (g x) := by
        rw [← integral_sub hIg hfg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [hh_def]
        simp only []
        ring
      rw [hstep, ← htrunc, ← hpars, ← hsplit]
      ring
    -- Cauchy--Schwarz on the tail, then Plancherel for the test function
    have hcs := MemLp.norm_integral_mul_conj_le (hRmem.restrict Aᶜ) (hSmem.restrict Aᶜ)
    have hSle : (∫ q in Aᶜ, ‖S q‖ ^ 2 ∂ridgeletParameterMeasure m)
        ≤ ∫ q, ‖S q‖ ^ 2 ∂ridgeletParameterMeasure m :=
      setIntegral_le_integral hSmem.integrable_norm_sq
        (Filter.Eventually.of_forall fun q => by positivity)
    have hplan : (∫ q, ‖S q‖ ^ 2 ∂ridgeletParameterMeasure m) = ∫ x, ‖g x‖ ^ 2 :=
      l1_plancherel_identity m hηself hKη hηc ⟨Cη, hηC⟩ hg1 hg2
    calc ‖∫ x, h x * conj (g x)‖
        = ‖∫ q in Aᶜ, R q * conj (S q) ∂ridgeletParameterMeasure m‖ := by
          rw [herr, norm_neg]
      _ ≤ M * Real.sqrt (∫ q in Aᶜ, ‖S q‖ ^ 2 ∂ridgeletParameterMeasure m) := hcs
      _ ≤ M * Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hM0
          exact hSle.trans_eq hplan
  -- the exhausting sequence of balls
  have hballmem : ∀ n : ℕ,
      Integrable (Set.indicator (Metric.closedBall (0 : InputSpace m) n) h) volume ∧
      MemLp (Set.indicator (Metric.closedBall (0 : InputSpace m) n) h) 2 volume := by
    intro n
    have hbm : MeasurableSet (Metric.closedBall (0 : InputSpace m) n) :=
      measurableSet_closedBall
    have hIon : IntegrableOn I (Metric.closedBall (0 : InputSpace m) n) volume := by
      refine Integrable.mono' (g := fun _ => CI) ?_ hIaesm.restrict
        (Filter.Eventually.of_forall fun x => hIbd x)
      exact integrableOn_const (measure_closedBall_lt_top).ne
    have hIind : Integrable (Set.indicator (Metric.closedBall (0 : InputSpace m) n) I) volume :=
      hIon.integrable_indicator hbm
    have hIindmem : MemLp (Set.indicator (Metric.closedBall (0 : InputSpace m) n) I) 2 volume := by
      refine memLp_two_of_integrable_of_bound hIind (M := CI) fun x => ?_
      by_cases hx : x ∈ Metric.closedBall (0 : InputSpace m) n
      · rw [Set.indicator_of_mem hx]
        exact hIbd x
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact le_trans (norm_nonneg (I x)) (hIbd x)
    have hsub : ∀ x, Set.indicator (Metric.closedBall (0 : InputSpace m) n) h x
        = Set.indicator (Metric.closedBall (0 : InputSpace m) n) I x
          - Set.indicator (Metric.closedBall (0 : InputSpace m) n) f x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : InputSpace m) n
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
          sub_zero]
    refine ⟨?_, ?_⟩
    · refine (hIind.sub (hf1.indicator hbm)).congr (Filter.Eventually.of_forall fun x => ?_)
      exact (hsub x).symm
    · refine MemLp.ae_eq (Filter.Eventually.of_forall fun x => (hsub x).symm)
        (hIindmem.sub (hf2.indicator hbm))
  refine eLpNorm_two_le_of_forall_indicator_pairing_le hM0
    (hIaesm.sub hf2.aestronglyMeasurable) (fun n => measurableSet_closedBall) ?_ ?_
    (fun n => (hballmem n).2) ?_
  · intro i j hij
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  · intro x
    refine ⟨⌈‖x‖⌉₊, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil _
  · intro n
    exact hweak _ (hballmem n).1 (hballmem n).2

/-- The energy of a square-integrable parameter function outside the scale annulus tends to zero
along the truncation filter: the annulus exhausts the parameter space up to the null set of
vanishing weights. -/
theorem tendsto_setIntegral_compl_annulus_norm_sq (m : ℕ) [NeZero m]
    {G : RidgeletParameterSpace m → ℂ}
    (hG : Integrable (fun p => ‖G p‖ ^ 2) (ridgeletParameterMeasure m)) :
    Filter.Tendsto (fun q : ℝ × ℝ =>
        ∫ p in {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ,
          ‖G p‖ ^ 2 ∂ridgeletParameterMeasure m)
      ridgeletTruncationFilter (𝓝 0) := by
  classical
  haveI : Filter.IsCountablyGenerated ridgeletTruncationFilter := by
    unfold ridgeletTruncationFilter
    infer_instance
  -- almost every parameter has a nonzero weight component
  have haeμ : ∀ᵐ p : RidgeletParameterSpace m ∂ridgeletParameterMeasure m, p.1 ≠ 0 := by
    have hvol : ∀ᵐ p : RidgeletParameterSpace m ∂volume, p.1 ≠ 0 := by
      rw [ae_iff]
      have hset : {p : RidgeletParameterSpace m | ¬ p.1 ≠ 0}
          = ({0} : Set (InputSpace m)) ×ˢ (Set.univ : Set ℝ) := by
        ext p
        simp [Set.mem_prod]
      rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
    unfold ridgeletParameterMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le hvol
  have hind : ∀ q : ℝ × ℝ,
      (∫ p, Set.indicator {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ
          (fun p => ‖G p‖ ^ 2) p ∂ridgeletParameterMeasure m)
        = ∫ p in {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ,
            ‖G p‖ ^ 2 ∂ridgeletParameterMeasure m := fun q =>
    integral_indicator (measurableSet_annulusParameter m q.1 q.2).compl
  refine Filter.Tendsto.congr hind ?_
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := ridgeletParameterMeasure m) (l := ridgeletTruncationFilter)
    (F := fun q : ℝ × ℝ => Set.indicator
      {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ (fun p => ‖G p‖ ^ 2))
    (f := fun _ : RidgeletParameterSpace m => (0 : ℝ))
    (bound := fun p => ‖G p‖ ^ 2) ?_ ?_ hG ?_
  · simpa using hlim
  · refine Filter.Eventually.of_forall fun q => ?_
    exact hG.aestronglyMeasurable.indicator (measurableSet_annulusParameter m q.1 q.2).compl
  · refine Filter.Eventually.of_forall fun q => Filter.Eventually.of_forall fun p => ?_
    refine le_trans (norm_indicator_le_norm_self _ _) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · filter_upwards [haeμ] with p hp0
    have hp : (0 : ℝ) < ‖p.1‖ := norm_pos_iff.mpr hp0
    have h1 : ∀ᶠ ε' in 𝓝[>] (0 : ℝ), ε' < ‖p.1‖ :=
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const hp
    have h2 : ∀ᶠ δ' in (Filter.atTop : Filter ℝ), ‖p.1‖ ≤ δ' := Filter.eventually_ge_atTop _
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    unfold ridgeletTruncationFilter
    refine Filter.eventually_of_mem (Filter.prod_mem_prod h1 h2) ?_
    intro q hq
    have hmem : p ∈ {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2} :=
      ⟨le_of_lt hq.1, hq.2⟩
    exact (Set.indicator_of_notMem (by simpa using hmem) _).symm

/-- Theorem 5.11 (`thm:formula.L2`), the reconstruction formula in `L²`: for normalized
self-admissible `ψ` and `η` with cross normalization `K_{ψ,η} = 1` and `f ∈ L¹ ∩ L²(ℝ^m)`, the
truncated reconstruction converges to `f` in `L²(ℝ^m)`. Together with
`l1_ridgeletTransform_L2_extension` this expresses the compatibility of the L1 and L2
reconstructions on `L¹ ∩ L²`.

The proof is the manuscript's duality argument made quantitative:
`eLpNorm_truncatedDualRidgeletTransform_sub_le` bounds the error norm by the ridgelet energy
outside the scale annulus, and `tendsto_setIntegral_compl_annulus_norm_sq` sends that energy to
zero along the truncation filter (the annulus exhausts `𝕐^{m+1}` up to the null set of vanishing
weights).

**Amendment (author-style decision 2026-07-25).** The manuscript states the theorem for an
admissibly decomposable pair and then opens its proof with "assume without loss of generality
that `(ψ, ψ)` and `(η, η)` are self-admissible respectively". That reduction is what carries the
decomposability hypothesis, and it needs the equivalence-invariance of the composite operator
`R†_η R_ψ` (which depends on the pair only through `conj (ψ~) ⋆ η`) — a distributional
statement about equivalent pairs that the function-level development does not have. The
self-admissibility of both members is therefore taken as a hypothesis, exactly as in the
amended Parseval relation `l1_parseval_relation` on which this proof rests, together with the
diagonal normalizations `K_{ψ,ψ} = K_{η,η} = 1`. The hypothesis `f ∈ L¹ ∩ L²(ℝ^m)` (rather than
`f ∈ L²`) is the one already present in the staged statement: it is what makes the ridgelet
transform of `f` a classical integral; the general `f ∈ L²` case follows from the bounded
extension `l1_ridgeletTransform_L2_extension`. -/
theorem l1_reconstruction_formula_L2 (m : ℕ) [NeZero m]
    {ψ η : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hψself : IsSelfAdmissible m ψ)
    (hKψ : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hηself : IsSelfAdmissible m η)
    (hKη : admissibilityConstant m η (angularFourier1D η) = 1)
    (hK : admissibilityConstant m ψ (angularFourier1D η) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Filter.Tendsto
      (fun q : ℝ × ℝ =>
        eLpNorm
          (fun x =>
            truncatedDualRidgeletTransform m 1 η
              (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x - f x) 2 volume)
      ridgeletTruncationFilter (𝓝 0) := by
  obtain ⟨Cψ, hψC⟩ := hψb
  obtain ⟨Cη, hηC⟩ := hηb
  have hRmem : MemLp (euclideanRidgeletTransform m 1 ψ f) 2 (ridgeletParameterMeasure m) :=
    memLp_two_euclideanRidgeletTransform m hψself hKψ hψc ⟨Cψ, hψC⟩ hf1 hf2
  have htail := tendsto_setIntegral_compl_annulus_norm_sq m hRmem.integrable_norm_sq
  have htail2 : Filter.Tendsto (fun q : ℝ × ℝ => ENNReal.ofReal (Real.sqrt
      (∫ p in {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ,
        ‖euclideanRidgeletTransform m 1 ψ f p‖ ^ 2 ∂ridgeletParameterMeasure m)))
      ridgeletTruncationFilter (𝓝 0) := by
    have h1 : Filter.Tendsto (fun q : ℝ × ℝ => Real.sqrt
        (∫ p in {p : RidgeletParameterSpace m | q.1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ q.2}ᶜ,
          ‖euclideanRidgeletTransform m 1 ψ f p‖ ^ 2 ∂ridgeletParameterMeasure m))
        ridgeletTruncationFilter (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp htail
      simpa [Function.comp_def] using h
    have h := ENNReal.tendsto_ofReal h1
    simpa using h
  have hpos : ∀ᶠ q : ℝ × ℝ in ridgeletTruncationFilter, 0 < q.1 := by
    unfold ridgeletTruncationFilter
    refine Filter.eventually_of_mem
      (Filter.prod_mem_prod self_mem_nhdsWithin Filter.univ_mem) ?_
    intro q hq
    exact hq.1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail2
    (Filter.Eventually.of_forall fun q => zero_le) ?_
  filter_upwards [hpos] with q hq
  exact eLpNorm_truncatedDualRidgeletTransform_sub_le m hψself hKψ hηself hKη hK hψc ⟨Cψ, hψC⟩
    hηc ⟨Cη, hηC⟩ hf1 hf2 hq

end LeanRidgelet
