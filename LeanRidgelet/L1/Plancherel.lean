/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.FourierExpression
public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.ToMathlib.FourierPlancherel
public import LeanRidgelet.ToMathlib.LpIntegrableDense
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# L1 theory: Plancherel, Parseval and the bounded `L²` extension

## Main results

* `LeanRidgelet.lintegral_enorm_euclideanRidgeletTransform_sq`,
  `LeanRidgelet.memLp_two_euclideanRidgeletTransform`,
  `LeanRidgelet.l1_plancherel_identity`: the Plancherel half of `thm:parseval`, for a
  self-admissible `ψ` with `K_{ψ,ψ} = 1`. The proof is a direct Fourier computation that does
  not pass through the reconstruction formula: `eq:fstridge`, the fibrewise `L¹ ∩ L²`
  Plancherel identity, the dilation change of variables in the weight, and the normalization.
* `LeanRidgelet.l1_parseval_relation`: the polarized companion, `thm:parseval`.
* `LeanRidgelet.l1_ridgeletTransform_L2_extension`: `thm:L2`, the unique bounded — indeed
  isometric — extension of the ridgelet transform to `L²(ℝ^m)`, by dense extension along
  `L¹ ∩ L²`.

## Standing hypotheses

Throughout this file both members of the pair are integrable (through self-admissibility),
continuous and bounded. At function level the `L²` layer therefore speaks about a pair of
*ridgelet functions*, not about an unbounded activation: the ReLU, the truncated powers, the
unit step, the sigmoid and Dirac's `δ` all fall outside it. The article has no such restriction
because it pairs in `𝒮 × 𝒮₀'`.

The restriction is an artefact of the function-level Euclidean formulation rather than a gap in
the project. A tempered distribution lies in a weighted Sobolev space, so an unbounded
activation enters the companion L2 theory through its coordinate in `ActivationSpace s t` — the
ReLU as `LeanRidgelet.reluActivation` for `t > 3/2` — and there the corresponding statements are
proved, in the sharper form of an exact operator identity rather than a truncation limit:
`LeanRidgelet.norm_adjoint_unitarySynthesis_sq` (`‖S†f‖² = c_L‖f‖²`, the analogue of `thm:L2`),
`LeanRidgelet.unitarySynthesis_comp_adjoint` (`S S† = c_L • id`, the analogue of `thm:parseval`)
and `LeanRidgelet.normalizedReLURightInverse_rightInverse` (the analogue of `thm:formula.L2`).
Connecting the two formulations is plan item M7 (R4); the implication does not go the easy way,
since the `L¹` statements are the finer ones about convergence of truncated Euclidean integrals.
Universality with an unbounded activation is in any case reached here through the `L¹` route
(`LeanRidgelet.l1_relu_network_universal_approximation`).

## Deviations from the article

`l1_parseval_relation` is amended. The article asserts the relation for `(ψ, η) ∈ 𝒮 × 𝒮₀'`,
"immediate by duality"; at function level the pairing on parameter space must converge
absolutely, which requires both transforms to lie in `L²(𝕐^{m+1})`. This holds when both
members are self-admissible — by Cauchy--Schwarz and AM--GM this also subsumes absolute
convergence of the cross admissibility integral — so self-admissibility of both members, with
the diagonal normalizations `K_{ψ,ψ} = K_{η,η} = 1`, is taken as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Strong measurability on parameter space -/

/-- The ridgelet transform of an integrable function against a continuous ridgelet function is
strongly measurable on the parameter space (with Lebesgue measure). -/
theorem aestronglyMeasurable_euclideanRidgeletTransform (m : ℕ) (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) :
    AEStronglyMeasurable (euclideanRidgeletTransform m s ψ f)
      (volume : Measure (RidgeletParameterSpace m)) := by
  have h1 : AEStronglyMeasurable
      (fun qx : RidgeletParameterSpace m × InputSpace m => f qx.2)
      ((volume : Measure (RidgeletParameterSpace m)).prod volume) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h2 : Measurable (fun qx : RidgeletParameterSpace m × InputSpace m =>
      conj (ψ (inner ℝ qx.1.1 qx.2 - qx.1.2)) * ((‖qx.1.1‖ ^ s : ℝ) : ℂ)) := by
    have hip : Continuous (fun qx : RidgeletParameterSpace m × InputSpace m =>
        inner ℝ qx.1.1 qx.2 - qx.1.2) :=
      (Continuous.inner continuous_fst.fst continuous_snd).sub continuous_fst.snd
    have hψm : Measurable (fun qx : RidgeletParameterSpace m × InputSpace m =>
        conj (ψ (inner ℝ qx.1.1 qx.2 - qx.1.2))) :=
      (RCLike.continuous_conj.comp (hψc.comp hip)).measurable
    have hnm : Measurable (fun qx : RidgeletParameterSpace m × InputSpace m =>
        ((‖qx.1.1‖ ^ s : ℝ) : ℂ)) :=
      (measurable_fst.fst.norm.pow measurable_const).complex_ofReal
    exact hψm.mul hnm
  have hker := (h1.mul h2.aestronglyMeasurable).integral_prod_right'
  refine hker.congr (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  unfold euclideanRidgeletTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

/-- The ridgelet transform of an integrable function against a continuous ridgelet function is
strongly measurable with respect to the weighted parameter measure `‖a‖⁻² da db`. -/
theorem aestronglyMeasurable_euclideanRidgeletTransform_parameterMeasure (m : ℕ) (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) :
    AEStronglyMeasurable (euclideanRidgeletTransform m s ψ f) (ridgeletParameterMeasure m) := by
  unfold ridgeletParameterMeasure
  exact (aestronglyMeasurable_euclideanRidgeletTransform m s hf hψc).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-! ## Plancherel and Parseval (`thm:parseval`) -/

/-- Plancherel's identity for the ridgelet transform (`thm:parseval`), `lintegral` form: for a
self-admissible `ψ` normalized by `K_{ψ,ψ} = 1` and `f ∈ L¹ ∩ L²(ℝ^m)`,
`∫⁻ ‖R_ψ f‖ₑ² d(‖a‖⁻² da db) = ∫⁻ ‖f‖ₑ²`. This form drives the square-integrability of the
transform and its bounded `L²` extension `l1_ridgeletTransform_L2_extension`. -/
theorem lintegral_enorm_euclideanRidgeletTransform_sq (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ q, ‖euclideanRidgeletTransform m 1 ψ f q‖ₑ ^ 2 ∂ridgeletParameterMeasure m =
      ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨C, hψC⟩ := hψb
  obtain ⟨hψint, hFdata, hKint, hKne⟩ := hself
  have hπpos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- continuity of the two Fourier factors
  have hFhatc : Continuous (Fourier.angularFourierIntegralInner f) :=
    Fourier.continuous_angularFourierIntegralInner hf1
  have hΨhatc : Continuous (angularFourier1D ψ) :=
    Fourier.continuous_angularFourierIntegralInner hψint
  -- measurability of the ridgelet transform on the parameter space
  have hRmeas : AEStronglyMeasurable (euclideanRidgeletTransform m 1 ψ f)
      (volume : Measure (RidgeletParameterSpace m)) :=
    aestronglyMeasurable_euclideanRidgeletTransform m 1 hf1 hψc
  -- the joint spectral density
  set G : InputSpace m → ℝ → ℝ≥0∞ := fun a ζ =>
    ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ₑ ^ 2 *
      ‖angularFourier1D ψ ζ‖ₑ ^ 2 with hG_def
  have hGmeas : Measurable (Function.uncurry G) := by
    have h1 : Measurable fun p : InputSpace m × ℝ =>
        ‖Fourier.angularFourierIntegralInner f (p.2 • p.1)‖ₑ ^ 2 :=
      ((hFhatc.comp (continuous_snd.smul continuous_fst)).enorm.measurable).pow_const 2
    have h2 : Measurable fun p : InputSpace m × ℝ =>
        ‖angularFourier1D ψ p.2‖ₑ ^ 2 :=
      ((hΨhatc.comp continuous_snd).enorm.measurable).pow_const 2
    exact h1.mul h2
  -- the fiberwise Plancherel identity through `eq:fstridge`
  have hfiber : ∀ a : InputSpace m,
      ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ b, ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2
        = ∫⁻ ζ, G a ζ * ENNReal.ofReal ‖a‖ ^ 2 := by
    intro a
    have hL1a := integrable_euclideanRidgeletTransform_bias m 1 hf1 hψint a
    have hL2a := memLp_two_euclideanRidgeletTransform_bias m 1 hf1 hψint hψc hψC a
    have hPl := Fourier.lintegral_enorm_angularFourierIntegralInner_sq hL1a hL2a
    rw [Module.finrank_self, pow_one] at hPl
    rw [← hPl]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    have hfac := angularFourier1D_euclideanRidgeletTransform m 1 hf1 hψint a ζ
    have hcoe : Fourier.angularFourierIntegralInner
        (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ
        = angularFourier1D (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ := rfl
    dsimp only
    rw [hG_def, hcoe, hfac, enorm_mul, enorm_mul, mul_pow, mul_pow]
    congr 1
    · congr 2
      rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]
    · congr 1
      rw [← ofReal_norm]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg (norm_nonneg _)]
  -- almost-everywhere nonvanishing of the weight and of the frequency
  have hae0 : ∀ᵐ a : InputSpace m ∂volume, a ≠ 0 := by
    rw [ae_iff]
    have hset : {a : InputSpace m | ¬ a ≠ 0} = {0} := by
      ext a
      simp
    rw [hset]
    exact measure_singleton 0
  have haeζ : ∀ᵐ ζ : ℝ ∂volume, ζ ≠ 0 := by
    rw [ae_iff]
    have hset : {ζ : ℝ | ¬ ζ ≠ 0} = {0} := by
      ext ζ
      simp
    rw [hset]
    exact measure_singleton 0
  have h2π0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr hπpos).ne'
  have h2πtop : ENNReal.ofReal (2 * Real.pi) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Step 1: unfold the weighted measure and apply Tonelli
  have hstep1 : ∫⁻ q, ‖euclideanRidgeletTransform m 1 ψ f q‖ₑ ^ 2 ∂ridgeletParameterMeasure m
      = ∫⁻ a : InputSpace m, ∫⁻ b : ℝ,
          ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) *
            ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2 := by
    have hdens : Measurable fun q : RidgeletParameterSpace m =>
        ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.norm.pow_const 2).inv)
    have hg : AEMeasurable (fun q : RidgeletParameterSpace m =>
        ‖euclideanRidgeletTransform m 1 ψ f q‖ₑ ^ 2) volume :=
      hRmeas.enorm.pow_const 2
    unfold ridgeletParameterMeasure
    rw [lintegral_withDensity_eq_lintegral_mul₀ hdens.aemeasurable hg]
    have hprodmeas : AEMeasurable
        ((fun q : RidgeletParameterSpace m => ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹)) *
          fun q => ‖euclideanRidgeletTransform m 1 ψ f q‖ₑ ^ 2) volume :=
      hdens.aemeasurable.mul hg
    rw [Measure.volume_eq_prod] at hprodmeas ⊢
    rw [lintegral_prod _ hprodmeas]
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [Pi.mul_apply]
  -- Step 2: fiberwise evaluation, cancelling the weight
  have hstep2 : ∀ᵐ a : InputSpace m ∂volume,
      (∫⁻ b : ℝ, ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) *
          ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2)
        = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ, G a ζ := by
    filter_upwards [hae0] with a ha0
    have hXmeas : AEMeasurable (fun b : ℝ =>
        ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2) volume :=
      ((integrable_euclideanRidgeletTransform_bias m 1 hf1 hψint
        a).aestronglyMeasurable.enorm.pow_const 2)
    rw [lintegral_const_mul'' _ hXmeas]
    have hGa : AEMeasurable (fun ζ : ℝ => G a ζ) volume := by
      have h1 : Measurable fun ζ : ℝ =>
          ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ₑ ^ 2 :=
        ((hFhatc.comp (continuous_id.smul continuous_const)).enorm.measurable).pow_const 2
      have h2 : Measurable fun ζ : ℝ => ‖angularFourier1D ψ ζ‖ₑ ^ 2 :=
        (hΨhatc.enorm.measurable).pow_const 2
      exact (h1.mul h2).aemeasurable
    have hA_eq : (∫⁻ ζ : ℝ, G a ζ * ENNReal.ofReal ‖a‖ ^ 2)
        = (∫⁻ ζ : ℝ, G a ζ) * ENNReal.ofReal ‖a‖ ^ 2 :=
      lintegral_mul_const'' _ hGa
    have hB : (∫⁻ b : ℝ, ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2)
        = (ENNReal.ofReal (2 * Real.pi))⁻¹ *
            ((∫⁻ ζ : ℝ, G a ζ) * ENNReal.ofReal ‖a‖ ^ 2) := by
      rw [← hA_eq, ← hfiber a, ← mul_assoc, ENNReal.inv_mul_cancel h2π0 h2πtop, one_mul]
    rw [hB]
    have hna : (‖a‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha0)
    have hcancel : ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ENNReal.ofReal ‖a‖ ^ 2 = 1 := by
      rw [← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)), inv_mul_cancel₀ hna,
        ENNReal.ofReal_one]
    calc ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) *
        ((ENNReal.ofReal (2 * Real.pi))⁻¹ * ((∫⁻ ζ : ℝ, G a ζ) * ENNReal.ofReal ‖a‖ ^ 2))
        = (ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ENNReal.ofReal ‖a‖ ^ 2) *
            ((ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ, G a ζ) := by ring
      _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ, G a ζ := by
          rw [hcancel, one_mul]
  -- Step 3: swap the parameter and frequency integrals
  have hswap : ∫⁻ a : InputSpace m, ∫⁻ ζ : ℝ, G a ζ
      = ∫⁻ ζ : ℝ, ∫⁻ a : InputSpace m, G a ζ :=
    lintegral_lintegral_swap hGmeas.aemeasurable
  -- Step 4: dilation in the weight variable and the `m`-dimensional Plancherel identity
  have hstep4 : ∀ᵐ ζ : ℝ ∂volume,
      (∫⁻ a : InputSpace m, G a ζ)
        = (ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2) *
            (ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
    filter_upwards [haeζ] with ζ hζ0
    have hFm : Measurable fun w : InputSpace m =>
        ‖Fourier.angularFourierIntegralInner f w‖ₑ ^ 2 :=
      (hFhatc.enorm.measurable).pow_const 2
    have hFam : AEMeasurable (fun a : InputSpace m =>
        ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ₑ ^ 2) volume :=
      (hFm.comp (measurable_const_smul ζ)).aemeasurable
    have hdila : (∫⁻ a : InputSpace m,
        ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ₑ ^ 2)
        = ENNReal.ofReal |(ζ ^ Module.finrank ℝ (InputSpace m))⁻¹| *
            ∫⁻ w, ‖Fourier.angularFourierIntegralInner f w‖ₑ ^ 2 := by
      rw [← lintegral_map hFm (measurable_const_smul ζ),
        Measure.map_addHaar_smul (volume : Measure (InputSpace m)) hζ0,
        lintegral_smul_measure, smul_eq_mul]
    calc ∫⁻ a : InputSpace m, G a ζ
        = (∫⁻ a : InputSpace m,
            ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ₑ ^ 2) *
              ‖angularFourier1D ψ ζ‖ₑ ^ 2 := by
          rw [hG_def]
          exact lintegral_mul_const'' _ hFam
      _ = (ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2) *
            (ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
          rw [hdila, Fourier.lintegral_enorm_angularFourierIntegralInner_sq hf1 hf2]
          simp only [finrank_euclideanSpace, Fintype.card_fin]
          ring
  -- Step 5: evaluate the frequency integral through the admissibility constant
  have hpt : ∀ ζ : ℝ, conj (angularFourier1D ψ ζ) * angularFourier1D ψ ζ /
      ((|ζ| ^ m : ℝ) : ℂ)
      = ((‖angularFourier1D ψ ζ‖ ^ 2 * (|ζ| ^ m)⁻¹ : ℝ) : ℂ) := by
    intro ζ
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_div, Complex.normSq_eq_norm_sq,
      div_eq_mul_inv]
  set g : ℝ → ℝ := fun ζ => ‖angularFourier1D ψ ζ‖ ^ 2 * (|ζ| ^ m)⁻¹ with hg_def
  have hcastKint : IntegrableOn (fun ζ : ℝ => ((g ζ : ℝ) : ℂ)) {(0 : ℝ)}ᶜ volume := by
    refine hKint.congr_fun ?_ (measurableSet_singleton _).compl
    intro ζ _
    exact hpt ζ
  have hg_int : IntegrableOn g {(0 : ℝ)}ᶜ volume := by
    have h := hcastKint.re
    refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp
  have hKI : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * angularFourier1D ψ ζ /
      ((|ζ| ^ m : ℝ) : ℂ)) = (((∫ ζ in {(0 : ℝ)}ᶜ, g ζ) : ℝ) : ℂ) := by
    have h1 : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * angularFourier1D ψ ζ /
        ((|ζ| ^ m : ℝ) : ℂ)) = ∫ ζ in {(0 : ℝ)}ᶜ, ((g ζ : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ζ => hpt ζ)
    rw [h1]
    norm_cast
  have hpow0 : ((2 * Real.pi) ^ (m - 1) : ℝ) ≠ 0 := by positivity
  have hgval : (∫ ζ in {(0 : ℝ)}ᶜ, g ζ) = (((2 * Real.pi) ^ (m - 1))⁻¹ : ℝ) := by
    have h1 := hK
    rw [admissibilityConstant, hKI] at h1
    have h2 : (2 * Real.pi) ^ (m - 1) * (∫ ζ in {(0 : ℝ)}ᶜ, g ζ) = 1 := by
      exact_mod_cast h1
    have h3 : (∫ ζ in {(0 : ℝ)}ᶜ, g ζ)
        = ((2 * Real.pi) ^ (m - 1))⁻¹ *
          ((2 * Real.pi) ^ (m - 1) * ∫ ζ in {(0 : ℝ)}ᶜ, g ζ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpow0, one_mul]
    rw [h3, h2, mul_one]
  have hres : (volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ = volume := by
    have h0 : (volume : Measure ℝ) ({(0 : ℝ)} : Set ℝ) = 0 := measure_singleton 0
    have hcompl : ({(0 : ℝ)}ᶜ : Set ℝ) =ᵐ[(volume : Measure ℝ)] (Set.univ : Set ℝ) := by
      rw [ae_eq_univ, compl_compl]
      exact h0
    rw [Measure.restrict_congr_set hcompl, Measure.restrict_univ]
  have hgnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ] g :=
    Filter.Eventually.of_forall fun ζ => by positivity
  have hJ : (∫⁻ ζ : ℝ, ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2)
      = ENNReal.ofReal (((2 * Real.pi) ^ (m - 1))⁻¹) := by
    have h1 : (∫⁻ ζ : ℝ, ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2)
        = ∫⁻ ζ in {(0 : ℝ)}ᶜ, ENNReal.ofReal (g ζ) := by
      rw [hres]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [hg_def]
      dsimp only
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
        abs_inv, abs_pow]
      ring
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hg_int hgnn, hgval]
  -- assemble
  have hζmeas : AEMeasurable (fun ζ : ℝ =>
      ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2) volume := by
    have h0 : Measurable fun ζ : ℝ => |(ζ ^ m)⁻¹| := by fun_prop
    have h1 : Measurable fun ζ : ℝ => ENNReal.ofReal |(ζ ^ m)⁻¹| :=
      ENNReal.measurable_ofReal.comp h0
    have h2 : Measurable fun ζ : ℝ => ‖angularFourier1D ψ ζ‖ₑ ^ 2 :=
      (hΨhatc.enorm.measurable).pow_const 2
    exact (h1.mul h2).aemeasurable
  calc ∫⁻ q, ‖euclideanRidgeletTransform m 1 ψ f q‖ₑ ^ 2 ∂ridgeletParameterMeasure m
      = ∫⁻ a : InputSpace m, ∫⁻ b : ℝ, ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) *
          ‖euclideanRidgeletTransform m 1 ψ f (a, b)‖ₑ ^ 2 := hstep1
    _ = ∫⁻ a : InputSpace m, (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ, G a ζ :=
        lintegral_congr_ae hstep2
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ a : InputSpace m, ∫⁻ ζ : ℝ, G a ζ :=
        lintegral_const_mul'' _ hGmeas.lintegral_prod_right'.aemeasurable
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ, ∫⁻ a : InputSpace m, G a ζ := by
        rw [hswap]
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ ζ : ℝ,
          (ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) *
            (ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2) := by
        refine congrArg (fun t => (ENNReal.ofReal (2 * Real.pi))⁻¹ * t) ?_
        refine lintegral_congr_ae (hstep4.mono fun ζ hζ => ?_)
        dsimp only
        rw [hζ]
        ring
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ((ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) *
            ∫⁻ ζ : ℝ, ENNReal.ofReal |(ζ ^ m)⁻¹| * ‖angularFourier1D ψ ζ‖ₑ ^ 2) := by
        rw [lintegral_const_mul'' _ hζmeas]
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ((ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) *
            ENNReal.ofReal (((2 * Real.pi) ^ (m - 1))⁻¹)) := by
        rw [hJ]
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
        have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne m))
        have hconst : ((2 * Real.pi)⁻¹ * ((2 * Real.pi) ^ m *
            ((2 * Real.pi) ^ (m - 1))⁻¹) : ℝ) = 1 := by
          have hpm : ((2 * Real.pi) ^ m : ℝ) = (2 * Real.pi) ^ (m - 1) * (2 * Real.pi) := by
            conv_lhs => rw [← hm1]
            rw [pow_succ]
          rw [hpm]
          field_simp
        calc (ENNReal.ofReal (2 * Real.pi))⁻¹ *
            ((ENNReal.ofReal ((2 * Real.pi) ^ m) * ∫⁻ x, ‖f x‖ₑ ^ 2) *
              ENNReal.ofReal (((2 * Real.pi) ^ (m - 1))⁻¹))
            = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                (ENNReal.ofReal ((2 * Real.pi) ^ m) *
                  ENNReal.ofReal (((2 * Real.pi) ^ (m - 1))⁻¹)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
              rw [ENNReal.ofReal_inv_of_pos hπpos]
              ring
          _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * ((2 * Real.pi) ^ m *
                ((2 * Real.pi) ^ (m - 1))⁻¹)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          _ = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
              rw [hconst, ENNReal.ofReal_one, one_mul]

/-- On `L¹ ∩ L²(ℝ^m)`, the ridgelet transform of a self-admissible normalized ridgelet function
is square-integrable on the parameter space: `R_ψ f ∈ L²(𝕐^{m+1})`. -/
theorem memLp_two_euclideanRidgeletTransform (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    MemLp (euclideanRidgeletTransform m 1 ψ f) 2 (ridgeletParameterMeasure m) := by
  refine ⟨aestronglyMeasurable_euclideanRidgeletTransform_parameterMeasure m 1 hf1 hψc, ?_⟩
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ 2) ≠ ∞ := by
    have h := hf2.eLpNorm_lt_top
    rw [eLpNorm_two_eq_lintegral_enorm_sq] at h
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact absurd h (lt_irrefl _)
  rw [eLpNorm_two_eq_lintegral_enorm_sq,
    lintegral_enorm_euclideanRidgeletTransform_sq m hself hK hψc hψb hf1 hf2]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin

/-- Theorem 5.9 (`thm:parseval`), Plancherel's identity: for a self-admissible `ψ` normalized by
`K_{ψ,ψ} = 1` and `f ∈ L¹ ∩ L²(ℝ^m)`, the ridgelet transform is an `L²`-isometry:
`‖R_ψ f‖_{L²(𝕐^{m+1})} = ‖f‖₂`. -/
theorem l1_plancherel_identity (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    ∫ q, ‖euclideanRidgeletTransform m 1 ψ f q‖ ^ 2 ∂ridgeletParameterMeasure m =
      ∫ x, ‖f x‖ ^ 2 := by
  rw [MeasureTheory.integral_norm_sq_eq_toReal_lintegral
      (aestronglyMeasurable_euclideanRidgeletTransform_parameterMeasure m 1 hf1 hψc),
    MeasureTheory.integral_norm_sq_eq_toReal_lintegral hf2.aestronglyMeasurable,
    lintegral_enorm_euclideanRidgeletTransform_sq m hself hK hψc hψb hf1 hf2]

set_option maxHeartbeats 800000 in
-- The proof is a single long assembly of fiberwise Plancherel identities and Fubini swaps.
/-- Theorem 5.9 (`thm:parseval`), Parseval's relation: for admissibly paired, normalized
self-admissible `ψ` and `η` and `f, g ∈ L¹ ∩ L²(ℝ^m)`,
`⟨R_ψ f, R_η g⟩_{L²(𝕐^{m+1})} = ⟨f, g⟩_{L²(ℝ^m)}`. The proof applies the fiberwise polarized
Plancherel identity in the bias variable, cancels the parameter weight, and evaluates the
spectral pairing by the dilation `ξ = ζa` and the `m`-dimensional polarized Plancherel
identity, producing the cross admissibility constant `K_{ψ,η}`.

**Amendment (author-style decision 2026-07-24).** The manuscript states the relation for an
admissible pair `(ψ, η) ∈ 𝒮 × 𝒮₀'` with `K_{ψ,η} = 1`, "immediate by duality". At function
level the parameter-space pairing must converge absolutely, which requires both transforms to
be square-integrable on `𝕐^{m+1}`; by the Plancherel theory this holds when `ψ` **and** `η`
are each self-admissible (their diagonal admissibility integrals are finite — by
Cauchy–Schwarz and AM–GM this also subsumes the absolute convergence of the cross
admissibility integral), and the diagonal normalizations `K_{ψ,ψ} = K_{η,η} = 1` are imposed
to reuse the normalized `L²`-membership `memLp_two_euclideanRidgeletTransform`. The
activation `η` is accordingly integrable and bounded, and its Fourier data is the classical
`η̂`; the cross normalization `K_{ψ,η} = 1` is the manuscript's. -/
theorem l1_parseval_relation (m : ℕ) [NeZero m]
    {ψ η : ℝ → ℂ} {f g : InputSpace m → ℂ}
    (hψself : IsSelfAdmissible m ψ)
    (hKψ : admissibilityConstant m ψ (angularFourier1D ψ) = 1)
    (hηself : IsSelfAdmissible m η)
    (hKη : admissibilityConstant m η (angularFourier1D η) = 1)
    (hK : admissibilityConstant m ψ (angularFourier1D η) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    ∫ q, euclideanRidgeletTransform m 1 ψ f q *
        conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m =
      ∫ x, f x * conj (g x) := by
  classical
  have hψint : Integrable ψ volume := hψself.1
  have hηint : Integrable η volume := hηself.1
  have hψKint := hψself.2.2.1
  have hηKint := hηself.2.2.1
  obtain ⟨Cψ, hψC⟩ := hψb
  obtain ⟨Cη, hηC⟩ := hηb
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- ==================== L² memberships and product integrability ====================
  have hR₁ : MemLp (euclideanRidgeletTransform m 1 ψ f) 2 (ridgeletParameterMeasure m) :=
    memLp_two_euclideanRidgeletTransform m hψself hKψ hψc ⟨Cψ, hψC⟩ hf1 hf2
  have hR₂ : MemLp (euclideanRidgeletTransform m 1 η g) 2 (ridgeletParameterMeasure m) :=
    memLp_two_euclideanRidgeletTransform m hηself hKη hηc ⟨Cη, hηC⟩ hg1 hg2
  have hprod : Integrable (fun q => euclideanRidgeletTransform m 1 ψ f q *
      conj (euclideanRidgeletTransform m 1 η g q)) (ridgeletParameterMeasure m) :=
    hR₁.integrable_mul_conj hR₂
  -- ==================== the weighted measure ====================
  have hwmeas : Measurable fun q : RidgeletParameterSpace m =>
      ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.norm.pow_const 2).inv)
  have hwlt : ∀ᵐ q : RidgeletParameterSpace m ∂(volume : Measure (RidgeletParameterSpace m)),
      ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹) < ∞ :=
    Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top
  have hW : (∫ q, euclideanRidgeletTransform m 1 ψ f q *
      conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m)
      = ∫ q : RidgeletParameterSpace m, ((‖q.1‖ ^ 2)⁻¹ : ℝ) •
          (euclideanRidgeletTransform m 1 ψ f q *
            conj (euclideanRidgeletTransform m 1 η g q)) := by
    unfold ridgeletParameterMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hwmeas hwlt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hjoint : Integrable (fun q : RidgeletParameterSpace m => ((‖q.1‖ ^ 2)⁻¹ : ℝ) •
      (euclideanRidgeletTransform m 1 ψ f q *
        conj (euclideanRidgeletTransform m 1 η g q)))
      (volume : Measure (RidgeletParameterSpace m)) := by
    have h := (integrable_withDensity_iff_integrable_smul' hwmeas hwlt).mp hprod
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (by positivity)]
  -- ==================== the fiberwise polarized Plancherel ====================
  have hae0 : ∀ᵐ a : InputSpace m ∂volume, a ≠ 0 := by
    refine mem_ae_iff.mpr ?_
    rw [show {a : InputSpace m | a ≠ 0}ᶜ = {(0 : InputSpace m)} from by ext a; simp]
    exact measure_singleton 0
  set S : ℝ → InputSpace m → ℂ := fun ζ a =>
    Fourier.angularFourierIntegralInner f (ζ • a) *
      conj (Fourier.angularFourierIntegralInner g (ζ • a)) *
      (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ) with hS_def
  have hfiber : ∀ᵐ a : InputSpace m ∂volume,
      (∫ b : ℝ, ((‖a‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f (a, b) *
        conj (euclideanRidgeletTransform m 1 η g (a, b))))
        = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ, S ζ a := by
    filter_upwards [hae0] with a ha0
    have hu1 := integrable_euclideanRidgeletTransform_bias m 1 hf1 hψint a
    have hu2 := memLp_two_euclideanRidgeletTransform_bias m 1 hf1 hψint hψc hψC a
    have hv1 := integrable_euclideanRidgeletTransform_bias m 1 hg1 hηint a
    have hv2 := memLp_two_euclideanRidgeletTransform_bias m 1 hg1 hηint hηc hηC a
    have hpar := Fourier.integral_angularFourierIntegralInner_mul_conj hu1 hu2 hv1 hv2
    rw [Module.finrank_self, pow_one] at hpar
    -- identify the fiber transforms with the spectral kernel
    have hkernel : ∀ ζ : ℝ, Fourier.angularFourierIntegralInner
        (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ *
        conj (Fourier.angularFourierIntegralInner
          (fun b => euclideanRidgeletTransform m 1 η g (a, b)) ζ)
        = S ζ a * ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      intro ζ
      have h1 := angularFourier1D_euclideanRidgeletTransform m 1 hf1 hψint a ζ
      have h2 := angularFourier1D_euclideanRidgeletTransform m 1 hg1 hηint a ζ
      have hc1 : Fourier.angularFourierIntegralInner
          (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ
          = angularFourier1D (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ := rfl
      have hc2 : Fourier.angularFourierIntegralInner
          (fun b => euclideanRidgeletTransform m 1 η g (a, b)) ζ
          = angularFourier1D (fun b => euclideanRidgeletTransform m 1 η g (a, b)) ζ := rfl
      rw [hc1, hc2, h1, h2, hS_def]
      simp only [Real.rpow_one]
      rw [map_mul, map_mul, RCLike.conj_conj, Complex.conj_ofReal]
      push_cast
      ring
    -- assemble, cancelling the weight
    have hsmul : (∫ b : ℝ, ((‖a‖ ^ 2)⁻¹ : ℝ) •
        (euclideanRidgeletTransform m 1 ψ f (a, b) *
          conj (euclideanRidgeletTransform m 1 η g (a, b))))
        = ((‖a‖ ^ 2)⁻¹ : ℝ) • ∫ b : ℝ,
            euclideanRidgeletTransform m 1 ψ f (a, b) *
              conj (euclideanRidgeletTransform m 1 η g (a, b)) :=
      MeasureTheory.integral_smul _ _
    have hb : (∫ b : ℝ, euclideanRidgeletTransform m 1 ψ f (a, b) *
        conj (euclideanRidgeletTransform m 1 η g (a, b)))
        = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ((∫ ζ : ℝ, S ζ a) * ((‖a‖ ^ 2 : ℝ) : ℂ)) := by
      have hζint : (∫ ζ : ℝ, Fourier.angularFourierIntegralInner
          (fun b => euclideanRidgeletTransform m 1 ψ f (a, b)) ζ *
          conj (Fourier.angularFourierIntegralInner
            (fun b => euclideanRidgeletTransform m 1 η g (a, b)) ζ))
          = (∫ ζ : ℝ, S ζ a) * ((‖a‖ ^ 2 : ℝ) : ℂ) := by
        rw [← integral_mul_const]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => hkernel ζ)
      rw [hζint] at hpar
      -- hpar : (∫ S)·‖a‖² = 2π·∫_b (...)
      have hcancel : ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hπ.ne']
        norm_num
      calc (∫ b : ℝ, euclideanRidgeletTransform m 1 ψ f (a, b) *
            conj (euclideanRidgeletTransform m 1 η g (a, b)))
          = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) *
              ∫ b : ℝ, euclideanRidgeletTransform m 1 ψ f (a, b) *
                conj (euclideanRidgeletTransform m 1 η g (a, b))) := by
            rw [← mul_assoc, hcancel, one_mul]
        _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) *
              ((∫ ζ : ℝ, S ζ a) * ((‖a‖ ^ 2 : ℝ) : ℂ)) := by
            rw [← hpar]
    rw [hsmul, hb, Complex.real_smul]
    have hna : ((‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr ha0))
    have hcancel2 : ((((‖a‖ ^ 2)⁻¹ : ℝ)) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul,
        inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr ha0))]
      norm_num
    calc ((((‖a‖ ^ 2)⁻¹ : ℝ)) : ℂ) * (((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) *
          ((∫ ζ : ℝ, S ζ a) * ((‖a‖ ^ 2 : ℝ) : ℂ)))
        = (((((‖a‖ ^ 2)⁻¹ : ℝ)) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ)) *
            (((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ, S ζ a) := by ring
      _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ, S ζ a := by
          rw [hcancel2, one_mul]
  -- ==================== the spectral kernel is jointly integrable ====================
  have haeζ : ∀ᵐ ζ : ℝ ∂(volume : Measure ℝ), ζ ≠ 0 := by
    refine mem_ae_iff.mpr ?_
    rw [show {ζ : ℝ | ζ ≠ 0}ᶜ = {(0 : ℝ)} from by ext ζ; simp]
    exact measure_singleton 0
  have hrestrict : (volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ = volume := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.restrict_apply hs, ← Set.sdiff_eq, measure_sdiff_null']
    exact measure_mono_null Set.inter_subset_right (measure_singleton 0)
  have hFf := Fourier.continuous_angularFourierIntegralInner hf1
  have hFg := Fourier.continuous_angularFourierIntegralInner hg1
  have hΨc : Continuous (angularFourier1D ψ) :=
    Fourier.continuous_angularFourierIntegralInner hψint
  have hΗc : Continuous (angularFourier1D η) :=
    Fourier.continuous_angularFourierIntegralInner hηint
  have hfg1 : Integrable (fun ξ : InputSpace m =>
      Fourier.angularFourierIntegralInner f ξ *
        conj (Fourier.angularFourierIntegralInner g ξ)) volume :=
    (Fourier.memLp_two_angularFourierIntegralInner hf1 hf2).integrable_mul_conj
      (Fourier.memLp_two_angularFourierIntegralInner hg1 hg2)
  have hSaesm : AEStronglyMeasurable (Function.uncurry S)
      ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := by
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact hFf.comp (continuous_fst.smul continuous_snd)
    · exact RCLike.continuous_conj.comp (hFg.comp (continuous_fst.smul continuous_snd))
    · exact (RCLike.continuous_conj.comp (hΨc.comp continuous_fst)).mul
        (hΗc.comp continuous_fst)
  -- the diagonal spectral densities are integrable
  have hdiag : ∀ (χ : ℝ → ℂ), IntegrableOn
      (fun ζ => conj (angularFourier1D χ ζ) * angularFourier1D χ ζ /
        ((|ζ| ^ m : ℝ) : ℂ)) {(0 : ℝ)}ᶜ volume →
      Integrable (fun ζ : ℝ => ‖angularFourier1D χ ζ‖ ^ 2 / |ζ| ^ m) volume := by
    intro χ hint
    have h : Integrable (fun ζ : ℝ => ‖angularFourier1D χ ζ‖ ^ 2 / |ζ| ^ m)
        ((volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ) := by
      refine hint.norm.congr (Filter.Eventually.of_forall fun ζ => ?_)
      simp only []
      rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ |ζ| ^ m)]
      ring
    rwa [hrestrict] at h
  have hDψ := hdiag ψ hψKint
  have hDη := hdiag η hηKint
  have hSint : Integrable (Function.uncurry S)
      ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := by
    rw [integrable_prod_iff hSaesm]
    constructor
    · filter_upwards [haeζ] with ζ hζ0
      have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure (InputSpace m))
        (fun ξ => Fourier.angularFourierIntegralInner f ξ *
          conj (Fourier.angularFourierIntegralInner g ξ)) hζ0).mpr hfg1
      exact (h.mul_const (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ)).congr
        (Filter.Eventually.of_forall fun a => rfl)
    · -- the marginal is dominated by the diagonal densities
      set NΦ : ℝ := ∫ ξ : InputSpace m, ‖Fourier.angularFourierIntegralInner f ξ *
        conj (Fourier.angularFourierIntegralInner g ξ)‖ with hNΦ_def
      have hNΦ0 : 0 ≤ NΦ := integral_nonneg fun ξ => norm_nonneg _
      have hDint : Integrable (fun ζ : ℝ =>
          (‖angularFourier1D ψ ζ‖ ^ 2 / |ζ| ^ m +
            ‖angularFourier1D η ζ‖ ^ 2 / |ζ| ^ m) / 2 * NΦ) volume :=
        ((hDψ.add hDη).div_const 2).mul_const NΦ
      refine hDint.mono' ?_ ?_
      · exact hSaesm.norm.integral_prod_right'
      · filter_upwards [haeζ] with ζ hζ0
        have hζ' : (0 : ℝ) < |ζ| := abs_pos.mpr hζ0
        -- closed form of the marginal
        have hmarg : (∫ a : InputSpace m, ‖Function.uncurry S (ζ, a)‖)
            = ‖conj (angularFourier1D ψ ζ) * angularFourier1D η ζ‖ *
                ((|ζ| ^ m)⁻¹ * NΦ) := by
          calc (∫ a : InputSpace m, ‖Function.uncurry S (ζ, a)‖)
              = ∫ a : InputSpace m, ‖Fourier.angularFourierIntegralInner f (ζ • a) *
                  conj (Fourier.angularFourierIntegralInner g (ζ • a))‖ *
                  ‖conj (angularFourier1D ψ ζ) * angularFourier1D η ζ‖ := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
                simp only [Function.uncurry, hS_def]
                rw [norm_mul]
            _ = (∫ a : InputSpace m, ‖Fourier.angularFourierIntegralInner f (ζ • a) *
                  conj (Fourier.angularFourierIntegralInner g (ζ • a))‖) *
                  ‖conj (angularFourier1D ψ ζ) * angularFourier1D η ζ‖ :=
                integral_mul_const _ _
            _ = ‖conj (angularFourier1D ψ ζ) * angularFourier1D η ζ‖ *
                  ((|ζ| ^ m)⁻¹ * NΦ) := by
                have hcov := MeasureTheory.Measure.integral_comp_smul
                  (μ := (volume : Measure (InputSpace m)))
                  (fun ξ => ‖Fourier.angularFourierIntegralInner f ξ *
                    conj (Fourier.angularFourierIntegralInner g ξ)‖) ζ
                rw [hcov, hNΦ_def, smul_eq_mul,
                  show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin,
                  abs_inv, abs_pow]
                ring
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun a => norm_nonneg _),
          hmarg]
        -- AM-GM domination
        rw [norm_mul, RCLike.norm_conj]
        have hAM : ‖angularFourier1D ψ ζ‖ * ‖angularFourier1D η ζ‖ ≤
            (‖angularFourier1D ψ ζ‖ ^ 2 + ‖angularFourier1D η ζ‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖angularFourier1D ψ ζ‖ - ‖angularFourier1D η ζ‖)]
        calc ‖angularFourier1D ψ ζ‖ * ‖angularFourier1D η ζ‖ * ((|ζ| ^ m)⁻¹ * NΦ)
            ≤ (‖angularFourier1D ψ ζ‖ ^ 2 + ‖angularFourier1D η ζ‖ ^ 2) / 2 *
                ((|ζ| ^ m)⁻¹ * NΦ) := by
              refine mul_le_mul_of_nonneg_right hAM (by positivity)
          _ = (‖angularFourier1D ψ ζ‖ ^ 2 / |ζ| ^ m +
                ‖angularFourier1D η ζ‖ ^ 2 / |ζ| ^ m) / 2 * NΦ := by
              field_simp
  -- ==================== assemble ====================
  set J : ℂ := ∫ ξ : InputSpace m, Fourier.angularFourierIntegralInner f ξ *
    conj (Fourier.angularFourierIntegralInner g ξ) with hJ_def
  have hJval : J = (((2 * Real.pi) ^ m : ℝ) : ℂ) * ∫ x, f x * conj (g x) := by
    rw [hJ_def, Fourier.integral_angularFourierIntegralInner_mul_conj hf1 hf2 hg1 hg2,
      show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin]
  have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne m))
  calc (∫ q, euclideanRidgeletTransform m 1 ψ f q *
      conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m)
      = ∫ q : RidgeletParameterSpace m, ((‖q.1‖ ^ 2)⁻¹ : ℝ) •
          (euclideanRidgeletTransform m 1 ψ f q *
            conj (euclideanRidgeletTransform m 1 η g q)) := hW
    _ = ∫ a : InputSpace m, ∫ b : ℝ, ((‖a‖ ^ 2)⁻¹ : ℝ) •
          (euclideanRidgeletTransform m 1 ψ f (a, b) *
            conj (euclideanRidgeletTransform m 1 η g (a, b))) := by
        rw [Measure.volume_eq_prod] at hjoint ⊢
        exact MeasureTheory.integral_prod _ hjoint
    _ = ∫ a : InputSpace m, ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ, S ζ a :=
        integral_congr_ae hfiber
    _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ a : InputSpace m, ∫ ζ : ℝ, S ζ a :=
        integral_const_mul _ _
    _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ, ∫ a : InputSpace m, S ζ a := by
        rw [← MeasureTheory.integral_integral_swap hSint]
    _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) * ∫ ζ : ℝ,
          (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ /
            ((|ζ| ^ m : ℝ) : ℂ)) * J := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [haeζ] with ζ hζ0
        have hζ' : (0 : ℝ) < |ζ| := abs_pos.mpr hζ0
        have hcast : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (by positivity)
        have hcov := MeasureTheory.Measure.integral_comp_smul
          (μ := (volume : Measure (InputSpace m)))
          (fun ξ => Fourier.angularFourierIntegralInner f ξ *
            conj (Fourier.angularFourierIntegralInner g ξ)) ζ
        calc (∫ a : InputSpace m, S ζ a)
            = (∫ a : InputSpace m, Fourier.angularFourierIntegralInner f (ζ • a) *
                conj (Fourier.angularFourierIntegralInner g (ζ • a))) *
                (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ) := by
              rw [← integral_mul_const]
          _ = (|((ζ : ℝ) ^ Module.finrank ℝ (InputSpace m))⁻¹| • J) *
                (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ) := by
              rw [hcov, hJ_def]
          _ = (conj (angularFourier1D ψ ζ) * angularFourier1D η ζ /
                ((|ζ| ^ m : ℝ) : ℂ)) * J := by
              rw [show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin,
                abs_inv, abs_pow, Complex.real_smul]
              push_cast
              field_simp
    _ = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) *
          ((∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * angularFourier1D η ζ /
            ((|ζ| ^ m : ℝ) : ℂ)) * J) := by
        rw [integral_mul_const]
        congr 2
        exact (congrArg (fun μ => ∫ ζ, conj (angularFourier1D ψ ζ) *
          angularFourier1D η ζ / ((|ζ| ^ m : ℝ) : ℂ) ∂μ) hrestrict).symm
    _ = ∫ x, f x * conj (g x) := by
        have hKval : ((2 : ℂ) * (Real.pi : ℂ)) ^ (m - 1) *
            (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * angularFourier1D η ζ /
              ((|ζ| ^ m : ℝ) : ℂ)) = 1 := by
          have h := hK
          rw [admissibilityConstant] at h
          exact h
        have hπC : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
          simp [Real.pi_ne_zero]
        have hpow : (((2 * Real.pi) ^ m : ℝ) : ℂ)
            = ((2 : ℂ) * (Real.pi : ℂ)) ^ (m - 1) * ((2 : ℂ) * (Real.pi : ℂ)) := by
          push_cast
          rw [← pow_succ, hm1]
        rw [hJval, hpow]
        have hint : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) *
            angularFourier1D η ζ / ((|ζ| ^ m : ℝ) : ℂ))
            = (((2 : ℂ) * (Real.pi : ℂ)) ^ (m - 1))⁻¹ := by
          have hne : ((2 : ℂ) * (Real.pi : ℂ)) ^ (m - 1) ≠ 0 := pow_ne_zero _ hπC
          field_simp
          linear_combination hKval
        rw [hint]
        push_cast
        field_simp

/-! ## The bounded `L²` extension (`thm:L2`) -/

/-- Theorem 5.10 (`thm:L2`), bounded extension of the ridgelet transform to `L²(ℝ^m)`: for a
self-admissible `ψ` with `K_{ψ,ψ} = 1`, there is a unique bounded operator
`L²(ℝ^m) → L²(𝕐^{m+1})` that agrees with the integral transform on `L¹ ∩ L²(ℝ^m)`, and it is an
isometry. -/
theorem l1_ridgeletTransform_L2_extension (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (angularFourier1D ψ) = 1) :
    ∃! R : TargetSpace m →L[ℂ] Lp ℂ 2 (ridgeletParameterMeasure m),
      (∀ f : TargetSpace m, Integrable (⇑f) volume →
        (⇑(R f) : RidgeletParameterSpace m → ℂ) =ᵐ[ridgeletParameterMeasure m]
          euclideanRidgeletTransform m 1 ψ (⇑f)) ∧
      ∀ f : TargetSpace m, ‖R f‖ = ‖f‖ := by
  obtain ⟨C, hψC⟩ := hψb
  -- the ridgelet transform respects almost-everywhere equality of the input
  have hcongr : ∀ {g g' : InputSpace m → ℂ}, g =ᵐ[volume] g' →
      euclideanRidgeletTransform m 1 ψ g = euclideanRidgeletTransform m 1 ψ g' := by
    intro g g' hgg'
    funext p
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with x hx
    rw [hx]
  -- additivity and homogeneity on integrable inputs
  have hadd : ∀ {g g' : InputSpace m → ℂ}, Integrable g volume → Integrable g' volume →
      euclideanRidgeletTransform m 1 ψ (g + g') =
        euclideanRidgeletTransform m 1 ψ g + euclideanRidgeletTransform m 1 ψ g' := by
    intro g g' hg hg'
    funext p
    have h1 := (l1_ridgelet_pointwise_convergent_L1_bounded m 1 hg hψc hψC p).1
    have h2 := (l1_ridgelet_pointwise_convergent_L1_bounded m 1 hg' hψc hψC p).1
    simp only [euclideanRidgeletTransform, Pi.add_apply]
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hsmul : ∀ (c : ℂ) (g : InputSpace m → ℂ),
      euclideanRidgeletTransform m 1 ψ (c • g) =
        c • euclideanRidgeletTransform m 1 ψ g := by
    intro c g
    funext p
    simp only [euclideanRidgeletTransform, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- the dense subspace of integrable classes, i.e. `L¹ ∩ L²(ℝ^m)`
  set D : Submodule ℂ (TargetSpace m) :=
    { carrier := {f : TargetSpace m | Integrable (⇑f) volume}
      add_mem' := fun hf hg => (hf.add hg).congr (Lp.coeFn_add _ _).symm
      zero_mem' := (integrable_zero _ _ _).congr (Lp.coeFn_zero ℂ 2 _).symm
      smul_mem' := fun c f hf => (hf.smul c).congr (Lp.coeFn_smul c f).symm }
    with hD_def
  have hD_dense : Dense (D : Set (TargetSpace m)) :=
    MeasureTheory.Lp.dense_setOf_integrable ENNReal.ofNat_ne_top
  -- membership of the transform in `L²(𝕐^{m+1})` on the dense subspace
  have hmem : ∀ f : D,
      MemLp (euclideanRidgeletTransform m 1 ψ (⇑(f : TargetSpace m))) 2
        (ridgeletParameterMeasure m) := fun f =>
    memLp_two_euclideanRidgeletTransform m hself hK hψc ⟨C, hψC⟩ f.2 (Lp.memLp _)
  -- the densely defined linear map
  set T₀ : D →ₗ[ℂ] Lp ℂ 2 (ridgeletParameterMeasure m) :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => by
        have h : euclideanRidgeletTransform m 1 ψ
            (⇑((f : TargetSpace m) + (g : TargetSpace m)))
            = euclideanRidgeletTransform m 1 ψ (⇑(f : TargetSpace m)) +
              euclideanRidgeletTransform m 1 ψ (⇑(g : TargetSpace m)) := by
          rw [hcongr (Lp.coeFn_add (f : TargetSpace m) (g : TargetSpace m))]
          exact hadd f.2 g.2
        exact (MemLp.toLp_congr (hmem (f + g)) ((hmem f).add (hmem g))
          h.eventuallyEq).trans (MemLp.toLp_add (hmem f) (hmem g))
      map_smul' := fun c f => by
        have h : euclideanRidgeletTransform m 1 ψ (⇑(c • (f : TargetSpace m)))
            = c • euclideanRidgeletTransform m 1 ψ (⇑(f : TargetSpace m)) := by
          rw [hcongr (Lp.coeFn_smul c (f : TargetSpace m))]
          exact hsmul c _
        exact (MemLp.toLp_congr (hmem (c • f)) ((hmem f).const_smul c)
          h.eventuallyEq).trans (MemLp.toLp_const_smul c (hmem f)) }
    with hT₀_def
  -- the densely defined map is isometric, by Plancherel's identity
  have hT₀norm : ∀ f : D, ‖T₀ f‖ = ‖f‖ := by
    intro f
    have h1 : ‖T₀ f‖ = (eLpNorm (euclideanRidgeletTransform m 1 ψ (⇑(f : TargetSpace m))) 2
        (ridgeletParameterMeasure m)).toReal :=
      Lp.norm_toLp (euclideanRidgeletTransform m 1 ψ (⇑(f : TargetSpace m))) (hmem f)
    have h2 : ‖f‖ = (eLpNorm (⇑(f : TargetSpace m)) 2 volume).toReal := by
      rw [show ‖f‖ = ‖(f : TargetSpace m)‖ from rfl]
      exact Lp.norm_def _
    rw [h1, h2, eLpNorm_two_eq_lintegral_enorm_sq, eLpNorm_two_eq_lintegral_enorm_sq,
      lintegral_enorm_euclideanRidgeletTransform_sq m hself hK hψc ⟨C, hψC⟩ f.2 (Lp.memLp _)]
  -- extend along the dense isometric inclusion
  set T : D →L[ℂ] Lp ℂ 2 (ridgeletParameterMeasure m) :=
    T₀.mkContinuous 1 (fun f => le_of_eq ((hT₀norm f).trans (one_mul ‖f‖).symm)) with hT_def
  have h_dense : DenseRange ⇑(D.subtypeL) := denseRange_subtype_val.mpr hD_dense
  have h_e : IsUniformInducing ⇑(D.subtypeL) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hText : ∀ f : D, T.extend D.subtypeL (D.subtypeL f) = T f := fun f =>
    T.extend_eq h_dense h_e f
  -- the extension agrees with the integral transform on `L¹ ∩ L²(ℝ^m)`
  have hagree : ∀ f : TargetSpace m, Integrable (⇑f) volume →
      (⇑(T.extend D.subtypeL f) : RidgeletParameterSpace m → ℂ)
        =ᵐ[ridgeletParameterMeasure m] euclideanRidgeletTransform m 1 ψ (⇑f) := by
    intro f hf
    have h1 : T.extend D.subtypeL f = T ⟨f, hf⟩ := hText ⟨f, hf⟩
    rw [h1]
    exact MemLp.coeFn_toLp (hmem ⟨f, hf⟩)
  -- the extension is a global isometry, by density and continuity of the norm
  have hiso : ∀ f : TargetSpace m, ‖T.extend D.subtypeL f‖ = ‖f‖ := by
    refine isClosed_property h_dense
      (isClosed_eq (continuous_norm.comp (T.extend D.subtypeL).continuous) continuous_norm)
      fun f => ?_
    calc ‖T.extend D.subtypeL (D.subtypeL f)‖ = ‖T f‖ := by rw [hText f]
      _ = ‖f‖ := hT₀norm f
      _ = ‖D.subtypeL f‖ := rfl
  refine ⟨T.extend D.subtypeL, ⟨hagree, hiso⟩, ?_⟩
  -- uniqueness: two continuous maps agreeing on a dense subspace are equal
  rintro R' ⟨hR'agree, -⟩
  refine ContinuousLinearMap.coeFn_injective ?_
  refine Continuous.ext_on hD_dense R'.continuous (T.extend D.subtypeL).continuous
    fun f hf => ?_
  exact Lp.ext ((hR'agree f hf).trans (hagree f hf).symm)

end LeanRidgelet
