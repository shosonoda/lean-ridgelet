/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.PairingExtension

/-!
# L1 theory: the reconstruction section and its spectral data (steps T1--T3)

The truncated reconstruction is the pairing of the activation against the section

`Ξ_{x,ε,δ}(r) = ∫_{ε ≤ ‖a‖ ≤ δ} ∫ f y ⬝ conj (ψ (r - ⟨a, x - y⟩)) dy da`,

whose Fourier data is computed by the spectral factor
`H_{x,ε,δ}(ζ) = ∫_{ε ≤ ‖a‖ ≤ δ} f̂(ζ a) e^{i ζ ⟨a, x⟩} da`.

## Main results

* `LeanRidgelet.truncatedDualRidgeletTransform_eq_section_pairing`: **step T1**,
  `R†_η[R_ψ f](x; ε, δ) = ∫ η(r) Ξ_{x,ε,δ}(r) dr`.
* `LeanRidgelet.integrable_weight_truncatedReconstructionSection`,
  `LeanRidgelet.angularFourier1D_truncatedReconstructionSection`,
  `LeanRidgelet.norm_truncatedSpectralFactor_le`,
  `LeanRidgelet.norm_truncatedSpectralFactor_le_of_ne`: **step T2**, the section lies in the
  `(1 + |r|)^k`-weighted `L¹`, its Fourier data is `Ξ̂(ζ) = conj (ψ̂ (-ζ)) H(-ζ)`, and `H` is
  bounded both uniformly and by `|ζ|^{-m} ‖f̂‖₁`.
* `LeanRidgelet.integral_pow_mul_truncatedReconstructionSection_eq_zero`: **step T3**, the
  section inherits the vanishing moments of `ψ`, which places it in the domain of the pairing
  extension.

The measurability bookkeeping of the iterated Fubini arguments goes through the parametrized
skew shears of `LeanRidgelet.ToMathlib.ProdShear`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The scale annulus and the reconstruction section (step T1) -/

/-- The scale annulus `ε ≤ ‖a‖ ≤ δ` of the truncated reconstruction. -/
def scaleAnnulus (m : ℕ) (ε δ : ℝ) : Set (InputSpace m) :=
  {a : InputSpace m | ε ≤ ‖a‖ ∧ ‖a‖ ≤ δ}

theorem measurableSet_scaleAnnulus (m : ℕ) (ε δ : ℝ) :
    MeasurableSet (scaleAnnulus m ε δ) := by
  have h : scaleAnnulus m ε δ
      = {a : InputSpace m | ε ≤ ‖a‖} ∩ {a : InputSpace m | ‖a‖ ≤ δ} := by
    ext a
    simp [scaleAnnulus]
  rw [h]
  exact ((isClosed_le continuous_const continuous_norm).measurableSet).inter
    ((isClosed_le continuous_norm continuous_const).measurableSet)

theorem volume_scaleAnnulus_lt_top (m : ℕ) (ε δ : ℝ) :
    volume (scaleAnnulus m ε δ) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_)
    (measure_closedBall_lt_top (x := (0 : InputSpace m)) (r := δ))
  intro a ha
  simp only [scaleAnnulus, Set.mem_setOf_eq] at ha
  simpa [Metric.mem_closedBall, dist_zero_right] using ha.2

/-- The reconstruction section `Ξ_{x,ε,δ}(r)` (step T1 of the reconstruction plan): the
ridgelet-side data of the truncated reconstruction, paired against the activation in the
variable `r`. -/
def truncatedReconstructionSection (m : ℕ) (ψ : ℝ → ℂ) (f : InputSpace m → ℂ)
    (x : InputSpace m) (ε δ : ℝ) : ℝ → ℂ :=
  fun r => ∫ a in scaleAnnulus m ε δ, ∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))

set_option maxHeartbeats 800000 in
-- The proof is a single long assembly of skew-shear transports and Fubini rearrangements.
/-- **Step T1 of the reconstruction plan**: the truncated reconstruction is the pairing of the
activation against the reconstruction section,
`R†_η[R_ψ f](x; ε, δ) = ∫ η(r) Ξ_{x,ε,δ}(r) dr`, absolutely convergent under matched `k`-th
moments. The proof substitutes `b ← ⟨a,x⟩ - r` fiberwise and swaps the scale and pairing
integrals through a triple-kernel integrability layer built from the parametrized skew shears
of `LeanRidgelet.ToMathlib.ProdShear`. -/
theorem truncatedDualRidgeletTransform_eq_section_pairing (m k : ℕ)
    {ψ η : ℝ → ℂ} {f : InputSpace m → ℂ} {Cη : ℝ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume) (hηm : AEStronglyMeasurable η volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (x : InputSpace m) {ε δ : ℝ} (hε : 0 < ε) :
    truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ x
      = ∫ r : ℝ, η r * truncatedReconstructionSection m ψ f x ε δ r := by
  classical
  have hCη : 0 ≤ Cη := polynomiallyBounded_nonneg_const hηk
  have hAmeas : MeasurableSet (scaleAnnulus m ε δ) := measurableSet_scaleAnnulus m ε δ
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  haveI hμAfin : IsFiniteMeasure μA := by
    refine ⟨?_⟩
    rw [hμA_def, Measure.restrict_apply_univ]
    exact volume_scaleAnnulus_lt_top m ε δ
  -- measurable parameter maps for the skew evaluations
  have hcinner : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 w.2 :=
    (Continuous.inner continuous_fst continuous_snd).measurable
  have hcx : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 x :=
    (Continuous.inner continuous_fst continuous_const).measurable
  -- ==================== the triple kernel in the order ((scale, input), bias) ==============
  set T : (InputSpace m × InputSpace m) × ℝ → ℂ := fun q =>
    f q.1.2 * conj (ψ (inner ℝ q.1.1 q.1.2 - q.2)) * η (inner ℝ q.1.1 x - q.2) with hT_def
  have hTaesm : AEStronglyMeasurable T
      ((μA.prod (volume : Measure (InputSpace m))).prod (volume : Measure ℝ)) := by
    have h1 : AEStronglyMeasurable (fun q : (InputSpace m × InputSpace m) × ℝ => f q.1.2)
        ((μA.prod volume).prod volume) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst)
    have h2 : AEStronglyMeasurable
        (fun q : (InputSpace m × InputSpace m) × ℝ =>
          conj (ψ (inner ℝ q.1.1 q.1.2 - q.2))) ((μA.prod volume).prod volume) := by
      refine RCLike.continuous_conj.comp_aestronglyMeasurable ?_
      exact hψm.comp_quasiMeasurePreserving
        (MeasureTheory.quasiMeasurePreserving_skewSubLeft (μA.prod volume) volume hcinner)
    have h3 : AEStronglyMeasurable
        (fun q : (InputSpace m × InputSpace m) × ℝ => η (inner ℝ q.1.1 x - q.2))
        ((μA.prod volume).prod volume) := by
      refine hηm.comp_quasiMeasurePreserving ?_
      exact MeasureTheory.quasiMeasurePreserving_skewSubLeft (μA.prod volume) volume hcx
    exact (h1.mul h2).mul h3
  -- a.e. membership in the annulus
  have haeA2 : ∀ᵐ w : InputSpace m × InputSpace m ∂(μA.prod volume),
      w.1 ∈ scaleAnnulus m ε δ :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hAmeas)
  have haeA : ∀ᵐ q : (InputSpace m × InputSpace m) × ℝ ∂((μA.prod volume).prod volume),
      q.1.1 ∈ scaleAnnulus m ε δ :=
    Measure.quasiMeasurePreserving_fst.ae haeA2
  -- integrability of the triple kernel via the skew shear transport
  have hD0int : Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (Cη * ((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
        (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) * ((1 + |q.2|) ^ k * ‖ψ q.2‖)))
      ((μA.prod volume).prod volume) := by
    have hcomp : Integrable (fun w : InputSpace m × InputSpace m =>
        (1 + ‖w.2‖) ^ k * ‖f w.2‖) (μA.prod volume) := hfk.comp_snd μA
    exact (hcomp.mul_prod hψk).const_mul _
  have hskewMP := MeasureTheory.measurePreserving_skewSubLeft (μA.prod volume)
    (volume : Measure ℝ) hcinner
  have hDint : Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (Cη * ((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
        (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) *
          ((1 + |inner ℝ q.1.1 q.1.2 - q.2|) ^ k * ‖ψ (inner ℝ q.1.1 q.1.2 - q.2)‖)))
      ((μA.prod volume).prod volume) := by
    have h := (hskewMP.integrable_comp hD0int.aestronglyMeasurable).mpr hD0int
    exact h.congr (Filter.Eventually.of_forall fun q => rfl)
  have hTint : Integrable T ((μA.prod volume).prod volume) := by
    refine hDint.mono' hTaesm ?_
    filter_upwards [haeA] with q hq
    simp only [scaleAnnulus, Set.mem_setOf_eq] at hq
    have hδ0 : 0 ≤ δ := le_trans hε.le (le_trans hq.1 hq.2)
    have hip : |inner ℝ q.1.1 x - inner ℝ q.1.1 q.1.2| ≤ δ * (‖x‖ + ‖q.1.2‖) := by
      rw [← inner_sub_right]
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have h1 : ‖x - q.1.2‖ ≤ ‖x‖ + ‖q.1.2‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (x - q.1.2), norm_nonneg q.1.1, hq.2,
        norm_nonneg x, norm_nonneg q.1.2]
    have hgrow : 1 + |inner ℝ q.1.1 x - q.2| ≤
        ((1 + δ * ‖x‖) * (1 + δ)) * (1 + ‖q.1.2‖) *
          (1 + |inner ℝ q.1.1 q.1.2 - q.2|) := by
      have h1 := one_add_abs_add_le_mul (inner ℝ q.1.1 x - inner ℝ q.1.1 q.1.2)
        (inner ℝ q.1.1 q.1.2 - q.2)
      have h2 : inner ℝ q.1.1 x - inner ℝ q.1.1 q.1.2 + (inner ℝ q.1.1 q.1.2 - q.2)
          = inner ℝ q.1.1 x - q.2 := by ring
      rw [h2] at h1
      refine le_trans h1 ?_
      have h3 : 1 + |inner ℝ q.1.1 x - inner ℝ q.1.1 q.1.2|
          ≤ (1 + δ * ‖x‖) * (1 + δ) * (1 + ‖q.1.2‖) := by
        refine le_trans (by linarith : 1 + |inner ℝ q.1.1 x - inner ℝ q.1.1 q.1.2|
          ≤ 1 + δ * (‖x‖ + ‖q.1.2‖)) ?_
        nlinarith [norm_nonneg x, norm_nonneg q.1.2, hδ0,
          mul_nonneg hδ0 (norm_nonneg x), mul_nonneg hδ0 (norm_nonneg q.1.2),
          mul_nonneg (mul_nonneg hδ0 (norm_nonneg x)) (norm_nonneg q.1.2),
          mul_nonneg (mul_nonneg hδ0 hδ0) (norm_nonneg x),
          mul_nonneg (mul_nonneg (mul_nonneg hδ0 hδ0) (norm_nonneg x)) (norm_nonneg q.1.2)]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hη' : ‖η (inner ℝ q.1.1 x - q.2)‖ ≤
        Cη * (((1 + δ * ‖x‖) * (1 + δ)) * (1 + ‖q.1.2‖) *
          (1 + |inner ℝ q.1.1 q.1.2 - q.2|)) ^ k := by
      refine (hηk _).trans (mul_le_mul_of_nonneg_left ?_ hCη)
      exact pow_le_pow_left₀ (by positivity) hgrow k
    calc ‖T q‖
        = ‖f q.1.2‖ * ‖ψ (inner ℝ q.1.1 q.1.2 - q.2)‖ * ‖η (inner ℝ q.1.1 x - q.2)‖ := by
          rw [hT_def]
          simp only [norm_mul, RCLike.norm_conj]
      _ ≤ ‖f q.1.2‖ * ‖ψ (inner ℝ q.1.1 q.1.2 - q.2)‖ *
            (Cη * (((1 + δ * ‖x‖) * (1 + δ)) * (1 + ‖q.1.2‖) *
              (1 + |inner ℝ q.1.1 q.1.2 - q.2|)) ^ k) := by
          exact mul_le_mul_of_nonneg_left hη' (by positivity)
      _ = (Cη * ((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
            (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) *
              ((1 + |inner ℝ q.1.1 q.1.2 - q.2|) ^ k *
                ‖ψ (inner ℝ q.1.1 q.1.2 - q.2)‖)) := by
          rw [mul_pow, mul_pow]
          ring
  -- ==================== the (scale, bias)-marginal bound ====================
  have hswapMP := MeasureTheory.measurePreserving_prodSwapRight μA
    (volume : Measure ℝ) (volume : Measure (InputSpace m))
  have hT2int : Integrable (fun q : (InputSpace m × ℝ) × InputSpace m =>
      T ((q.1.1, q.2), q.1.2)) ((μA.prod (volume : Measure ℝ)).prod volume) :=
    (hswapMP.integrable_comp hTaesm).mpr hTint
  have hMint : Integrable (fun p : InputSpace m × ℝ =>
      ∫ y : InputSpace m, ‖T ((p.1, y), p.2)‖) (μA.prod (volume : Measure ℝ)) :=
    hT2int.integral_norm_prod_left
  -- ==================== the truncated integrand ====================
  set G0 : RidgeletParameterSpace m → ℂ := fun p =>
    euclideanRidgeletTransform m 1 ψ f p * η (inner ℝ p.1 x - p.2) *
      ((‖p.1‖ ^ (1 : ℝ) : ℝ) : ℂ)⁻¹ with hG0_def
  have hnormmeas : Measurable fun p : InputSpace m × ℝ => ((‖p.1‖ ^ (1 : ℝ) : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact (measurable_norm.comp measurable_fst).pow measurable_const
  have hRaesm : AEStronglyMeasurable (euclideanRidgeletTransform m 1 ψ f)
      (μA.prod (volume : Measure ℝ)) := by
    have hker : AEStronglyMeasurable (fun q : (InputSpace m × ℝ) × InputSpace m =>
        f q.2 * conj (ψ (inner ℝ q.1.1 q.2 - q.1.2)) * ((‖q.1.1‖ ^ (1 : ℝ) : ℝ) : ℂ))
        ((μA.prod (volume : Measure ℝ)).prod volume) := by
      have h1 : AEStronglyMeasurable (fun q : (InputSpace m × ℝ) × InputSpace m => f q.2)
          ((μA.prod (volume : Measure ℝ)).prod volume) :=
        hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      have h2 : AEStronglyMeasurable
          (fun q : (InputSpace m × ℝ) × InputSpace m =>
            conj (ψ (inner ℝ q.1.1 q.2 - q.1.2)))
          ((μA.prod (volume : Measure ℝ)).prod volume) := by
        refine RCLike.continuous_conj.comp_aestronglyMeasurable ?_
        refine hψm.comp_quasiMeasurePreserving ?_
        exact (MeasureTheory.quasiMeasurePreserving_skewSubLeft (μA.prod volume) volume
          hcinner).comp hswapMP.quasiMeasurePreserving
      have h3 : AEStronglyMeasurable
          (fun q : (InputSpace m × ℝ) × InputSpace m => ((‖q.1.1‖ ^ (1 : ℝ) : ℝ) : ℂ))
          ((μA.prod (volume : Measure ℝ)).prod volume) :=
        (hnormmeas.comp measurable_fst).aestronglyMeasurable
      exact (h1.mul h2).mul h3
    exact hker.integral_prod_right'
  have hG0aesm : AEStronglyMeasurable G0 (μA.prod (volume : Measure ℝ)) := by
    refine (hRaesm.mul ?_).mul ?_
    · refine hηm.comp_quasiMeasurePreserving ?_
      exact MeasureTheory.quasiMeasurePreserving_skewSubLeft μA volume
        (Continuous.inner continuous_id continuous_const).measurable
    · exact hnormmeas.inv.aestronglyMeasurable
  have haeAp : ∀ᵐ p : InputSpace m × ℝ ∂(μA.prod (volume : Measure ℝ)),
      p.1 ∈ scaleAnnulus m ε δ :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hAmeas)
  have hG0int : Integrable G0 (μA.prod (volume : Measure ℝ)) := by
    refine hMint.mono' hG0aesm ?_
    filter_upwards [haeAp] with p hp
    simp only [scaleAnnulus, Set.mem_setOf_eq] at hp
    have hnε : (0 : ℝ) < ‖p.1‖ := lt_of_lt_of_le hε hp.1
    have hR : ‖euclideanRidgeletTransform m 1 ψ f p‖ ≤
        (∫ y : InputSpace m, ‖f y‖ * ‖ψ (inner ℝ p.1 y - p.2)‖) * ‖p.1‖ := by
      unfold euclideanRidgeletTransform
      refine le_trans (norm_integral_le_integral_norm _) ?_
      rw [← integral_mul_const]
      refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
      simp only []
      rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        Real.rpow_one, abs_of_pos hnε]
    have hnormval : ‖((‖p.1‖ ^ (1 : ℝ) : ℝ) : ℂ)⁻¹‖ = ‖p.1‖⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hnε]
    calc ‖G0 p‖
        = ‖euclideanRidgeletTransform m 1 ψ f p‖ * ‖η (inner ℝ p.1 x - p.2)‖ *
            ‖((‖p.1‖ ^ (1 : ℝ) : ℝ) : ℂ)⁻¹‖ := by
          rw [hG0_def]
          simp only [norm_mul]
      _ ≤ ((∫ y : InputSpace m, ‖f y‖ * ‖ψ (inner ℝ p.1 y - p.2)‖) * ‖p.1‖) *
            ‖η (inner ℝ p.1 x - p.2)‖ * ‖p.1‖⁻¹ := by
          rw [hnormval]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = (∫ y : InputSpace m, ‖f y‖ * ‖ψ (inner ℝ p.1 y - p.2)‖) *
            ‖η (inner ℝ p.1 x - p.2)‖ * (‖p.1‖ * ‖p.1‖⁻¹) := by ring
      _ = (∫ y : InputSpace m, ‖f y‖ * ‖ψ (inner ℝ p.1 y - p.2)‖) *
            ‖η (inner ℝ p.1 x - p.2)‖ := by
          rw [mul_inv_cancel₀ hnε.ne', mul_one]
      _ = ∫ y : InputSpace m, ‖T ((p.1, y), p.2)‖ := by
          rw [← integral_mul_const]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          rw [hT_def]
          simp only [norm_mul, RCLike.norm_conj]
  -- ==================== reduce the truncated transform to iterated form ====================
  have hSprod : {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}
      = (scaleAnnulus m ε δ) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [scaleAnnulus]
  have hres : ((volume : Measure (InputSpace m)).prod (volume : Measure ℝ)).restrict
      ((scaleAnnulus m ε δ) ×ˢ (Set.univ : Set ℝ)) = μA.prod (volume : Measure ℝ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  calc truncatedDualRidgeletTransform m 1 η (euclideanRidgeletTransform m 1 ψ f) ε δ x
      = ∫ p in (scaleAnnulus m ε δ) ×ˢ (Set.univ : Set ℝ), G0 p := by
        rw [truncatedDualRidgeletTransform, hSprod]
    _ = ∫ a in scaleAnnulus m ε δ, ∫ b : ℝ, G0 (a, b) := by
        rw [Measure.volume_eq_prod]
        rw [MeasureTheory.setIntegral_prod]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          rw [Measure.restrict_univ]
        · rw [MeasureTheory.IntegrableOn, hres]
          exact hG0int
    _ = ∫ a in scaleAnnulus m ε δ, ∫ r : ℝ,
          η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hAmeas] with a ha
        simp only [scaleAnnulus, Set.mem_setOf_eq] at ha
        have hnε : (0 : ℝ) < ‖a‖ := lt_of_lt_of_le hε ha.1
        have hb : ∀ b : ℝ, G0 (a, b) =
            (fun r : ℝ => η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))))
              (inner ℝ a x - b) := by
          intro b
          simp only []
          rw [hG0_def]
          simp only []
          unfold euclideanRidgeletTransform
          simp only [Real.rpow_one]
          rw [integral_mul_const]
          have hccancel : ((‖a‖ : ℝ) : ℂ) * ((‖a‖ : ℝ) : ℂ)⁻¹ = 1 :=
            mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnε.ne')
          have hη : η (inner ℝ a x - b) *
              (∫ y, f y * conj (ψ (inner ℝ a y - b)))
              = η (inner ℝ a x - b) *
                ∫ y, f y * conj (ψ ((inner ℝ a x - b) - inner ℝ a (x - y))) := by
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only []
            have harg : inner ℝ a x - b - inner ℝ a (x - y) = inner ℝ a y - b := by
              rw [inner_sub_right]
              ring
            rw [harg]
          calc (∫ y, f y * conj (ψ (inner ℝ a y - b))) * ((‖a‖ : ℝ) : ℂ) *
                η (inner ℝ a x - b) * ((‖a‖ : ℝ) : ℂ)⁻¹
              = η (inner ℝ a x - b) * (∫ y, f y * conj (ψ (inner ℝ a y - b))) *
                  (((‖a‖ : ℝ) : ℂ) * ((‖a‖ : ℝ) : ℂ)⁻¹) := by ring
            _ = η (inner ℝ a x - b) * ∫ y, f y * conj (ψ (inner ℝ a y - b)) := by
                rw [hccancel, mul_one]
            _ = η (inner ℝ a x - b) *
                  ∫ y, f y * conj (ψ ((inner ℝ a x - b) - inner ℝ a (x - y))) := hη
        calc (∫ b : ℝ, G0 (a, b))
            = ∫ b : ℝ, (fun r : ℝ =>
                η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))) (inner ℝ a x - b) :=
              integral_congr_ae (Filter.Eventually.of_forall hb)
          _ = ∫ r : ℝ, η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))) := by
              exact integral_sub_left_eq_self
                (fun r : ℝ => η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))))
                volume (inner ℝ a x)
    _ = ∫ r : ℝ, η r * truncatedReconstructionSection m ψ f x ε δ r := by
        -- the substituted kernel and the final swap
        have hskewMP2 := MeasureTheory.measurePreserving_skewSubLeft (μA.prod volume)
          (volume : Measure ℝ) hcx
        have hTtilde : Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
            T (q.1, inner ℝ q.1.1 x - q.2)) ((μA.prod volume).prod volume) :=
          (hskewMP2.integrable_comp hTaesm).mpr hTint
        have hswapMP3 := MeasureTheory.measurePreserving_prodSwapRight μA
          (volume : Measure (InputSpace m)) (volume : Measure ℝ)
        have hU0 : Integrable (fun q : (InputSpace m × ℝ) × InputSpace m =>
            T ((q.1.1, q.2), inner ℝ q.1.1 x - q.1.2))
            ((μA.prod (volume : Measure ℝ)).prod volume) := by
          have hswapMP4 := MeasureTheory.measurePreserving_prodSwapRight μA
            (volume : Measure ℝ) (volume : Measure (InputSpace m))
          exact (hswapMP4.integrable_comp hTtilde.aestronglyMeasurable).mpr hTtilde
        have hUint : Integrable (fun p : InputSpace m × ℝ =>
            ∫ y, T ((p.1, y), inner ℝ p.1 x - p.2)) (μA.prod (volume : Measure ℝ)) :=
          hU0.integral_prod_left
        have hUcongr : ∀ p : InputSpace m × ℝ,
            (∫ y, T ((p.1, y), inner ℝ p.1 x - p.2))
              = η p.2 * ∫ y, f y * conj (ψ (p.2 - inner ℝ p.1 (x - y))) := by
          intro p
          calc (∫ y, T ((p.1, y), inner ℝ p.1 x - p.2))
              = ∫ y, (f y * conj (ψ (p.2 - inner ℝ p.1 (x - y)))) * η p.2 := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
                rw [hT_def]
                simp only []
                have harg1 : inner ℝ p.1 y - (inner ℝ p.1 x - p.2)
                    = p.2 - inner ℝ p.1 (x - y) := by
                  rw [inner_sub_right]
                  ring
                have harg2 : inner ℝ p.1 x - (inner ℝ p.1 x - p.2) = p.2 := by ring
                rw [harg1, harg2]
            _ = (∫ y, f y * conj (ψ (p.2 - inner ℝ p.1 (x - y)))) * η p.2 :=
                integral_mul_const _ _
            _ = η p.2 * ∫ y, f y * conj (ψ (p.2 - inner ℝ p.1 (x - y))) := mul_comm _ _
        have hU : Integrable (Function.uncurry fun (a : InputSpace m) (r : ℝ) =>
            η r * ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))))
            (μA.prod (volume : Measure ℝ)) := by
          refine hUint.congr (Filter.Eventually.of_forall fun p => ?_)
          exact hUcongr p
        rw [MeasureTheory.integral_integral_swap hU]
        refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        simp only []
        rw [integral_const_mul]
        rfl

-- ==================== T2: the kernel layer ====================

/-! ## Weighted `L¹` membership and vanishing moments (steps T2--T3) -/

/-- Step T2 master bound: the polynomially weighted reconstruction kernel is integrable over
annulus × input × ℝ. -/
theorem integrable_weight_truncatedReconstructionKernel (m k : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (x : InputSpace m) (ε δ : ℝ) :
    Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (((1 + |q.2|) ^ k : ℝ) : ℂ) *
        (f q.1.2 * conj (ψ (q.2 - inner ℝ q.1.1 (x - q.1.2)))))
      (((volume.restrict (scaleAnnulus m ε δ)).prod volume).prod volume) := by
  classical
  have hAmeas : MeasurableSet (scaleAnnulus m ε δ) := measurableSet_scaleAnnulus m ε δ
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  haveI hμAfin : IsFiniteMeasure μA := by
    refine ⟨?_⟩
    rw [hμA_def, Measure.restrict_apply_univ]
    exact volume_scaleAnnulus_lt_top m ε δ
  have hcsub : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 (x - w.2) :=
    (Continuous.inner continuous_fst (continuous_const.sub continuous_snd)).measurable
  have haesm : AEStronglyMeasurable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (((1 + |q.2|) ^ k : ℝ) : ℂ) *
        (f q.1.2 * conj (ψ (q.2 - inner ℝ q.1.1 (x - q.1.2)))))
      ((μA.prod volume).prod volume) := by
    have h0 : AEStronglyMeasurable (fun q : (InputSpace m × InputSpace m) × ℝ =>
        (((1 + |q.2|) ^ k : ℝ) : ℂ)) ((μA.prod volume).prod volume) := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have h1 : AEStronglyMeasurable (fun q : (InputSpace m × InputSpace m) × ℝ => f q.1.2)
        ((μA.prod volume).prod volume) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst)
    have h2 : AEStronglyMeasurable (fun q : (InputSpace m × InputSpace m) × ℝ =>
        conj (ψ (q.2 - inner ℝ q.1.1 (x - q.1.2)))) ((μA.prod volume).prod volume) := by
      refine RCLike.continuous_conj.comp_aestronglyMeasurable ?_
      refine hψm.comp_quasiMeasurePreserving ?_
      exact MeasureTheory.quasiMeasurePreserving_skewSubRight (μA.prod volume) volume hcsub
    exact h0.mul (h1.mul h2)
  have hshearMP := MeasureTheory.measurePreserving_skewSubRight (μA.prod volume)
    (volume : Measure ℝ) hcsub
  have hD0 : Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
        (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) * ((1 + |q.2|) ^ k * ‖ψ q.2‖)))
      ((μA.prod volume).prod volume) := by
    have hcomp : Integrable (fun w : InputSpace m × InputSpace m =>
        (1 + ‖w.2‖) ^ k * ‖f w.2‖) (μA.prod volume) := hfk.comp_snd μA
    exact (hcomp.mul_prod hψk).const_mul _
  have hD : Integrable (fun q : (InputSpace m × InputSpace m) × ℝ =>
      (((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
        (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) *
          ((1 + |q.2 - inner ℝ q.1.1 (x - q.1.2)|) ^ k *
            ‖ψ (q.2 - inner ℝ q.1.1 (x - q.1.2))‖)))
      ((μA.prod volume).prod volume) := by
    have h := (hshearMP.integrable_comp hD0.aestronglyMeasurable).mpr hD0
    exact h.congr (Filter.Eventually.of_forall fun q => rfl)
  refine hD.mono' haesm ?_
  have haeA : ∀ᵐ q : (InputSpace m × InputSpace m) × ℝ ∂((μA.prod volume).prod volume),
      q.1.1 ∈ scaleAnnulus m ε δ :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hAmeas))
  filter_upwards [haeA] with q hq
  simp only [scaleAnnulus, Set.mem_setOf_eq] at hq
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg q.1.1) hq.2
  have hip : |inner ℝ q.1.1 (x - q.1.2)| ≤ δ * (‖x‖ + ‖q.1.2‖) := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have h1 : ‖x - q.1.2‖ ≤ ‖x‖ + ‖q.1.2‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (x - q.1.2), norm_nonneg q.1.1, hq.2,
      norm_nonneg x, norm_nonneg q.1.2]
  have hgrow : 1 + |q.2| ≤ ((1 + δ * ‖x‖) * (1 + δ)) * (1 + ‖q.1.2‖) *
      (1 + |q.2 - inner ℝ q.1.1 (x - q.1.2)|) := by
    have h1 := one_add_abs_add_le_mul (inner ℝ q.1.1 (x - q.1.2))
      (q.2 - inner ℝ q.1.1 (x - q.1.2))
    have h2 : inner ℝ q.1.1 (x - q.1.2) + (q.2 - inner ℝ q.1.1 (x - q.1.2)) = q.2 := by
      ring
    rw [h2] at h1
    refine le_trans h1 ?_
    have h3 : 1 + |inner ℝ q.1.1 (x - q.1.2)|
        ≤ (1 + δ * ‖x‖) * (1 + δ) * (1 + ‖q.1.2‖) := by
      refine le_trans (by linarith : (1 : ℝ) + |inner ℝ q.1.1 (x - q.1.2)|
        ≤ 1 + δ * (‖x‖ + ‖q.1.2‖)) ?_
      nlinarith [norm_nonneg x, norm_nonneg q.1.2, hδ0,
        mul_nonneg hδ0 (norm_nonneg x), mul_nonneg hδ0 (norm_nonneg q.1.2),
        mul_nonneg (mul_nonneg hδ0 (norm_nonneg x)) (norm_nonneg q.1.2),
        mul_nonneg (mul_nonneg hδ0 hδ0) (norm_nonneg x),
        mul_nonneg (mul_nonneg (mul_nonneg hδ0 hδ0) (norm_nonneg x)) (norm_nonneg q.1.2)]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  calc ‖(((1 + |q.2|) ^ k : ℝ) : ℂ) *
        (f q.1.2 * conj (ψ (q.2 - inner ℝ q.1.1 (x - q.1.2))))‖
      = (1 + |q.2|) ^ k *
          (‖f q.1.2‖ * ‖ψ (q.2 - inner ℝ q.1.1 (x - q.1.2))‖) := by
        rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |q.2|) ^ k)]
    _ ≤ (((1 + δ * ‖x‖) * (1 + δ)) * (1 + ‖q.1.2‖) *
          (1 + |q.2 - inner ℝ q.1.1 (x - q.1.2)|)) ^ k *
          (‖f q.1.2‖ * ‖ψ (q.2 - inner ℝ q.1.1 (x - q.1.2))‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hgrow k
    _ = (((1 + δ * ‖x‖) * (1 + δ)) ^ k) *
          (((1 + ‖q.1.2‖) ^ k * ‖f q.1.2‖) *
            ((1 + |q.2 - inner ℝ q.1.1 (x - q.1.2)|) ^ k *
              ‖ψ (q.2 - inner ℝ q.1.1 (x - q.1.2))‖)) := by
        rw [mul_pow, mul_pow]
        ring

/-- The reconstruction section is a.e. strongly measurable (step T2). -/
theorem aestronglyMeasurable_truncatedReconstructionSection (m : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψm : AEStronglyMeasurable ψ volume)
    (x : InputSpace m) (ε δ : ℝ) :
    AEStronglyMeasurable (truncatedReconstructionSection m ψ f x ε δ) volume := by
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  have hcsub : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 (x - w.2) :=
    (Continuous.inner continuous_fst (continuous_const.sub continuous_snd)).measurable
  have hker : AEStronglyMeasurable (fun q : (ℝ × InputSpace m) × InputSpace m =>
      f q.2 * conj (ψ (q.1.1 - inner ℝ q.1.2 (x - q.2))))
      (((volume : Measure ℝ).prod μA).prod volume) := by
    have h1 : AEStronglyMeasurable (fun q : (ℝ × InputSpace m) × InputSpace m => f q.2)
        (((volume : Measure ℝ).prod μA).prod volume) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
    have hm1 : MeasurePreserving
        (Prod.map (Prod.swap : ℝ × InputSpace m → InputSpace m × ℝ)
          (id : InputSpace m → InputSpace m))
        (((volume : Measure ℝ).prod μA).prod volume)
        ((μA.prod (volume : Measure ℝ)).prod volume) :=
      Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
    have hm2 := MeasureTheory.measurePreserving_prodSwapRight μA
      (volume : Measure ℝ) (volume : Measure (InputSpace m))
    have he := MeasureTheory.quasiMeasurePreserving_skewSubRight
      (μA.prod (volume : Measure (InputSpace m))) (volume : Measure ℝ) hcsub
    have hqmp := he.comp (hm2.quasiMeasurePreserving.comp hm1.quasiMeasurePreserving)
    exact h1.mul (RCLike.continuous_conj.comp_aestronglyMeasurable
      (hψm.comp_quasiMeasurePreserving hqmp))
  have hF : AEStronglyMeasurable (fun p : ℝ × InputSpace m =>
      ∫ y, f y * conj (ψ (p.1 - inner ℝ p.2 (x - y)))) ((volume : Measure ℝ).prod μA) :=
    hker.integral_prod_right'
  exact hF.integral_prod_right'

/-- The reconstruction section lies in the polynomially weighted `L¹` (step T2). -/
theorem integrable_weight_truncatedReconstructionSection (m k : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (x : InputSpace m) (ε δ : ℝ) :
    Integrable (fun r : ℝ =>
      (1 + |r|) ^ k * ‖truncatedReconstructionSection m ψ f x ε δ r‖) volume := by
  classical
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  have hK0 := integrable_weight_truncatedReconstructionKernel m k hf hfk hψm hψk x ε δ
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := μA.prod (volume : Measure (InputSpace m)))
  have hK : Integrable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      (((1 + |p.1|) ^ k : ℝ) : ℂ) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) := by
    have h := (hswap.integrable_comp hK0.aestronglyMeasurable).mpr hK0
    exact h
  have hN : Integrable (fun r : ℝ => ∫ w : InputSpace m × InputSpace m,
      ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
        (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))‖ ∂(μA.prod volume)) volume :=
    hK.integral_norm_prod_left
  have hsec : ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      Integrable (fun w : InputSpace m × InputSpace m =>
        (((1 + |r|) ^ k : ℝ) : ℂ) *
          (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))) (μA.prod volume) :=
    hK.prod_right_ae
  have hΞm := aestronglyMeasurable_truncatedReconstructionSection m hf hψm x ε δ
  refine hN.mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun r : ℝ =>
      (1 + |r|) ^ k)).aestronglyMeasurable.mul hΞm.norm
  · filter_upwards [hsec] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    -- step 1: the outer integral bound
    have h1 : ‖truncatedReconstructionSection m ψ f x ε δ r‖
        ≤ ∫ a, ‖∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))‖ ∂μA :=
      norm_integral_le_integral_norm _
    -- step 2: the per-scale bound against the section marginal
    have hrnorm : Integrable (fun w : InputSpace m × InputSpace m =>
        ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
          (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))‖) (μA.prod volume) := hr.norm
    have hmarg : Integrable (fun a : InputSpace m => ∫ y : InputSpace m,
        ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
          (f y * conj (ψ (r - inner ℝ a (x - y))))‖) μA :=
      hr.integral_norm_prod_left
    have h2 : (∫ a, (1 + |r|) ^ k *
        ‖∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))‖ ∂μA)
        ≤ ∫ a, (∫ y : InputSpace m,
          ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
            (f y * conj (ψ (r - inner ℝ a (x - y))))‖) ∂μA := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => by positivity)
        hmarg (Filter.Eventually.of_forall fun a => ?_)
      simp only []
      have h3 : (1 + |r|) ^ k * ‖∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))‖
          = ‖∫ y, (((1 + |r|) ^ k : ℝ) : ℂ) *
              (f y * conj (ψ (r - inner ℝ a (x - y))))‖ := by
        rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |r|) ^ k)]
      rw [h3]
      exact norm_integral_le_integral_norm _
    -- step 3: iterated equals joint for the norm kernel
    have h4 : (∫ a, (∫ y : InputSpace m,
        ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
          (f y * conj (ψ (r - inner ℝ a (x - y))))‖) ∂μA)
        = ∫ w : InputSpace m × InputSpace m,
          ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
            (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))‖ ∂(μA.prod volume) :=
      MeasureTheory.integral_integral hrnorm
    calc (1 + |r|) ^ k * ‖truncatedReconstructionSection m ψ f x ε δ r‖
        ≤ (1 + |r|) ^ k *
            ∫ a, ‖∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))‖ ∂μA := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ∫ a, (1 + |r|) ^ k *
            ‖∫ y, f y * conj (ψ (r - inner ℝ a (x - y)))‖ ∂μA :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ a, (∫ y : InputSpace m,
            ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
              (f y * conj (ψ (r - inner ℝ a (x - y))))‖) ∂μA := h2
      _ = ∫ w : InputSpace m × InputSpace m,
            ‖(((1 + |r|) ^ k : ℝ) : ℂ) *
              (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))‖ ∂(μA.prod volume) := h4

/-- **Step T3 of the reconstruction plan**: the reconstruction section inherits the vanishing
moments of the ridgelet function, `∫ r^j Ξ_{x,ε,δ}(r) dr = 0` for every `j ≤ k`. This is the
integrated form of `integral_pow_mul_conj_comp_sub_eq_zero`: after a Fubini swap through the
weighted master kernel, every fiber `∫ r^j conj (ψ (r - c)) dr` vanishes. Together with the
weighted-`L¹` membership this places `Ξ` in the domain of the pairing extension
`hasFourierAwayFromOrigin_pairing_extension`. -/
theorem integral_pow_mul_truncatedReconstructionSection_eq_zero (m k : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    (x : InputSpace m) (ε δ : ℝ) {j : ℕ} (hj : j ≤ k) :
    (∫ r : ℝ, (r : ℂ) ^ j * truncatedReconstructionSection m ψ f x ε δ r) = 0 := by
  classical
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  have hcsub : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 (x - w.2) :=
    (Continuous.inner continuous_fst (continuous_const.sub continuous_snd)).measurable
  -- the master kernel in the (bias, (scale, input)) order
  have hK0 := integrable_weight_truncatedReconstructionKernel m k hf hfk hψm hψk x ε δ
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := μA.prod (volume : Measure (InputSpace m)))
  have hK : Integrable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      (((1 + |p.1|) ^ k : ℝ) : ℂ) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) :=
    (hswap.integrable_comp hK0.aestronglyMeasurable).mpr hK0
  -- the monomial kernel
  have hMaesm : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      (p.1 : ℂ) ^ j * (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) := by
    have h0 : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
        (p.1 : ℂ) ^ j) ((volume : Measure ℝ).prod (μA.prod volume)) := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × (InputSpace m × InputSpace m) => f p.2.2)
        ((volume : Measure ℝ).prod (μA.prod volume)) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd)
    have h2 : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
        conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))
        ((volume : Measure ℝ).prod (μA.prod volume)) := by
      refine RCLike.continuous_conj.comp_aestronglyMeasurable ?_
      refine hψm.comp_quasiMeasurePreserving ?_
      have he := MeasureTheory.quasiMeasurePreserving_skewSubRight
        (μA.prod (volume : Measure (InputSpace m))) (volume : Measure ℝ) hcsub
      exact he.comp (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := μA.prod (volume : Measure (InputSpace m)))).quasiMeasurePreserving
    exact h0.mul (h1.mul h2)
  have hM : Integrable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      (p.1 : ℂ) ^ j * (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) := by
    refine hK.norm.mono' hMaesm (Filter.Eventually.of_forall fun p => ?_)
    have hL : ‖(p.1 : ℂ) ^ j *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))‖
        = |p.1| ^ j * ‖f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hR : ‖(((1 + |p.1|) ^ k : ℝ) : ℂ) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))‖
        = (1 + |p.1|) ^ k *
          ‖f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |p.1|) ^ k)]
    rw [hL, hR]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |p.1| ^ j ≤ (1 + |p.1|) ^ j :=
          pow_le_pow_left₀ (abs_nonneg p.1) (le_add_of_nonneg_left zero_le_one) j
      _ ≤ (1 + |p.1|) ^ k :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg p.1)) hj
  have hsec : ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      Integrable (fun w : InputSpace m × InputSpace m =>
        (r : ℂ) ^ j * (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))))
      (μA.prod volume) := hM.prod_right_ae
  -- assemble
  calc (∫ r : ℝ, (r : ℂ) ^ j * truncatedReconstructionSection m ψ f x ε δ r)
      = ∫ r : ℝ, ∫ w : InputSpace m × InputSpace m,
          (r : ℂ) ^ j * (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))
          ∂(μA.prod volume) := by
        refine integral_congr_ae ?_
        filter_upwards [hsec] with r hr
        calc (r : ℂ) ^ j * truncatedReconstructionSection m ψ f x ε δ r
            = ∫ a, (r : ℂ) ^ j *
                ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))) ∂volume ∂μA :=
              (integral_const_mul _ _).symm
          _ = ∫ a, ∫ y, (r : ℂ) ^ j *
                (f y * conj (ψ (r - inner ℝ a (x - y)))) ∂volume ∂μA := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
              simp only []
              exact (integral_const_mul _ _).symm
          _ = ∫ w : InputSpace m × InputSpace m,
                (r : ℂ) ^ j * (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))
                ∂(μA.prod volume) :=
              MeasureTheory.integral_integral hr
    _ = ∫ w : InputSpace m × InputSpace m, ∫ r : ℝ,
          (r : ℂ) ^ j * (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))
          ∂(volume : Measure ℝ) ∂(μA.prod volume) :=
        MeasureTheory.integral_integral_swap hM
    _ = ∫ w : InputSpace m × InputSpace m, (0 : ℂ) ∂(μA.prod volume) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only []
        calc (∫ r : ℝ, (r : ℂ) ^ j *
              (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))))
            = f w.2 * ∫ r : ℝ, (r : ℂ) ^ j *
                conj (ψ (r - inner ℝ w.1 (x - w.2))) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
              ring
          _ = 0 := by
              rw [integral_pow_mul_conj_comp_sub_eq_zero hψm hψk hψvm hj
                (inner ℝ w.1 (x - w.2)), mul_zero]
    _ = 0 := integral_zero _ _

/-! ## The spectral factor and the Fourier data of the section -/

/-- The spectral factor `H_{x,ε,δ}(ζ) = ∫_{ε≤‖a‖≤δ} f̂(ζa) e^{iζ⟨a,x⟩} da` of the
truncated reconstruction (step T2). -/
def truncatedSpectralFactor (m : ℕ) (f : InputSpace m → ℂ) (x : InputSpace m)
    (ε δ : ℝ) : ℝ → ℂ :=
  fun ζ => ∫ a in scaleAnnulus m ε δ,
    Fourier.angularFourierIntegralInner f (ζ • a) *
      Complex.exp (Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ))

set_option maxHeartbeats 800000 in
-- The proof is a single long assembly of Fubini swaps and oscillatory-integral evaluations.
/-- Fourier representation of the reconstruction section (step T2):
`Ξ̂(ζ) = conj (ψ̂(-ζ)) ⋅ H(-ζ)`. -/
theorem angularFourier1D_truncatedReconstructionSection (m k : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (x : InputSpace m) (ε δ : ℝ) (ζ : ℝ) :
    angularFourier1D (truncatedReconstructionSection m ψ f x ε δ) ζ
      = conj (angularFourier1D ψ (-ζ)) * truncatedSpectralFactor m f x ε δ (-ζ) := by
  classical
  set μA : Measure (InputSpace m) := volume.restrict (scaleAnnulus m ε δ) with hμA_def
  haveI hμAfin : IsFiniteMeasure μA := by
    refine ⟨?_⟩
    rw [hμA_def, Measure.restrict_apply_univ]
    exact volume_scaleAnnulus_lt_top m ε δ
  have hinner_mul : ∀ a c : ℝ, (inner ℝ a c : ℝ) = a * c := by
    intro a c
    rw [RCLike.inner_apply, conj_trivial]
    ring
  have hcsub : Measurable fun w : InputSpace m × InputSpace m => inner ℝ w.1 (x - w.2) :=
    (Continuous.inner continuous_fst (continuous_const.sub continuous_snd)).measurable
  have hcsubc : Continuous fun w : InputSpace m × InputSpace m => inner ℝ w.1 (x - w.2) :=
    Continuous.inner continuous_fst (continuous_const.sub continuous_snd)
  -- the weighted kernel in the (bias, (scale, input)) order
  have hK0 := integrable_weight_truncatedReconstructionKernel m k hf hfk hψm hψk x ε δ
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := μA.prod (volume : Measure (InputSpace m)))
  have hK : Integrable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      (((1 + |p.1|) ^ k : ℝ) : ℂ) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) :=
    (hswap.integrable_comp hK0.aestronglyMeasurable).mpr hK0
  -- the oscillatory kernel
  have hEaesm : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      Complex.exp (-Complex.I * ((inner ℝ p.1 ζ : ℝ) : ℂ)) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) := by
    have h0 : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
        Complex.exp (-Complex.I * ((inner ℝ p.1 ζ : ℝ) : ℂ)))
        ((volume : Measure ℝ).prod (μA.prod volume)) := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have h1 : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) => f p.2.2)
        ((volume : Measure ℝ).prod (μA.prod volume)) :=
      hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd)
    have h2 : AEStronglyMeasurable (fun p : ℝ × (InputSpace m × InputSpace m) =>
        conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))
        ((volume : Measure ℝ).prod (μA.prod volume)) := by
      refine RCLike.continuous_conj.comp_aestronglyMeasurable ?_
      refine hψm.comp_quasiMeasurePreserving ?_
      have he := MeasureTheory.quasiMeasurePreserving_skewSubRight
        (μA.prod (volume : Measure (InputSpace m))) (volume : Measure ℝ) hcsub
      exact he.comp (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := μA.prod (volume : Measure (InputSpace m)))).quasiMeasurePreserving
    exact h0.mul (h1.mul h2)
  have hE : Integrable (fun p : ℝ × (InputSpace m × InputSpace m) =>
      Complex.exp (-Complex.I * ((inner ℝ p.1 ζ : ℝ) : ℂ)) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))))
      ((volume : Measure ℝ).prod (μA.prod volume)) := by
    refine hK.norm.mono' hEaesm (Filter.Eventually.of_forall fun p => ?_)
    have hre : (-Complex.I * ((inner ℝ p.1 ζ : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    have hL : ‖Complex.exp (-Complex.I * ((inner ℝ p.1 ζ : ℝ) : ℂ)) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))‖
        = ‖f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))‖ := by
      rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
    have hR : ‖(((1 + |p.1|) ^ k : ℝ) : ℂ) *
        (f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2))))‖
        = (1 + |p.1|) ^ k *
          ‖f p.2.2 * conj (ψ (p.1 - inner ℝ p.2.1 (x - p.2.2)))‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |p.1|) ^ k)]
    rw [hL, hR]
    have h1 : (1 : ℝ) ≤ (1 + |p.1|) ^ k :=
      one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg p.1))
    exact le_mul_of_one_le_left (norm_nonneg _) h1
  have hsecE : ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      Integrable (fun w : InputSpace m × InputSpace m =>
        Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
          (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2))))) (μA.prod volume) :=
    hE.prod_right_ae
  -- the fiber Fourier computation
  have hfiber : ∀ w : InputSpace m × InputSpace m,
      (∫ r : ℝ, Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
        (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))))
        = conj (angularFourier1D ψ (-ζ)) *
          (f w.2 * Complex.exp (-Complex.I *
            ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))) := by
    intro w
    have hconj : (∫ s : ℝ, Complex.exp (-Complex.I * ((s * ζ : ℝ) : ℂ)) * conj (ψ s))
        = conj (angularFourier1D ψ (-ζ)) := by
      rw [angularFourier1D, Fourier.angularFourierIntegralInner, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only []
      rw [map_mul]
      congr 1
      rw [← Complex.exp_conj]
      congr 1
      rw [hinner_mul]
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    calc (∫ r : ℝ, Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
          (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))))
        = ∫ s : ℝ, (fun r : ℝ => Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
            (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))))
              (s + inner ℝ w.1 (x - w.2)) := by
          exact (MeasureTheory.integral_add_right_eq_self _ (inner ℝ w.1 (x - w.2))).symm
      _ = ∫ s : ℝ, (f w.2 * Complex.exp (-Complex.I *
            ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))) *
            (Complex.exp (-Complex.I * ((s * ζ : ℝ) : ℂ)) * conj (ψ s)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          simp only []
          rw [hinner_mul]
          have harg : s + inner ℝ w.1 (x - w.2) - inner ℝ w.1 (x - w.2) = s := by ring
          rw [harg]
          have hexp : Complex.exp (-Complex.I *
              (((s + inner ℝ w.1 (x - w.2)) * ζ : ℝ) : ℂ))
              = Complex.exp (-Complex.I * ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ((s * ζ : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp]
          ring
      _ = (f w.2 * Complex.exp (-Complex.I *
            ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))) *
            ∫ s : ℝ, Complex.exp (-Complex.I * ((s * ζ : ℝ) : ℂ)) * conj (ψ s) :=
          integral_const_mul _ _
      _ = conj (angularFourier1D ψ (-ζ)) *
            (f w.2 * Complex.exp (-Complex.I *
              ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))) := by
          rw [hconj]
          ring
  -- the input-side integrability for the de-jointification
  have hfexp : Integrable (fun w : InputSpace m × InputSpace m =>
      f w.2 * Complex.exp (-Complex.I * ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ)))
      (μA.prod volume) := by
    have hdom : Integrable (fun w : InputSpace m × InputSpace m => ‖f w.2‖)
        (μA.prod volume) := hf.norm.comp_snd μA
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      · refine Continuous.aestronglyMeasurable ?_
        exact Complex.continuous_exp.comp (by fun_prop :
          Continuous fun w : InputSpace m × InputSpace m =>
            -Complex.I * ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))
    · rw [norm_mul, Complex.norm_exp]
      have hre : (-Complex.I * ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero, mul_one]
  -- assemble
  calc angularFourier1D (truncatedReconstructionSection m ψ f x ε δ) ζ
      = ∫ r : ℝ, ∫ w : InputSpace m × InputSpace m,
          Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
            (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))) ∂(μA.prod volume) := by
        rw [angularFourier1D, Fourier.angularFourierIntegralInner]
        refine integral_congr_ae ?_
        filter_upwards [hsecE] with r hr
        calc Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
              truncatedReconstructionSection m ψ f x ε δ r
            = ∫ a, Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
                ∫ y, f y * conj (ψ (r - inner ℝ a (x - y))) ∂volume ∂μA :=
              (integral_const_mul _ _).symm
          _ = ∫ a, ∫ y, Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
                (f y * conj (ψ (r - inner ℝ a (x - y)))) ∂volume ∂μA := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
              simp only []
              exact (integral_const_mul _ _).symm
          _ = ∫ w : InputSpace m × InputSpace m,
                Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
                  (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))) ∂(μA.prod volume) :=
              MeasureTheory.integral_integral hr
    _ = ∫ w : InputSpace m × InputSpace m, ∫ r : ℝ,
          Complex.exp (-Complex.I * ((inner ℝ r ζ : ℝ) : ℂ)) *
            (f w.2 * conj (ψ (r - inner ℝ w.1 (x - w.2)))) ∂(volume : Measure ℝ)
          ∂(μA.prod volume) :=
        MeasureTheory.integral_integral_swap hE
    _ = conj (angularFourier1D ψ (-ζ)) * ∫ w : InputSpace m × InputSpace m,
          f w.2 * Complex.exp (-Complex.I * ((inner ℝ w.1 (x - w.2) * ζ : ℝ) : ℂ))
          ∂(μA.prod volume) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only []
        rw [hfiber w]
    _ = conj (angularFourier1D ψ (-ζ)) * ∫ a, ∫ y,
          f y * Complex.exp (-Complex.I * ((inner ℝ a (x - y) * ζ : ℝ) : ℂ))
          ∂volume ∂μA := by
        congr 1
        exact (MeasureTheory.integral_integral (f := fun (a : InputSpace m)
          (y : InputSpace m) => f y * Complex.exp (-Complex.I *
            ((inner ℝ a (x - y) * ζ : ℝ) : ℂ))) hfexp).symm
    _ = conj (angularFourier1D ψ (-ζ)) * truncatedSpectralFactor m f x ε δ (-ζ) := by
        congr 1
        rw [truncatedSpectralFactor]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only []
        have hsplit : ∀ y : InputSpace m,
            Complex.exp (-Complex.I * ((inner ℝ a (x - y) * ζ : ℝ) : ℂ))
              = Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ((inner ℝ y ((-ζ) • a) : ℝ) : ℂ)) := by
          intro y
          rw [← Complex.exp_add]
          congr 1
          rw [inner_sub_right, real_inner_smul_right, real_inner_comm y a]
          push_cast
          ring
        calc (∫ y, f y *
              Complex.exp (-Complex.I * ((inner ℝ a (x - y) * ζ : ℝ) : ℂ)))
            = ∫ y, Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ)) *
                (Complex.exp (-Complex.I * ((inner ℝ y ((-ζ) • a) : ℝ) : ℂ)) * f y) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              simp only []
              rw [hsplit y]
              ring
          _ = Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ)) *
                ∫ y, Complex.exp (-Complex.I * ((inner ℝ y ((-ζ) • a) : ℝ) : ℂ)) * f y :=
              integral_const_mul _ _
          _ = Fourier.angularFourierIntegralInner f ((-ζ) • a) *
                Complex.exp (Complex.I * ((-ζ * inner ℝ a x : ℝ) : ℂ)) := by
              rw [Fourier.angularFourierIntegralInner]
              have hexp2 : Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ))
                  = Complex.exp (Complex.I * ((-ζ * inner ℝ a x : ℝ) : ℂ)) := by
                congr 1
                push_cast
                ring
              rw [hexp2]
              ring

/-- Uniform bound of the spectral factor by the signal mass (step T2). -/
theorem norm_truncatedSpectralFactor_le (m : ℕ) (f : InputSpace m → ℂ)
    (x : InputSpace m) (ε δ : ℝ) (ζ : ℝ) :
    ‖truncatedSpectralFactor m f x ε δ ζ‖
      ≤ (∫ y, ‖f y‖) * (volume (scaleAnnulus m ε δ)).toReal := by
  have hfhat_bound : ∀ ξ : InputSpace m,
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
  rw [truncatedSpectralFactor]
  refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (volume_scaleAnnulus_lt_top m ε δ) fun a _ => ?_
  rw [norm_mul, Complex.norm_exp]
  have hre : (Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]
  exact hfhat_bound _

/-- Dilation bound of the spectral factor by the spectral mass (step T2):
`‖H(ζ)‖ ≤ |ζ|⁻ᵐ ‖f̂‖₁` for `ζ ≠ 0`. -/
theorem norm_truncatedSpectralFactor_le_of_ne (m : ℕ) {f : InputSpace m → ℂ}
    (hfhat : Integrable (Fourier.angularFourierIntegralInner f) volume)
    (x : InputSpace m) (ε δ : ℝ) {ζ : ℝ} (hζ : ζ ≠ 0) :
    ‖truncatedSpectralFactor m f x ε δ ζ‖
      ≤ |ζ|⁻¹ ^ m * ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := by
  have h1 : ‖truncatedSpectralFactor m f x ε δ ζ‖
      ≤ ∫ a in scaleAnnulus m ε δ, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ := by
    rw [truncatedSpectralFactor]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_))
    simp only []
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * ((ζ * inner ℝ a x : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  have hglob : Integrable (fun a : InputSpace m =>
      ‖Fourier.angularFourierIntegralInner f (ζ • a)‖) volume :=
    (MeasureTheory.integrable_comp_smul_iff (volume : Measure (InputSpace m))
      (fun ξ => ‖Fourier.angularFourierIntegralInner f ξ‖) hζ).mpr hfhat.norm
  have h2 : (∫ a in scaleAnnulus m ε δ, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖)
      ≤ ∫ a : InputSpace m, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ :=
    setIntegral_le_integral hglob (Filter.Eventually.of_forall fun a => norm_nonneg _)
  have h3 : (∫ a : InputSpace m, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖)
      = |ζ|⁻¹ ^ m * ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := by
    have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume :
      Measure (InputSpace m))) (fun ξ => ‖Fourier.angularFourierIntegralInner f ξ‖) ζ
    rw [h, smul_eq_mul]
    congr 1
    rw [abs_inv, abs_pow]
    rw [show Module.finrank ℝ (InputSpace m) = m from finrank_euclideanSpace_fin]
    rw [inv_pow]
  calc ‖truncatedSpectralFactor m f x ε δ ζ‖
      ≤ ∫ a in scaleAnnulus m ε δ, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ := h1
    _ ≤ ∫ a : InputSpace m, ‖Fourier.angularFourierIntegralInner f (ζ • a)‖ := h2
    _ = |ζ|⁻¹ ^ m * ∫ ξ, ‖Fourier.angularFourierIntegralInner f ξ‖ := h3

end LeanRidgelet
