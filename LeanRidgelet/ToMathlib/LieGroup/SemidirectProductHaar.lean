/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.WithDensity
public import LeanRidgelet.ToMathlib.LieGroup.TopologicalSemidirectProduct

/-!
# Haar measure of a topological semidirect product

Left Haar measure of a semidirect product `N ⋊[φ] G` is a product measure: Haar measure of `N`
times a *relatively* invariant measure on `G`, the correction being exactly the factor by which the
action of `G` rescales Haar measure of `N`. Left translation by a fixed element acts on the product
coordinates separately — the linear coordinate of the translation is fixed — so the invariance proof
is `MeasureTheory.Measure.map_prod_map` together with the two coordinate computations.

## Main results

* `MeasureTheory.map_mul_left_withDensity_monoidHom`: twisting a left-invariant measure by a
  multiplicative character makes left translation rescale it by the character. This produces the
  relatively invariant measure on `G`.
* `SemidirectProduct.prodMeasure`: the product measure transported to the semidirect product.
* `SemidirectProduct.isHaarMeasure_prodMeasure`: it is a Haar measure.
* `SemidirectProduct.exists_haar_eq_smul_prodMeasure`: the canonical Haar measure of the semidirect
  product is a positive multiple of it.
* `SemidirectProduct.exists_map_right_haar_restrict_le`: on a compact set, the image of Haar measure
  under the projection to `G` is dominated by the relatively invariant measure. This is the estimate
  that a quotient-integral bound for an induced representation needs.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory

/-- Twisting a left-invariant measure by a multiplicative character rescales left translation by the
character of the translating element.  No positivity or finiteness of the character is needed: the
scaling factor is written as the value at the inverse. -/
theorem map_mul_left_withDensity_monoidHom {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [ContinuousMul G] (κ : Measure G)
    [κ.IsMulLeftInvariant] (χ : G →* ℝ≥0∞) (hχ : Measurable χ) (g₀ : G) :
    Measure.map (fun g ↦ g₀ * g) (κ.withDensity χ) = χ g₀⁻¹ • κ.withDensity χ := by
  have hmeasurable : Measurable (fun g : G ↦ g₀ * g) := (continuous_const_mul g₀).measurable
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hmeasurable hs, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (hmeasurable hs), withDensity_apply _ hs]
  have hshift : ∀ g : G, χ g = χ g₀⁻¹ * χ (g₀ * g) := by
    intro g
    rw [← map_mul]
    congr 1
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  calc
    ∫⁻ g in (fun g : G ↦ g₀ * g) ⁻¹' s, χ g ∂κ =
        ∫⁻ g in (fun g : G ↦ g₀ * g) ⁻¹' s, χ g₀⁻¹ * χ (g₀ * g) ∂κ :=
      lintegral_congr fun g ↦ hshift g
    _ = χ g₀⁻¹ * ∫⁻ g in (fun g : G ↦ g₀ * g) ⁻¹' s, χ (g₀ * g) ∂κ :=
      lintegral_const_mul _ (hχ.comp hmeasurable)
    _ = χ g₀⁻¹ * ∫⁻ g in s, χ g ∂(Measure.map (fun g : G ↦ g₀ * g) κ) := by
      congr 1
      exact (setLIntegral_map hs hχ hmeasurable).symm
    _ = χ g₀⁻¹ * ∫⁻ g in s, χ g ∂κ := by
      rw [map_mul_left_eq_self]

/-- A measure with a density bounded on a set is dominated there by a multiple of the original
measure.  This converts a relatively invariant twisted measure back to Haar measure on compact
sets, where the twisting character is bounded. -/
theorem withDensity_restrict_le_smul_restrict {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ≥0∞} {s : Set X} (hs : MeasurableSet s) {C : ℝ≥0∞}
    (hC : ∀ x ∈ s, f x ≤ C) :
    (μ.withDensity f).restrict s ≤ C • μ.restrict s := by
  rw [Measure.le_iff]
  intro t ht
  calc
    (μ.withDensity f).restrict s t = ∫⁻ x in t ∩ s, f x ∂μ := by
      rw [Measure.restrict_apply ht, withDensity_apply _ (ht.inter hs)]
    _ ≤ ∫⁻ _ in t ∩ s, C ∂μ :=
      setLIntegral_mono' (ht.inter hs) fun x hx ↦ hC x hx.2
    _ = C * μ (t ∩ s) := by rw [setLIntegral_const]
    _ = (C • μ.restrict s) t := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht]

end MeasureTheory

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] [TopologicalSpace N] [TopologicalSpace G]
  [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology N] [SecondCountableTopology G]
  (φ : G →* MulAut N) (ν : Measure N) (lam : Measure G)

/-- The product measure of a measure on `N` and a measure on `G`, transported to the semidirect
product through the canonical product homeomorphism. -/
def prodMeasure : Measure (N ⋊[φ] G) :=
  Measure.map (homeomorphProd φ).symm (ν.prod lam)

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [SecondCountableTopology N] in
theorem measurable_homeomorphProd_symm :
    Measurable ((homeomorphProd φ).symm : N × G → N ⋊[φ] G) :=
  (homeomorphProd φ).symm.continuous.measurable

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [SecondCountableTopology N] in
theorem measurable_homeomorphProd :
    Measurable (homeomorphProd φ : N ⋊[φ] G → N × G) :=
  (homeomorphProd φ).continuous.measurable

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [SecondCountableTopology N] in
theorem prodMeasure_apply [SFinite lam] {s : Set (N ⋊[φ] G)} (hs : MeasurableSet s) :
    prodMeasure φ ν lam s = (ν.prod lam) ((homeomorphProd φ).symm ⁻¹' s) := by
  rw [prodMeasure, Measure.map_apply (measurable_homeomorphProd_symm φ) hs]

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology N] [SecondCountableTopology G] in
/-- Left translation on a semidirect product acts separately on the two product coordinates: the
group coordinate of the translating element is fixed, so its action on `N` does not depend on the
point being translated. -/
theorem homeomorphProd_symm_comp_mul_left (x₀ : N ⋊[φ] G) :
    (fun x : N ⋊[φ] G ↦ x₀ * x) ∘ (homeomorphProd φ).symm =
      (homeomorphProd φ).symm ∘
        Prod.map (fun n : N ↦ x₀.left * φ x₀.right n) (fun g : G ↦ x₀.right * g) := by
  funext p
  rfl

variable {φ ν lam}

omit [T2Space N] [T2Space G] [SecondCountableTopology N] in
/-- The transported product measure is left invariant when the measure on `N` is left invariant, the
measure on `G` is relatively invariant, and the two scaling factors are reciprocal. -/
theorem isMulLeftInvariant_prodMeasure [IsTopologicalGroup (N ⋊[φ] G)]
    [SFinite ν] [SFinite lam] [ν.IsMulLeftInvariant]
    {χ : G →* ℝ≥0∞} (hφν : ∀ g : G, Measure.map (φ g) ν = χ g • ν)
    (hlam : ∀ g₀ : G, Measure.map (fun g ↦ g₀ * g) lam = χ g₀⁻¹ • lam)
    (hcontinuousφ : ∀ g : G, Continuous (φ g)) :
    (prodMeasure φ ν lam).IsMulLeftInvariant := by
  constructor
  intro x₀
  have hleft : Measurable (fun n : N ↦ x₀.left * φ x₀.right n) :=
    (continuous_const_mul x₀.left).measurable.comp (hcontinuousφ x₀.right).measurable
  have hright : Measurable (fun g : G ↦ x₀.right * g) := (continuous_const_mul x₀.right).measurable
  have hmapleft : Measure.map (fun n : N ↦ x₀.left * φ x₀.right n) ν = χ x₀.right • ν := by
    rw [show (fun n : N ↦ x₀.left * φ x₀.right n) =
        (fun n : N ↦ x₀.left * n) ∘ (φ x₀.right : N → N) from rfl,
      ← Measure.map_map (continuous_const_mul x₀.left).measurable
        (hcontinuousφ x₀.right).measurable, hφν x₀.right, Measure.map_smul,
      map_mul_left_eq_self]
  have hcancel : χ x₀.right * χ x₀.right⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [prodMeasure, Measure.map_map (continuous_const_mul x₀).measurable
      (measurable_homeomorphProd_symm φ)]
  rw [show (fun x : N ⋊[φ] G ↦ x₀ * x) ∘ (homeomorphProd φ).symm =
      (homeomorphProd φ).symm ∘
        Prod.map (fun n : N ↦ x₀.left * φ x₀.right n) (fun g : G ↦ x₀.right * g) from
    homeomorphProd_symm_comp_mul_left φ x₀]
  rw [← Measure.map_map (measurable_homeomorphProd_symm φ) (hleft.prodMap hright)]
  congr 1
  rw [← Measure.map_prod_map ν lam hleft hright, hmapleft, hlam x₀.right,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, hcancel, one_smul]

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [SecondCountableTopology N] in
/-- The transported product measure is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_prodMeasure [SFinite lam] [IsFiniteMeasureOnCompacts ν]
    [IsFiniteMeasureOnCompacts lam] :
    IsFiniteMeasureOnCompacts (prodMeasure φ ν lam) := by
  constructor
  intro S hS
  have himage : IsCompact ((homeomorphProd φ).symm ⁻¹' S) := by
    rw [← (homeomorphProd φ).image_eq_preimage_symm S]
    exact hS.image (homeomorphProd φ).continuous
  rw [prodMeasure_apply φ ν lam hS.measurableSet]
  exact himage.measure_lt_top

omit [IsTopologicalGroup N] [IsTopologicalGroup G] [T2Space N] [T2Space G]
  [SecondCountableTopology N] in
/-- The transported product measure is positive on nonempty open sets. -/
theorem isOpenPosMeasure_prodMeasure [SFinite lam] [ν.IsOpenPosMeasure]
    [lam.IsOpenPosMeasure] :
    (prodMeasure φ ν lam).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [prodMeasure_apply φ ν lam hU.measurableSet]
  refine ((hU.preimage (homeomorphProd φ).symm.continuous).measure_pos (ν.prod lam) ?_).ne'
  obtain ⟨x, hx⟩ := hUne
  exact ⟨homeomorphProd φ x, by simpa using hx⟩

omit [SecondCountableTopology N] in
/-- Left Haar measure of a topological semidirect product is the product of Haar measure of the
normal factor and a relatively invariant measure on the acting factor. -/
theorem isHaarMeasure_prodMeasure [IsTopologicalGroup (N ⋊[φ] G)]
    [SFinite ν] [SFinite lam] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure]
    {χ : G →* ℝ≥0∞} (hφν : ∀ g : G, Measure.map (φ g) ν = χ g • ν)
    (hlam : ∀ g₀ : G, Measure.map (fun g ↦ g₀ * g) lam = χ g₀⁻¹ • lam)
    (hcontinuousφ : ∀ g : G, Continuous (φ g)) :
    (prodMeasure φ ν lam).IsHaarMeasure where
  lt_top_of_isCompact := (isFiniteMeasureOnCompacts_prodMeasure (φ := φ) (ν := ν)
    (lam := lam)).lt_top_of_isCompact
  map_mul_left_eq_self := (isMulLeftInvariant_prodMeasure hφν hlam
    hcontinuousφ).map_mul_left_eq_self
  open_pos := (isOpenPosMeasure_prodMeasure (φ := φ) (ν := ν) (lam := lam)).open_pos

/-- Uniqueness of Haar measure identifies the canonical Haar measure of a semidirect product with
the explicit product measure, up to a positive finite factor. -/
theorem exists_haar_eq_smul_prodMeasure [IsTopologicalGroup (N ⋊[φ] G)]
    [LocallyCompactSpace N] [LocallyCompactSpace G]
    [SFinite ν] [SFinite lam] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure]
    {χ : G →* ℝ≥0∞} (hφν : ∀ g : G, Measure.map (φ g) ν = χ g • ν)
    (hlam : ∀ g₀ : G, Measure.map (fun g ↦ g₀ * g) lam = χ g₀⁻¹ • lam)
    (hcontinuousφ : ∀ g : G, Continuous (φ g)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ s : Set (N ⋊[φ] G),
        (Measure.haar : Measure (N ⋊[φ] G)) s = c * prodMeasure φ ν lam s := by
  haveI : IsFiniteMeasureOnCompacts (prodMeasure φ ν lam) :=
    isFiniteMeasureOnCompacts_prodMeasure
  haveI : (prodMeasure φ ν lam).IsMulLeftInvariant :=
    isMulLeftInvariant_prodMeasure hφν hlam hcontinuousφ
  haveI : (prodMeasure φ ν lam).IsHaarMeasure :=
    isHaarMeasure_prodMeasure hφν hlam hcontinuousφ
  obtain ⟨k, hkpos, heq⟩ : ∃ k : ℝ≥0, 0 < k ∧
      prodMeasure φ ν lam = k • (Measure.haar : Measure (N ⋊[φ] G)) :=
    ⟨Measure.haarScalarFactor (prodMeasure φ ν lam) (Measure.haar : Measure (N ⋊[φ] G)),
      Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
      Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hne : ((k : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hkpos.ne'
  refine ⟨((k : ℝ≥0) : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.mpr hne, fun s ↦ ?_⟩
  have hval : prodMeasure φ ν lam s =
      ((k : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure (N ⋊[φ] G)) s := by
    rw [heq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hval, ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]

/-- On a compact set, the image of the semidirect-product Haar measure under the projection to the
acting factor is dominated by the relatively invariant measure of that factor.  The constant is the
Haar measure of the compact projection to the normal factor.

This is the estimate needed to bound an integral over a compact subset of the group by an integral
over the acting factor alone, which is the first step of a quotient-integral estimate for an induced
representation. -/
theorem exists_map_right_haar_restrict_le [IsTopologicalGroup (N ⋊[φ] G)]
    [LocallyCompactSpace N] [LocallyCompactSpace G]
    [SFinite ν] [SFinite lam] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure]
    {χ : G →* ℝ≥0∞} (hφν : ∀ g : G, Measure.map (φ g) ν = χ g • ν)
    (hlam : ∀ g₀ : G, Measure.map (fun g ↦ g₀ * g) lam = χ g₀⁻¹ • lam)
    (hcontinuousφ : ∀ g : G, Continuous (φ g))
    {S : Set (N ⋊[φ] G)} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map SemidirectProduct.right
          ((Measure.haar : Measure (N ⋊[φ] G)).restrict S) ≤
        C • lam.restrict (SemidirectProduct.right '' S) := by
  obtain ⟨c, _, hctop, hcs⟩ :=
    exists_haar_eq_smul_prodMeasure hφν hlam hcontinuousφ
  have himage : IsCompact (homeomorphProd φ '' S) := hS.image (homeomorphProd φ).continuous
  have hfst : IsCompact (Prod.fst '' (homeomorphProd φ '' S)) := himage.image continuous_fst
  have hsnd : IsCompact (Prod.snd '' (homeomorphProd φ '' S)) := himage.image continuous_snd
  refine ⟨c * ν (Prod.fst '' (homeomorphProd φ '' S)),
    ENNReal.mul_ne_top hctop hfst.measure_lt_top.ne, ?_⟩
  rw [Measure.le_iff]
  intro t ht
  have hrightmeasurable : Measurable (SemidirectProduct.right : N ⋊[φ] G → G) :=
    (continuous_right φ).measurable
  have hpre : MeasurableSet (SemidirectProduct.right ⁻¹' t : Set (N ⋊[φ] G)) :=
    ht.preimage hrightmeasurable
  have hrightimage : Prod.snd '' (homeomorphProd φ '' S) = SemidirectProduct.right '' S := by
    rw [← Set.image_comp]
    rfl
  have hsubset : (homeomorphProd φ).symm ⁻¹' (SemidirectProduct.right ⁻¹' t ∩ S) ⊆
      (Prod.fst '' (homeomorphProd φ '' S)) ×ˢ (t ∩ Prod.snd '' (homeomorphProd φ '' S)) := by
    intro p hp
    obtain ⟨hpt, hpS⟩ := hp
    have hmem : (p.1, p.2) ∈ homeomorphProd φ '' S := by
      refine ⟨(homeomorphProd φ).symm p, hpS, ?_⟩
      simp
    exact ⟨⟨_, hmem, rfl⟩, hpt, ⟨_, hmem, rfl⟩⟩
  calc
    Measure.map SemidirectProduct.right
        ((Measure.haar : Measure (N ⋊[φ] G)).restrict S) t =
        (Measure.haar : Measure (N ⋊[φ] G)) (SemidirectProduct.right ⁻¹' t ∩ S) := by
      rw [Measure.map_apply hrightmeasurable ht, Measure.restrict_apply hpre]
    _ = c * prodMeasure φ ν lam (SemidirectProduct.right ⁻¹' t ∩ S) := hcs _
    _ = c * (ν.prod lam) ((homeomorphProd φ).symm ⁻¹' (SemidirectProduct.right ⁻¹' t ∩ S)) := by
      rw [prodMeasure_apply φ ν lam (hpre.inter hS.measurableSet)]
    _ ≤ c * (ν.prod lam) ((Prod.fst '' (homeomorphProd φ '' S)) ×ˢ
        (t ∩ Prod.snd '' (homeomorphProd φ '' S))) := mul_le_mul_right (measure_mono hsubset) c
    _ = c * (ν (Prod.fst '' (homeomorphProd φ '' S)) *
        lam (t ∩ Prod.snd '' (homeomorphProd φ '' S))) := by
      rw [Measure.prod_prod]
    _ = c * (ν (Prod.fst '' (homeomorphProd φ '' S)) *
        (lam.restrict (SemidirectProduct.right '' S)) t) := by
      rw [Measure.restrict_apply ht, hrightimage]
    _ = (c * ν (Prod.fst '' (homeomorphProd φ '' S))) *
        (lam.restrict (SemidirectProduct.right '' S)) t := by rw [mul_assoc]
    _ = ((c * ν (Prod.fst '' (homeomorphProd φ '' S))) •
        lam.restrict (SemidirectProduct.right '' S)) t := by
      rw [Measure.smul_apply, smul_eq_mul]

end SemidirectProduct
