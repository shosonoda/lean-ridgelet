/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pushing a compactly restricted Haar measure by a surjective linear map

Mathlib's `LinearMap.exists_map_addHaar_eq_smul_addHaar'` pushes a *whole* additive Haar measure
forward along a surjective linear map; the proportionality factor is infinite as soon as the map has
a nontrivial kernel, because the fibers are then unbounded. Restricting the source measure to a
compact set removes that divergence: the fibers of the restriction are bounded, so the image measure
is dominated by a finite multiple of additive Haar measure on the target.

This is the estimate that converts an integral over a compact set of matrices into an integral over
the vector space that a fixed vector is sent to, which is what the quotient-integral estimate of an
induced representation needs.

## Main results

* `MeasureTheory.map_snd_restrict_prod_le`: the second projection of a restricted product measure is
  dominated by the second factor, with constant the first factor of the projected restriction set.
* `LinearMap.exists_map_restrict_addHaar_le_smul_addHaar`: the compactly restricted pushforward
  bound.
-/
@[expose] public section

noncomputable section

open MeasureTheory Measure Set
open scoped ENNReal NNReal

namespace MeasureTheory

/-- The image of a restricted product measure under the second projection is dominated by the second
factor, with the measure of the first projection of the restriction set as constant. -/
theorem map_snd_restrict_prod_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (K : Set (X × Y)) :
    Measure.map Prod.snd ((μ.prod ν).restrict K) ≤
      μ (Prod.fst '' K) • ν.restrict (Prod.snd '' K) := by
  rw [Measure.le_iff]
  intro t ht
  have hpre : MeasurableSet (Prod.snd ⁻¹' t : Set (X × Y)) := ht.preimage measurable_snd
  have hsubset : (Prod.snd ⁻¹' t : Set (X × Y)) ∩ K ⊆
      (Prod.fst '' K) ×ˢ (t ∩ Prod.snd '' K) := by
    intro p hp
    exact ⟨⟨p, hp.2, rfl⟩, hp.1, ⟨p, hp.2, rfl⟩⟩
  calc
    Measure.map Prod.snd ((μ.prod ν).restrict K) t = (μ.prod ν) (Prod.snd ⁻¹' t ∩ K) := by
      rw [Measure.map_apply measurable_snd ht, Measure.restrict_apply hpre]
    _ ≤ (μ.prod ν) ((Prod.fst '' K) ×ˢ (t ∩ Prod.snd '' K)) := measure_mono hsubset
    _ = μ (Prod.fst '' K) * ν (t ∩ Prod.snd '' K) := Measure.prod_prod _ _
    _ = (μ (Prod.fst '' K) • ν.restrict (Prod.snd '' K)) t := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht]

end MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F]

/-- The image under a surjective linear map of an additive Haar measure restricted to a compact set
is dominated by a finite multiple of additive Haar measure on the target.

The proof follows the decomposition used by `LinearMap.exists_map_addHaar_eq_smul_addHaar'`: a
complement `T` of the kernel `S` splits the source as `S × T`, the map becomes the second
projection followed by a linear equivalence, and the compact restriction set has a bounded
kernel projection. -/
theorem LinearMap.exists_map_restrict_addHaar_le_smul_addHaar
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    {L : E →ₗ[ℝ] F} (hL : Function.Surjective L) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map L (μ.restrict K) ≤ C • ν.restrict ((L : E → F) '' K) := by
  classical
  set S : Submodule ℝ E := LinearMap.ker L with hS
  obtain ⟨T, hT⟩ : ∃ T : Submodule ℝ E, IsCompl S T := Submodule.exists_isCompl S
  set M : (S × T) ≃ₗ[ℝ] E := Submodule.prodEquivOfIsCompl S T hT with hM
  have hMcont : Continuous (M : S × T → E) := LinearMap.continuous_of_finiteDimensional _
  have hMsymmcont : Continuous (M.symm : E → S × T) := LinearMap.continuous_of_finiteDimensional _
  set P : S × T →ₗ[ℝ] T := LinearMap.snd ℝ S T with hP
  have hbijective : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 hT.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hL).2 hT.symm.codisjoint⟩
  set L' : T ≃ₗ[ℝ] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) hbijective with hL'
  have hL'cont : Continuous (L' : T → F) := LinearMap.continuous_of_finiteDimensional _
  have hfactor : ∀ p : S × T, L (M p) = L' (P p) := by
    intro p
    have hp1 : L (p.1 : E) = 0 := p.1.2
    simp [hM, hP, hL', Submodule.coe_prodEquivOfIsCompl', hp1]
  -- the source Haar measure is a multiple of the product Haar measure through `M`
  set μS : Measure S := Measure.addHaar with hμS
  set μT : Measure T := Measure.addHaar with hμT
  have hmapM : (Measure.map (M : S × T → E) (μS.prod μT)).IsAddHaarMeasure :=
    M.toContinuousLinearEquiv.isAddHaarMeasure_map (μS.prod μT)
  obtain ⟨c, hctop, hc⟩ : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      μ = c • Measure.map (M : S × T → E) (μS.prod μT) :=
    ⟨Measure.addHaarScalarFactor μ (Measure.map (M : S × T → E) (μS.prod μT)),
      ENNReal.coe_ne_top, Measure.isAddLeftInvariant_eq_smul _ _⟩
  -- the target Haar measure is a multiple of the pushforward of the complement Haar measure
  have hmapL' : (Measure.map (L' : T → F) μT).IsAddHaarMeasure := by
    infer_instance
  obtain ⟨d, hdtop, hd⟩ : ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ Measure.map (L' : T → F) μT = d • ν :=
    ⟨Measure.addHaarScalarFactor (Measure.map (L' : T → F) μT) ν, ENNReal.coe_ne_top,
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  -- the compact restriction set has compact image in the product coordinates
  have hpreimage : (M : S × T → E) ⁻¹' K = (M.symm : E → S × T) '' K := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun hp ↦ ⟨M p, hp, by simp⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    simpa using hx
  have hKcompact : IsCompact ((M : S × T → E) ⁻¹' K) := by
    rw [hpreimage]
    exact hK.image hMsymmcont
  have hfstcompact : IsCompact (Prod.fst '' ((M : S × T → E) ⁻¹' K)) :=
    hKcompact.image continuous_fst
  refine ⟨c * μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) * d,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hctop hfstcompact.measure_lt_top.ne) hdtop, ?_⟩
  rw [Measure.le_iff]
  intro t ht
  have hLmeasurable : Measurable (L : E → F) :=
    (LinearMap.continuous_of_finiteDimensional L).measurable
  have hL'measurable : Measurable (L' : T → F) := hL'cont.measurable
  have hpre : MeasurableSet ((L : E → F) ⁻¹' t) := ht.preimage hLmeasurable
  have himagecompact : IsCompact ((L : E → F) '' K) :=
    hK.image (LinearMap.continuous_of_finiteDimensional L)
  have hfiber : ((L' : T → F) ⁻¹' t ∩ Prod.snd '' ((M : S × T → E) ⁻¹' K)) ⊆
      (L' : T → F) ⁻¹' (t ∩ (L : E → F) '' K) := by
    rintro x ⟨hxt, p, hp, rfl⟩
    refine ⟨hxt, M p, hp, ?_⟩
    simpa [hP] using hfactor p
  have hsets : (M : S × T → E) ⁻¹' ((L : E → F) ⁻¹' t ∩ K) =
      (Prod.snd ⁻¹' ((L' : T → F) ⁻¹' t)) ∩ ((M : S × T → E) ⁻¹' K) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, hfactor p, hP, LinearMap.snd_apply]
  calc
    Measure.map (L : E → F) (μ.restrict K) t = μ ((L : E → F) ⁻¹' t ∩ K) := by
      rw [Measure.map_apply hLmeasurable ht, Measure.restrict_apply hpre]
    _ = c * (μS.prod μT) ((M : S × T → E) ⁻¹' ((L : E → F) ⁻¹' t ∩ K)) := by
      rw [hc, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply hMcont.measurable (hpre.inter hK.measurableSet)]
    _ = c * ((μS.prod μT).restrict ((M : S × T → E) ⁻¹' K))
        (Prod.snd ⁻¹' ((L' : T → F) ⁻¹' t)) := by
      rw [hsets, Measure.restrict_apply (measurable_snd (ht.preimage hL'measurable))]
    _ = c * (Measure.map Prod.snd
        ((μS.prod μT).restrict ((M : S × T → E) ⁻¹' K))) ((L' : T → F) ⁻¹' t) := by
      rw [Measure.map_apply measurable_snd (ht.preimage hL'measurable)]
    _ ≤ c * ((μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) •
        μT.restrict (Prod.snd '' ((M : S × T → E) ⁻¹' K))) ((L' : T → F) ⁻¹' t)) :=
      mul_le_mul_right ((Measure.le_iff.mp
        (map_snd_restrict_prod_le μS μT ((M : S × T → E) ⁻¹' K)))
        ((L' : T → F) ⁻¹' t) (ht.preimage hL'measurable)) c
    _ = c * (μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) *
        μT ((L' : T → F) ⁻¹' t ∩ Prod.snd '' ((M : S × T → E) ⁻¹' K))) := by
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (ht.preimage hL'measurable)]
    _ ≤ c * (μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) *
        μT ((L' : T → F) ⁻¹' (t ∩ (L : E → F) '' K))) :=
      mul_le_mul_right (mul_le_mul_right (measure_mono hfiber) _) c
    _ = c * (μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) *
        (Measure.map (L' : T → F) μT) (t ∩ (L : E → F) '' K)) := by
      rw [Measure.map_apply hL'measurable (ht.inter himagecompact.measurableSet)]
    _ = c * (μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) * (d * ν (t ∩ (L : E → F) '' K))) := by
      rw [hd, Measure.smul_apply, smul_eq_mul]
    _ = (c * μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) * d) *
        (ν.restrict ((L : E → F) '' K)) t := by
      rw [Measure.restrict_apply ht]
      ring
    _ = ((c * μS (Prod.fst '' ((M : S × T → E) ⁻¹' K)) * d) •
        ν.restrict ((L : E → F) '' K)) t := by
      rw [Measure.smul_apply, smul_eq_mul]
