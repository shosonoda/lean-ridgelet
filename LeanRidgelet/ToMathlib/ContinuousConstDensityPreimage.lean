/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# Continuity of preimages for maps with constant measure density

This file extends the set-level input of
`MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero` from measure-preserving maps to
continuous maps whose pushforward measure is a continuously varying finite scalar multiple of the
target measure.  This is the form needed for determinant-corrected actions on `Lᵖ` spaces.

The multiplier is parametrized by `ℝ≥0`, rather than `ℝ≥0∞`, so that finiteness of every density is
part of the type and no extra side condition is needed.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal symmDiff Topology

namespace MeasureTheory

variable {α X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
  {μ : Measure X} {ν : Measure Y} [μ.InnerRegularCompactLTTop]
  [ν.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

omit [R1Space X] [R1Space Y] [μ.InnerRegularCompactLTTop] [ν.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure ν] in
/-- If the pushforward of `μ` is a finite scalar multiple of `ν`, preimages of measurable sets
have the correspondingly scaled measure. -/
theorem measure_preimage_eq_nnreal_smul {f : C(X, Y)} {c : ℝ≥0}
    (hmap : μ.map f = (c : ℝ≥0∞) • ν) {s : Set Y} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = (c : ℝ≥0∞) * ν s := by
  rw [← Measure.map_apply (map_continuous f).measurable hs, hmap, Measure.smul_apply, smul_eq_mul]

omit [R1Space Y] [ν.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν] in
/-- Preimages of a finite-measure open set vary continuously in symmetric-difference measure for
a convergent family of continuous maps whose pushforward measures have convergent constant
densities. -/
theorem tendsto_measure_symmDiff_preimage_nhds_zero_of_isOpen_of_map_eq_nnreal_smul
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {c : α → ℝ≥0} {d : ℝ≥0}
    {s : Set Y} (hfg : Tendsto f l (𝓝 g)) (hc : Tendsto c l (𝓝 d))
    (hf : ∀ᶠ a in l, μ.map (f a) = (c a : ℝ≥0∞) • ν)
    (hg : μ.map g = (d : ℝ≥0∞) • ν) (hs : IsOpen s) (hνs : ν s ≠ ∞) :
    Tendsto (fun a ↦ μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hgs : μ (g ⁻¹' s) = (d : ℝ≥0∞) * ν s :=
    measure_preimage_eq_nnreal_smul hg hs.measurableSet
  have hgs_top : μ (g ⁻¹' s) ≠ ∞ := by
    rw [hgs]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hνs.lt_top).ne
  obtain ⟨K, hKg, hKco, hKcl, hKμ⟩ :=
    ((map_continuous g).measurable hs.measurableSet).exists_isCompact_isClosed_sdiff_lt hgs_top
      (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).ne'
  have hKm : NullMeasurableSet K μ := hKcl.nullMeasurableSet
  have hKtop : μ K ≠ ∞ := ne_top_of_le_ne_top hgs_top (measure_mono hKg)
  have hbase : (d : ℝ≥0∞) * ν s ≤ μ K + ε / 3 := by
    rw [← hgs]
    exact (measure_sdiff_le_iff_le_add hKm hKg hKtop).1 hKμ.le
  have hc' : Tendsto (fun a ↦ (c a : ℝ≥0∞)) l (𝓝 (d : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto d).comp hc
  have hmass : Tendsto (fun a ↦ (c a : ℝ≥0∞) * ν s) l
      (𝓝 ((d : ℝ≥0∞) * ν s)) :=
    ENNReal.Tendsto.mul_const hc' (Or.inr hνs)
  have hmass_lt : ∀ᶠ a in l,
      (c a : ℝ≥0∞) * ν s < (d : ℝ≥0∞) * ν s + ε / 3 :=
    hmass.eventually (gt_mem_nhds <|
      ENNReal.lt_add_right (ENNReal.mul_lt_top ENNReal.coe_lt_top hνs.lt_top).ne
        (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).ne')
  filter_upwards [hf, hmass_lt,
    ContinuousMap.tendsto_nhds_compactOpen.mp hfg K hKco s hs hKg] with a hfa hca ha
  rw [← ENNReal.add_thirds ε]
  refine (measure_symmDiff_le _ K _).trans ?_
  rw [symmDiff_of_ge ha.subset_preimage, symmDiff_of_le hKg]
  apply add_le_add
  · rw [measure_sdiff_le_iff_le_add hKm ha.subset_preimage hKtop,
      measure_preimage_eq_nnreal_smul hfa hs.measurableSet]
    exact hca.le.trans <| by
      calc
        (d : ℝ≥0∞) * ν s + ε / 3 ≤ (μ K + ε / 3) + ε / 3 :=
          by simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hbase (ε / 3)
        _ = μ K + (ε / 3 + ε / 3) := by rw [add_assoc]
  · exact hKμ.le

/-- Let `f a : C(X, Y)` converge to `g` in the compact-open topology, and suppose that the
pushforward of `μ` under these maps is a finite constant multiple of `ν`, with multipliers
converging in `ℝ≥0`. Then preimages of every finite-measure measurable set converge in
symmetric-difference measure. -/
theorem tendsto_measure_symmDiff_preimage_nhds_zero_of_map_eq_nnreal_smul
    {l : Filter α} {f : α → C(X, Y)} {g : C(X, Y)} {c : α → ℝ≥0} {d : ℝ≥0}
    {s : Set Y} (hfg : Tendsto f l (𝓝 g)) (hc : Tendsto c l (𝓝 d))
    (hf : ∀ᶠ a in l, μ.map (f a) = (c a : ℝ≥0∞) • ν)
    (hg : μ.map g = (d : ℝ≥0∞) • ν) (hs : MeasurableSet s) (hνs : ν s ≠ ∞) :
    Tendsto (fun a ↦ μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  let D : ℝ≥0∞ := (d : ℝ≥0∞) + 1
  have hD0 : D ≠ 0 := by simp [D]
  have hDtop : D ≠ ∞ := by simp [D]
  have hδ : 0 < (ε / 3) / D := ENNReal.div_pos
    (ENNReal.div_ne_zero.2 ⟨hε.ne', by norm_num⟩) hDtop
  obtain ⟨U, hUo, hUtop, hUs⟩ :=
    hs.exists_isOpen_symmDiff_lt hνs hδ.ne'
  have hc' : Tendsto (fun a ↦ (c a : ℝ≥0∞)) l (𝓝 (d : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto d).comp hc
  have hbound : ∀ᶠ a in l, (c a : ℝ≥0∞) < D :=
    hc'.eventually (gt_mem_nhds <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
  have hopen :=
    tendsto_measure_symmDiff_preimage_nhds_zero_of_isOpen_of_map_eq_nnreal_smul
      hfg hc hf hg hUo hUtop.ne
  filter_upwards [hf, hbound, hopen.eventually (show {x : ℝ≥0∞ | x < ε / 3} ∈ 𝓝 0 by
    exact gt_mem_nhds <| ENNReal.div_pos hε.ne' (by norm_num))] with a hfa hca ha
  refine (show μ ((f a ⁻¹' s) ∆ (g ⁻¹' s)) < ε from ?_).le
  calc
    μ ((f a ⁻¹' s) ∆ (g ⁻¹' s))
        ≤ μ ((f a ⁻¹' s) ∆ (f a ⁻¹' U)) +
            μ ((f a ⁻¹' U) ∆ (g ⁻¹' U)) +
            μ ((g ⁻¹' U) ∆ (g ⁻¹' s)) := by
          refine (measure_symmDiff_le _ (g ⁻¹' U) _).trans ?_
          gcongr
          apply measure_symmDiff_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · rw [← preimage_symmDiff,
          measure_preimage_eq_nnreal_smul hfa (hs.symmDiff hUo.measurableSet)]
        calc
          (c a : ℝ≥0∞) * ν (s ∆ U) < D * ((ε / 3) / D) := by
            gcongr
            simpa only [symmDiff_comm] using hUs
          _ = ε / 3 := ENNReal.mul_div_cancel hD0 hDtop
      · rw [← preimage_symmDiff,
          measure_preimage_eq_nnreal_smul hg (hUo.measurableSet.symmDiff hs)]
        calc
          (d : ℝ≥0∞) * ν (U ∆ s) < D * ((ε / 3) / D) := by
            gcongr
            exact ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero
          _ = ε / 3 := ENNReal.mul_div_cancel hD0 hDtop
    _ = ε := ENNReal.add_thirds ε

end MeasureTheory
