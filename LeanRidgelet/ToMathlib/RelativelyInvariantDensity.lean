/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Relatively invariant densities

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

A measure of the form `μ.withDensity w` transforms very simply under a map `T` that rescales `μ`
and rescales `w`: if `T` multiplies `μ` by `c` and `w ∘ T = κ • w`, then `T` multiplies
`μ.withDensity w` by `κ⁻¹ * c`.  Choosing `w` so that `κ⁻¹ * c` is the reciprocal of a prescribed
character is the standard way to manufacture a relatively invariant measure out of a Haar measure
and a relative invariant.

Nothing here needs local finiteness of `μ.withDensity w`; the statements are pure identities of
measures, proved by evaluating both sides on measurable sets.

## Main results

* `MeasureTheory.Measure.map_withDensity_of_map_eq_smul`: the transformation law above.
* `MeasureTheory.Measure.map_restrict_of_map_eq_smul`: the same rescaling survives restriction to
  a set invariant under `T`, which is what lets one delete a degenerate locus before weighting.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- Pushforward of a weighted measure by a map that rescales both the base measure and the
weight.  If `T` sends `μ` to `c • μ` and multiplies the weight `w` by the constant `κ`, then it
sends `μ.withDensity w` to `(κ⁻¹ * c) • μ.withDensity w`.  The constant `κ` must be neither zero
nor infinite so that it can be divided out. -/
theorem map_withDensity_of_map_eq_smul {μ : Measure X} {T : X → X} {w : X → ℝ≥0∞} {c κ : ℝ≥0∞}
    (hT : Measurable T) (hw : Measurable w) (hmap : μ.map T = c • μ)
    (hweight : ∀ x, w (T x) = κ * w x) (hκ : κ ≠ 0) (hκ' : κ ≠ ∞) :
    (μ.withDensity w).map T = (κ⁻¹ * c) • μ.withDensity w := by
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hs, ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have hpt : ∀ x, (T ⁻¹' s).indicator w x = κ⁻¹ * s.indicator w (T x) := by
    intro x
    by_cases hx : T x ∈ s
    · rw [Set.indicator_of_mem (by exact hx) w, Set.indicator_of_mem hx w, hweight x,
        ← mul_assoc, ENNReal.inv_mul_cancel hκ hκ', one_mul]
    · rw [Set.indicator_of_notMem (by exact hx) w, Set.indicator_of_notMem hx w, mul_zero]
  have hcomp : Measurable fun x ↦ s.indicator w (T x) := (hw.indicator hs).comp hT
  simp_rw [hpt]
  rw [lintegral_const_mul _ hcomp, ← lintegral_map (hw.indicator hs) hT, hmap,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc]

/-- Restricting to a set invariant under `T` preserves the rescaling law `μ.map T = c • μ`. -/
theorem map_restrict_of_map_eq_smul {μ : Measure X} {T : X → X} {c : ℝ≥0∞} {s : Set X}
    (hT : Measurable T) (hmap : μ.map T = c • μ) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s) :
    (μ.restrict s).map T = c • μ.restrict s := by
  rw [← hinv, ← Measure.restrict_map hT hs, hmap, Measure.restrict_smul, hinv]

end MeasureTheory.Measure
