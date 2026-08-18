/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Order.Disjointed
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Discretizing a Bochner integral of a Lipschitz family by finite sums

Let `Ξ` be a compact metric space carrying a finite Borel measure `μ`, let `F` be a Banach space
and let `φ : Ξ → F` be Lipschitz. This file shows that `φ` is Bochner integrable and that its
integral is approximated in norm, to any prescribed accuracy, by a *finite* sum of point
evaluations `∑ i, w i • φ (ξ i)` with nonnegative weights `w i`.

## Main results

* `MeasureTheory.exists_fin_measurable_partition_subset_ball`: a compact metric space is the
  disjoint union of finitely many measurable pieces, the `i`-th one contained in the ball of
  radius `δ` about a point `c i`. This is the finite cover of the compactness argument, made
  disjoint by `disjointed`.
* `MeasureTheory.integrable_of_lipschitzWith`: a Lipschitz map on a compact space is Bochner
  integrable for a finite measure.
* `MeasureTheory.exists_finsetSum_approx_integral_of_lipschitz`: the discretization theorem.
* `MeasureTheory.exists_finsetSum_approx_integral_boundedContinuous_of_lipschitz`: its
  specialization to `F := X →ᵇ Y`, where the norm is the supremum norm, so that the conclusion
  reads as *uniform* approximation on `X`.

## Why these hypotheses

Compactness of `Ξ` produces the finite cover by `δ`-balls, hence the finite index set; the metric
turns the Lipschitz hypothesis into the pointwise bound `‖φ x - φ (c i)‖ ≤ L * δ` on each piece;
and finiteness of `μ` converts that pointwise bound into the uniform estimate
`‖∫ φ - ∑ i, μ.real (S i) • φ (c i)‖ ≤ L * δ * μ.real univ`, which is what lets a single choice
of `δ` serve for the whole integral. The weights are the measures of the pieces, so they are
nonnegative and sum to `μ.real univ`.

In the bounded-continuous corollary the domain `X` of the functions carries no measure and no
compactness assumption: the discretization happens entirely on the parameter space `Ξ`, and `X`
only enters through the Banach space `X →ᵇ Y`.
-/

@[expose] public section

noncomputable section

open Metric Set

open scoped ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section Partition

variable (Ξ : Type*) [MetricSpace Ξ] [CompactSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

/-- A compact metric space is a finite disjoint union of measurable pieces of small diameter:
for `δ > 0` there are finitely many points `c i` and pairwise disjoint measurable sets `S i`
covering the space with `S i ⊆ ball (c i) δ`. The sets are obtained by making a finite cover by
`δ`-balls disjoint with `disjointed`. -/
theorem exists_fin_measurable_partition_subset_ball {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (c : Fin n → Ξ) (S : Fin n → Set Ξ), (∀ i, MeasurableSet (S i)) ∧
      (∀ i, S i ⊆ ball (c i) δ) ∧ Pairwise (Function.onFun Disjoint S) ∧
        ∀ x : Ξ, ∃ i, x ∈ S i := by
  classical
  obtain ⟨n, c, hcover⟩ : ∃ (n : ℕ) (c : Fin n → Ξ), ∀ x : Ξ, ∃ i, x ∈ ball (c i) δ := by
    obtain ⟨t, -, htfin, htcover⟩ :=
      finite_cover_balls_of_compact (isCompact_univ (X := Ξ)) hδ
    haveI : Fintype t := htfin.fintype
    refine ⟨Fintype.card t, fun i => ((Fintype.equivFin t).symm i : Ξ), fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (htcover (mem_univ x))
    exact ⟨Fintype.equivFin t ⟨y, hy⟩, by simpa using hxy⟩
  refine ⟨n, c, disjointed fun i => ball (c i) δ, fun i => ?_,
    fun i => disjointed_subset _ i, disjoint_disjointed _, fun x => ?_⟩
  · rw [disjointed_eq_inter_compl]
    exact measurableSet_ball.inter
      (MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_ball.compl)
  · have hx : x ∈ ⋃ i, disjointed (fun i => ball (c i) δ) i := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr (hcover x)
    exact mem_iUnion.mp hx

end Partition

section Discretization

variable {Ξ F : Type*} [MetricSpace Ξ] [CompactSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A Lipschitz map from a compact metric space to a Banach space is Bochner integrable with
respect to any finite Borel measure: it is continuous, hence measurable and bounded, and a bounded
function is integrable for a finite measure. -/
theorem integrable_of_lipschitzWith (μ : Measure Ξ) [IsFiniteMeasure μ] {L : ℝ≥0} {φ : Ξ → F}
    (hφ : LipschitzWith L φ) : Integrable φ μ := by
  have hcont : Continuous φ := hφ.continuous
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : Ξ, ‖φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hcont).isBounded.exists_norm_le
    exact ⟨C, fun x => hC _ ⟨x, mem_univ x, rfl⟩⟩
  exact ⟨hcont.aestronglyMeasurable, HasFiniteIntegral.of_bounded (ae_of_all μ hC)⟩

/-- **Discretization of a Bochner integral of a Lipschitz family.** For a Lipschitz map `φ` from a
compact metric space with a finite Borel measure `μ` to a Banach space, the integral `∫ φ ∂μ` is
approximated in norm, to any accuracy `ε > 0`, by a finite sum `∑ i, w i • φ (ξ i)` of point
evaluations with nonnegative weights. The weights are the measures of the pieces of a partition
into sets of radius `δ`, with `δ` chosen so that `L * δ * μ.real univ < ε`, and the points are the
centres of those pieces. -/
theorem exists_finsetSum_approx_integral_of_lipschitz [CompleteSpace F] (μ : Measure Ξ)
    [IsFiniteMeasure μ] {L : ℝ≥0} {φ : Ξ → F} (hφ : LipschitzWith L φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (ξ : Fin n → Ξ), (∀ i, 0 ≤ w i) ∧
      ‖(∫ x, φ x ∂μ) - ∑ i, w i • φ (ξ i)‖ < ε := by
  classical
  have hM : 0 ≤ μ.real univ := measureReal_nonneg
  have hLM : 0 ≤ (L : ℝ) * μ.real univ := mul_nonneg L.coe_nonneg hM
  -- Step 1: a radius `δ` small enough for the final estimate.
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ (L : ℝ) * δ * μ.real univ < ε := by
    refine ⟨ε / (2 * ((L : ℝ) * μ.real univ + 1)), by positivity, ?_⟩
    have hpos : (0 : ℝ) < 2 * ((L : ℝ) * μ.real univ + 1) := by positivity
    have hrw : (L : ℝ) * (ε / (2 * ((L : ℝ) * μ.real univ + 1))) * μ.real univ
        = ((L : ℝ) * μ.real univ) * ε / (2 * ((L : ℝ) * μ.real univ + 1)) := by
      field_simp
    rw [hrw, div_lt_iff₀ hpos]
    nlinarith [mul_nonneg hLM hε.le]
  -- Step 2: a finite measurable partition into pieces of radius `δ`.
  obtain ⟨n, c, S, hSmeas, hSsub, hSdisj, hScover⟩ :=
    exists_fin_measurable_partition_subset_ball Ξ hδ
  -- Step 3: the associated simple approximation of `φ`.
  set g : Ξ → F := fun x => ∑ i, (S i).indicator (fun _ => φ (c i)) x with hgdef
  have hgeval : ∀ (x : Ξ) (i : Fin n), x ∈ S i → g x = φ (c i) := by
    intro x i hxi
    have hother : ∀ j ∈ Finset.univ, j ≠ i → (S j).indicator (fun _ => φ (c j)) x = 0 := by
      intro j _ hji
      have hxj : x ∉ S j := fun hxj => Set.disjoint_left.mp (hSdisj hji) hxj hxi
      exact Set.indicator_of_notMem hxj _
    simp only [hgdef, Finset.sum_eq_single i hother fun h => absurd (Finset.mem_univ i) h,
      Set.indicator_of_mem hxi]
  -- Step 4: the pointwise Lipschitz estimate on each piece.
  have hgbound : ∀ x : Ξ, ‖φ x - g x‖ ≤ (L : ℝ) * δ := by
    intro x
    obtain ⟨i, hxi⟩ := hScover x
    have hdist : dist x (c i) ≤ δ := (mem_ball.mp (hSsub i hxi)).le
    calc ‖φ x - g x‖ = dist (φ x) (φ (c i)) := by rw [hgeval x i hxi, dist_eq_norm]
      _ ≤ (L : ℝ) * δ := hφ.dist_le_mul_of_le hdist
  -- Step 5: integrate the estimate.
  have hφint : Integrable φ μ := integrable_of_lipschitzWith μ hφ
  have hindint : ∀ i : Fin n, Integrable ((S i).indicator fun _ => φ (c i)) μ := fun i =>
    (integrable_const (φ (c i))).indicator (hSmeas i)
  have hgint : Integrable g μ := by
    rw [hgdef]
    exact integrable_finsetSum _ fun i _ => hindint i
  have hintg : ∫ x, g x ∂μ = ∑ i, μ.real (S i) • φ (c i) := by
    simp only [hgdef]
    rw [integral_finsetSum _ fun i _ => hindint i]
    exact Finset.sum_congr rfl fun i _ => integral_indicator_const _ (hSmeas i)
  have hnorm : ‖(∫ x, φ x ∂μ) - ∫ x, g x ∂μ‖ ≤ (L : ℝ) * δ * μ.real univ := by
    rw [← integral_sub hφint hgint]
    exact norm_integral_le_of_norm_le_const (ae_of_all μ hgbound)
  have hfinal : ‖(∫ x, φ x ∂μ) - ∑ i, μ.real (S i) • φ (c i)‖ < ε := by
    rw [← hintg]
    exact hnorm.trans_lt hδε
  exact ⟨n, fun i => μ.real (S i), c, fun _ => measureReal_nonneg, hfinal⟩

end Discretization

section BoundedContinuous

variable {Ξ X Y : Type*} [MetricSpace Ξ] [CompactSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
  [TopologicalSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- **Uniform approximation of a bounded-continuous integral representation by finite sums.** The
case `F := X →ᵇ Y` of `MeasureTheory.exists_finsetSum_approx_integral_of_lipschitz`. Since the
norm of `X →ᵇ Y` is the supremum norm, the estimate is uniform in `x : X`, as the last conjunct
spells out; neither a measure nor compactness is assumed on `X`. -/
theorem exists_finsetSum_approx_integral_boundedContinuous_of_lipschitz (μ : Measure Ξ)
    [IsFiniteMeasure μ] {L : ℝ≥0} {φ : Ξ → X →ᵇ Y} (hφ : LipschitzWith L φ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (ξ : Fin n → Ξ), (∀ i, 0 ≤ w i) ∧
      ‖(∫ t, φ t ∂μ) - ∑ i, w i • φ (ξ i)‖ < ε ∧
        ∀ x : X, ‖(∫ t, φ t ∂μ) x - ∑ i, w i • φ (ξ i) x‖ < ε := by
  obtain ⟨n, w, ξ, hw, hlt⟩ := exists_finsetSum_approx_integral_of_lipschitz μ hφ hε
  refine ⟨n, w, ξ, hw, hlt, fun x => ?_⟩
  have hx : ‖(∫ t, φ t ∂μ) x - ∑ i, w i • φ (ξ i) x‖
      ≤ ‖(∫ t, φ t ∂μ) - ∑ i, w i • φ (ξ i)‖ := by
    simpa using
      BoundedContinuousFunction.norm_coe_le_norm ((∫ t, φ t ∂μ) - ∑ i, w i • φ (ξ i)) x
  exact hx.trans_lt hlt

end BoundedContinuous

end MeasureTheory
