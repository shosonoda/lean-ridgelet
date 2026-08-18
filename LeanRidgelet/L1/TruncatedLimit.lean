/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs

/-!
# L1 theory: the truncation limit of the dual ridgelet transform

`LeanRidgelet.truncatedDualRidgeletTransform` integrates the dual ridgelet integrand over the
scale annulus `ε ≤ ‖a‖ ≤ δ`, and `LeanRidgelet.euclideanDualRidgeletTransform` integrates it
over the whole parameter space `𝕐^{m+1} = ℝ^m × ℝ`. This file contains the elementary
dominated-convergence step relating the two: as soon as the full integrand is `volume`-integrable,
the truncated transform converges to the untruncated one along
`LeanRidgelet.ridgeletTruncationFilter`.

The proof is the standard one. The truncated transform is the integral of the full integrand
against the indicator of the annulus; along the filter `(𝓝[>] 0) ×ˢ atTop` those indicators
converge pointwise to `1` at every parameter with `a ≠ 0`, which is almost every parameter once
the input space is nontrivial; and they are dominated by the norm of the integrand itself.

## Main results

* `LeanRidgelet.measurableSet_truncationAnnulus`: the scale annulus is measurable.
* `LeanRidgelet.ae_parameter_fst_ne_zero`: almost every parameter has `a ≠ 0`.
* `LeanRidgelet.truncatedDualRidgeletTransform_eq_integral_indicator`: the truncated transform
  as an integral over the whole parameter space against the indicator of the annulus.
* `LeanRidgelet.tendsto_truncatedDualRidgeletTransform_of_integrable`: the truncation limit,
  `R†_η T (x; ε, δ) → R†_η T (x)` along `ridgeletTruncationFilter`.

## What this does **not** give

This lemma does **not** discharge the reconstruction hypothesis of the `L¹` endpoints
`LeanRidgelet.l1_reconstruction_formula` and `LeanRidgelet.l1_reconstruction_formula_L2`, and it
does **not** turn the hypothesis `hrec` of `LeanRidgelet.affineBochner_reconstruction_of_euclidean`
into a theorem. Its hypothesis is genuinely unavailable there. For the admissible pairs the `L¹`
track actually constructs — those of `LeanRidgelet.L1.BumpRidgelet`, feeding
`LeanRidgelet.l1_relu_network_universal_approximation` — the coefficient function is
`T = LeanRidgelet.euclideanRidgeletTransform m 1 ψ f`, and all that is known about it is
`LeanRidgelet.memLp_two_euclideanRidgeletTransform`: it is *square*-integrable against
`LeanRidgelet.ridgeletParameterMeasure m = volume.withDensity (‖a‖²)⁻¹`. Neither square
integrability against that measure nor anything else in the development yields integrability of
`p ↦ T p * η (⟪a, x⟫ - b) * ‖a‖⁻¹` against `volume`, which is what the hypothesis below asks for;
in particular `η` there is the ReLU, which is unbounded. So this is a conditional bridge, and the
condition is real: supplying it for the constructed pairs is new analytic work, not a corollary of
this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal Topology

namespace LeanRidgelet

/-! ## The annulus and the null set of vanishing weights -/

/-- The scale annulus `ε ≤ ‖a‖ ≤ δ` of the parameter space `𝕐^{m+1}` is measurable: it is the
preimage of `Set.Icc ε δ` under the continuous map `p ↦ ‖p.1‖`. -/
theorem measurableSet_truncationAnnulus (m : ℕ) (ε δ : ℝ) :
    MeasurableSet {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ} := by
  have hset : {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}
      = (fun p : RidgeletParameterSpace m => ‖p.1‖) ⁻¹' Set.Icc ε δ := rfl
  rw [hset]
  exact measurable_fst.norm measurableSet_Icc

/-- Almost every parameter has a nonzero weight component: the slice `a = 0` of the parameter
space is a null set as soon as the input space is nontrivial. This is what makes the scale
annulus exhaust `𝕐^{m+1}` up to a null set. -/
theorem ae_parameter_fst_ne_zero (m : ℕ) [NeZero m] :
    ∀ᵐ p : RidgeletParameterSpace m ∂volume, p.1 ≠ 0 := by
  rw [ae_iff]
  have hset : {p : RidgeletParameterSpace m | ¬ p.1 ≠ 0}
      = ({0} : Set (InputSpace m)) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]

/-! ## The truncation limit -/

/-- The truncated dual ridgelet transform is the integral over the whole parameter space of the
dual ridgelet integrand against the indicator of the scale annulus. -/
theorem truncatedDualRidgeletTransform_eq_integral_indicator (m : ℕ) (s : ℝ) (η : ℝ → ℂ)
    (T : RidgeletParameterSpace m → ℂ) (ε δ : ℝ) (x : InputSpace m) :
    truncatedDualRidgeletTransform m s η T ε δ x =
      ∫ p : RidgeletParameterSpace m,
        {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ}.indicator
          (fun p => T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ s : ℝ) : ℂ)⁻¹) p := by
  rw [truncatedDualRidgeletTransform, integral_indicator (measurableSet_truncationAnnulus m ε δ)]

/-- **The truncation limit of the dual ridgelet transform.** If the full dual ridgelet integrand
`p ↦ T p * η (⟪a, x⟫ - b) * ‖a‖^{-s}` is `volume`-integrable on the parameter space, then the
truncated dual ridgelet transform converges to the untruncated one along the truncation filter
`ridgeletTruncationFilter = (𝓝[>] 0) ×ˢ atTop`, i.e. as `ε → 0⁺` and `δ → ∞` jointly.

Read the honesty warning in the module docstring before using this: the integrability hypothesis
is not available for the admissible pairs constructed in `LeanRidgelet.L1.BumpRidgelet`, so this
does not upgrade the `L¹` reconstruction endpoints to untruncated statements. -/
theorem tendsto_truncatedDualRidgeletTransform_of_integrable (m : ℕ) [NeZero m] (s : ℝ)
    (η : ℝ → ℂ) (T : RidgeletParameterSpace m → ℂ) (x : InputSpace m)
    (hint : Integrable (fun p : RidgeletParameterSpace m =>
      T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ s : ℝ) : ℂ)⁻¹) volume) :
    Filter.Tendsto (fun q : ℝ × ℝ => truncatedDualRidgeletTransform m s η T q.1 q.2 x)
      ridgeletTruncationFilter (𝓝 (euclideanDualRidgeletTransform m s η T x)) := by
  classical
  haveI : Filter.IsCountablyGenerated ridgeletTruncationFilter := by
    unfold ridgeletTruncationFilter
    infer_instance
  set G : RidgeletParameterSpace m → ℂ := fun p =>
    T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ s : ℝ) : ℂ)⁻¹
  have hfull : euclideanDualRidgeletTransform m s η T x = ∫ p, G p := rfl
  rw [hfull]
  refine Filter.Tendsto.congr
    (fun q => (truncatedDualRidgeletTransform_eq_integral_indicator m s η T q.1 q.2 x).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖G p‖) ?_ ?_ hint.norm ?_
  · exact Filter.Eventually.of_forall fun q =>
      hint.aestronglyMeasurable.indicator (measurableSet_truncationAnnulus m q.1 q.2)
  · exact Filter.Eventually.of_forall fun q =>
      Filter.Eventually.of_forall fun p => norm_indicator_le_norm_self _ _
  · filter_upwards [ae_parameter_fst_ne_zero m] with p hp0
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
    exact (Set.indicator_of_mem hmem G).symm

end LeanRidgelet
