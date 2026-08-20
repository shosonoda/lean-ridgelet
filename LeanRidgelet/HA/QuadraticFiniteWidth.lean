/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.BochnerMeasurability
public import LeanRidgelet.HA.SecondDifference
public import LeanRidgelet.ToMathlib.LipschitzDiscretization

/-!
# Finite-width approximation of the quadratic-form network

Appendix C of the article approximates an integral representation uniformly by finite networks.  The
general statement is proved in `LeanRidgelet.ToMathlib.LipschitzDiscretization` -- for a Lipschitz
family of bounded continuous functions indexed by a compact metric space carrying a finite measure,
the Bochner integral is a uniform limit of nonnegative-weighted finite sums -- and this file
instantiates it at the quadratic feature.

Two conditions on the activation make the instantiation possible, and both are the usual ones for a
uniform-approximation theorem.  It has to be continuous, so that the feature is continuous in the
data; and it has to be bounded, so that the feature lies in the space of bounded continuous
functions
whose norm is the supremum norm.  An activation of polynomial growth, the rectified linear unit
included, is excluded here for the second reason: `x ↦ σ (q_ξ x)` is unbounded, so it is not an
element
of that space at all, and a uniform-in-`x` approximation over an unbounded data space is not what
one
would want for it either.

The parameter side has to be compact and of finite measure, which the relatively invariant parameter
measure is not, so the family is indexed by an abstract compact metric space mapping into the
parameter space.  That is the honest form: a finite network is a finite sum of features at finitely
many parameters, and the theorem says the integral over any compact family is approximated by such a
sum, uniformly in the data.

## Main results

* `LeanRidgelet.quadraticFeatureBoundedContinuous`: the quadratic feature at a fixed parameter, as a
  bounded continuous function of the data, for a bounded continuous activation.
* `LeanRidgelet.exists_finite_quadraticNetwork_approx`: **Appendix C for the quadratic-form
  network.**  The synthesis integral over a compact family of parameters is approximated, uniformly
  in
  the data, by a finite network with nonnegative weights.

## What is assumed

Continuity and boundedness of the activation; a compact metric index space with a finite Borel
measure; and that the coefficient-weighted feature family is Lipschitz in the index.  The last is
the
hypothesis of the general theorem and is where the geometry of the parameter family enters; it is
carried rather than derived, since it depends on the family and on the activation's modulus of
continuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The feature as a bounded continuous function -/

/-- The quadratic feature at a fixed parameter is continuous in the data: the scalar argument is
jointly continuous, and the activation is continuous. -/
theorem continuous_quadraticVectorFeature {σ : ℝ → ℂ} (hσ : Continuous σ)
    (ξ : QuadraticParameter E) :
    Continuous fun x : E ↦ quadraticVectorFeature σ x ξ :=
  hσ.comp (continuous_uncurry_quadraticArgument.comp (continuous_id.prodMk continuous_const))

/-- **The quadratic feature as a bounded continuous function of the data.**  For a bounded
continuous
activation the feature at a fixed parameter is an element of the space whose norm is the supremum
norm, which is the space Appendix C's approximation is uniform in. -/
def quadraticFeatureBoundedContinuous {σ : ℝ → ℂ} (hσc : Continuous σ) {C : ℝ}
    (hσb : ∀ z : ℝ, ‖σ z‖ ≤ C) (ξ : QuadraticParameter E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ quadraticVectorFeature σ x ξ, continuous_quadraticVectorFeature hσc ξ⟩ (2 * C)
    fun x y ↦ by
      calc dist (quadraticVectorFeature σ x ξ) (quadraticVectorFeature σ y ξ)
          = ‖quadraticVectorFeature σ x ξ - quadraticVectorFeature σ y ξ‖ := dist_eq_norm _ _
        _ ≤ ‖quadraticVectorFeature σ x ξ‖ + ‖quadraticVectorFeature σ y ξ‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hσb _) (hσb _)
        _ = 2 * C := by ring

theorem quadraticFeatureBoundedContinuous_apply {σ : ℝ → ℂ} (hσc : Continuous σ) {C : ℝ}
    (hσb : ∀ z : ℝ, ‖σ z‖ ≤ C) (ξ : QuadraticParameter E) (x : E) :
    quadraticFeatureBoundedContinuous hσc hσb ξ x = quadraticVectorFeature σ x ξ := rfl

/-! ### Appendix C for the quadratic-form network -/

/-- **Uniform approximation of the quadratic-form network by a finite network.**  The synthesis
integral of a coefficient function over a compact family of quadratic parameters is approximated, to
any accuracy and uniformly in the data, by a finite sum of features at finitely many parameters with
nonnegative weights.  This is Appendix C of the article at the Section 7 architecture.

The hypotheses are those of the general theorem: the activation is continuous and bounded, the index
space is compact metric with a finite Borel measure, and the coefficient-weighted family is
Lipschitz
in the index.  The conclusion is stated pointwise in the data, which is what the supremum norm of
the
approximating space gives. -/
theorem exists_finite_quadraticNetwork_approx {σ : ℝ → ℂ} (hσc : Continuous σ) {C : ℝ}
    (hσb : ∀ z : ℝ, ‖σ z‖ ≤ C) {Ξ : Type*} [MetricSpace Ξ] [CompactSpace Ξ] [MeasurableSpace Ξ]
    [BorelSpace Ξ] (κ : Measure Ξ) [IsFiniteMeasure κ] (ι : Ξ → QuadraticParameter E) (γ : Ξ → ℂ)
    {L : ℝ≥0}
    (hlip : LipschitzWith L fun t ↦ γ t • quadraticFeatureBoundedContinuous hσc hσb (ι t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (t : Fin n → Ξ), (∀ i, 0 ≤ w i) ∧
      ∀ x : E, ‖(∫ s, γ s • quadraticVectorFeature σ x (ι s) ∂κ) -
        ∑ i, w i • (γ (t i) • quadraticVectorFeature σ x (ι (t i)))‖ < ε := by
  set φ : Ξ → E →ᵇ ℂ := fun t ↦ γ t • quadraticFeatureBoundedContinuous hσc hσb (ι t) with hφ
  obtain ⟨n, w, t, hw, _, hunif⟩ :=
    exists_finsetSum_approx_integral_boundedContinuous_of_lipschitz κ hlip hε
  refine ⟨n, w, t, hw, fun x ↦ ?_⟩
  have hint : Integrable φ κ := integrable_of_lipschitzWith κ hlip
  have heval : (∫ s, φ s ∂κ) x = ∫ s, γ s • quadraticVectorFeature σ x (ι s) ∂κ := by
    have h := (ContinuousLinearMap.integral_comp_comm
      (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) x) hint).symm
    simpa [hφ, quadraticFeatureBoundedContinuous_apply, smul_eq_mul] using h
  have h := hunif x
  rw [heval] at h
  simpa [hφ, quadraticFeatureBoundedContinuous_apply, smul_eq_mul] using h

/-! ### The hat function satisfies the hypotheses -/

/-- **The reduced activation as a bounded continuous feature.**  The hat function of
`LeanRidgelet.HA.SecondDifference` -- the second difference of the rectified linear unit -- is
continuous and bounded, so the feature it defines is an element of the space whose norm is the
supremum norm.  An activation of polynomial growth is not; differencing it twice is what makes the
finite-width theorem applicable, and it costs only a change of analysis feature. -/
def quadraticHatFeatureBoundedContinuous (h : ℝ) (ξ : QuadraticParameter E) : E →ᵇ ℂ :=
  quadraticFeatureBoundedContinuous (continuous_hatComplex h) (norm_hatComplex_le h) ξ

theorem quadraticHatFeatureBoundedContinuous_apply (h : ℝ) (ξ : QuadraticParameter E) (x : E) :
    quadraticHatFeatureBoundedContinuous h ξ x = quadraticVectorFeature (hatComplex h) x ξ := rfl

/-- **Appendix C for the reduced activation.**  The finite-width approximation applies to the hat
function, hence -- through the reduction of
`LeanRidgelet.bochnerSynthesis_bochnerRidgelet_reluComplex_secondDifference` -- to a network whose
activation is the rectified linear unit, once the second difference is built into the analysis
feature. -/
theorem exists_finite_quadraticNetwork_approx_hat (h : ℝ) {Ξ : Type*} [MetricSpace Ξ]
    [CompactSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ] (κ : Measure Ξ) [IsFiniteMeasure κ]
    (ι : Ξ → QuadraticParameter E) (γ : Ξ → ℂ) {L : ℝ≥0}
    (hlip : LipschitzWith L fun t ↦ γ t • quadraticHatFeatureBoundedContinuous h (ι t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (t : Fin n → Ξ), (∀ i, 0 ≤ w i) ∧
      ∀ x : E, ‖(∫ s, γ s • quadraticVectorFeature (hatComplex h) x (ι s) ∂κ) -
        ∑ i, w i • (γ (t i) • quadraticVectorFeature (hatComplex h) x (ι (t i)))‖ < ε :=
  exists_finite_quadraticNetwork_approx (continuous_hatComplex h) (norm_hatComplex_le h) κ ι γ
    hlip hε

end LeanRidgelet
