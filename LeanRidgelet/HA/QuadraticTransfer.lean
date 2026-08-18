/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import LeanRidgelet.HA.QuadraticComposite

/-!
# Transferring derivatives across the quadratic analysis transform

The obstruction recorded in `LeanRidgelet.HA.QuadraticComposite` is that a square-integrable kernel
makes the reconstruction operator compact, so the Schur constant vanishes.  Escaping it needs a
weight that is not of that form, and the weight the L1 and L2 theories use comes from smoothness:
the
analysis transform is a convolution in the additive parameter, so a derivative in that parameter can
be moved onto the analysis feature, and iterating produces decay of the transform in the dual
variable.  A weighted space with that decay as its weight is then an intermediate space through
which
the analysis and the synthesis are separately bounded, and neither is Hilbert--Schmidt.

This file proves the transfer step for the quadratic feature.  The constant coefficient of a
quadratic parameter enters the feature additively, so differentiating the analysis transform in it
replaces the analysis feature by its derivative and changes nothing else.  That is the transfer the
weights rest on.

## Main results

* `LeanRidgelet.hasDerivAt_quadraticAnalysisPairing`: the integrand's derivative in the constant
  coefficient is the integrand of the derivative feature.
* `LeanRidgelet.hasDerivAt_bochnerRidgelet_quadraticVectorFeature`: the analysis transform is
  differentiable in the constant coefficient, with derivative the analysis transform of the
  derivative feature.
* `LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature`: iterating it, the `k`-th
  derivative in the constant coefficient is the analysis transform of the `k`-th feature.

## Where the weights come from

Iterating the second result gives, for a `k`-times differentiable analysis feature, that the `k`-th
derivative of the transform in the constant coefficient is the transform of the `k`-th derivative
feature.  On the Fourier side in that variable this is multiplication by the `k`-th power of the
frequency, so a bound on the transform of the derivative feature is a bound on the transform in the
weighted space with weight the `2k`-th power of the frequency.  That exponent is the analogue of the
smoothness index `s` of the L2 activation spaces; the growth index `t` arises the same way from
multiplication by a polynomial in the constant coefficient, which on the Fourier side is a
derivative.  Neither weight can be moved onto the parameter measure, whose balance is fixed by
`LeanRidgelet.HA.QuadraticRelativeMeasure`, which is why it belongs on the coefficient space.

The hypotheses of the differentiation are the ones Mathlib's dominated-convergence differentiation
lemma consumes, and they are exactly where smoothness of the data and of the analysis feature enter:
the dominating function is what a bound on the data and on the derivative feature supplies.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The constant coefficient of a quadratic parameter enters the feature additively. -/
theorem quadraticArgument_const_add (x : E) (A : QuadraticSymmetric E) (b : E) (c : ℝ) :
    quadraticArgument x (A, b, c) = (⟪x, (A : E →L[ℝ] E) x⟫_ℝ + ⟪x, b⟫_ℝ) + c := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Differentiating the integrand of the analysis transform in the constant coefficient replaces the
analysis feature by its derivative.  This is the transfer of a derivative across the convolution in
the additive parameter. -/
theorem hasDerivAt_quadraticAnalysisPairing {ρ ρ' : ℝ → ℂ}
    (hderiv : ∀ z : ℝ, HasDerivAt ρ (ρ' z) z) (v : ℂ) (x : E) (A : QuadraticSymmetric E) (b : E)
    (c : ℝ) :
    HasDerivAt (fun c : ℝ ↦ v * conj (quadraticVectorFeature ρ x (A, b, c)))
      (v * conj (quadraticVectorFeature ρ' x (A, b, c))) c := by
  have hshift : HasDerivAt
      (fun c : ℝ ↦ ρ (quadraticArgument x (A, b, c)))
      (ρ' (quadraticArgument x (A, b, c))) c :=
    (hderiv ((⟪x, (A : E →L[ℝ] E) x⟫_ℝ + ⟪x, b⟫_ℝ) + c)).comp_const_add
      (⟪x, (A : E →L[ℝ] E) x⟫_ℝ + ⟪x, b⟫_ℝ) c
  simpa [quadraticVectorFeature, RCLike.star_def] using
    (HasDerivAt.star hshift).const_mul v

variable [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

omit [Nontrivial E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The analysis transform of the quadratic feature is differentiable in the constant coefficient of
the parameter, with derivative the analysis transform of the derivative feature.  The hypotheses are
those of the dominated-convergence differentiation lemma: the dominating function is what smoothness
of the data and of the analysis feature supplies. -/
theorem hasDerivAt_bochnerRidgelet_quadraticVectorFeature {ρ ρ' : ℝ → ℂ} (f : E → ℂ)
    (A : QuadraticSymmetric E) (b : E) (c₀ : ℝ) {ε : ℝ} (hε : 0 < ε) {bound : E → ℝ}
    (hderiv : ∀ z : ℝ, HasDerivAt ρ (ρ' z) z)
    (hmeas : ∀ᶠ c in nhds c₀, AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature ρ x (A, b, c))) (volume : Measure E))
    (hint : Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature ρ x (A, b, c₀))) (volume : Measure E))
    (hmeas' : AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature ρ' x (A, b, c₀))) (volume : Measure E))
    (hbound : ∀ᵐ x ∂(volume : Measure E), ∀ c ∈ Metric.ball c₀ ε,
      ‖f x * conj (quadraticVectorFeature ρ' x (A, b, c))‖ ≤ bound x)
    (hboundint : Integrable bound (volume : Measure E)) :
    HasDerivAt
      (fun c : ℝ ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ρ) f (A, b, c))
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ρ') f (A, b, c₀)) c₀ := by
  have hpair : ∀ (τ : ℝ → ℂ) (c : ℝ),
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature τ) f (A, b, c) =
        ∫ x, f x * conj (quadraticVectorFeature τ x (A, b, c)) ∂(volume : Measure E) := by
    intro τ c
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [RCLike.inner_apply]
  simp only [hpair]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds c₀ hε)
    hmeas hint hmeas' hbound hboundint ?_).2
  filter_upwards with x
  intro c _
  exact hasDerivAt_quadraticAnalysisPairing hderiv (f x) x A b c


omit [Nontrivial E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- **Iterating the transfer.**  Given a sequence of analysis features each the derivative of the
previous one, the `k`-th derivative of the analysis transform in the constant coefficient is the
analysis transform of the `k`-th feature.  This is the identity that produces the frequency weight:
on the Fourier side in the constant coefficient the left-hand side is multiplication by the `k`-th
power of the frequency, so the transform lies in the space weighted by the `2k`-th power of the
frequency with its norm controlled by the `k`-th feature. -/
theorem iteratedDeriv_bochnerRidgelet_quadraticVectorFeature {ρ : ℕ → ℝ → ℂ} (f : E → ℂ)
    (A : QuadraticSymmetric E) (b : E) {bound : ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ i c, AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ i c, Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ i, ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound i x)
    (hboundint : ∀ i, Integrable (bound i) (volume : Measure E)) (k : ℕ) :
    iteratedDeriv k
        (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f (A, b, c)) =
      fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ k)) f (A, b, c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ∀ c₀ : ℝ, HasDerivAt
        (fun c ↦ bochnerRidgelet (volume : Measure E)
          (quadraticVectorFeature (ρ k)) f (A, b, c))
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ (k + 1))) f (A, b, c₀))
        c₀ := by
      intro c₀
      refine hasDerivAt_bochnerRidgelet_quadraticVectorFeature f A b c₀ one_pos
        (hderiv k) (Filter.Eventually.of_forall fun c ↦ hmeas k c) (hint k c₀)
        (hmeas (k + 1) c₀) ?_ (hboundint k)
      filter_upwards [hbound k] with x hx
      exact fun c _ ↦ hx c
    rw [iteratedDeriv_succ, ih]
    funext c
    exact (hstep c).deriv

end LeanRidgelet
