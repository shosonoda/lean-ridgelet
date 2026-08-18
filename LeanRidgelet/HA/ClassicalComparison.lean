/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.Affine
public import LeanRidgelet.L1.Defs
public import LeanRidgelet.Operator.ClassicalSynthesis

/-!
# The affine depth-two Bochner pair is the classical Euclidean ridgelet pair

This file is the link recorded as Theorem 2.3 of arXiv:2405.13682. The abstract Bochner synthesis
and ridgelet integrals of `LeanRidgelet.HA.BochnerIntertwining`, instantiated at the affine
fully-connected feature `φ(x, (a, b)) = σ(⟪a, x⟫ - b)` of `LeanRidgelet.HA.Affine` and at Lebesgue
measure, *are* the classical Euclidean transforms of the `L¹` track and the classical network
integral of the `L²` track.

Nothing is transported. `LeanRidgelet.RidgeletParameterSpace m` is by definition
`InputSpace m × ℝ`, which is already the harmonic-analysis parameter type `E × ℝ` for
`E := InputSpace m`, and `LeanRidgelet.affineRidgeArgument x p` is syntactically
`inner ℝ p.1 x - p.2`. So the four statements below are equalities of one integral with itself,
after the scalar action `•` on `ℂ` is read as multiplication and the homogeneity weight is read as
`1`. What they buy is that the harmonic-analysis composite becomes the object the classical
reconstruction theorems talk about: a Euclidean reconstruction formula, from either the `L¹` track
or the Fourier slice scheme, then transports to the affine Bochner pair verbatim.

## Main results

* `LeanRidgelet.bochnerSynthesis_affineFeature_eq_euclideanDualRidgeletTransform`: the affine
  Bochner synthesis integral is the classical dual ridgelet transform.
* `LeanRidgelet.bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform`: the affine Bochner
  ridgelet pairing is the classical Euclidean ridgelet transform.
* `LeanRidgelet.bochnerSynthesis_affineFeature_eq_classicalSynthesisIntegral`: the same synthesis
  integral is the `L²` track's classical network integral `∫ γ(a, b) σcl(⟪a, x⟫ - b) da db`.
* `LeanRidgelet.affineBochner_reconstruction_of_euclidean`: the payoff. Given a Euclidean
  reconstruction formula with constant `c`, the affine Bochner synthesis of the affine Bochner
  ridgelet transform of `f` is `c • f`, pointwise and with no further hypothesis.
* `LeanRidgelet.networkSynthesis_ae_eq_bochnerSynthesis_affineFeature`: on the Schwartz
  compatibility domain the bounded `L²` synthesis operator of `LeanRidgelet.HA.L2Bridge` is almost
  everywhere the affine Bochner synthesis integral.

## Deviations from the article

The comparison is made at homogeneity index `s = 0`, where the `L¹` weight `‖a‖^{±s}` is `1` and
the parameter measures of the two tracks agree on the nose. The manuscript fixes `s = 1` from its
Section 4 on; there the `L¹` parameter space carries `LeanRidgelet.ridgeletParameterMeasure`
rather than `volume`, and the comparison would first have to absorb `‖a‖^{-s}` into the
coefficient function. Nothing below depends on that case.

The Euclidean reconstruction formula enters
`LeanRidgelet.affineBochner_reconstruction_of_euclidean` as the hypothesis `hrec` rather than as a
fixed theorem, matching `LeanRidgelet.fs_groupConv_synthesis_ridgelet`. This is not only for
generality. The `L¹` endpoints `LeanRidgelet.l1_reconstruction_formula` and
`LeanRidgelet.l1_reconstruction_formula_L2` are limits of
`LeanRidgelet.truncatedDualRidgeletTransform` along `LeanRidgelet.ridgeletTruncationFilter` at
`s = 1`, whereas `LeanRidgelet.bochnerSynthesis` is a single absolutely convergent integral over
the whole parameter space. Replacing the truncated limit by the untruncated integral needs the
integrand to be `volume`-integrable there, and that fails for the admissible pairs the `L¹` theory
constructs: `LeanRidgelet.euclideanRidgeletTransform m 1 ψ f` is only square-integrable against
`LeanRidgelet.ridgeletParameterMeasure m`. Discharging `hrec` therefore needs analysis the
repository does not have, so it stays a hypothesis.

Neither side's depth-two formula contains a Fourier transform, so the angular/Mathlib
normalization distinction does not enter these statements. It enters only the admissibility
constants, which are untouched here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace LeanRidgelet

/-- The affine Bochner synthesis integral against Lebesgue measure on the ridge parameters is the
classical dual ridgelet transform at homogeneity index `s = 0`. Both sides are literally the same
integral: `•` on `ℂ` is multiplication and the weight `‖a‖^0` is `1`. -/
theorem bochnerSynthesis_affineFeature_eq_euclideanDualRidgeletTransform
    {m : ℕ} (η : ℝ → ℂ) (T : RidgeletParameterSpace m → ℂ) (x : InputSpace m) :
    bochnerSynthesis (Y := ℂ) (volume : Measure (RidgeletParameterSpace m))
        (affineFeature (E := InputSpace m) η) T x =
      euclideanDualRidgeletTransform m 0 η T x := by
  have hweight : ∀ a : InputSpace m, ((‖a‖ ^ (0 : ℝ) : ℝ) : ℂ)⁻¹ = 1 := by
    intro a
    rw [Real.rpow_zero, Complex.ofReal_one, inv_one]
  have hpoint : ∀ p : RidgeletParameterSpace m,
      T p • affineFeature (E := InputSpace m) η x p =
        T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ (0 : ℝ) : ℝ) : ℂ)⁻¹ := by
    intro p
    rw [hweight p.1, mul_one]
    rfl
  simp only [bochnerSynthesis, euclideanDualRidgeletTransform]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- The affine Bochner ridgelet pairing against Lebesgue measure on the data is the classical
Euclidean ridgelet transform at homogeneity index `s = 0`. Mathlib's inner product on `ℂ` is
conjugate-linear in its first argument, which is exactly the conjugation on the analysing
function in the classical formula. -/
theorem bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform
    {m : ℕ} (ψ : ℝ → ℂ) (f : InputSpace m → ℂ) (p : RidgeletParameterSpace m) :
    bochnerRidgelet (Y := ℂ) (volume : Measure (InputSpace m))
        (affineFeature (E := InputSpace m) ψ) f p =
      euclideanRidgeletTransform m 0 ψ f p := by
  have hweight : ((‖p.1‖ ^ (0 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [Real.rpow_zero, Complex.ofReal_one]
  have hpoint : ∀ x : InputSpace m,
      ⟪affineFeature (E := InputSpace m) ψ x p, f x⟫_ℂ =
        f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ (0 : ℝ) : ℝ) : ℂ) := by
    intro x
    rw [hweight, mul_one]
    exact RCLike.inner_apply _ _
  simp only [bochnerRidgelet, euclideanRidgeletTransform]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- The affine Bochner synthesis integral of a Schwartz coefficient function is the `L²` track's
classical network integral. -/
theorem bochnerSynthesis_affineFeature_eq_classicalSynthesisIntegral
    {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (σcl : ℝ → ℂ) (x : InputSpace m) :
    bochnerSynthesis (Y := ℂ) (volume : Measure (InputSpace m × ℝ))
        (affineFeature (E := InputSpace m) σcl) (⇑γ) x =
      classicalSynthesisIntegral γ σcl x := by
  have hpoint : ∀ p : InputSpace m × ℝ,
      γ p • affineFeature (E := InputSpace m) σcl x p =
        γ p * σcl (inner ℝ p.1 x - p.2) := fun _ => rfl
  simp only [bochnerSynthesis, classicalSynthesisIntegral]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- **The classical reconstruction formula for the affine depth-two Bochner pair.** Whenever the
classical Euclidean dual ridgelet transform inverts the classical Euclidean ridgelet transform up
to a constant `c`, the affine Bochner synthesis inverts the affine Bochner ridgelet transform up
to the same constant, pointwise and with no hypothesis on the target.

The Euclidean reconstruction formula is a hypothesis rather than a fixed theorem, as in
`LeanRidgelet.fs_groupConv_synthesis_ridgelet`, so that any of them may be used; see the module
docstring for why the `L¹` endpoints of this repository do not currently supply it. -/
theorem affineBochner_reconstruction_of_euclidean
    {m : ℕ} {η ψ : ℝ → ℂ} {c : ℂ}
    (hrec : ∀ (F : InputSpace m → ℂ) (y : InputSpace m),
      euclideanDualRidgeletTransform m 0 η (euclideanRidgeletTransform m 0 ψ F) y = c * F y)
    (f : InputSpace m → ℂ) (x : InputSpace m) :
    bochnerSynthesis (Y := ℂ) (volume : Measure (InputSpace m × ℝ))
        (affineFeature (E := InputSpace m) η)
        (bochnerRidgelet (Y := ℂ) (volume : Measure (InputSpace m))
          (affineFeature (E := InputSpace m) ψ) f) x =
      c * f x := by
  have hcoef : bochnerRidgelet (Y := ℂ) (volume : Measure (InputSpace m))
      (affineFeature (E := InputSpace m) ψ) f = euclideanRidgeletTransform m 0 ψ f :=
    funext fun p => bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform ψ f p
  rw [hcoef, bochnerSynthesis_affineFeature_eq_euclideanDualRidgeletTransform, hrec]

/-- On the Schwartz compatibility domain of the `L²` track, the bounded synthesis operator is
almost everywhere the affine Bochner synthesis integral. This is what connects the operator-level
bridge of `LeanRidgelet.HA.L2Bridge` to the integral formulas above; the hypotheses are exactly
those of `LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae`. -/
theorem networkSynthesis_ae_eq_bochnerSynthesis_affineFeature
    {m : ℕ} [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) {σcl : ℝ → ℂ}
    (hσcl : ∀ φ : SchwartzMap ℝ ℂ,
      activationRealization s t σ φ = ∫ z : ℝ, φ z * σcl z)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume)
    (hint : ∀ x : InputSpace m,
      Integrable (fun p : InputSpace m × ℝ ↦ γ p * σcl (inner ℝ p.1 x - p.2))) :
    networkSynthesis m s t σ (parameterSchwartzRealization s t γ hγ) =ᵐ[volume]
      bochnerSynthesis (Y := ℂ) (volume : Measure (InputSpace m × ℝ))
        (affineFeature (E := InputSpace m) σcl) (⇑γ) := by
  filter_upwards [networkSynthesis_parameterSchwartzRealization_classical_ae s t σ hσcl γ hγ hint]
    with x hx
  rw [hx, bochnerSynthesis_affineFeature_eq_classicalSynthesisIntegral]

end LeanRidgelet
