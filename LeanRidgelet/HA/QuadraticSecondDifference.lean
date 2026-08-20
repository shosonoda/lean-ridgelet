/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.SecondDifference
public import LeanRidgelet.HA.QuadraticShear
public import LeanRidgelet.HA.QuadraticTransfer

/-!
# Moving a second difference across the quadratic transforms

`LeanRidgelet.HA.SecondDifference` computes that a second difference turns the rectified linear unit
into the hat function -- bounded, compactly supported, of positive integral.  This file moves the
difference where it has to go: **onto the activation**, so that a synthesis integral against an
activation of polynomial growth becomes a synthesis integral against the hat function.

The mechanism is the one the derivative transfer of `LeanRidgelet.HA.QuadraticTransfer` uses, and it
is cheaper.  The constant coefficient enters the feature additively, so a difference in it is a
combination of translations of the activation's argument, and moving it across the parameter
integral
is summation by parts: three translations, three changes of variable, no integration by parts and no
boundary term.  What the measure has to supply is translation invariance in the constant
coefficient,
which is a hypothesis here and which the factorization of
`LeanRidgelet.HA.QuadraticParameterFactor` supplies.

The same move works on the analysis side without any hypothesis on the measure at all: a difference
in the constant coefficient of the analysis transform is the analysis transform of the differenced
feature, because the difference acts on the data integral's integrand pointwise.

Both moves respect the group action.  The action is a shear in the constant coefficient, so it
commutes with a translation there, hence with a difference: `LeanRidgelet` records this as
`LeanRidgelet.quadraticConstSecondDifference_comp_smul`, the difference analogue of the derivative
statement in `LeanRidgelet.HA.QuadraticShear` and easier, since no differentiability is involved.

## Main results

* `LeanRidgelet.quadraticConstSecondDifference`: the second difference in the constant coefficient
of
  a coefficient function on the parameter space.
* `LeanRidgelet.quadraticConstSecondDifference_comp_smul`: it commutes with the parameter action.
* `LeanRidgelet.bochnerRidgelet_secondDifference_feature`: **the analysis side.**  Differencing the
  analysis feature differences the transform in the constant coefficient.
* `LeanRidgelet.bochnerSynthesis_quadraticConstSecondDifference`: **the synthesis side.**  The
  synthesis integral of a differenced coefficient function against an activation is the synthesis
  integral of the coefficient function against the differenced activation.

## What is assumed

On the analysis side, integrability of the three translated integrands -- what splitting one
integral
into three needs.  On the synthesis side, the same for the parameter integral, together with
invariance of the parameter measure under a translation of the constant coefficient.  Nothing is
assumed about the activation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The difference in the constant coefficient -/

/-- The second difference in the constant coefficient of a coefficient function on the parameter
space. -/
def quadraticConstSecondDifference (h : ℝ) (T : QuadraticParameter E → ℂ) :
    QuadraticParameter E → ℂ :=
  fun ξ ↦ T (ξ.1, ξ.2.1, ξ.2.2 + h) - 2 * T ξ + T (ξ.1, ξ.2.1, ξ.2.2 - h)

@[simp]
theorem quadraticConstSecondDifference_apply (h : ℝ) (T : QuadraticParameter E → ℂ)
    (ξ : QuadraticParameter E) :
    quadraticConstSecondDifference h T ξ =
      T (ξ.1, ξ.2.1, ξ.2.2 + h) - 2 * T ξ + T (ξ.1, ξ.2.1, ξ.2.2 - h) := rfl

/-- The second difference in the constant coefficient is the second difference of the slice. -/
theorem quadraticConstSecondDifference_eq_slice (h : ℝ) (T : QuadraticParameter E → ℂ)
    (ξ : QuadraticParameter E) :
    quadraticConstSecondDifference h T ξ =
      secondDifference h (quadraticConstSlice T (ξ.1, ξ.2.1)) ξ.2.2 := rfl

/-- **The difference commutes with the parameter action.**  The action is a shear in the constant
coefficient, so it translates that coefficient by an amount depending only on the other two, and a
translation commutes with a difference on the nose.  This is the difference analogue of
`LeanRidgelet.quadraticConstIteratedDeriv_comp_smul`, and it needs no differentiability. -/
theorem quadraticConstSecondDifference_comp_smul (h : ℝ) (T : QuadraticParameter E → ℂ)
    (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticConstSecondDifference h (fun η ↦ T (g • η)) ξ =
      quadraticConstSecondDifference h T (g • ξ) := by
  have hshear : ∀ t : ℝ, (g • (ξ.1, ξ.2.1, ξ.2.2 + t) : QuadraticParameter E) =
      ((g • ξ).1, (g • ξ).2.1, (g • ξ).2.2 + t) := by
    intro t
    change quadraticParameterLinearEquiv g (ξ.1, ξ.2.1, ξ.2.2 + t) =
      ((quadraticParameterLinearEquiv g (ξ.1, ξ.2.1, ξ.2.2)).1,
        (quadraticParameterLinearEquiv g (ξ.1, ξ.2.1, ξ.2.2)).2.1,
        (quadraticParameterLinearEquiv g (ξ.1, ξ.2.1, ξ.2.2)).2.2 + t)
    rw [quadraticParameterLinearEquiv_apply_shear g ξ.1 ξ.2.1 (ξ.2.2 + t),
      quadraticParameterLinearEquiv_apply_shear g ξ.1 ξ.2.1 ξ.2.2]
    exact Prod.ext rfl (Prod.ext rfl (by ring))
  simp only [quadraticConstSecondDifference_apply, hshear h, sub_eq_add_neg, hshear (-h)]

/-! ### The scalar argument under a shift of the constant coefficient -/

/-- The constant coefficient enters the scalar argument additively, so shifting it shifts the
argument. -/
theorem quadraticArgument_const_shift (t : ℝ) (x : E) (ξ : QuadraticParameter E) :
    quadraticArgument x (ξ.1, ξ.2.1, ξ.2.2 + t) = quadraticArgument x ξ + t := by
  simp only [quadraticArgument]
  ring

/-! ### The analysis side -/

variable [MeasurableSpace E] [BorelSpace E]

/-- **Differencing the analysis feature differences the transform.**  The constant coefficient
enters
the feature additively, so a difference in it acts on the data integral's integrand pointwise; the
only hypothesis is the integrability that lets one integral be split into three. -/
theorem bochnerRidgelet_secondDifference_feature (h : ℝ) {ψ : ℝ → ℂ} (f : E → ℂ)
    (ξ : QuadraticParameter E)
    (hplus : Integrable (fun x ↦ f x * conj (ψ (quadraticArgument x ξ + h)))
      (volume : Measure E))
    (hzero : Integrable (fun x ↦ f x * conj (ψ (quadraticArgument x ξ))) (volume : Measure E))
    (hminus : Integrable (fun x ↦ f x * conj (ψ (quadraticArgument x ξ - h)))
      (volume : Measure E)) :
    bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (secondDifference h ψ)) f ξ =
      quadraticConstSecondDifference h
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) f) ξ := by
  have hsplit : ∀ x : E,
      f x * conj (secondDifference h ψ (quadraticArgument x ξ)) =
        (f x * conj (ψ (quadraticArgument x ξ + h)) -
            2 * (f x * conj (ψ (quadraticArgument x ξ)))) +
          f x * conj (ψ (quadraticArgument x ξ - h)) := by
    intro x
    simp only [secondDifference_apply, map_add, map_sub, map_mul, Complex.conj_ofNat]
    ring
  have key : ∀ t : ℝ,
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) f
          (ξ.1, ξ.2.1, ξ.2.2 + t) =
        ∫ x, f x * conj (ψ (quadraticArgument x ξ + t)) ∂(volume : Measure E) := by
    intro t
    simp only [bochnerRidgelet, quadraticVectorFeature, RCLike.inner_apply,
      quadraticArgument_const_shift]
  have key0 : bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) f ξ =
      ∫ x, f x * conj (ψ (quadraticArgument x ξ)) ∂(volume : Measure E) := by
    simp only [bochnerRidgelet, quadraticVectorFeature, RCLike.inner_apply]
  have keyD : bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (secondDifference h ψ)) f ξ =
      ∫ x, f x * conj (secondDifference h ψ (quadraticArgument x ξ)) ∂(volume : Measure E) := by
    simp only [bochnerRidgelet, quadraticVectorFeature, RCLike.inner_apply]
  rw [keyD, quadraticConstSecondDifference_apply, key h, key0,
    show ξ.2.2 - h = ξ.2.2 + (-h) from by ring, key (-h)]
  simp only [← sub_eq_add_neg]
  have hsub : Integrable (fun x ↦ f x * conj (ψ (quadraticArgument x ξ + h)) -
      2 * (f x * conj (ψ (quadraticArgument x ξ)))) (volume : Measure E) :=
    hplus.sub (hzero.const_mul 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add hsub hminus,
    integral_sub hplus (hzero.const_mul 2), integral_const_mul]

/-! ### The synthesis side -/

variable [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The translation of the constant coefficient, as a measurable equivalence of the parameter
space. -/
def quadraticConstTranslate (t : ℝ) : QuadraticParameter E ≃ᵐ QuadraticParameter E :=
  (MeasurableEquiv.refl (QuadraticSymmetric E)).prodCongr
    ((MeasurableEquiv.refl E).prodCongr (MeasurableEquiv.addRight t))

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
@[simp]
theorem quadraticConstTranslate_apply (t : ℝ) (ξ : QuadraticParameter E) :
    quadraticConstTranslate t ξ = (ξ.1, ξ.2.1, ξ.2.2 + t) := rfl

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The scalar argument of the feature at a translated parameter is the argument translated: the
constant coefficient enters additively. -/
theorem quadraticArgument_quadraticConstTranslate (t : ℝ) (x : E) (ξ : QuadraticParameter E) :
    quadraticArgument x (quadraticConstTranslate (E := E) t ξ) = quadraticArgument x ξ + t :=
  quadraticArgument_const_shift t x ξ

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- Integrating a translated integrand against a translation-invariant measure changes nothing. -/
theorem integral_comp_quadraticConstTranslate {ν : Measure (QuadraticParameter E)} {t : ℝ}
    (hν : Measure.map (quadraticConstTranslate (E := E) t) ν = ν)
    (F : QuadraticParameter E → ℂ) :
    ∫ ξ, F (quadraticConstTranslate (E := E) t ξ) ∂ν = ∫ ξ, F ξ ∂ν := by
  rw [← integral_map_equiv (quadraticConstTranslate (E := E) t) F, hν]

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- Integrability transports along the translation. -/
theorem integrable_comp_quadraticConstTranslate {ν : Measure (QuadraticParameter E)} {t : ℝ}
    (hν : Measure.map (quadraticConstTranslate (E := E) t) ν = ν)
    {F : QuadraticParameter E → ℂ} (hF : Integrable F ν) :
    Integrable (fun ξ ↦ F (quadraticConstTranslate (E := E) t ξ)) ν :=
  (integrable_map_equiv (quadraticConstTranslate (E := E) t) F).1 (by rwa [hν])

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **Summation by parts in the constant coefficient.**  For a parameter measure invariant under
translation of the constant coefficient, the synthesis integral of a differenced coefficient
function
against an activation is the synthesis integral of the coefficient function against the differenced
activation.  Three translations and three changes of variable; no integration by parts, no boundary
term, and no hypothesis on the activation.

This is what reduces an activation of polynomial growth to a bounded one: combined with
`LeanRidgelet.secondDifference_relu`, the right-hand side is a synthesis integral against the hat
function. -/
theorem bochnerSynthesis_quadraticConstSecondDifference {ν : Measure (QuadraticParameter E)}
    {h : ℝ} (hνp : Measure.map (quadraticConstTranslate (E := E) h) ν = ν)
    (hνm : Measure.map (quadraticConstTranslate (E := E) (-h)) ν = ν) {σ : ℝ → ℂ}
    (γ : QuadraticParameter E → ℂ) (x : E)
    (hplus : Integrable (fun ξ ↦ γ ξ * σ (quadraticArgument x ξ + h)) ν)
    (hzero : Integrable (fun ξ ↦ γ ξ * σ (quadraticArgument x ξ)) ν)
    (hminus : Integrable (fun ξ ↦ γ ξ * σ (quadraticArgument x ξ - h)) ν) :
    bochnerSynthesis ν (quadraticVectorFeature σ) (quadraticConstSecondDifference h γ) x =
      bochnerSynthesis ν (quadraticVectorFeature (secondDifference h σ)) γ x := by
  have hAint : Integrable
      (fun ξ ↦ γ (quadraticConstTranslate (E := E) h ξ) * σ (quadraticArgument x ξ)) ν := by
    have := integrable_comp_quadraticConstTranslate hνp hminus
    exact this.congr (Filter.Eventually.of_forall fun ξ ↦ by
      simp [quadraticArgument_const_shift])
  have hBint : Integrable
      (fun ξ ↦ γ (quadraticConstTranslate (E := E) (-h) ξ) * σ (quadraticArgument x ξ)) ν := by
    have := integrable_comp_quadraticConstTranslate hνm hplus
    exact this.congr (Filter.Eventually.of_forall fun ξ ↦ by
      simp [quadraticArgument_const_shift])
  have hA : ∫ ξ, γ (quadraticConstTranslate (E := E) h ξ) * σ (quadraticArgument x ξ) ∂ν =
      ∫ ξ, γ ξ * σ (quadraticArgument x ξ - h) ∂ν := by
    rw [← integral_comp_quadraticConstTranslate hνp
      fun η ↦ γ η * σ (quadraticArgument x η - h)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by
      simp [quadraticArgument_const_shift])
  have hB : ∫ ξ, γ (quadraticConstTranslate (E := E) (-h) ξ) * σ (quadraticArgument x ξ) ∂ν =
      ∫ ξ, γ ξ * σ (quadraticArgument x ξ + h) ∂ν := by
    rw [← integral_comp_quadraticConstTranslate hνm
      fun η ↦ γ η * σ (quadraticArgument x η + h)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by
      simp [quadraticArgument_const_shift])
  simp only [bochnerSynthesis, smul_eq_mul, quadraticVectorFeature, secondDifference_apply,
    quadraticConstSecondDifference_apply]
  have hleft : ∀ ξ : QuadraticParameter E,
      (γ (ξ.1, ξ.2.1, ξ.2.2 + h) - 2 * γ ξ + γ (ξ.1, ξ.2.1, ξ.2.2 - h)) *
          σ (quadraticArgument x ξ) =
        (γ (quadraticConstTranslate (E := E) h ξ) * σ (quadraticArgument x ξ) -
            2 * (γ ξ * σ (quadraticArgument x ξ))) +
          γ (quadraticConstTranslate (E := E) (-h) ξ) * σ (quadraticArgument x ξ) := by
    intro ξ
    simp only [quadraticConstTranslate_apply, ← sub_eq_add_neg]
    ring
  have hright : ∀ ξ : QuadraticParameter E,
      γ ξ * (σ (quadraticArgument x ξ + h) - 2 * σ (quadraticArgument x ξ) +
          σ (quadraticArgument x ξ - h)) =
        (γ ξ * σ (quadraticArgument x ξ + h) - 2 * (γ ξ * σ (quadraticArgument x ξ))) +
          γ ξ * σ (quadraticArgument x ξ - h) := by
    intro ξ
    ring
  have hsubA : Integrable (fun ξ ↦ γ (quadraticConstTranslate (E := E) h ξ) *
      σ (quadraticArgument x ξ) - 2 * (γ ξ * σ (quadraticArgument x ξ))) ν :=
    hAint.sub (hzero.const_mul 2)
  have hsubP : Integrable (fun ξ ↦ γ ξ * σ (quadraticArgument x ξ + h) -
      2 * (γ ξ * σ (quadraticArgument x ξ))) ν := hplus.sub (hzero.const_mul 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hleft),
    integral_congr_ae (Filter.Eventually.of_forall hright),
    integral_add hsubA hBint, integral_add hsubP hminus,
    integral_sub hAint (hzero.const_mul 2), integral_sub hplus (hzero.const_mul 2), hA, hB]
  ring

/-! ### The reduction: the rectified linear unit becomes the hat function -/

omit [BorelSpace (QuadraticSymmetric E)] in
/-- **The reduction.**  Build the second difference into the analysis feature and the composite
against the rectified linear unit becomes the composite against the hat function -- bounded,
compactly supported, of positive integral.

Two moves and one computation: the difference passes from the feature to the transform on the
analysis side, then from the coefficient function to the activation on the synthesis side, and the
second difference of the rectified linear unit *is* the hat function.  Nothing distributional
appears, because a second difference is a finite combination of translations.

This is what the remaining admissibility placeholder can be attacked through: the pair
`(reluComplex, secondDifference h ψ₀)` has the same composite as the pair `(hatComplex h, ψ₀)`, so a
probe for the second is a probe for the first, and the activation on the right is one that
Appendix C and the bounded-continuous theory can see. -/
theorem bochnerSynthesis_bochnerRidgelet_reluComplex_secondDifference
    {ν : Measure (QuadraticParameter E)} {h : ℝ} (hh : 0 ≤ h)
    (hνp : Measure.map (quadraticConstTranslate (E := E) h) ν = ν)
    (hνm : Measure.map (quadraticConstTranslate (E := E) (-h)) ν = ν) {ψ₀ : ℝ → ℂ} (f : E → ℂ)
    (x : E)
    (hRplus : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ + h))) (volume : Measure E))
    (hRzero : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ))) (volume : Measure E))
    (hRminus : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ - h))) (volume : Measure E))
    (hSplus : Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ + h)) ν)
    (hSzero : Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ)) ν)
    (hSminus : Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ - h)) ν) :
    bochnerSynthesis ν (quadraticVectorFeature reluComplex)
        (bochnerRidgelet (volume : Measure E)
          (quadraticVectorFeature (secondDifference h ψ₀)) f) x =
      bochnerSynthesis ν (quadraticVectorFeature (hatComplex h))
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f) x := by
  have hcoeff : bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (secondDifference h ψ₀)) f =
      quadraticConstSecondDifference h
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f) :=
    funext fun ξ ↦ bochnerRidgelet_secondDifference_feature h f ξ (hRplus ξ) (hRzero ξ) (hRminus ξ)
  rw [hcoeff, bochnerSynthesis_quadraticConstSecondDifference hνp hνm _ x hSplus hSzero hSminus,
    secondDifference_reluComplex hh]

omit [BorelSpace (QuadraticSymmetric E)] in
/-- **The probe transfers.**  If the composite of the hat function with an analysis feature does not
vanish on a datum, neither does the composite of the rectified linear unit with the differenced
analysis feature.  This is the nonvanishing half of admissibility, moved from an activation of
polynomial growth to a bounded compactly supported one. -/
theorem not_bochnerSynthesis_bochnerRidgelet_reluComplex_ae_zero
    {ν : Measure (QuadraticParameter E)} {h : ℝ} (hh : 0 ≤ h)
    (hνp : Measure.map (quadraticConstTranslate (E := E) h) ν = ν)
    (hνm : Measure.map (quadraticConstTranslate (E := E) (-h)) ν = ν) {ψ₀ : ℝ → ℂ} (f : E → ℂ)
    (hRplus : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ + h))) (volume : Measure E))
    (hRzero : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ))) (volume : Measure E))
    (hRminus : ∀ ξ : QuadraticParameter E, Integrable
      (fun y ↦ f y * conj (ψ₀ (quadraticArgument y ξ - h))) (volume : Measure E))
    (hSplus : ∀ x : E, Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ + h)) ν)
    (hSzero : ∀ x : E, Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ)) ν)
    (hSminus : ∀ x : E, Integrable (fun ξ ↦
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f ξ *
        reluComplex (quadraticArgument x ξ - h)) ν)
    (hhat : ¬ bochnerSynthesis ν (quadraticVectorFeature (hatComplex h))
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ₀) f)
      =ᵐ[(volume : Measure E)] 0) :
    ¬ bochnerSynthesis ν (quadraticVectorFeature reluComplex)
        (bochnerRidgelet (volume : Measure E)
          (quadraticVectorFeature (secondDifference h ψ₀)) f)
      =ᵐ[(volume : Measure E)] 0 := by
  intro hrelu
  refine hhat ?_
  refine (Filter.EventuallyEq.of_eq (funext fun x ↦ ?_)).trans hrelu
  exact (bochnerSynthesis_bochnerRidgelet_reluComplex_secondDifference hh hνp hνm f x
    hRplus hRzero hRminus (hSplus x) (hSzero x) (hSminus x)).symm

end LeanRidgelet
