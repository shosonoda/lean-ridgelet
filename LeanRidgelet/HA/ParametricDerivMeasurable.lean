/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import LeanRidgelet.HA.BochnerMeasurability
public import LeanRidgelet.HA.QuadraticShear
public import LeanRidgelet.HA.QuadraticTransfer

/-!
# Measurability of an iterated derivative in a parameter

`LeanRidgelet.HA.QuadraticShear` carries two measurability hypotheses it cannot discharge, and its
"What is established and what is not" paragraph records why: nothing in this development says that
an iterated derivative in one coordinate of a parameter is measurable in the remaining coordinates. 
The two hypotheses are `Measurable (LeanRidgelet.quadraticConstIteratedDeriv j T)`, in
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul` and in
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul`, and
`AEStronglyMeasurable (iteratedDeriv j (LeanRidgelet.quadraticConstSlice T p)) volume`, in
`LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul`.  This file discharges both.

The two are of very different difficulty, and Mathlib already settles the easier one.

*The slice-wise hypothesis is free.*  `MeasureTheory.stronglyMeasurable_deriv` says that `deriv g`
is strongly measurable for **every** `g`, differentiable or not, because the derivative is `0` off
the differentiability set and that set is Borel.  Since `iteratedDeriv (j + 1) g = deriv
(iteratedDeriv j g)`, iterating costs nothing: `LeanRidgelet.stronglyMeasurable_iteratedDeriv_succ`
needs no hypothesis on `g` at all.  Only order `0` needs anything, namely measurability of `g`
itself.

*The hypothesis in the parameter has real content.*  Mathlib's
`measurable_deriv_with_param` is the sharp one-step statement: for a family `f : α → 𝕜 → F` whose
uncurried form is **jointly continuous**, the parametric derivative `(a, t) ↦ deriv (f a) t` is
jointly measurable, again with no differentiability assumed.  It cannot be iterated on its own,
because the joint continuity it consumes is not something it produces.  So the iteration is done
here by the continuity route: for a jointly `ContDiff` function the parametric derivative in the
last variable is again jointly `ContDiff`, one order down (`LeanRidgelet.contDiff_parametricDeriv`,
which is `ContDiff.fderiv_succ` composed with evaluation at `1`), and an induction on the order
gives joint *continuity* of the parametric iterated derivative.  Feeding that continuity into
Mathlib's one-step lemma then gains one order: `ContDiff ℝ j` gives measurability of the parametric
derivative of order `j + 1`, not merely of order `j`.

## Main results

* `LeanRidgelet.stronglyMeasurable_iteratedDeriv_succ`: for every `g : ℝ → F` into a complete space
  and every `j`, `iteratedDeriv (j + 1) g` is strongly measurable.  No hypothesis whatsoever.
* `LeanRidgelet.parametricDeriv` and `LeanRidgelet.parametricIteratedDeriv`: the derivative and the
  iterated derivative in the last variable of a function of a pair, as functions of the pair,
  together with the two recursions `LeanRidgelet.parametricIteratedDeriv_succ` (peel off the
  innermost derivative) and `LeanRidgelet.parametricIteratedDeriv_succ'` (peel off the outermost).
* `LeanRidgelet.contDiff_parametricDeriv`: the parametric derivative of a `ContDiff (m + 1)`
  function of a pair is `ContDiff m`.
* `LeanRidgelet.continuous_parametricIteratedDeriv`: **the continuity route.**  For `ContDiff ℝ j`,
  the parametric iterated derivative of order `j` is jointly continuous, hence measurable
  (`LeanRidgelet.measurable_parametricIteratedDeriv`).
* `LeanRidgelet.measurable_parametricIteratedDeriv_succ_of_continuous`: **the limit route**, which
  is Mathlib's `measurable_deriv_with_param`: joint continuity of the parametric iterated derivative
  of order `j` gives joint measurability of order `j + 1`, with no differentiability hypothesis.
  Combined with the previous item, `ContDiff ℝ j` gives measurability of order `j + 1`
  (`LeanRidgelet.measurable_parametricIteratedDeriv_succ`).
* `LeanRidgelet.continuous_quadraticConstIteratedDeriv` and
  `LeanRidgelet.measurable_quadraticConstIteratedDeriv`: the instantiation at the quadratic
  parameter space, whose constant coefficient is the last of three coordinates rather than the
  second of two; `LeanRidgelet.quadraticConstPair` and `LeanRidgelet.quadraticParameterPair` are the
  reassociation that mediates, and they cost nothing because reassociation of a product is a
  linear homeomorphism.
* `LeanRidgelet.aestronglyMeasurable_iteratedDeriv_quadraticConstSlice_succ` and
  `LeanRidgelet.aestronglyMeasurable_iteratedDeriv_quadraticConstSlice`: the slice-wise hypothesis,
  unconditionally for a positive order and from measurability of `T` for order `0`.
* `LeanRidgelet.measurable_quadraticConstIteratedDeriv_of_eq` and
  `LeanRidgelet.measurable_quadraticConstIteratedDeriv_bochnerRidgelet`: **the transfer route**, for
  the one function this development actually cares about.  No joint smoothness of the analysis
  transform is known here, so the `ContDiff` route is not available for it; but
  `LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` says its `j`-th derivative in
  the constant coefficient *is* another analysis transform, and
  `LeanRidgelet.stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature` says that one is
  measurable in the parameter.  So for the analysis transform the hypothesis is discharged from the
  transfer hypotheses alone.

## What is assumed

For the slice-wise statements, completeness of the target --
`MeasureTheory.stronglyMeasurable_deriv` needs it to know that the differentiability set is Borel --
and nothing else.

For the continuity route, that the parameter is a normed space, so that `ContDiff` in the pair makes
sense, and `ContDiff ℝ j` of the function of the pair.  That is the natural hypothesis for a
concrete ridgelet function built from a smooth activation, and it is genuinely a joint hypothesis:
continuity of each derivative separately in each variable would not do.

For the limit route, only that the parameter is a topological space carrying a measurable structure
for which open sets are measurable, plus joint continuity of the parametric iterated derivative one
order down.  It assumes no differentiability, but it does not iterate.

For the transfer route, the hypotheses of
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` at every base parameter -- a
sequence of features each the derivative of the previous, integrability of each pairing, and a
dominating function -- together with strong measurability of the `j`-th feature and of the data,
which is what `LeanRidgelet.HA.BochnerMeasurability` consumes.  Nothing is assumed about
differentiability in the first two coefficients, which is exactly why this route is the usable one
for the analysis transform.

## What this discharges

`hmeas` of `LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul` at every order `j + 1`
with no hypothesis, and at order `0` from measurability of `T`; `hT` of
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul` and of
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul` from `ContDiff ℝ j T`, or
from the transfer hypotheses when `T` is an analysis transform.  Nothing else about
`LeanRidgelet.HA.QuadraticShear` changes: the shear, the commutation and the seminorm identities are
independent of this file, and it still defines no space `Γ^k`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

/-! ### Iterated derivatives of a single function are measurable -/

section OneVariable

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **An iterated derivative of positive order is strongly measurable, unconditionally.**  For every
function on the line into a complete space, differentiable or not, the `(j + 1)`-st iterated
derivative is strongly measurable.  Only Mathlib's `MeasureTheory.stronglyMeasurable_deriv` is used:
the derivative vanishes off the differentiability set, which is Borel, so no regularity of `g` is
needed, and `iteratedDeriv (j + 1) g = deriv (iteratedDeriv j g)` iterates that for free.  Order `0`
is the only order that needs a hypothesis, since there the iterated derivative is `g` itself. -/
theorem stronglyMeasurable_iteratedDeriv_succ (j : ℕ) (g : ℝ → F) :
    StronglyMeasurable (iteratedDeriv (j + 1) g) := by
  rw [iteratedDeriv_succ]
  exact stronglyMeasurable_deriv _

/-- Every iterated derivative of a strongly measurable function is strongly measurable.  For a
positive order the hypothesis is not used; it is needed only at order `0`. -/
theorem stronglyMeasurable_iteratedDeriv (j : ℕ) {g : ℝ → F} (hg : StronglyMeasurable g) :
    StronglyMeasurable (iteratedDeriv j g) := by
  cases j with
  | zero => rwa [iteratedDeriv_zero]
  | succ j => exact stronglyMeasurable_iteratedDeriv_succ j g

end OneVariable

/-! ### The derivative in the last variable of a function of a pair -/

section Parametric

variable {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The parametric derivative.**  The derivative in the last variable of a function of a pair,
read again as a function of the pair.  The first component is the parameter and is not
differentiated. -/
def parametricDeriv (f : α × ℝ → F) : α × ℝ → F :=
  fun p ↦ deriv (fun t ↦ f (p.1, t)) p.2

/-- **The parametric iterated derivative.**  The `j`-th derivative in the last variable of a
function of a pair, read again as a function of the pair.  This is the shape of
`LeanRidgelet.quadraticConstIteratedDeriv`, up to the reassociation of the parameter space handled
below. -/
def parametricIteratedDeriv (j : ℕ) (f : α × ℝ → F) : α × ℝ → F :=
  fun p ↦ iteratedDeriv j (fun t ↦ f (p.1, t)) p.2

/-- A slice of the parametric derivative is the derivative of the slice.  This holds by
definition. -/
theorem parametricDeriv_slice (f : α × ℝ → F) (a : α) :
    (fun t ↦ parametricDeriv f (a, t)) = deriv (fun t ↦ f (a, t)) := rfl

/-- A slice of the parametric iterated derivative is the iterated derivative of the slice.  This
holds by definition, and it is the bridge between statements about the pair and slice-wise
statements. -/
theorem parametricIteratedDeriv_slice (j : ℕ) (f : α × ℝ → F) (a : α) :
    (fun t ↦ parametricIteratedDeriv j f (a, t)) = iteratedDeriv j (fun t ↦ f (a, t)) := rfl

/-- The parametric iterated derivative of order zero is the function itself. -/
theorem parametricIteratedDeriv_zero (f : α × ℝ → F) : parametricIteratedDeriv 0 f = f := by
  funext p
  change iteratedDeriv 0 (fun t ↦ f (p.1, t)) p.2 = f p
  rw [iteratedDeriv_zero]

/-- **Peeling off the innermost derivative.**  The parametric iterated derivative of order `j + 1`
is the one of order `j` of the parametric derivative.  This is the recursion the continuity route
descends. -/
theorem parametricIteratedDeriv_succ (j : ℕ) (f : α × ℝ → F) :
    parametricIteratedDeriv (j + 1) f = parametricIteratedDeriv j (parametricDeriv f) := by
  funext p
  change iteratedDeriv (j + 1) (fun t ↦ f (p.1, t)) p.2 =
    iteratedDeriv j (fun t ↦ parametricDeriv f (p.1, t)) p.2
  rw [parametricDeriv_slice, iteratedDeriv_succ']

/-- **Peeling off the outermost derivative.**  The parametric iterated derivative of order `j + 1`
is the parametric derivative of the one of order `j`.  This is the recursion the limit route uses,
since Mathlib's parametric statement is about a single derivative of a jointly continuous family. -/
theorem parametricIteratedDeriv_succ' (j : ℕ) (f : α × ℝ → F) :
    parametricIteratedDeriv (j + 1) f = parametricDeriv (parametricIteratedDeriv j f) := by
  funext p
  change iteratedDeriv (j + 1) (fun t ↦ f (p.1, t)) p.2 =
    deriv (fun t ↦ parametricIteratedDeriv j f (p.1, t)) p.2
  rw [parametricIteratedDeriv_slice, iteratedDeriv_succ]

end Parametric

/-! ### The limit route: one derivative of a jointly continuous family -/

section Limit

variable {α F : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]

/-- **One parametric derivative of a jointly continuous function is jointly measurable.**  This is
Mathlib's `measurable_deriv_with_param` in the notation of this file, and it is the sharp form of
the limit route: the parametric derivative is a pointwise limit of difference quotients, so no
differentiability is needed anywhere, only joint continuity.  What it does not do is iterate, since
joint continuity of the derivative is not part of its conclusion. -/
theorem measurable_parametricDeriv_of_continuous {f : α × ℝ → F} (hf : Continuous f) :
    Measurable (parametricDeriv f) :=
  measurable_deriv_with_param (f := fun (a : α) (t : ℝ) ↦ f (a, t)) hf

/-- **The limit route, one order up.**  If the parametric iterated derivative of order `j` is
jointly continuous, then the one of order `j + 1` is jointly measurable.  This gains one order over
what continuity alone would give, and needs no differentiability. -/
theorem measurable_parametricIteratedDeriv_succ_of_continuous {j : ℕ} {f : α × ℝ → F}
    (hf : Continuous (parametricIteratedDeriv j f)) :
    Measurable (parametricIteratedDeriv (j + 1) f) := by
  rw [parametricIteratedDeriv_succ']
  exact measurable_parametricDeriv_of_continuous hf

end Limit

/-! ### The continuity route: joint smoothness in the pair -/

section Continuity

variable {α F : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The parametric derivative of a jointly smooth function is jointly smooth, one order down.**
The derivative in the last variable is the full derivative in the pair, evaluated at the last basis
covector, so `ContDiff.fderiv_succ` gives it directly; evaluation at `1` is a continuous linear map,
which costs no smoothness.  Nothing is assumed about how the two variables interact. -/
theorem contDiff_parametricDeriv {m : WithTop ℕ∞} {f : α × ℝ → F} (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (parametricDeriv f) := by
  have huncurry : ContDiff ℝ (m + 1)
      (Function.uncurry fun (p : α × ℝ) (z : ℝ) ↦ f (p.1, z)) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (ContDiff.fderiv_succ huncurry contDiff_snd).clm_apply contDiff_const

/-- **The continuity route.**  For a function of a pair that is `j` times continuously
differentiable in the pair, the `j`-th derivative in the last variable is jointly continuous in the
pair.  The induction descends `LeanRidgelet.parametricIteratedDeriv_succ`, spending one order of
smoothness per derivative and reading off continuity from `ContDiff ℝ 0` at the end.

This is the honest general form of "the parametric iterated derivative is continuous, hence
measurable": the hypothesis is joint smoothness, which is what a concrete ridgelet function built
from a smooth activation has, and there is no differentiability side condition to check, since
`ContDiff` supplies it. -/
theorem continuous_parametricIteratedDeriv {j : ℕ} {f : α × ℝ → F} (hf : ContDiff ℝ j f) :
    Continuous (parametricIteratedDeriv j f) := by
  induction j generalizing f with
  | zero =>
    rw [parametricIteratedDeriv_zero]
    exact hf.continuous
  | succ j ih =>
    rw [parametricIteratedDeriv_succ]
    refine ih (contDiff_parametricDeriv ?_)
    exact_mod_cast hf

variable [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace F] [BorelSpace F]

/-- **The continuity route, as measurability.**  Joint continuity of the parametric iterated
derivative makes it measurable for the Borel structure of the pair. -/
theorem measurable_parametricIteratedDeriv {j : ℕ} {f : α × ℝ → F} (hf : ContDiff ℝ j f) :
    Measurable (parametricIteratedDeriv j f) :=
  (continuous_parametricIteratedDeriv hf).measurable

/-- **The two routes combined.**  `j` orders of joint smoothness give joint measurability of the
parametric iterated derivative of order `j + 1`: the first `j` derivatives are continuous by the
continuity route, and the last one is measurable by Mathlib's parametric statement, which needs only
continuity of the previous one.  At `j = 0` this says that joint continuity of `f` alone makes the
parametric first derivative measurable. -/
theorem measurable_parametricIteratedDeriv_succ [CompleteSpace F] {j : ℕ} {f : α × ℝ → F}
    (hf : ContDiff ℝ j f) :
    Measurable (parametricIteratedDeriv (j + 1) f) :=
  measurable_parametricIteratedDeriv_succ_of_continuous (continuous_parametricIteratedDeriv hf)

end Continuity

/-! ### The quadratic instantiation -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The quadratic parameter, reassociated.**  The parameter `(A, b, c)` read as the pair
`((A, b), c)` of the base parameter with the constant coefficient, so that the constant coefficient
is the last variable of a pair and the general statements above apply.  Reassociation of a product
is a linear homeomorphism, so this costs nothing. -/
def quadraticParameterPair (ξ : QuadraticParameter E) : (QuadraticSymmetric E × E) × ℝ :=
  ((ξ.1, ξ.2.1), ξ.2.2)

/-- **A function of the quadratic parameter, reassociated.**  The same function read on pairs
`((A, b), c)`.  Its slices in the last variable are exactly the slices of
`LeanRidgelet.quadraticConstSlice`. -/
def quadraticConstPair (T : QuadraticParameter E → ℂ) : (QuadraticSymmetric E × E) × ℝ → ℂ :=
  fun q ↦ T (q.1.1, q.1.2, q.2)

/-- The reassociation of the quadratic parameter is continuous. -/
theorem continuous_quadraticParameterPair :
    Continuous (quadraticParameterPair (E := E)) :=
  (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

/-- The slices of the reassociated function in the last variable are the slices in the constant
coefficient.  This holds by definition. -/
theorem quadraticConstPair_slice (T : QuadraticParameter E → ℂ) (p : QuadraticSymmetric E × E) :
    (fun t ↦ quadraticConstPair T (p, t)) = quadraticConstSlice T p := rfl

/-- **The derivative in the constant coefficient is the parametric derivative of the reassociated
function.**  This holds by definition, and it is what carries the general results to the quadratic
parameter space. -/
theorem quadraticConstIteratedDeriv_eq_parametric (j : ℕ) (T : QuadraticParameter E → ℂ) :
    quadraticConstIteratedDeriv j T =
      parametricIteratedDeriv j (quadraticConstPair T) ∘ quadraticParameterPair := rfl

/-- The `j`-th derivative in the constant coefficient of a slice, as a slice of the parametric
iterated derivative.  This holds by definition. -/
theorem iteratedDeriv_quadraticConstSlice_eq_parametric (j : ℕ) (T : QuadraticParameter E → ℂ)
    (p : QuadraticSymmetric E × E) :
    iteratedDeriv j (quadraticConstSlice T p) =
      fun t ↦ parametricIteratedDeriv j (quadraticConstPair T) (p, t) := rfl

/-- Reassociating the quadratic parameter preserves joint smoothness, being a continuous linear
map. -/
theorem contDiff_quadraticConstPair {m : WithTop ℕ∞} {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ m T) :
    ContDiff ℝ m (quadraticConstPair T) :=
  hT.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))

/-! #### The slice-wise hypothesis -/

/-- **The slice-wise hypothesis of
`LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul` at a positive order, with no
hypothesis at all.** For every function on the quadratic parameter space, every base parameter and
every `j`, the `(j + 1)`-st derivative in the constant coefficient of the slice is almost everywhere
strongly measurable for Lebesgue measure on the line.  This is
`LeanRidgelet.stronglyMeasurable_iteratedDeriv_succ`; the caller instantiates the base parameter at
`LeanRidgelet.quadraticBaseLinearEquiv g p`.
-/
theorem aestronglyMeasurable_iteratedDeriv_quadraticConstSlice_succ (j : ℕ)
    (T : QuadraticParameter E → ℂ) (p : QuadraticSymmetric E × E) :
    AEStronglyMeasurable (iteratedDeriv (j + 1) (quadraticConstSlice T p)) (volume : Measure ℝ) :=
  (stronglyMeasurable_iteratedDeriv_succ j (quadraticConstSlice T p)).aestronglyMeasurable

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- A slice in the constant coefficient of a measurable function is measurable, the slice being the
composition with an affine map of the line. -/
theorem stronglyMeasurable_quadraticConstSlice {T : QuadraticParameter E → ℂ} (hT : Measurable T)
    (p : QuadraticSymmetric E × E) :
    StronglyMeasurable (quadraticConstSlice T p) :=
  (hT.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).stronglyMeasurable

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The slice-wise hypothesis of
`LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul` at every order.**  For a
measurable `T` the `j`-th derivative in the constant coefficient of every slice is almost everywhere
strongly measurable.  For a positive order the hypothesis on `T` is not used; it is needed only at
order `0`, where the iterated derivative is the slice itself.
-/
theorem aestronglyMeasurable_iteratedDeriv_quadraticConstSlice (j : ℕ)
    {T : QuadraticParameter E → ℂ} (hT : Measurable T) (p : QuadraticSymmetric E × E) :
    AEStronglyMeasurable (iteratedDeriv j (quadraticConstSlice T p)) (volume : Measure ℝ) :=
  (stronglyMeasurable_iteratedDeriv j
    (stronglyMeasurable_quadraticConstSlice hT p)).aestronglyMeasurable

/-! #### The hypothesis in the parameter, from joint smoothness -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- **The derivative in the constant coefficient of a jointly smooth function is jointly
continuous.**  The continuity route at the quadratic parameter space: for `T` that is `j` times
continuously differentiable on `QuadraticParameter E`, the function
`LeanRidgelet.quadraticConstIteratedDeriv j T` is continuous on the whole parameter space.  Only the
reassociation `LeanRidgelet.quadraticParameterPair` is interposed. -/
theorem continuous_quadraticConstIteratedDeriv (j : ℕ) {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ j T) :
    Continuous (quadraticConstIteratedDeriv j T) := by
  rw [quadraticConstIteratedDeriv_eq_parametric]
  exact (continuous_parametricIteratedDeriv (contDiff_quadraticConstPair hT)).comp
    continuous_quadraticParameterPair

/-- **The hypothesis `hT` of
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul` and of
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul`, from joint smoothness.**
For `T` that is `j` times continuously differentiable on the quadratic parameter space, the `j`-th
derivative in the constant coefficient is measurable as a function on that space. -/
theorem measurable_quadraticConstIteratedDeriv (j : ℕ) {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ j T) :
    Measurable (quadraticConstIteratedDeriv j T) :=
  (continuous_quadraticConstIteratedDeriv j hT).measurable

/-- **The same hypothesis one order up, from Mathlib's parametric derivative.**  `j` orders of joint
smoothness of `T` give measurability of the derivative of order `j + 1` in the constant coefficient,
because the last derivative only needs joint continuity of the previous one.  At `j = 0` this says
that joint continuity of `T` alone makes the first derivative in the constant coefficient
measurable. -/
theorem measurable_quadraticConstIteratedDeriv_succ (j : ℕ) {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ j T) :
    Measurable (quadraticConstIteratedDeriv (j + 1) T) := by
  rw [quadraticConstIteratedDeriv_eq_parametric]
  exact (measurable_parametricIteratedDeriv_succ (contDiff_quadraticConstPair hT)).comp
    continuous_quadraticParameterPair.measurable

/-! #### The hypothesis in the parameter, from the transfer -/

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The transfer route.**  If the `j`-th derivative in the constant coefficient of `T` is, base
parameter by base parameter, the slice of some function `S` on the parameter space, then
measurability of `S` gives measurability of the derivative.  This is a triviality, and it is stated
because it is exactly the shape that
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` produces: for the analysis
transform the derivative in the constant coefficient *is* another analysis transform, so no
smoothness in the first two coefficients has to be known. -/
theorem measurable_quadraticConstIteratedDeriv_of_eq (j : ℕ) {T S : QuadraticParameter E → ℂ}
    (hTS : ∀ (A : QuadraticSymmetric E) (b : E),
      iteratedDeriv j (quadraticConstSlice T (A, b)) = fun c ↦ S (A, b, c))
    (hS : Measurable S) :
    Measurable (quadraticConstIteratedDeriv j T) := by
  have hEq : quadraticConstIteratedDeriv j T = S := by
    funext ξ
    change iteratedDeriv j (quadraticConstSlice T (ξ.1, ξ.2.1)) ξ.2.2 = S ξ
    rw [hTS ξ.1 ξ.2.1]
  rw [hEq]
  exact hS

/-- **The hypothesis `hT` of
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul` for the analysis transform.**
Under the hypotheses of `LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature`, imposed
at every base parameter, the `j`-th derivative in the constant coefficient of the analysis transform
of the quadratic feature of `ρ 0` is measurable on the parameter space, because it equals the
analysis transform of the quadratic feature of `ρ j`, which is measurable by
`LeanRidgelet.stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature`.

This is the instantiation to use in practice.  Nothing is assumed about differentiability of the
transform in the symmetric or the linear coefficient -- only in the constant one, where the transfer
lives. -/
theorem measurable_quadraticConstIteratedDeriv_bochnerRidgelet {ρ : ℕ → ℝ → ℂ} (f : E → ℂ) (j : ℕ)
    {bound : QuadraticSymmetric E × E → ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ i (A : QuadraticSymmetric E) (b : E) (c : ℝ), AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ i (A : QuadraticSymmetric E) (b : E) (c : ℝ), Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ i (A : QuadraticSymmetric E) (b : E), ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound (A, b) i x)
    (hboundint : ∀ i (A : QuadraticSymmetric E) (b : E),
      Integrable (bound (A, b) i) (volume : Measure E))
    (hρ : StronglyMeasurable (ρ j)) (hf : AEStronglyMeasurable f (volume : Measure E)) :
    Measurable (quadraticConstIteratedDeriv j
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f)) :=
  measurable_quadraticConstIteratedDeriv_of_eq j
    (S := bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f)
    (fun A b ↦ iteratedDeriv_bochnerRidgelet_quadraticVectorFeature f A b hderiv
      (fun i c ↦ hmeas i A b c) (fun i c ↦ hint i A b c) (fun i ↦ hbound i A b)
      (fun i ↦ hboundint i A b) j)
    (stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature
      (volume : Measure E) hρ hf).measurable

end Quadratic

end LeanRidgelet
