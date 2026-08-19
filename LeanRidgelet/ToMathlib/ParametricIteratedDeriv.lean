/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Measurability of an iterated derivative in a parameter

Mathlib knows that a single derivative is measurable without any differentiability assumption --
`MeasureTheory.stronglyMeasurable_deriv` for one variable and `measurable_deriv_with_param` for a
jointly continuous family -- but neither statement iterates on its own.  The parametric one is the
sharp one-step result and consumes joint continuity that it does not produce, so an induction on the
order needs a second ingredient.  This file supplies it and states both routes.

*One variable is free.*  A derivative vanishes off the differentiability set and that set is Borel,
so `MeasureTheory.stronglyMeasurable_deriv` holds for every function; iterating costs nothing, and a
positive order needs no hypothesis at all.

*A parameter has content.*  The continuity route is the induction: the parametric derivative of a
jointly `ContDiff` function is again jointly `ContDiff`, one order down, so an induction on the
order gives joint *continuity* of the parametric iterated derivative.  Feeding that continuity into
Mathlib's one-step lemma then gains one order, so `ContDiff ℝ j` gives measurability of order
`j + 1` rather than merely of order `j`.

This file is a Mathlib upstream candidate and has no dependencies on the rest of the `LeanRidgelet`
project.  Its declarations sit in the `MeasureTheory` namespace, as this project's other upstream
candidates do; Mathlib's own counterparts are at the root, so upstreaming would drop the prefix.

## Main results

* `MeasureTheory.stronglyMeasurable_iteratedDeriv_succ`: for every `g : ℝ → F` into a complete space
  and every `j`, `iteratedDeriv (j + 1) g` is strongly measurable.  No hypothesis whatsoever.
* `MeasureTheory.parametricDeriv` and `MeasureTheory.parametricIteratedDeriv`: the derivative and
  the iterated derivative in the last variable of a function of a pair, as functions of the pair,
  together with the two recursions `MeasureTheory.parametricIteratedDeriv_succ` (peel off the
  innermost derivative) and `MeasureTheory.parametricIteratedDeriv_succ'` (peel off the outermost).
* `MeasureTheory.contDiff_parametricDeriv`: the parametric derivative of a `ContDiff (m + 1)`
  function of a pair is `ContDiff m`.
* `MeasureTheory.continuous_parametricIteratedDeriv`: **the continuity route.**  For `ContDiff ℝ j`,
  the parametric iterated derivative of order `j` is jointly continuous, hence measurable
  (`MeasureTheory.measurable_parametricIteratedDeriv`).
* `MeasureTheory.measurable_parametricIteratedDeriv_succ_of_continuous`: **the limit route**, which
  is Mathlib's `measurable_deriv_with_param`: joint continuity of the parametric iterated derivative
  of order `j` gives joint measurability of order `j + 1`, with no differentiability hypothesis.
  Combined with the previous item, `ContDiff ℝ j` gives measurability of order `j + 1`
  (`MeasureTheory.measurable_parametricIteratedDeriv_succ`).

## What is assumed

For the one-variable statements, completeness of the target --
`MeasureTheory.stronglyMeasurable_deriv` needs it to know that the differentiability set is Borel --
and nothing else.

For the continuity route, that the parameter is a normed space, so that `ContDiff` in the pair makes
sense, and `ContDiff ℝ j` of the function of the pair.  It is genuinely a joint hypothesis:
continuity of each derivative separately in each variable would not do.

For the limit route, only that the parameter is a topological space carrying a measurable structure
for which open sets are measurable, plus joint continuity of the parametric iterated derivative one
order down.  It assumes no differentiability, but it does not iterate.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MeasureTheory

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

end MeasureTheory
