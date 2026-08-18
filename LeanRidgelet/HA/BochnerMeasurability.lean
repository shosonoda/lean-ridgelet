/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticRelativeMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of the Bochner transforms in their output variable

`LeanRidgelet.bochnerRidgelet` and `LeanRidgelet.bochnerSynthesis`
(`LeanRidgelet.HA.BochnerIntertwining`) are raw Bochner integrals, defined with no hypotheses at
all: the analysis transform integrates over the data space and produces a function of the parameter,
the synthesis integrates over the parameter space and produces a function of the data.  Nothing in
this development says that either output is measurable, and the "What remains" paragraph of
`LeanRidgelet.HA.QuadraticWeighted` records that gap as the obstruction to integrating its slice
estimate over the remaining parameters: Tonelli needs joint measurability of the transform in the
parameters, and there was no measurability of `LeanRidgelet.bochnerRidgelet` in the parameter
anywhere.  This file supplies it.

The argument is the one `MeasureTheory.aestronglyMeasurable_integral_mul_conj_kernel`
(`LeanRidgelet.ToMathlib.HilbertSchmidtKernel`) uses for a kernel operator: the integrand is jointly
measurable on the product, and `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` turns joint
measurability of an integrand into measurability of the integral in the outer variable.  The only
new work is bookkeeping about which of the two product orders the hypotheses are stated in.

## Main results

* `LeanRidgelet.aestronglyMeasurable_bochnerRidgelet`: the analysis transform is
  `MeasureTheory.AEStronglyMeasurable` in the parameter, for a jointly measurable feature and
  measurable data.
* `LeanRidgelet.stronglyMeasurable_bochnerRidgelet`: with the feature genuinely jointly strongly
  measurable rather than only almost everywhere so, the conclusion is `StronglyMeasurable` and no
  parameter measure enters at all.
* `LeanRidgelet.aestronglyMeasurable_bochnerSynthesis` and
  `LeanRidgelet.stronglyMeasurable_bochnerSynthesis`: the mirror statements for the synthesis, in
  the data variable.
* `LeanRidgelet.continuous_uncurry_quadraticArgument`: the scalar argument of the quadratic feature
  is jointly continuous on `E × QuadraticParameter E`.
* `LeanRidgelet.stronglyMeasurable_uncurry_quadraticVectorFeature` and its continuous and measurable
  variants: joint measurability of the quadratic feature.
* `LeanRidgelet.aestronglyMeasurable_bochnerRidgelet_quadraticVectorFeature`: the analysis transform
  of the quadratic feature is measurable in the parameter.

## What is assumed

For the general statements, σ-finiteness of the measure that is integrated over -- the data measure
for the analysis transform, the parameter measure for the synthesis -- which is what the Fubini
lemmas of `MeasureTheory.Measure.prod` consume, together with joint measurability of the feature and
measurability of the data resp. of the coefficient.  The two almost-everywhere statements assume
σ-finiteness of the *output* measure as well: their hypotheses are stated for the product measure in
the `X × Ξ` order, and reaching the order the Fubini lemma consumes costs a `Prod.swap` for the
analysis transform and a projection for the coefficient, both of which need the second measure to be
σ-finite.  The two `StronglyMeasurable` statements assume no output measure at all, so they need no
such hypothesis; they are the ones to use when the output measurability is wanted for a measure that
has not been chosen yet, as in the Tonelli step above.

For the quadratic instantiation, only the standing measurable-space conventions of
`LeanRidgelet.HA.QuadraticBounded` -- `[MeasurableSpace E] [BorelSpace E]` and the same two for
`QuadraticSymmetric E` -- plus measurability of the activation.  Joint continuity of
`LeanRidgelet.quadraticArgument` is unconditional: the only non-formal ingredient is that evaluation
`(A, x) ↦ A x` of a continuous linear map is continuous in the pair, which is
`isBoundedBilinearMap_apply`.

## What this unblocks

The parameter-side measurability that plan item P1.7 (d) of the development plan names as the next
thing to build.  It is one of the three things that paragraph lists as missing for the integrated
weighted estimate; the other two -- factoring an abstract Haar measure on the triple product as a
product with a measure on the constant coefficient, and matching the post-Fourier space whose last
coordinate is a frequency against the restricted weighted Haar measure -- are untouched here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace LeanRidgelet

/-! ### The general statements -/

section General

variable {X Ξ Y : Type*} [MeasurableSpace X] [MeasurableSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- **The analysis transform is measurable in the parameter.**  If the feature is jointly almost
everywhere strongly measurable for the product of the data measure with the parameter measure and
the data is measurable, then `LeanRidgelet.bochnerRidgelet` is almost everywhere strongly
measurable on the parameter space.

The integrand `(ξ, x) ↦ ⟪ψ x ξ, f x⟫` is jointly measurable, being the continuous inner product of
two jointly measurable functions, so
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` applies.  The hypothesis on the feature is
stated in the `X × Ξ` order, which is the uncurried order of `ψ : X → Ξ → Y`; the Fubini lemma wants
the parameter outside, so the proof exchanges the two arguments, and that exchange is what makes
σ-finiteness of the parameter measure a hypothesis here. -/
theorem aestronglyMeasurable_bochnerRidgelet (μ : Measure X) [SFinite μ]
    (ν : Measure Ξ) [SFinite ν] {ψ : X → Ξ → Y} {f : X → Y}
    (hψ : AEStronglyMeasurable (Function.uncurry ψ) (μ.prod ν))
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (bochnerRidgelet μ ψ f) ν := by
  have hswap : AEStronglyMeasurable (fun p : Ξ × X ↦ ψ p.2 p.1) (ν.prod μ) := hψ.prod_swap
  have hdata : AEStronglyMeasurable (fun p : Ξ × X ↦ f p.2) (ν.prod μ) := hf.comp_snd
  exact ((continuous_inner (𝕜 := ℂ) (E := Y)).comp_aestronglyMeasurable
    (hswap.prodMk hdata)).integral_prod_right'

/-- **The analysis transform is measurable in the parameter, without a parameter measure.**  If the
feature is jointly strongly measurable -- not merely almost everywhere so for some product measure
-- then `LeanRidgelet.bochnerRidgelet` is strongly measurable on the parameter space, and only the
data measure is involved.  The data is still allowed to be measurable only almost everywhere,
because changing it on a null set of the data space does not change the integral for any parameter:
the two transforms are equal as functions, not just almost everywhere.

This is the form to use when the parameter measure is not yet fixed, for instance before a Tonelli
step that will replace the parameter measure by a product. -/
theorem stronglyMeasurable_bochnerRidgelet (μ : Measure X) [SFinite μ] {ψ : X → Ξ → Y} {f : X → Y}
    (hψ : StronglyMeasurable (Function.uncurry ψ)) (hf : AEStronglyMeasurable f μ) :
    StronglyMeasurable (bochnerRidgelet μ ψ f) := by
  have hmk : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  have hjoint : StronglyMeasurable fun p : Ξ × X ↦ ⟪ψ p.2 p.1, hf.mk f p.2⟫_ℂ :=
    (continuous_inner (𝕜 := ℂ) (E := Y)).comp_stronglyMeasurable
      ((hψ.comp_measurable measurable_swap).prodMk (hmk.comp_measurable measurable_snd))
  have heq : bochnerRidgelet μ ψ f = bochnerRidgelet μ ψ (hf.mk f) := by
    funext ξ
    refine integral_congr_ae ?_
    filter_upwards [hf.ae_eq_mk] with x hx
    rw [hx]
  rw [heq]
  exact hjoint.integral_prod_right'

/-- **The synthesis is measurable in the data variable.**  The mirror of
`LeanRidgelet.aestronglyMeasurable_bochnerRidgelet`, and it needs nothing extra: the uncurried
feature `X × Ξ → Y` is already in the order the Fubini lemma wants, since the synthesis integrates
out the parameter and produces a function of the data, so no exchange of arguments occurs.  What
still costs σ-finiteness of the output measure is the coefficient, which has to be read as a
function on the product. -/
theorem aestronglyMeasurable_bochnerSynthesis (μ : Measure Ξ) [SFinite μ]
    (ν : Measure X) [SFinite ν] {φ : X → Ξ → Y} {γ : Ξ → ℂ}
    (hφ : AEStronglyMeasurable (Function.uncurry φ) (ν.prod μ))
    (hγ : AEStronglyMeasurable γ μ) :
    AEStronglyMeasurable (bochnerSynthesis μ φ γ) ν :=
  ((hγ.comp_snd).smul hφ).integral_prod_right'

/-- **The synthesis is measurable in the data variable, without a data measure.**  The mirror of
`LeanRidgelet.stronglyMeasurable_bochnerRidgelet`: a jointly strongly measurable feature and an
almost everywhere measurable coefficient give a strongly measurable synthesis, with no measure on
the data space. -/
theorem stronglyMeasurable_bochnerSynthesis (μ : Measure Ξ) [SFinite μ] {φ : X → Ξ → Y} {γ : Ξ → ℂ}
    (hφ : StronglyMeasurable (Function.uncurry φ)) (hγ : AEStronglyMeasurable γ μ) :
    StronglyMeasurable (bochnerSynthesis μ φ γ) := by
  have hmk : StronglyMeasurable (hγ.mk γ) := hγ.stronglyMeasurable_mk
  have hjoint : StronglyMeasurable fun p : X × Ξ ↦ hγ.mk γ p.2 • φ p.1 p.2 :=
    (hmk.comp_measurable measurable_snd).smul hφ
  have heq : bochnerSynthesis μ φ γ = bochnerSynthesis μ φ (hγ.mk γ) := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [hγ.ae_eq_mk] with ξ hξ
    rw [hξ]
  rw [heq]
  exact hjoint.integral_prod_right'

end General

/-! ### The quadratic instantiation -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- **The quadratic argument is jointly continuous.**  The scalar functional
`⟪x, A x⟫ + ⟪x, b⟫ + c` of `LeanRidgelet.quadraticArgument` is continuous in the pair of the data
and the parameter.  The three summands are continuous for the same reason in three degrees of
difficulty: the constant coefficient is a coordinate projection, the linear term is the inner
product of two projections, and the quadratic term is the inner product of a projection with the
evaluation `(A, x) ↦ A x`, which is continuous in the pair because it is a bounded bilinear map
(`isBoundedBilinearMap_apply`).  The symmetric coefficient enters that evaluation through the
coercion of `LeanRidgelet.QuadraticSymmetric E` into `E →L[ℝ] E`, which is continuous because the
subtype carries the induced topology. -/
theorem continuous_uncurry_quadraticArgument :
    Continuous (Function.uncurry (quadraticArgument (E := E))) := by
  change Continuous fun p : E × QuadraticParameter E ↦
    ⟪p.1, ((p.2.1 : QuadraticSymmetric E) : E →L[ℝ] E) p.1⟫_ℝ + ⟪p.1, p.2.2.1⟫_ℝ + p.2.2.2
  have hsym : Continuous fun p : E × QuadraticParameter E ↦
      ((p.2.1 : QuadraticSymmetric E) : E →L[ℝ] E) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have happ : Continuous fun p : E × QuadraticParameter E ↦
      ((p.2.1 : QuadraticSymmetric E) : E →L[ℝ] E) p.1 :=
    isBoundedBilinearMap_apply.continuous.comp (hsym.prodMk continuous_fst)
  exact ((continuous_fst.inner happ).add
    (continuous_fst.inner (continuous_fst.comp (continuous_snd.comp continuous_snd)))).add
      (continuous_snd.comp (continuous_snd.comp continuous_snd))

omit [InnerProductSpace ℂ Y] in
/-- **The quadratic feature is jointly continuous for a continuous activation.**  Immediate from
`LeanRidgelet.continuous_uncurry_quadraticArgument`, the feature being the activation composed with
the scalar argument. -/
theorem continuous_uncurry_quadraticVectorFeature {σ : ℝ → Y} (hσ : Continuous σ) :
    Continuous (Function.uncurry (quadraticVectorFeature (E := E) σ)) :=
  hσ.comp continuous_uncurry_quadraticArgument

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- **The quadratic argument is jointly measurable.**  The Borel structures on the data space and on
the symmetric coefficients make the jointly continuous scalar argument jointly measurable. -/
theorem measurable_uncurry_quadraticArgument :
    Measurable (Function.uncurry (quadraticArgument (E := E))) :=
  continuous_uncurry_quadraticArgument.measurable

omit [InnerProductSpace ℂ Y] in
/-- **The quadratic feature is jointly strongly measurable for a strongly measurable activation.**
This is the hypothesis that
`LeanRidgelet.stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature` consumes; for a
scalar-valued activation it is the same as plain measurability, and a continuous activation
satisfies it through `LeanRidgelet.continuous_uncurry_quadraticVectorFeature`. -/
theorem stronglyMeasurable_uncurry_quadraticVectorFeature {σ : ℝ → Y}
    (hσ : StronglyMeasurable σ) :
    StronglyMeasurable (Function.uncurry (quadraticVectorFeature (E := E) σ)) :=
  hσ.comp_measurable measurable_uncurry_quadraticArgument

omit [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] in
/-- **The quadratic feature is jointly measurable for a measurable activation.**  The plain
measurable form, for an activation into a bare measurable space. -/
theorem measurable_uncurry_quadraticVectorFeature [MeasurableSpace Y] {σ : ℝ → Y}
    (hσ : Measurable σ) :
    Measurable (Function.uncurry (quadraticVectorFeature (E := E) σ)) :=
  hσ.comp measurable_uncurry_quadraticArgument

/-- **The analysis transform of the quadratic feature is measurable in the parameter.**  The
instantiation of `LeanRidgelet.stronglyMeasurable_bochnerRidgelet` at the quadratic feature: for a
strongly measurable activation and measurable data, the analysis transform is a strongly measurable
function of the quadratic parameter `(A, b, c)`.  No parameter measure enters. -/
theorem stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature (μ : Measure E) [SFinite μ]
    {σ : ℝ → Y} (hσ : StronglyMeasurable σ) {f : E → Y} (hf : AEStronglyMeasurable f μ) :
    StronglyMeasurable (bochnerRidgelet μ (quadraticVectorFeature σ) f) :=
  stronglyMeasurable_bochnerRidgelet μ
    (stronglyMeasurable_uncurry_quadraticVectorFeature hσ) hf

/-- **The analysis transform of the quadratic feature is measurable in the parameter, almost
everywhere form.**  The same statement for an arbitrary measure on the quadratic parameter space,
which is the shape a Tonelli argument over the parameters consumes.  Since the previous theorem
gives genuine strong measurability, this holds for every parameter measure with no σ-finiteness
hypothesis on it -- in particular for `LeanRidgelet.quadraticRelativeMeasure`. -/
theorem aestronglyMeasurable_bochnerRidgelet_quadraticVectorFeature (μ : Measure E) [SFinite μ]
    (ν : Measure (QuadraticParameter E)) {σ : ℝ → Y} (hσ : StronglyMeasurable σ) {f : E → Y}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (bochnerRidgelet μ (quadraticVectorFeature σ) f) ν :=
  (stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature μ hσ hf).aestronglyMeasurable

end Quadratic

end LeanRidgelet
