/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.ParametricIteratedDeriv
public import LeanRidgelet.HA.BochnerMeasurability
public import LeanRidgelet.HA.QuadraticShear
public import LeanRidgelet.HA.QuadraticTransfer

/-!
# The quadratic parameter: iterated derivatives measurable in the base parameter

`LeanRidgelet.HA.QuadraticShear` carries two measurability hypotheses it cannot discharge, and its
"What is established and what is not" paragraph records why: nothing else in this development says
that an iterated derivative in one coordinate of a parameter is measurable in the remaining
coordinates.  The two hypotheses are `Measurable (LeanRidgelet.quadraticConstIteratedDeriv j T)`, in
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul` and in
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul`, and
`AEStronglyMeasurable (iteratedDeriv j (LeanRidgelet.quadraticConstSlice T p)) volume`, in
`LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul`.  This file discharges both.

The general statements the two rest on are ridgelet-independent and live in
`LeanRidgelet.ToMathlib.ParametricIteratedDeriv`: an iterated derivative of positive order is
strongly measurable for every function on the line, and for a function of a pair the iterated
derivative in the last variable is jointly measurable either from joint smoothness (the continuity
route) or from joint continuity one order down (Mathlib's one-step lemma).  This file only
instantiates them, and adds the one route those statements cannot cover.

Instantiating is nearly free: the quadratic parameter's constant coefficient is the last of three
coordinates rather than the second of two, and reassociating a product is a linear homeomorphism, so
the general statements apply through `LeanRidgelet.quadraticParameterPair` unchanged.

The route the general statements cannot cover is the analysis transform.  Its joint smoothness in
the parameter is not known here, so the continuity route is unavailable for it; but
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` says its `j`-th derivative in
the constant coefficient *is* another analysis transform, and
`LeanRidgelet.stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature` says that one is measurable
in the parameter.  So for the one function the boundedness route actually needs, the hypothesis is
discharged from the transfer hypotheses alone.

## Main results

* `LeanRidgelet.quadraticParameterPair` and `LeanRidgelet.quadraticConstPair`: the reassociation,
  with `LeanRidgelet.quadraticConstIteratedDeriv_eq_parametric` and
  `LeanRidgelet.iteratedDeriv_quadraticConstSlice_eq_parametric` identifying both forms of the
  derivative in the constant coefficient with the general parametric one.
* `LeanRidgelet.aestronglyMeasurable_iteratedDeriv_quadraticConstSlice_succ` and
  `LeanRidgelet.aestronglyMeasurable_iteratedDeriv_quadraticConstSlice`: **the slice-wise
  hypothesis**, unconditionally for a positive order and from measurability of `T` for order `0`.
* `LeanRidgelet.continuous_quadraticConstIteratedDeriv`,
  `LeanRidgelet.measurable_quadraticConstIteratedDeriv` and
  `LeanRidgelet.measurable_quadraticConstIteratedDeriv_succ`: **the hypothesis in the parameter**
  for a jointly smooth coefficient function, by the continuity route.
* `LeanRidgelet.measurable_quadraticConstIteratedDeriv_of_eq` and
  `LeanRidgelet.measurable_quadraticConstIteratedDeriv_bochnerRidgelet`: **the transfer route**, for
  the analysis transform.

## What is assumed

For the slice-wise statements, nothing at a positive order, and measurability of the coefficient
function at order `0`.  For the continuity route, `ContDiff ℝ j` of the coefficient function on the
whole parameter space -- the natural hypothesis for a concrete ridgelet function built from a smooth
activation.  For the transfer route, the hypotheses of the derivative transfer together with
measurability of the analysis features and of the data; no smoothness of the transform is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal InnerProductSpace NNReal

namespace LeanRidgelet


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
