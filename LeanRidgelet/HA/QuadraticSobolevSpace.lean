/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import LeanRidgelet.ToMathlib.L2Duality
public import LeanRidgelet.HA.ParametricDerivMeasurable
public import LeanRidgelet.HA.QuadraticShear
public import LeanRidgelet.HA.QuadraticTransfer

/-!
# The intermediate coefficient space: a Sobolev structure in the constant coefficient

`LeanRidgelet.HA.QuadraticComposite` records why a square-integrable composite kernel can never
produce a nonzero reconstruction constant, and what the L1 and L2 theories do instead: they bound
the analysis and the synthesis *separately*, through an intermediate coefficient space in which
neither operator is Hilbert--Schmidt.  This file builds that intermediate space for the quadratic
feature.

## The space

It is the order-`k` Sobolev space in the **constant coefficient** of the parameter, over the
relatively invariant parameter measure; informally

`Γ^k = L²(base ; H^k(ℝ))`,

the base being the first two coefficients `(A, b)` and the line being the constant coefficient `c`.
`LeanRidgelet.quadraticSobolevSeminorm` is its seminorm — the sum over `j ≤ k` of the `L²` norms
against `LeanRidgelet.quadraticRelativeMeasure` of the `j`-th derivative in the constant coefficient
`LeanRidgelet.quadraticConstIteratedDeriv` — and `LeanRidgelet.MemQuadraticSobolev` is membership.
`LeanRidgelet.quadraticBaseSobolevSeminorm` is the same quantity read through the factorization of
`LeanRidgelet.HA.QuadraticParameterFactor`, as an integral over the base parameter of the squared
`L²` norm on the line; the two agree up to the positive finite constant of that factorization, which
is what makes the informal reading `L²(base ; H^k(ℝ))` literal.

The seminorm is valued in `ℝ≥0∞`, so it is defined for every function with no side condition, and
finiteness is what membership asserts.  This matches the use of `eLpNorm` throughout the
development.

## Why this coordinate, and not the Fourier side

Because the action is a shear.  By `LeanRidgelet.quadraticParameterLinearEquiv_apply_shear` the
parameter action of `g` sends `(A, b, c)` to `(A', b', c + s)` with `A'`, `b'` and `s` independent
of `c`.  So differentiation in the constant coefficient commutes with the pull-back with no factor —
a translation has derivative one — and Lebesgue measure on the line absorbs the translation.  The
whole Sobolev structure is therefore carried along by the action, and the only constant that appears
is the square root of the one the parameter measure contributes on its own.  Transporting to the
Fourier side in the constant coefficient, the route `LeanRidgelet.HA.QuadraticWeighted` takes for a
single slice, would give an equivalent weighted space but needs Plancherel and joint measurability
of a partial Fourier transform; none of that is used here, and no Fourier transform occurs anywhere
in this file.

## Main results

* `LeanRidgelet.quadraticSobolevSeminorm` and `LeanRidgelet.MemQuadraticSobolev`: the seminorm and
  the membership predicate, with `LeanRidgelet.MemQuadraticSobolev.memLp` placing the space inside
  `L²` of the parameter measure and `LeanRidgelet.quadraticSobolevSeminorm_mono` making it decrease
  in the order.
* `LeanRidgelet.quadraticSobolevSeminorm_comp_smul`: **invariance under the action.**  Pulling back
  along the parameter action of `g` multiplies the seminorm by exactly
  `‖det L‖₊ ^ (1 / 2)`, the square root of the constant the quasi-invariance of the parameter
  measure contributes.  `LeanRidgelet.MemQuadraticSobolev.comp_smul` is the resulting stability of
  the predicate, so the space is a legitimate intermediate space for the reconstruction argument:
  the action scales the seminorm by a known factor and by nothing else.
* `LeanRidgelet.quadraticBaseSobolevSeminorm_comp_smul`: the same statement one factor down, through
  the factorization of the parameter measure, and
  `LeanRidgelet.exists_quadraticSobolevSeminorm_eq_mul_quadraticBaseSobolevSeminorm` identifying the
  two seminorms up to the constant of that factorization.
* `LeanRidgelet.quadraticConstIteratedDeriv_bochnerRidgelet` and
  `LeanRidgelet.quadraticSobolevSeminorm_bochnerRidgelet`: **the analysis-side identity.**  The
  Sobolev seminorm of the analysis transform of a feature is computed by the *features*: it is the
  sum over `j ≤ k` of the `L²` norms of the analysis transforms of the `j`-th features.  This is the
  payoff of the design — smoothness of the analysis feature is exactly what puts its transform in
  the space, and `LeanRidgelet.memQuadraticSobolev_bochnerRidgelet` says so.
* `LeanRidgelet.enorm_bochnerSynthesis_le_quadraticSobolevSeminorm_mul`: **the synthesis-side
  bound** in dual form.  The synthesis integral against a coefficient function is bounded by the
  seminorm times the `L²` norm of the synthesis feature in the parameter, by Cauchy--Schwarz; only
  the order `0` term of the seminorm is used, so the bound holds for every order.

## What is assumed

Measurability hypotheses, in exactly the shape `LeanRidgelet.HA.QuadraticShear` carries them:
`Measurable (LeanRidgelet.quadraticConstIteratedDeriv j T)`, the derivative in the constant
coefficient viewed as a function on the whole parameter space.  There is no measurability of
`iteratedDeriv` in a parameter anywhere in this development, so it is carried rather than
discharged; see the corresponding remark in `LeanRidgelet.HA.QuadraticShear`.  As there, an additive
Haar measure `lam` on the parameter space appears as a hypothesis of the base-level invariance
statement without appearing in its conclusion: it is only the witness that routes the base statement
through the quasi-invariance proved upstairs.  The analysis-side identity assumes the hypotheses of
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` uniformly in the base parameter,
which is what a concrete ridgelet function is checked against.  The synthesis-side bound assumes
`AEMeasurable` for the two factors it pairs.

## What is deliberately not done

There is **no** Hilbert space here, and no completeness.  This file defines a seminorm and a
predicate on functions, not a normed space on equivalence classes: no carrier is chosen, no quotient
is taken, no `Lp`-valued `Lp` space is built, and the action is not promoted to a bounded operator
or an isometry of anything.  Completeness of the space and the packaging that would turn
`LeanRidgelet.quadraticSobolevSeminorm_comp_smul` into a (quasi-)unitary representation are a
separate and larger question, deliberately left open; the reconstruction argument's needs are to be
stated against the predicate and the seminorm below for now.  Nor is any *bound* on the analysis or
the synthesis operator proved: what is proved is that the analysis transform's seminorm is computed
by the features and that the synthesis integral is dominated by the seminorm, which are the two
inputs such bounds are assembled from.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

/-! ### Two facts about the `L²` seminorm -/

/-- The square of the `L²` seminorm is the lower Lebesgue integral of the squared enorm.  This is
`MeasureTheory.eLpNorm_two_eq_lintegral_enorm_sq` with the square root cleared, which is the form in
which the seminorms below meet the `lintegral` identities of `LeanRidgelet.HA.QuadraticShear`. -/
theorem eLpNorm_two_sq_eq_lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : Type*} [NormedAddCommGroup F] (u : α → F) :
    eLpNorm u 2 μ ^ 2 = ∫⁻ a, ‖u a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_two_eq_lintegral_enorm_sq,
    ← ENNReal.rpow_natCast ((∫⁻ a, ‖u a‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Cauchy--Schwarz for lower Lebesgue integrals.**  The integral of a product of two enorms is at
most the product of the two `L²` seminorms.  This is Hölder's inequality at the conjugate pair
`(2, 2)`, and it is what turns the synthesis integral into a pairing of the seminorm with a dual
quantity for the synthesis feature. -/
theorem lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F G : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
    [OpensMeasurableSpace F] [NormedAddCommGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {u : α → F} {v : α → G} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    ∫⁻ a, ‖u a‖ₑ * ‖v a‖ₑ ∂μ ≤ eLpNorm u 2 μ * eLpNorm v 2 μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hu.enorm hv.enorm
  simp only [Pi.mul_apply] at h
  refine h.trans_eq ?_
  rw [eLpNorm_two_eq_lintegral_enorm_sq, eLpNorm_two_eq_lintegral_enorm_sq]
  norm_num [ENNReal.rpow_natCast]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The derivative in the constant coefficient at order zero -/

/-- At order `0` the derivative in the constant coefficient is the function itself. -/
@[simp]
theorem quadraticConstIteratedDeriv_zero (T : QuadraticParameter E → ℂ) :
    quadraticConstIteratedDeriv 0 T = T := by
  funext ξ
  simp only [quadraticConstIteratedDeriv, iteratedDeriv_zero, quadraticConstSlice]

/-- The derivative in the constant coefficient evaluated at a split parameter is the derivative of
the slice at the base parameter.  This is the bridge between the global form of the seminorm and its
base-level form. -/
theorem quadraticConstIteratedDeriv_apply (j : ℕ) (T : QuadraticParameter E → ℂ)
    (p : QuadraticSymmetric E × E) (t : ℝ) :
    quadraticConstIteratedDeriv j T (p.1, p.2, t) = iteratedDeriv j (quadraticConstSlice T p) t :=
  rfl

section Analysis

variable [MeasurableSpace E] [BorelSpace E]

/-! ### The analysis transform through the derivative transfer -/

/-- **The derivative transfer, on the whole parameter space.**  For a sequence of analysis features
each the derivative of the previous one, the `j`-th derivative in the constant coefficient of the
analysis transform of the first feature is the analysis transform of the `j`-th feature, at every
parameter.  This is `LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` with its
hypotheses taken uniformly in the base parameter, so that the conclusion is an identity of two
functions on the parameter space rather than one for each frozen slice. -/
theorem quadraticConstIteratedDeriv_bochnerRidgelet {ρ : ℕ → ℝ → ℂ} (f : E → ℂ)
    {bound : QuadraticSymmetric E → E → ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ), ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound A b i x)
    (hboundint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ),
      Integrable (bound A b i) (volume : Measure E))
    (j : ℕ) :
    quadraticConstIteratedDeriv j
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f) =
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f := by
  funext ξ
  exact congrFun (iteratedDeriv_bochnerRidgelet_quadraticVectorFeature f ξ.1 ξ.2.1 hderiv
    (hmeas ξ.1 ξ.2.1) (hint ξ.1 ξ.2.1) (hbound ξ.1 ξ.2.1) (hboundint ξ.1 ξ.2.1) j) ξ.2.2

end Analysis

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-! ### The seminorm and the membership predicate -/

/-- **The order-`k` Sobolev seminorm in the constant coefficient.**  The sum over `j ≤ k` of the
`L²` norms, against the relatively invariant parameter measure, of the `j`-th derivative in the
constant coefficient.  This is the seminorm of the intermediate coefficient space `Γ^k`, informally
`L²(base ; H^k(ℝ))`; see `LeanRidgelet.quadraticBaseSobolevSeminorm` for the reading that makes the
informal description literal.  It is `ℝ≥0∞`-valued, so it is defined for every `T` with no
finiteness or measurability side condition. -/
def quadraticSobolevSeminorm (lam : Measure (QuadraticParameter E)) (k : ℕ)
    (T : QuadraticParameter E → ℂ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1),
    eLpNorm (quadraticConstIteratedDeriv j T) 2 (quadraticRelativeMeasure lam)

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- At order `0` the seminorm is the `L²` norm of the coefficient function itself. -/
@[simp]
theorem quadraticSobolevSeminorm_zero (lam : Measure (QuadraticParameter E))
    (T : QuadraticParameter E → ℂ) :
    quadraticSobolevSeminorm lam 0 T = eLpNorm T 2 (quadraticRelativeMeasure lam) := by
  simp [quadraticSobolevSeminorm]

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- Each term of the seminorm is bounded by the seminorm. -/
theorem eLpNorm_quadraticConstIteratedDeriv_le_quadraticSobolevSeminorm
    (lam : Measure (QuadraticParameter E)) {j k : ℕ} (hj : j ≤ k)
    (T : QuadraticParameter E → ℂ) :
    eLpNorm (quadraticConstIteratedDeriv j T) 2 (quadraticRelativeMeasure lam) ≤
      quadraticSobolevSeminorm lam k T :=
  Finset.single_le_sum
    (f := fun i ↦ eLpNorm (quadraticConstIteratedDeriv i T) 2 (quadraticRelativeMeasure lam))
    (fun _ _ ↦ zero_le) (Finset.mem_range_succ_iff.2 hj)

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The seminorm dominates the plain `L²` norm: the space sits inside `L²` of the parameter
measure. -/
theorem eLpNorm_le_quadraticSobolevSeminorm (lam : Measure (QuadraticParameter E)) (k : ℕ)
    (T : QuadraticParameter E → ℂ) :
    eLpNorm T 2 (quadraticRelativeMeasure lam) ≤ quadraticSobolevSeminorm lam k T := by
  simpa using
    eLpNorm_quadraticConstIteratedDeriv_le_quadraticSobolevSeminorm lam (Nat.zero_le k) T

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The seminorm increases with the order, so the spaces decrease. -/
theorem quadraticSobolevSeminorm_mono (lam : Measure (QuadraticParameter E)) {k l : ℕ} (h : k ≤ l)
    (T : QuadraticParameter E → ℂ) :
    quadraticSobolevSeminorm lam k T ≤ quadraticSobolevSeminorm lam l T :=
  Finset.sum_le_sum_of_subset fun _ hj ↦
    Finset.mem_range.2 ((Finset.mem_range.1 hj).trans_le (Nat.succ_le_succ h))

/-- **Membership in the intermediate coefficient space `Γ^k`.**  A coefficient function lies in the
space when each of its derivatives up to order `k` in the constant coefficient is measurable as a
function on the parameter space and the order-`k` Sobolev seminorm is finite.  The measurability is
carried in exactly the shape `LeanRidgelet.HA.QuadraticShear` uses it; it is not available anywhere
in this development for `iteratedDeriv` in a parameter, and is what the statements below consume. -/
structure MemQuadraticSobolev (lam : Measure (QuadraticParameter E)) (k : ℕ)
    (T : QuadraticParameter E → ℂ) : Prop where
  /-- Every derivative up to order `k` in the constant coefficient is measurable. -/
  measurable : ∀ j ≤ k, Measurable (quadraticConstIteratedDeriv j T)
  /-- The order-`k` Sobolev seminorm is finite. -/
  seminorm_lt_top : quadraticSobolevSeminorm lam k T < ∞

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- A member of the space is square integrable for the parameter measure. -/
theorem MemQuadraticSobolev.memLp {lam : Measure (QuadraticParameter E)} {k : ℕ}
    {T : QuadraticParameter E → ℂ} (h : MemQuadraticSobolev lam k T) :
    MemLp T 2 (quadraticRelativeMeasure lam) := by
  have hm : Measurable T := by simpa using h.measurable 0 (Nat.zero_le k)
  exact ⟨hm.aestronglyMeasurable,
    lt_of_le_of_lt (eLpNorm_le_quadraticSobolevSeminorm lam k T) h.seminorm_lt_top⟩

/-! ### Invariance under the action -/

/-- **The action scales the seminorm by a known factor.**  Pulling a coefficient function back along
the parameter action of `g` multiplies its order-`k` Sobolev seminorm in the constant coefficient by
exactly `‖det L‖₊ ^ (1 / 2)`, the square root of the constant that the quasi-invariance of
`LeanRidgelet.quadraticRelativeMeasure` contributes; the square root appears because the seminorm is
an `L²` norm and the quasi-invariance is a statement about the squared integrand.

Nothing else happens, and that is the point: by
`LeanRidgelet.quadraticConstIteratedDeriv_comp_smul` the action is a shear in the constant
coefficient, so it neither differentiates nor rescales that coordinate, and the derivative of a
pull-back is the pull-back of the derivative with no factor.  The whole Sobolev structure is
therefore carried along, term by term, with one and the same constant, which is why the constant
factors out of the sum.  In particular the same square-root normalization of the pull-back that
makes `LeanRidgelet.quadraticRelativeParameterLpUnitaryRepresentation` unitary makes this seminorm
invariant on the nose. -/
theorem quadraticSobolevSeminorm_comp_smul (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) (k : ℕ) {T : QuadraticParameter E → ℂ}
    (hT : ∀ j ≤ k, Measurable (quadraticConstIteratedDeriv j T)) :
    quadraticSobolevSeminorm lam k (fun η ↦ T (g • η)) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) ^ ((1 : ℝ) / 2) *
        quadraticSobolevSeminorm lam k T := by
  rw [quadraticSobolevSeminorm, quadraticSobolevSeminorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eLpNorm_two_eq_lintegral_enorm_sq, eLpNorm_two_eq_lintegral_enorm_sq,
    lintegral_enorm_quadraticConstIteratedDeriv_comp_smul lam g j
      (hT j (Finset.mem_range_succ_iff.1 hj)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]

/-- **The predicate is preserved by the action.**  Pulling back along the parameter action of `g`
keeps a coefficient function in the space: the measurability is transported by the equivariance of
the derivative in the constant coefficient, and the seminorm stays finite because the action only
multiplies it by the finite constant of
`LeanRidgelet.quadraticSobolevSeminorm_comp_smul`.  Together with that identity this is what makes
`Γ^k` a legitimate intermediate space for the reconstruction argument. -/
theorem MemQuadraticSobolev.comp_smul {lam : Measure (QuadraticParameter E)}
    [lam.IsAddHaarMeasure] {k : ℕ} {T : QuadraticParameter E → ℂ}
    (h : MemQuadraticSobolev lam k T) (g : E ≃ᵃ[ℝ] E) :
    MemQuadraticSobolev lam k (fun η ↦ T (g • η)) := by
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [quadraticConstIteratedDeriv_comp_smul_eq]
    exact (h.measurable j hj).comp (quadraticParameter_measurable g)
  · rw [quadraticSobolevSeminorm_comp_smul lam g k h.measurable]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.coe_ne_top)) h.seminorm_lt_top

/-! ### The base-level reading of the seminorm -/

/-- **The seminorm read through the factorization of the parameter measure.**  The order-`k` Sobolev
seminorm of a coefficient function, with the constant coefficient integrated first: the sum over
`j ≤ k` of the square roots of the integrals over the base parameter of the squared `L²` norm on the
line of the `j`-th derivative of the slice.  This is the literal form of the informal description
`Γ^k = L²(base ; H^k(ℝ))`, and by
`LeanRidgelet.exists_quadraticSobolevSeminorm_eq_mul_quadraticBaseSobolevSeminorm` it agrees with
`LeanRidgelet.quadraticSobolevSeminorm` up to the positive finite constant of the factorization. -/
def quadraticBaseSobolevSeminorm (κ : Measure (QuadraticSymmetric E × E)) (k : ℕ)
    (T : QuadraticParameter E → ℂ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1),
    (∫⁻ p : QuadraticSymmetric E × E,
        eLpNorm (iteratedDeriv j (quadraticConstSlice T p)) 2 (volume : Measure ℝ) ^ 2
        ∂(quadraticBaseRelativeMeasure κ)) ^ ((1 : ℝ) / 2)

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The base-level seminorm as an iterated lower Lebesgue integral, which is the form the invariance
statements of `LeanRidgelet.HA.QuadraticShear` are stated in. -/
theorem quadraticBaseSobolevSeminorm_eq_lintegral (κ : Measure (QuadraticSymmetric E × E)) (k : ℕ)
    (T : QuadraticParameter E → ℂ) :
    quadraticBaseSobolevSeminorm κ k T =
      ∑ j ∈ Finset.range (k + 1),
        (∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t,
            ‖iteratedDeriv j (quadraticConstSlice T p) t‖ₑ ^ 2 ∂(volume : Measure ℝ)
            ∂(quadraticBaseRelativeMeasure κ)) ^ ((1 : ℝ) / 2) := by
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact lintegral_congr fun p ↦ eLpNorm_two_sq_eq_lintegral_enorm_sq _

/-- **Invariance of the base-level seminorm.**  The same constant `‖det L‖₊ ^ (1 / 2)` appears one
factor down, after the parameter measure has been factored over the constant coefficient; the
undetermined constant of the factorization cancels between the two sides.  As in
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul`, the additive Haar measure
`lam` on the full parameter space is only a witness: it does not appear in the conclusion, and it is
there because the base parameter measure has no quasi-invariance of its own in this development. -/
theorem quadraticBaseSobolevSeminorm_comp_smul (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (κ : Measure (QuadraticSymmetric E × E)) [κ.IsAddHaarMeasure]
    (g : E ≃ᵃ[ℝ] E) (k : ℕ) {T : QuadraticParameter E → ℂ}
    (hT : ∀ j ≤ k, Measurable (quadraticConstIteratedDeriv j T)) :
    quadraticBaseSobolevSeminorm κ k (fun η ↦ T (g • η)) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) ^ ((1 : ℝ) / 2) *
        quadraticBaseSobolevSeminorm κ k T := by
  rw [quadraticBaseSobolevSeminorm_eq_lintegral, quadraticBaseSobolevSeminorm_eq_lintegral,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul lam κ g j
      (hT j (Finset.mem_range_succ_iff.1 hj)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]

/-- **The two readings of the seminorm agree.**  The order-`k` Sobolev seminorm over the parameter
measure is a positive finite multiple of its base-level form, the multiple being the square root of
the constant of the factorization of `LeanRidgelet.HA.QuadraticParameterFactor`.  This is the
precise content of the informal identification `Γ^k = L²(base ; H^k(ℝ))`; the constant is
undetermined because `lam` and `κ` are each only fixed up to a scalar. -/
theorem exists_quadraticSobolevSeminorm_eq_mul_quadraticBaseSobolevSeminorm
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (κ : Measure (QuadraticSymmetric E × E)) [κ.IsAddHaarMeasure] (k : ℕ)
    {T : QuadraticParameter E → ℂ} (hT : ∀ j ≤ k, Measurable (quadraticConstIteratedDeriv j T)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      quadraticSobolevSeminorm lam k T =
        c ^ ((1 : ℝ) / 2) * quadraticBaseSobolevSeminorm κ k T := by
  obtain ⟨c, hc0, hctop, hmap⟩ := exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul lam κ
  refine ⟨c, hc0, hctop, ?_⟩
  rw [quadraticSobolevSeminorm, quadraticBaseSobolevSeminorm_eq_lintegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eLpNorm_two_eq_lintegral_enorm_sq,
    lintegral_quadraticRelativeMeasure_of_map_eq_smul hmap
      ((hT j (Finset.mem_range_succ_iff.1 hj)).enorm.pow_const 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
  simp only [quadraticConstIteratedDeriv_apply]

/-! ### The analysis-side identity -/

omit [BorelSpace (QuadraticSymmetric E)] in
/-- **The seminorm of the analysis transform is computed by the features.**  For a sequence of
analysis features each the derivative of the previous one, the order-`k` Sobolev seminorm in the
constant coefficient of the analysis transform of the first feature is the sum over `j ≤ k` of the
`L²` norms of the analysis transforms of the `j`-th features.

This is the payoff of putting the Sobolev structure in the constant coefficient: no Fourier
transform appears, and the smoothness of the analysis feature is exactly what puts its transform in
the space.  Compare `LeanRidgelet.eLpNorm_pow_smul_angularFourier_bochnerRidgelet_slice`, which
records the same information one slice at a time and on the Fourier side, at the cost of a
Plancherel constant. -/
theorem quadraticSobolevSeminorm_bochnerRidgelet (lam : Measure (QuadraticParameter E))
    {ρ : ℕ → ℝ → ℂ} (f : E → ℂ) {bound : QuadraticSymmetric E → E → ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ), ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound A b i x)
    (hboundint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ),
      Integrable (bound A b i) (volume : Measure E))
    (k : ℕ) :
    quadraticSobolevSeminorm lam k
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f) =
      ∑ j ∈ Finset.range (k + 1),
        eLpNorm (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f) 2
          (quadraticRelativeMeasure lam) := by
  rw [quadraticSobolevSeminorm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quadraticConstIteratedDeriv_bochnerRidgelet f hderiv hmeas hint hbound hboundint j]

omit [BorelSpace (QuadraticSymmetric E)] in
/-- **Smoothness of the analysis feature puts its transform in the space.**  If in addition each of
the analysis transforms of the features up to order `k` is measurable in the parameter and square
integrable for the parameter measure, then the analysis transform of the first feature lies in
`Γ^k`.  The two extra hypotheses are conditions on the features, not on the transform of the first
one, which is the form a concrete ridgelet function is checked against. -/
theorem memQuadraticSobolev_bochnerRidgelet (lam : Measure (QuadraticParameter E))
    {ρ : ℕ → ℝ → ℂ} (f : E → ℂ) {bound : QuadraticSymmetric E → E → ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ), ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound A b i x)
    (hboundint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ),
      Integrable (bound A b i) (volume : Measure E))
    (k : ℕ)
    (htmeas : ∀ j ≤ k,
      Measurable (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f))
    (htfin : ∀ j ≤ k,
      eLpNorm (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f) 2
        (quadraticRelativeMeasure lam) < ∞) :
    MemQuadraticSobolev lam k
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f) := by
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [quadraticConstIteratedDeriv_bochnerRidgelet f hderiv hmeas hint hbound hboundint j]
    exact htmeas j hj
  · rw [quadraticSobolevSeminorm_bochnerRidgelet lam f hderiv hmeas hint hbound hboundint k]
    exact ENNReal.sum_lt_top.2 fun j hj ↦ htfin j (Finset.mem_range_succ_iff.1 hj)

/-! ### The synthesis-side bound -/

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The synthesis integral is dominated by the seminorm.**  The Bochner synthesis of a coefficient
function against the quadratic synthesis feature is bounded, at every data point, by the order-`k`
Sobolev seminorm of the coefficient function times the `L²` norm in the parameter of the synthesis
feature at that point.  This is the dual form of the synthesis bound: the second factor is the dual
quantity for the synthesis feature, and it is the only place the feature enters.

Only the order-`0` term of the seminorm is used, so the bound holds for every order; the smoothness
in the constant coefficient is what the *analysis* side needs, not the synthesis side.  Combining
this with `LeanRidgelet.quadraticSobolevSeminorm_bochnerRidgelet` is how a bound on the composite is
assembled without either operator being Hilbert--Schmidt, but that assembly is not carried out
here. -/
theorem enorm_bochnerSynthesis_le_quadraticSobolevSeminorm_mul
    (lam : Measure (QuadraticParameter E)) (k : ℕ) (φ : ℝ → ℂ)
    {γ : QuadraticParameter E → ℂ} (x : E)
    (hγ : AEMeasurable γ (quadraticRelativeMeasure lam))
    (hφ : AEMeasurable (fun ξ ↦ quadraticVectorFeature φ x ξ) (quadraticRelativeMeasure lam)) :
    ‖bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature φ) γ x‖ₑ ≤
      quadraticSobolevSeminorm lam k γ *
        eLpNorm (fun ξ ↦ quadraticVectorFeature φ x ξ) 2 (quadraticRelativeMeasure lam) := by
  rw [bochnerSynthesis]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp only [smul_eq_mul, enorm_mul]
  refine le_trans (lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two _ hγ hφ) ?_
  gcongr
  exact eLpNorm_le_quadraticSobolevSeminorm lam k γ

/-! ### Discharging the measurability hypotheses -/

/-- The derivatives up to order `k` in the constant coefficient of a `k` times continuously
differentiable coefficient function are measurable on the parameter space.  This is the continuity
route of `LeanRidgelet.HA.ParametricDerivMeasurable`, packaged in the shape the statements above
consume, so that for a smooth coefficient function nothing has to be assumed. -/
theorem measurable_quadraticConstIteratedDeriv_le_of_contDiff {k : ℕ}
    {T : QuadraticParameter E → ℂ} (hT : ContDiff ℝ k T) :
    ∀ j ≤ k, Measurable (quadraticConstIteratedDeriv j T) := fun j hj ↦
  measurable_quadraticConstIteratedDeriv j (hT.of_le (by exact_mod_cast hj))

/-- **The invariance of the seminorm for a smooth coefficient function, with no measurability
hypothesis left.**  For `T` that is `k` times continuously differentiable on the parameter space the
order-`k` seminorm of the pull-back is the square root of the determinant of the linear part times
the seminorm of `T`.  This is `LeanRidgelet.quadraticSobolevSeminorm_comp_smul` with its
measurability family discharged. -/
theorem quadraticSobolevSeminorm_comp_smul_of_contDiff (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) {k : ℕ} {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ k T) :
    quadraticSobolevSeminorm lam k (fun η ↦ T (g • η)) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) ^ ((1 : ℝ) / 2) *
        quadraticSobolevSeminorm lam k T :=
  quadraticSobolevSeminorm_comp_smul lam g k
    (measurable_quadraticConstIteratedDeriv_le_of_contDiff hT)

/-- **Membership from smoothness and finiteness alone.**  A `k` times continuously differentiable
coefficient function of finite order-`k` seminorm lies in the space. -/
theorem memQuadraticSobolev_of_contDiff {lam : Measure (QuadraticParameter E)} {k : ℕ}
    {T : QuadraticParameter E → ℂ} (hT : ContDiff ℝ k T)
    (hfin : quadraticSobolevSeminorm lam k T < ∞) :
    MemQuadraticSobolev lam k T :=
  ⟨measurable_quadraticConstIteratedDeriv_le_of_contDiff hT, hfin⟩

/-- **The analysis transform lies in the space, with only checkable hypotheses.**  This is
`LeanRidgelet.memQuadraticSobolev_bochnerRidgelet` with its measurability hypothesis on the
transforms replaced by measurability of the analysis features and of the data, which is what
`LeanRidgelet.stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature` supplies.  What is left
assumed is the transfer of derivatives and finiteness of each transform's `L²` norm; no
measurability of an `iteratedDeriv` in a parameter is assumed anywhere. -/
theorem memQuadraticSobolev_bochnerRidgelet_of_stronglyMeasurable
    (lam : Measure (QuadraticParameter E)) {ρ : ℕ → ℝ → ℂ} (f : E → ℂ)
    {bound : QuadraticSymmetric E → E → ℕ → E → ℝ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ) (c : ℝ), Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ), ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound A b i x)
    (hboundint : ∀ (A : QuadraticSymmetric E) (b : E) (i : ℕ),
      Integrable (bound A b i) (volume : Measure E))
    (k : ℕ) (hρmeas : ∀ i, StronglyMeasurable (ρ i))
    (hf : AEStronglyMeasurable f (volume : Measure E))
    (htfin : ∀ j ≤ k,
      eLpNorm (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ j)) f) 2
        (quadraticRelativeMeasure lam) < ∞) :
    MemQuadraticSobolev lam k
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f) :=
  memQuadraticSobolev_bochnerRidgelet lam f hderiv hmeas hint hbound hboundint k
    (fun j _ ↦ (stronglyMeasurable_bochnerRidgelet_quadraticVectorFeature (volume : Measure E)
      (hρmeas j) hf).measurable) htfin

end Measure

end LeanRidgelet
