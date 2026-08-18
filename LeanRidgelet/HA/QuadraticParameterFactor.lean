/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticRelativeMeasure
public import LeanRidgelet.ToMathlib.HaarProdAssoc

/-!
# Factoring the quadratic parameter measure over the constant coefficient

`LeanRidgelet.HA.QuadraticWeighted` proves a frequency-weighted `L²` identity for each slice of the
quadratic analysis transform in the constant coefficient, and lists three obstructions to
integrating those slices over the remaining parameters.  This file removes the second one, which is
pure measure bookkeeping.

The parameter space `LeanRidgelet.QuadraticParameter E = QuadraticSymmetric E × E × ℝ` is a
right-nested triple product whose last coordinate is the constant coefficient, and the parameter
measure `LeanRidgelet.quadraticRelativeMeasure lam` is built from an abstract additive Haar measure
`lam` on it by restricting to the nondegenerate locus and weighting by a power of the absolute
symmetric determinant.  An abstract Haar measure is not a product, so Tonelli does not apply to it.
But both the restricting set `LeanRidgelet.quadraticNondegenerate` and the weight
`LeanRidgelet.quadraticRelativeWeight` are defined through `LeanRidgelet.quadraticSymmetricDet`,
which reads only the symmetric coefficient; so both factor through the *base parameter*
`(A, b) : QuadraticSymmetric E × E`, and only the Haar measure itself stands in the way.
`LeanRidgelet.ToMathlib.HaarProdAssoc` disposes of that: after transport along the associativity
equivalence `QuadraticSymmetric E × E × ℝ ≃ᵐ (QuadraticSymmetric E × E) × ℝ`, an additive Haar
measure is a positive finite multiple of a product of additive Haar measures, and restriction and
weighting through the first factor commute with the transport.

The outcome is that the transported parameter measure is a positive finite multiple of
`(quadraticBaseRelativeMeasure κ).prod volume`, where `quadraticBaseRelativeMeasure κ` is the same
restrict-and-weight construction applied to an additive Haar measure `κ` on the base parameter
space.  The Lebesgue measure in the last slot is the one the Plancherel step of
`LeanRidgelet.HA.QuadraticWeighted` produces, so the two sides of a future integration now speak
about the same measure in the constant coefficient.

## Main results

* `LeanRidgelet.quadraticBaseRelativeMeasure`: the base-parameter analogue of
  `LeanRidgelet.quadraticRelativeMeasure`, with its nondegenerate locus
  `LeanRidgelet.quadraticBaseNondegenerate` and weight `LeanRidgelet.quadraticBaseWeight`.
* `LeanRidgelet.exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul`: the factorization.
* `LeanRidgelet.lintegral_quadraticRelativeMeasure_of_map_eq_smul`: the factorization spent on a
  lower Lebesgue integral, in the iterated form a Tonelli argument consumes.
* `LeanRidgelet.exists_lintegral_quadraticRelativeMeasure_eq_mul_lintegral`: the two combined.

## What is assumed

One hypothesis that cannot be discharged here: an additive Haar measure `κ` on the base parameter
space `QuadraticSymmetric E × E`, to compare the transported measure against.  It is a hypothesis
rather than a construction because `lam` itself is abstract, so there is no canonical `κ` to build;
any additive Haar measure will do, and changing it only changes the constant.  Everything else is
unconditional.

## What remains

Only the measure bookkeeping is done here.  The weighted slice estimate of
`LeanRidgelet.HA.QuadraticWeighted` is **not** integrated, and this file does not bring that any
closer than the two remaining obstructions listed there allow: the integrand of a Tonelli step over
the weighted side is the partial Fourier transform of the slice, whose joint measurability in the
parameter is what `LeanRidgelet.HA.BochnerMeasurability` supplies, and the weighted side is a
function of a frequency rather than of a constant coefficient, so the identity to be integrated is
not an identity of two functions on the parameter space.  What is settled is that the measure poses
no obstruction: it factors, with a positive finite constant, over exactly the coordinate the
estimate is stated in.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The base parameter space -/

/-- The determinant of the symmetric coefficient of a *base parameter* `(A, b)`, that is, of a
quadratic parameter with the constant coefficient dropped.  This is
`LeanRidgelet.quadraticSymmetricDet` read on the first two coordinates only. -/
def quadraticBaseDet (p : QuadraticSymmetric E × E) : ℝ := (p.1 : E →L[ℝ] E).det

/-- The symmetric determinant of a quadratic parameter reads only its base parameter.  This is the
factorization that makes the whole file work. -/
theorem quadraticSymmetricDet_eq_quadraticBaseDet (ξ : QuadraticParameter E) :
    quadraticSymmetricDet ξ = quadraticBaseDet (ξ.1, ξ.2.1) := rfl

/-- The nondegenerate locus of base parameters.  Compare
`LeanRidgelet.quadraticNondegenerate`. -/
def quadraticBaseNondegenerate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Set (QuadraticSymmetric E × E) :=
  {p | quadraticBaseDet p ≠ 0}

/-- The nondegenerate locus of quadratic parameters is the cylinder over the nondegenerate locus of
base parameters. -/
theorem quadraticNondegenerate_eq_preimage :
    quadraticNondegenerate E =
      {ξ : QuadraticParameter E | (ξ.1, ξ.2.1) ∈ quadraticBaseNondegenerate E} := rfl

/-- The relatively invariant weight on the base parameter space, with the same exponent
`-(m + 1) / 2` as `LeanRidgelet.quadraticRelativeWeight`. -/
def quadraticBaseWeight (p : QuadraticSymmetric E × E) : ℝ≥0∞ :=
  ENNReal.ofReal (|quadraticBaseDet p| ^ (-(Module.finrank ℝ E + 1 : ℝ) / 2))

/-- The relatively invariant weight of a quadratic parameter reads only its base parameter. -/
theorem quadraticRelativeWeight_eq_quadraticBaseWeight :
    (quadraticRelativeWeight : QuadraticParameter E → ℝ≥0∞) =
      fun ξ ↦ quadraticBaseWeight (ξ.1, ξ.2.1) := rfl

/-! ### The base parameter measure -/

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- **The base parameter measure.**  An additive Haar measure `κ` on the base parameter space,
restricted to the nondegenerate locus and weighted by `LeanRidgelet.quadraticBaseWeight`; the exact
analogue of `LeanRidgelet.quadraticRelativeMeasure` one factor down. -/
def quadraticBaseRelativeMeasure (κ : Measure (QuadraticSymmetric E × E)) :
    Measure (QuadraticSymmetric E × E) :=
  (κ.restrict (quadraticBaseNondegenerate E)).withDensity quadraticBaseWeight

omit [BorelSpace E] in
/-- The base symmetric determinant is measurable, being continuous in the symmetric
coefficient. -/
theorem measurable_quadraticBaseDet :
    Measurable (quadraticBaseDet : QuadraticSymmetric E × E → ℝ) :=
  (ContinuousLinearMap.continuous_det.comp continuous_subtype_val).measurable.comp measurable_fst

omit [BorelSpace E] in
/-- The nondegenerate locus of base parameters is measurable. -/
theorem measurableSet_quadraticBaseNondegenerate :
    MeasurableSet (quadraticBaseNondegenerate E) :=
  (measurable_quadraticBaseDet (measurableSet_singleton (0 : ℝ))).compl

omit [BorelSpace E] in
/-- The base weight is measurable. -/
theorem measurable_quadraticBaseWeight :
    Measurable (quadraticBaseWeight : QuadraticSymmetric E × E → ℝ≥0∞) := by
  have habs : Measurable fun p : QuadraticSymmetric E × E ↦ |quadraticBaseDet p| :=
    continuous_abs.measurable.comp measurable_quadraticBaseDet
  exact ENNReal.measurable_ofReal.comp (habs.pow_const _)

/-! ### The factorization -/

/-- **The quadratic parameter measure factors over the constant coefficient.**  Transported along
the associativity equivalence, `LeanRidgelet.quadraticRelativeMeasure lam` is a positive finite
multiple of the product of the base parameter measure of any additive Haar measure `κ` on
`QuadraticSymmetric E × E` with the Lebesgue measure of the constant coefficient.  The constant is
not determined: `lam` and `κ` are each only fixed up to a scalar. -/
theorem exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (κ : Measure (QuadraticSymmetric E × E)) [κ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      (quadraticRelativeMeasure lam).map MeasurableEquiv.prodAssoc.symm =
        c • (quadraticBaseRelativeMeasure κ).prod (volume : Measure ℝ) := by
  obtain ⟨c, hc0, hctop, hc⟩ :=
    Measure.exists_map_prodAssoc_symm_eq_smul_prod lam κ (volume : Measure ℝ)
  refine ⟨c, hc0, hctop, ?_⟩
  rw [quadraticRelativeMeasure, quadraticNondegenerate_eq_preimage,
    quadraticRelativeWeight_eq_quadraticBaseWeight]
  exact Measure.map_prodAssoc_symm_withDensity_of_map_eq_smul measurable_quadraticBaseWeight
    (Measure.map_prodAssoc_symm_restrict_of_map_eq_smul measurableSet_quadraticBaseNondegenerate hc)

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The factorization spent on an integral.**  Given the factorization, a lower Lebesgue integral
against the quadratic parameter measure is the constant times the iterated integral over the base
parameter and the constant coefficient — the form a Tonelli argument consumes.  Only the outer
measure is abstract; the inner one is the Lebesgue measure of the constant coefficient. -/
theorem lintegral_quadraticRelativeMeasure_of_map_eq_smul
    {lam : Measure (QuadraticParameter E)} {κ : Measure (QuadraticSymmetric E × E)} {c : ℝ≥0∞}
    (hmap : (quadraticRelativeMeasure lam).map MeasurableEquiv.prodAssoc.symm =
      c • (quadraticBaseRelativeMeasure κ).prod (volume : Measure ℝ))
    {g : QuadraticParameter E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂(quadraticRelativeMeasure lam) =
      c * ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t, g (p.1, p.2, t) ∂(volume : Measure ℝ)
        ∂(quadraticBaseRelativeMeasure κ) := by
  have hcomp : Measurable fun q : (QuadraticSymmetric E × E) × ℝ ↦ g (q.1.1, q.1.2, q.2) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hkey := lintegral_map_equiv (μ := quadraticRelativeMeasure lam)
    (fun q : (QuadraticSymmetric E × E) × ℝ ↦ g (q.1.1, q.1.2, q.2)) MeasurableEquiv.prodAssoc.symm
  rw [hmap, lintegral_smul_measure, lintegral_prod _ hcomp.aemeasurable] at hkey
  exact hkey.symm

/-- The two previous results combined: the integral against the quadratic parameter measure is a
positive finite multiple of the iterated integral over the base parameter and the constant
coefficient, for any additive Haar measures `lam` and `κ`. -/
theorem exists_lintegral_quadraticRelativeMeasure_eq_mul_lintegral
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (κ : Measure (QuadraticSymmetric E × E)) [κ.IsAddHaarMeasure]
    {g : QuadraticParameter E → ℝ≥0∞} (hg : Measurable g) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∫⁻ ξ, g ξ ∂(quadraticRelativeMeasure lam) =
        c * ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t, g (p.1, p.2, t) ∂(volume : Measure ℝ)
          ∂(quadraticBaseRelativeMeasure κ) := by
  obtain ⟨c, hc0, hctop, hmap⟩ :=
    exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul lam κ
  exact ⟨c, hc0, hctop, lintegral_quadraticRelativeMeasure_of_map_eq_smul hmap hg⟩

end LeanRidgelet
