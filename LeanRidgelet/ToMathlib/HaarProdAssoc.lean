/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Additive Haar measure on a right-nested triple product

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

An abstract additive Haar measure `lam` on a triple product `X × Y × Z` is not literally a product
measure, so Fubini and Tonelli do not apply to it.  It becomes one after transport along the
associativity equivalence: `lam.map MeasurableEquiv.prodAssoc.symm` is an additive Haar measure on
the left-nested product `(X × Y) × Z`, as is the product `κ.prod ν` of additive Haar measures on the
two factors, and uniqueness of additive Haar measure identifies the two up to a positive finite
constant.  This is the only step in which the Haar hypothesis is used; the constant is
`MeasureTheory.Measure.addHaarScalarFactor`, and it cannot be pinned down further, since `lam`, `κ`
and `ν` are each only determined up to a scalar.

The transport is stated with the *measurable* equivalence `MeasurableEquiv.prodAssoc.symm`, because
that is the form `MeasureTheory.lintegral_map_equiv` and the Tonelli lemmas consume.  Inside the
proof the same function is viewed as the continuous additive equivalence
`(AddEquiv.prodAssoc _ _ _).symm`, which is what the Haar pushforward lemma
`AddEquiv.isAddHaarMeasure_map` accepts.

Two commutation lemmas accompany the factorization, for the two operations that a relatively
invariant measure applies to a Haar measure.  Restricting `lam` to a set that only constrains the
`X` and `Y` coordinates, and weighting it by a density that only reads those coordinates, both
survive the transport and turn the product into the product of the restricted or weighted first
factor with the untouched second factor.  Neither needs the Haar hypothesis: they are stated for an
arbitrary measure satisfying the conclusion of the factorization.

## Main results

* `MeasureTheory.Measure.exists_map_prodAssoc_symm_eq_smul_prod`: the factorization of an additive
  Haar measure on `X × Y × Z` as a positive finite multiple of a product measure on `(X × Y) × Z`.
* `MeasureTheory.Measure.map_prodAssoc_symm_restrict_of_map_eq_smul` and
  `MeasureTheory.Measure.map_prodAssoc_symm_withDensity_of_map_eq_smul`: the two commutation
  lemmas.
* `MeasureTheory.Measure.map_withDensity_measurableEquiv`: the auxiliary transport of a weighted
  measure along a measurable equivalence, absent from Mathlib in this form.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

/-! ### Transport of a density along a measurable equivalence -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushing a weighted measure forward along a measurable equivalence weights the pushforward by
the transported density.  Both sides are evaluated on a measurable set, where the identity is the
change of variables for the lower Lebesgue integral of an indicator. -/
theorem map_withDensity_measurableEquiv (μ : Measure α) (e : α ≃ᵐ β) {w : β → ℝ≥0∞}
    (hw : Measurable w) :
    (μ.withDensity fun x ↦ w (e x)).map e = (μ.map e).withDensity w := by
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs,
    lintegral_map hw e.measurable]

/-! ### Uniqueness of additive Haar measure on a right-nested triple product -/

section Haar

variable {X Y Z : Type*}
  [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X]
  [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] [LocallyCompactSpace Y]
  [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z] [LocallyCompactSpace Z]

/-- **An additive Haar measure on a right-nested triple product is a multiple of a product.**
After transport along the associativity equivalence, an additive Haar measure `lam` on `X × Y × Z`
is a positive finite multiple of the product of additive Haar measures `κ` on `X × Y` and `ν` on
`Z`.  The constant depends on the three measures and is not otherwise determined. -/
theorem exists_map_prodAssoc_symm_eq_smul_prod (lam : Measure (X × Y × Z)) [lam.IsAddHaarMeasure]
    (κ : Measure (X × Y)) [κ.IsAddHaarMeasure] (ν : Measure Z) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      lam.map (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm = c • κ.prod ν := by
  have hcont : Continuous ((AddEquiv.prodAssoc (M := X) (N := Y) (P := Z)).symm) :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  have hcont' : Continuous ((AddEquiv.prodAssoc (M := X) (N := Y) (P := Z)).symm.symm) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hHaar :
      (lam.map (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam _ hcont hcont'
  set μ := lam.map (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  refine ⟨(addHaarScalarFactor μ (κ.prod ν) : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (addHaarScalarFactor_pos_of_isAddHaarMeasure μ (κ.prod ν)).ne',
    ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact isAddLeftInvariant_eq_smul μ (κ.prod ν)

end Haar

/-! ### Restriction and weighting through the first two factors -/

section Commutation

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The set `{p | (p.1, p.2.1) ∈ t}` of a right-nested triple product, for `t` a set of the
left-nested pair, is exactly the preimage of the cylinder `t ×ˢ univ` under the associativity
equivalence.  This is the bookkeeping that makes the two commutation lemmas below apply. -/
theorem preimage_prodAssoc_symm_prod_univ (t : Set (X × Y)) :
    (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm ⁻¹' (t ×ˢ Set.univ) =
      {p : X × Y × Z | (p.1, p.2.1) ∈ t} := by
  ext p
  simp [MeasurableEquiv.prodAssoc]

/-- **Restriction through the first two factors commutes with the transport.**  If a measure `μ` on
`X × Y × Z` transports to `c • κ.prod ν`, then its restriction to a set constraining only the `X`
and `Y` coordinates transports to `c • (κ.restrict t).prod ν`. -/
theorem map_prodAssoc_symm_restrict_of_map_eq_smul {μ : Measure (X × Y × Z)} {κ : Measure (X × Y)}
    {ν : Measure Z} [SFinite κ] [SFinite ν] {c : ℝ≥0∞} {t : Set (X × Y)} (ht : MeasurableSet t)
    (h : μ.map (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm = c • κ.prod ν) :
    (μ.restrict {p : X × Y × Z | (p.1, p.2.1) ∈ t}).map
        (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm =
      c • (κ.restrict t).prod ν := by
  rw [← preimage_prodAssoc_symm_prod_univ (Z := Z) t,
    ← Measure.restrict_map (MeasurableEquiv.measurable _) (ht.prod MeasurableSet.univ), h,
    Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]

/-- **Weighting through the first two factors commutes with the transport.**  If a measure `μ` on
`X × Y × Z` transports to `c • κ.prod ν`, then weighting it by a density that reads only the `X` and
`Y` coordinates transports to `c • (κ.withDensity w).prod ν`. -/
theorem map_prodAssoc_symm_withDensity_of_map_eq_smul {μ : Measure (X × Y × Z)}
    {κ : Measure (X × Y)} {ν : Measure Z} [SFinite ν] {c : ℝ≥0∞} {w : X × Y → ℝ≥0∞}
    (hw : Measurable w)
    (h : μ.map (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm = c • κ.prod ν) :
    (μ.withDensity fun p : X × Y × Z ↦ w (p.1, p.2.1)).map
        (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm =
      c • (κ.withDensity w).prod ν := by
  have hw' : Measurable fun q : (X × Y) × Z ↦ w q.1 := hw.comp measurable_fst
  have hfun : (fun p : X × Y × Z ↦ w (p.1, p.2.1)) =
      fun p : X × Y × Z ↦ (fun q : (X × Y) × Z ↦ w q.1)
        ((MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm p) := rfl
  rw [hfun, map_withDensity_measurableEquiv μ _ hw', h, withDensity_smul_measure,
    ← prod_withDensity_left hw]

end Commutation

end MeasureTheory.Measure
