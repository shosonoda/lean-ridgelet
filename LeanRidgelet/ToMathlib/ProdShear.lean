/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Parametrized shears and rearrangements of product measures

Two elementary transports for iterated Fubini arguments, absent from Mathlib (as of the
pinned version):

* `MeasureTheory.measurePreserving_prodSwapRight`: the rearrangement
  `((a, b), c) ↦ ((a, c), b)` exchanging the two right factors of a left-nested triple
  product of s-finite measures.
* `MeasureTheory.measurePreserving_skewDivLeft` and its additive version
  `MeasureTheory.measurePreserving_skewSubLeft`: the parametrized shear
  `(w, b) ↦ (w, c w / b)` on `μ.prod ν` for a measurable parameter map `c` and an
  inversion- and left-invariant fiber measure `ν`, together with the quasi-measure-preserving
  evaluations `(w, b) ↦ c w / b` (`quasiMeasurePreserving_skewDivLeft`,
  `quasiMeasurePreserving_skewSubLeft`). The evaluation is the standard device for the joint
  measurability of kernels `(w, b) ↦ g (c w - b)` with `g` merely a.e. strongly measurable.

Candidates for upstreaming to Mathlib.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The rearrangement `((a, b), c) ↦ ((a, c), b)` exchanging the two right factors of a
left-nested triple product preserves the product measures. -/
theorem measurePreserving_prodSwapRight (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun q : (α × β) × γ => ((q.1.1, q.2), q.1.2))
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have h2 : MeasurePreserving (Prod.map (id : α → α) (Prod.swap : β × γ → γ × β))
      (μ.prod (ν.prod ρ)) (μ.prod (ρ.prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have h3' : MeasurePreserving (MeasurableEquiv.prodAssoc : (α × γ) × β ≃ᵐ α × γ × β)
      ((μ.prod ρ).prod ν) (μ.prod (ρ.prod ν)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have h3 := MeasurePreserving.symm _ h3'
  exact (h3.comp (h2.comp h1) :)

variable {G : Type*} [MeasurableSpace G]

/-- The parametrized shear `(w, b) ↦ (w, c w / b)` preserves the product with an inversion-
and left-invariant fiber measure. -/
@[to_additive
  /-- The parametrized shear `(w, b) ↦ (w, c w - b)` preserves the product with a negation-
  and left-invariant fiber measure. -/]
theorem measurePreserving_skewDivLeft [Group G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure α) (ν : Measure G) [SFinite μ] [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] {c : α → G} (hc : Measurable c) :
    MeasurePreserving (fun q : α × G => (q.1, c q.1 / q.2)) (μ.prod ν) (μ.prod ν) := by
  refine MeasurePreserving.skew_product (μc := ν) (μd := ν)
    (g := fun w b => c w / b) (MeasurePreserving.id μ) ?_ ?_
  · change Measurable fun q : α × G => c q.1 / q.2
    simp only [div_eq_mul_inv]
    exact (hc.comp measurable_fst).mul measurable_snd.inv
  · exact Filter.Eventually.of_forall fun w =>
      (Measure.measurePreserving_div_left ν (c w)).map_eq

/-- The parametrized evaluation `(w, b) ↦ c w / b` is quasi-measure-preserving from a product
with an inversion- and left-invariant fiber measure to the fiber. This is the standard device
for the joint measurability of kernels `(w, b) ↦ g (c w / b)` with `g` merely a.e. strongly
measurable. -/
@[to_additive
  /-- The parametrized evaluation `(w, b) ↦ c w - b` is quasi-measure-preserving from a
  product with a negation- and left-invariant fiber measure to the fiber. This is the standard
  device for the joint measurability of kernels `(w, b) ↦ g (c w - b)` with `g` merely a.e.
  strongly measurable. -/]
theorem quasiMeasurePreserving_skewDivLeft [Group G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure α) (ν : Measure G) [SFinite μ] [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] {c : α → G} (hc : Measurable c) :
    Measure.QuasiMeasurePreserving (fun q : α × G => c q.1 / q.2) (μ.prod ν) ν :=
  Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_skewDivLeft μ ν hc).quasiMeasurePreserving

/-- The parametrized shear `(w, b) ↦ (w, b / c w)` preserves the product with a
right-invariant fiber measure. -/
@[to_additive
  /-- The parametrized shear `(w, b) ↦ (w, b - c w)` preserves the product with a
  right-invariant fiber measure. -/]
theorem measurePreserving_skewDivRight [Group G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure α) (ν : Measure G) [SFinite μ] [SFinite ν]
    [ν.IsMulRightInvariant] {c : α → G} (hc : Measurable c) :
    MeasurePreserving (fun q : α × G => (q.1, q.2 / c q.1)) (μ.prod ν) (μ.prod ν) := by
  refine MeasurePreserving.skew_product (μc := ν) (μd := ν)
    (g := fun w b => b / c w) (MeasurePreserving.id μ) ?_ ?_
  · change Measurable fun q : α × G => q.2 / c q.1
    simp only [div_eq_mul_inv]
    exact measurable_snd.mul (hc.comp measurable_fst).inv
  · exact Filter.Eventually.of_forall fun w =>
      (measurePreserving_div_right ν (c w)).map_eq

/-- The parametrized evaluation `(w, b) ↦ b / c w` is quasi-measure-preserving from a product
with a right-invariant fiber measure to the fiber. -/
@[to_additive
  /-- The parametrized evaluation `(w, b) ↦ b - c w` is quasi-measure-preserving from a
  product with a right-invariant fiber measure to the fiber. -/]
theorem quasiMeasurePreserving_skewDivRight [Group G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure α) (ν : Measure G) [SFinite μ] [SFinite ν]
    [ν.IsMulRightInvariant] {c : α → G} (hc : Measurable c) :
    Measure.QuasiMeasurePreserving (fun q : α × G => q.2 / c q.1) (μ.prod ν) ν :=
  Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_skewDivRight μ ν hc).quasiMeasurePreserving

end MeasureTheory
