/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import LeanRidgelet.HA.AffineFrequency
public import LeanRidgelet.ToMathlib.LpFunctor
public import LeanRidgelet.ToMathlib.LieGroup.PolishUnits

/-!
# Measures for the affine Mackey model

This file constructs the intrinsic measure on the conull nonzero dual orbit, transports it to
the affine homogeneous quotient, and proves the constant Radon--Nikodym formulas needed by the
quasi-regular L2 representation. It contains no choice of section and no irreducibility claim.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContRepresentation ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The homogeneous left-coset space of the full affine group by the Mackey inducing subgroup at
the frequency `xi`. -/
abbrev AffineTopologicalMackeyQuotient (xi : E) :=
  AffineEquiv.TopologicalSemidirectProduct E ⧸
    (affineTopologicalMackeySubgroup xi).toSubgroup

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The unique nonzero dual orbit is a measurable open subset of frequency space. -/
theorem measurableSet_affineDualOrbit : MeasurableSet (affineDualOrbit (E := E)) := by
  exact (isClosed_singleton : IsClosed ({0} : Set E)).isOpen_compl.measurableSet

/-- The intrinsic measure on the nonzero-frequency subtype, obtained by pulling Lebesgue measure
back along the subtype inclusion. -/
noncomputable def affineDualOrbitSubtypeMeasure : Measure (affineDualOrbit (E := E)) :=
  Measure.comap Subtype.val (volume : Measure E)

/-- The intrinsic orbit measure is finite on compact sets.  This is the measure-theoretic input
needed to send compactly supported continuous orbit sections to `L²`. -/
noncomputable instance instIsFiniteMeasureOnCompactsAffineDualOrbitSubtypeMeasure :
    IsFiniteMeasureOnCompacts (affineDualOrbitSubtypeMeasure (E := E)) := by
  rw [affineDualOrbitSubtypeMeasure]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure E) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit)

/-- The intrinsic orbit measure is positive on nonempty open sets, because the orbit is an open
subset of frequency space and Lebesgue measure is positive on nonempty open sets.  This is what
makes a continuous section that vanishes almost everywhere vanish identically. -/
noncomputable instance instIsOpenPosMeasureAffineDualOrbitSubtypeMeasure :
    (affineDualOrbitSubtypeMeasure (E := E)).IsOpenPosMeasure := by
  rw [affineDualOrbitSubtypeMeasure]
  exact Measure.IsOpenPosMeasure.comap (volume : Measure E)
    ((isClosed_singleton : IsClosed ({0} : Set E)).isOpen_compl.isOpenEmbedding_subtypeVal)

/-- Lebesgue measure restricted to the unique nonzero orbit of the affine dual action.  Keeping
the ambient carrier `E` makes the null complement explicit while avoiding any choice of a
measurable quotient model. -/
noncomputable def affineDualOrbitMeasure : Measure E :=
  (volume : Measure E).restrict (affineDualOrbit (E := E))

/-- The restricted orbit measure is Lebesgue measure because the missing zero orbit is null. -/
theorem affineDualOrbitMeasure_eq_volume :
    affineDualOrbitMeasure (E := E) = (volume : Measure E) := by
  exact Measure.restrict_eq_self_of_ae_mem <|
    Filter.eventuallyEq_univ.mp (affineDualOrbit_ae_eq_univ (volume : Measure E))

/-- Pushing the intrinsic orbit measure into the ambient frequency space recovers Lebesgue
measure, not merely its restriction, because the orbit is conull. -/
theorem affineDualOrbitSubtypeMeasure_map_subtypeVal :
    (affineDualOrbitSubtypeMeasure (E := E)).map Subtype.val = (volume : Measure E) := by
  rw [affineDualOrbitSubtypeMeasure, map_comap_subtype_coe measurableSet_affineDualOrbit]
  exact affineDualOrbitMeasure_eq_volume

/-- The constant Radon--Nikodym density of the inverse dual action, written in the topological
semidirect-product coordinates used by Mackey theory. -/
def affineTopologicalDualJacobian
    (g : AffineEquiv.TopologicalSemidirectProduct E) : ℝ≥0 :=
  affineDualJacobian (AffineEquiv.topologicalSemidirectProductEquiv E g) 0

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The dual density is the inverse of the data-side affine density. -/
@[simp]
theorem affineTopologicalDualJacobian_eq_inv
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalDualJacobian g = (affineTopologicalJacobian g)⁻¹ := rfl

omit [Nontrivial E] in
/-- Each affine group element acts measurably on the intrinsic nonzero dual orbit. -/
theorem measurable_affineTopologicalDualOrbit_smul
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
        (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
    Measurable fun eta : affineDualOrbit (E := E) ↦ g • eta := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  letI : ContinuousSMul (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbit_continuousSMul
  exact (continuous_const_smul g).measurable

/-- The intrinsic orbit measure is strongly quasi-invariant under the dual affine action, with
the same constant density as ambient Lebesgue measure. -/
theorem affineDualOrbitSubtypeMeasure_map_inv_smul
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
        (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
    (affineDualOrbitSubtypeMeasure (E := E)).map (fun eta ↦ g⁻¹ • eta) =
      (affineTopologicalDualJacobian g : ℝ≥0∞) •
        affineDualOrbitSubtypeMeasure (E := E) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  apply (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_affineTopologicalDualOrbit_smul g⁻¹)]
  rw [Measure.map_smul]
  rw [affineDualOrbitSubtypeMeasure_map_subtypeVal]
  have hfun :
      (Subtype.val ∘ fun eta : affineDualOrbit (E := E) ↦ g⁻¹ • eta) =
        affineDualAction (AffineEquiv.topologicalSemidirectProductEquiv E g)⁻¹ ∘
          Subtype.val := by
    funext eta
    change affineTopologicalDualAction (g⁻¹).right eta.1 = _
    simp only [SemidirectProduct.inv_right, affineTopologicalDualAction_eq_linearEquiv]
    rfl
  rw [hfun, ← Measure.map_map
    (affineDualAction_measurable
      (AffineEquiv.topologicalSemidirectProductEquiv E g)⁻¹)
    measurable_subtype_coe]
  rw [affineDualOrbitSubtypeMeasure_map_subtypeVal]
  rw [affineDualAction_map_eq_withDensity]
  have hj :
      (fun z : E ↦
        (affineDualJacobian
          (AffineEquiv.topologicalSemidirectProductEquiv E g) z : ℝ≥0∞)) =
      fun _ ↦ (affineTopologicalDualJacobian g : ℝ≥0∞) := rfl
  rw [hj, withDensity_const]

/-- Inverse dual translation is quasi-measure-preserving on the intrinsic nonzero orbit. -/
theorem affineDualOrbitSubtype_quasiMeasurePreserving
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
        (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
    Measure.QuasiMeasurePreserving (fun eta : affineDualOrbit (E := E) ↦ g⁻¹ • eta)
      (affineDualOrbitSubtypeMeasure (E := E))
      (affineDualOrbitSubtypeMeasure (E := E)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  refine ⟨measurable_affineTopologicalDualOrbit_smul g⁻¹, ?_⟩
  rw [affineDualOrbitSubtypeMeasure_map_inv_smul g]
  exact Measure.AbsolutelyContinuous.rfl.smul_left _

/-- The inclusion of the intrinsic nonzero orbit into frequency space is measure preserving. -/
theorem affineDualOrbitSubtype_measurePreserving :
    MeasurePreserving (Subtype.val : affineDualOrbit (E := E) → E)
      (affineDualOrbitSubtypeMeasure (E := E)) (volume : Measure E) :=
  ⟨measurable_subtype_coe, affineDualOrbitSubtypeMeasure_map_subtypeVal⟩

/-- Restriction of a full-frequency `L²` class to the intrinsic nonzero orbit, as a linear
isometry supplied by Mathlib's measure-preserving composition API. -/
noncomputable def affineDualOrbitRestrictionLpLinearIsometry :
    Lp ℂ 2 (volume : Measure E) →ₗᵢ[ℂ]
      Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) :=
  Lp.compMeasurePreservingₗᵢ ℂ Subtype.val affineDualOrbitSubtype_measurePreserving

/-- The intrinsic restriction isometry is represented by ordinary restriction to nonzero
frequencies. -/
theorem affineDualOrbitRestrictionLpLinearIsometry_apply_ae
    (f : Lp ℂ 2 (volume : Measure E)) :
    (affineDualOrbitRestrictionLpLinearIsometry (E := E) f :
      Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) =ᵐ[
        affineDualOrbitSubtypeMeasure (E := E)] fun xi ↦ f xi.1 := by
  exact Lp.coeFn_compMeasurePreserving f affineDualOrbitSubtype_measurePreserving

/-- Restriction to the conull nonzero orbit is onto: an intrinsic orbit class is extended by zero
at the missing frequency. -/
theorem affineDualOrbitRestrictionLpLinearIsometry_surjective :
    Function.Surjective (affineDualOrbitRestrictionLpLinearIsometry (E := E)) := by
  intro g
  let f : E → ℂ := Function.extend Subtype.val (g : affineDualOrbit (E := E) → ℂ) 0
  have hfStronglyMeasurable : StronglyMeasurable f :=
    (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit).stronglyMeasurable_extend
      (Lp.stronglyMeasurable g) stronglyMeasurable_const
  have hcomp : f ∘ (Subtype.val : affineDualOrbit (E := E) → E) = g := by
    funext xi
    exact (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit).injective.extend_apply
      (g : affineDualOrbit (E := E) → ℂ) 0 xi
  have hnorm := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    hfStronglyMeasurable.aestronglyMeasurable affineDualOrbitSubtype_measurePreserving
  rw [hcomp] at hnorm
  have hf : MemLp f 2 (volume : Measure E) :=
    ⟨hfStronglyMeasurable.aestronglyMeasurable, by
      rw [← hnorm]
      exact Lp.eLpNorm_lt_top g⟩
  refine ⟨hf.toLp f, ?_⟩
  change Lp.compMeasurePreserving Subtype.val affineDualOrbitSubtype_measurePreserving
    (hf.toLp f) = g
  rw [Lp.toLp_compMeasurePreserving hf affineDualOrbitSubtype_measurePreserving]
  exact (MemLp.toLp_congr
    (hf.comp_measurePreserving affineDualOrbitSubtype_measurePreserving) (Lp.memLp g)
    (Filter.Eventually.of_forall fun xi ↦ congrFun hcomp xi)).trans
      (Lp.toLp_coeFn g (Lp.memLp g))

/-- The full frequency `L²` space and the intrinsic `L²` space on the nonzero-frequency subtype
are canonically linearly isometric. -/
noncomputable def affineDualOrbitSubtypeLpEquiv :
    Lp ℂ 2 (volume : Measure E) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) :=
  LinearIsometryEquiv.ofSurjective (affineDualOrbitRestrictionLpLinearIsometry (E := E))
    affineDualOrbitRestrictionLpLinearIsometry_surjective

@[simp]
theorem affineDualOrbitSubtypeLpEquiv_apply (f : Lp ℂ 2 (volume : Measure E)) :
    affineDualOrbitSubtypeLpEquiv (E := E) f =
      affineDualOrbitRestrictionLpLinearIsometry (E := E) f := rfl

/-- The inverse intrinsic-orbit equivalence agrees almost everywhere with the original full-space
class on the conull nonzero subtype. -/
theorem affineDualOrbitSubtypeLpEquiv_symm_apply_ae
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    (fun eta : affineDualOrbit (E := E) ↦
      ((affineDualOrbitSubtypeLpEquiv (E := E)).symm f :
        Lp ℂ 2 (volume : Measure E)) eta.1) =ᵐ[
          affineDualOrbitSubtypeMeasure (E := E)] f := by
  have h := affineDualOrbitRestrictionLpLinearIsometry_apply_ae
    ((affineDualOrbitSubtypeLpEquiv (E := E)).symm f)
  rw [← affineDualOrbitSubtypeLpEquiv_apply] at h
  rw [(affineDualOrbitSubtypeLpEquiv (E := E)).apply_symm_apply] at h
  exact h.symm

/-- The measure on the affine homogeneous space obtained by transporting the intrinsic Lebesgue
measure of the nonzero dual orbit through the quotient-orbit homeomorphism. -/
noncomputable def affineTopologicalMackeyQuotientMeasure {xi : E} (hxi : xi ≠ 0) :
    Measure (AffineTopologicalMackeyQuotient xi) :=
  (affineDualOrbitSubtypeMeasure (E := E)).map
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm

/-- The transported homogeneous-space measure is finite on compact sets. -/
noncomputable instance instIsFiniteMeasureOnCompactsAffineTopologicalMackeyQuotientMeasure
    {xi : E} (hxi : xi ≠ 0) :
    IsFiniteMeasureOnCompacts (affineTopologicalMackeyQuotientMeasure hxi) := by
  rw [affineTopologicalMackeyQuotientMeasure]
  exact Measure.IsFiniteMeasureOnCompacts.map (affineDualOrbitSubtypeMeasure (E := E))
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm

/-- The transported homogeneous-space measure is regular. -/
noncomputable instance instRegularAffineTopologicalMackeyQuotientMeasure
    {xi : E} (hxi : xi ≠ 0) :
    Measure.Regular (affineTopologicalMackeyQuotientMeasure hxi) :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure
    (affineTopologicalMackeyQuotientMeasure hxi)

/-- The transported homogeneous-space measure is positive on nonempty open sets, since the
quotient-orbit homeomorphism is a surjective continuous map. -/
noncomputable instance instIsOpenPosMeasureAffineTopologicalMackeyQuotientMeasure
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeyQuotientMeasure hxi).IsOpenPosMeasure := by
  rw [affineTopologicalMackeyQuotientMeasure]
  exact Continuous.isOpenPosMeasure_map
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm.continuous
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm.surjective

omit [Nontrivial E] in
/-- The quotient-orbit homeomorphism preserves the transported homogeneous-space measure. -/
theorem affineTopologicalMackeyQuotient_measurePreserving {xi : E} (hxi : xi ≠ 0) :
    MeasurePreserving (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi)
      (affineTopologicalMackeyQuotientMeasure hxi)
      (affineDualOrbitSubtypeMeasure (E := E)) := by
  refine ⟨Continuous.measurable
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).continuous, ?_⟩
  exact MeasurableEquiv.map_map_symm
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).toMeasurableEquiv

omit [Nontrivial E] in
/-- The inverse quotient-orbit homeomorphism is also measure preserving. -/
theorem affineTopologicalMackeyQuotient_symm_measurePreserving {xi : E} (hxi : xi ≠ 0) :
    MeasurePreserving (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm
      (affineDualOrbitSubtypeMeasure (E := E))
      (affineTopologicalMackeyQuotientMeasure hxi) := by
  refine ⟨Continuous.measurable
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm.continuous, ?_⟩
  rfl

/-- The Radon--Nikodym cocycle for the transported measure on the affine homogeneous space.  It
is constant on the quotient because the dual action has constant determinant density. -/
def affineTopologicalMackeyQuotientJacobian {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (_ : AffineTopologicalMackeyQuotient xi) : ℝ≥0 :=
  affineTopologicalDualJacobian g

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Left translation on the affine homogeneous quotient is measurable. -/
theorem measurable_affineTopologicalMackeyQuotient_smul {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    Measurable fun q : AffineTopologicalMackeyQuotient xi ↦ g • q :=
  measurable_const_smul g

/-- The quotient-orbit homeomorphism transports the constant-density quasi-invariance of the
intrinsic orbit measure to the homogeneous space. -/
theorem affineTopologicalMackeyQuotientMeasure_map_inv_smul {xi : E}
    (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E) :
    (affineTopologicalMackeyQuotientMeasure hxi).map (fun q ↦ g⁻¹ • q) =
      (affineTopologicalDualJacobian g : ℝ≥0∞) •
        affineTopologicalMackeyQuotientMeasure hxi := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  let e := affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi
  let ee := e.toMeasurableEquiv
  apply ee.measurableEmbedding.map_injective
  rw [Measure.map_map ee.measurable
    (measurable_affineTopologicalMackeyQuotient_smul g⁻¹)]
  rw [Measure.map_smul]
  have hfun : ee ∘ (fun q ↦ g⁻¹ • q) = (fun eta ↦ g⁻¹ • eta) ∘ ee := by
    funext q
    exact affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul hxi g⁻¹ q
  rw [hfun, ← Measure.map_map
    (measurable_affineTopologicalDualOrbit_smul g⁻¹) ee.measurable]
  have hemap :
      (affineTopologicalMackeyQuotientMeasure hxi).map ee =
        affineDualOrbitSubtypeMeasure (E := E) := by
    exact (affineTopologicalMackeyQuotient_measurePreserving hxi).map_eq
  rw [hemap]
  rw [affineDualOrbitSubtypeMeasure_map_inv_smul g]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The homogeneous-space Jacobian is measurable. -/
theorem affineTopologicalMackeyQuotientJacobian_measurable {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    Measurable (affineTopologicalMackeyQuotientJacobian (xi := xi) g) :=
  measurable_const

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The homogeneous-space Jacobian is everywhere nonzero. -/
theorem affineTopologicalMackeyQuotientJacobian_ne_zero {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientJacobian g q ≠ 0 := by
  exact affineDualJacobian_ne_zero
    (AffineEquiv.topologicalSemidirectProductEquiv E g) 0

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The homogeneous-space Jacobian at the identity is one. -/
@[simp]
theorem affineTopologicalMackeyQuotientJacobian_one {xi : E}
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientJacobian
      (1 : AffineEquiv.TopologicalSemidirectProduct E) q = 1 := by
  simp [affineTopologicalMackeyQuotientJacobian, affineTopologicalDualJacobian]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The homogeneous-space density satisfies the Radon--Nikodym cocycle law. -/
theorem affineTopologicalMackeyQuotientJacobian_cocycle {xi : E}
    (g h : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientJacobian (g * h) q =
      affineTopologicalMackeyQuotientJacobian g (h • q) *
        affineTopologicalMackeyQuotientJacobian h q := by
  simpa [affineTopologicalMackeyQuotientJacobian, affineTopologicalDualJacobian,
    affineDualJacobian] using affineDualJacobian_cocycle
      (AffineEquiv.topologicalSemidirectProductEquiv E g)
      (AffineEquiv.topologicalSemidirectProductEquiv E h) 0

/-- Strong quasi-invariance of the homogeneous-space measure, in the `withDensity` form consumed
by the general quasi-invariant `L²` construction. -/
theorem affineTopologicalMackeyQuotientMeasure_map_eq_withDensity {xi : E}
    (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E) :
    (affineTopologicalMackeyQuotientMeasure hxi).map (fun q ↦ g⁻¹ • q) =
      (affineTopologicalMackeyQuotientMeasure hxi).withDensity
        fun q ↦ (affineTopologicalMackeyQuotientJacobian g q : ℝ≥0∞) := by
  rw [affineTopologicalMackeyQuotientMeasure_map_inv_smul hxi g]
  have hj :
      (fun q : AffineTopologicalMackeyQuotient xi ↦
        (affineTopologicalMackeyQuotientJacobian g q : ℝ≥0∞)) =
      fun _ ↦ (affineTopologicalDualJacobian g : ℝ≥0∞) := rfl
  rw [hj, withDensity_const]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Folland's Radon--Nikodym correction on the homogeneous quotient is the positive square root
of the data-side affine determinant. -/
theorem affineTopologicalMackeyQuotientRadonNikodymWeight {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    radonNikodymWeight
        (affineTopologicalMackeyQuotientJacobian (xi := xi)) g q =
      ((affineTopologicalJacobian g).sqrt : ℂ) := by
  simp only [radonNikodymWeight_apply, affineTopologicalMackeyQuotientJacobian,
    affineTopologicalDualJacobian]
  rw [show affineDualJacobian
      (AffineEquiv.topologicalSemidirectProductEquiv E g) 0 =
        (affineTopologicalJacobian g)⁻¹ by rfl]
  simp [NNReal.sqrt_inv]

end LeanRidgelet
