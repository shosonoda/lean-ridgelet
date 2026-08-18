/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import LeanRidgelet.HA.AffineMackeyInduction
public import LeanRidgelet.HA.AffineMackeySmoothing
public import LeanRidgelet.ToMathlib.BochnerIntegralL2
public import LeanRidgelet.ToMathlib.FourierCharacterMultiplier
public import LeanRidgelet.ToMathlib.LpCompactlySupportedMultiplier
public import LeanRidgelet.ToMathlib.LieGroup.GroupConvolution
public import LeanRidgelet.ToMathlib.LieGroup.HaarApproximateIdentity
public import LeanRidgelet.ToMathlib.LieGroup.Schur

/-!
# Intertwiners and irreducibility for the affine Mackey model

This terminal module transports the explicit Fourier representation through the intrinsic orbit
and homogeneous quotient L2 spaces, bundles inverse bounded intertwiners, and isolates the exact
translation-spectral and imprimitivity-commutant steps in affine irreducibility. The
translation-spectral step, the operator-theoretic remainder of Folland 6.28, and the
extreme-subspace part of the Folland 6.30 inducing-fiber correspondence are complete, and so is
Folland 6.29: the Haar-smoothed vector is identified almost everywhere with the pointwise
compact-kernel group convolution of the measurable induced-model lift, which is continuous, and the
compact cutoff and regular-section density argument that follows is proved here. The article
endpoint carries no analytic input.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra CompactlySupported ContRepresentation ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Pullback through the quotient-orbit homeomorphism as a linear isometry from orbit `L²` to
homogeneous-space `L²`. -/
noncomputable def affineTopologicalMackeyQuotientLpLinearIsometry {xi : E} (hxi : xi ≠ 0) :
    Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) →ₗᵢ[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi)
    (affineTopologicalMackeyQuotient_measurePreserving hxi)

omit [Nontrivial E] in
/-- The homogeneous-space pullback is represented almost everywhere by composition with the
quotient-orbit homeomorphism. -/
theorem affineTopologicalMackeyQuotientLpLinearIsometry_apply_ae {xi : E} (hxi : xi ≠ 0)
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    (affineTopologicalMackeyQuotientLpLinearIsometry hxi f :
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =ᵐ[
        affineTopologicalMackeyQuotientMeasure hxi]
      f ∘ affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi := by
  exact Lp.coeFn_compMeasurePreserving f
    (affineTopologicalMackeyQuotient_measurePreserving hxi)

omit [Nontrivial E] in
/-- Pullback through the quotient-orbit homeomorphism is onto; its inverse is pullback through the
inverse homeomorphism. -/
theorem affineTopologicalMackeyQuotientLpLinearIsometry_surjective {xi : E} (hxi : xi ≠ 0) :
    Function.Surjective (affineTopologicalMackeyQuotientLpLinearIsometry hxi) := by
  intro g
  let e := affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi
  let f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) :=
    Lp.compMeasurePreserving e.symm
      (affineTopologicalMackeyQuotient_symm_measurePreserving hxi) g
  refine ⟨f, ?_⟩
  change Lp.compMeasurePreserving e
      (affineTopologicalMackeyQuotient_measurePreserving hxi)
      (Lp.compMeasurePreserving e.symm
        (affineTopologicalMackeyQuotient_symm_measurePreserving hxi) g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g
    (affineTopologicalMackeyQuotient_symm_measurePreserving hxi)
    (affineTopologicalMackeyQuotient_measurePreserving hxi)]
  have he :
      (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm ∘
          affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi = id := by
    funext q
    exact e.symm_apply_apply q
  simpa only [he] using Lp.compMeasurePreserving_id_apply g

/-- The intrinsic orbit `L²` space and the homogeneous quotient `L²` space are canonically
linearly isometric. -/
noncomputable def affineTopologicalMackeyQuotientLpEquiv {xi : E} (hxi : xi ≠ 0) :
    Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  LinearIsometryEquiv.ofSurjective
    (affineTopologicalMackeyQuotientLpLinearIsometry hxi)
    (affineTopologicalMackeyQuotientLpLinearIsometry_surjective hxi)

omit [Nontrivial E] in
@[simp]
theorem affineTopologicalMackeyQuotientLpEquiv_apply {xi : E} (hxi : xi ≠ 0)
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    affineTopologicalMackeyQuotientLpEquiv hxi f =
      affineTopologicalMackeyQuotientLpLinearIsometry hxi f := rfl

omit [Nontrivial E] in
/-- The inverse homogeneous-space equivalence is represented by pullback through the inverse
quotient-orbit homeomorphism. -/
theorem affineTopologicalMackeyQuotientLpEquiv_symm_apply_ae {xi : E} (hxi : xi ≠ 0)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((affineTopologicalMackeyQuotientLpEquiv hxi).symm f :
      Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) =ᵐ[
        affineDualOrbitSubtypeMeasure (E := E)]
      f ∘ (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm := by
  let e := affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi
  let k : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) :=
    Lp.compMeasurePreserving e.symm
      (affineTopologicalMackeyQuotient_symm_measurePreserving hxi) f
  have hk : affineTopologicalMackeyQuotientLpEquiv hxi k = f := by
    change Lp.compMeasurePreserving e
      (affineTopologicalMackeyQuotient_measurePreserving hxi)
      (Lp.compMeasurePreserving e.symm
        (affineTopologicalMackeyQuotient_symm_measurePreserving hxi) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (affineTopologicalMackeyQuotient_symm_measurePreserving hxi)
      (affineTopologicalMackeyQuotient_measurePreserving hxi)]
    have he :
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).symm ∘
          affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi = id := by
      funext q
      exact e.symm_apply_apply q
    simpa only [he] using Lp.compMeasurePreserving_id_apply f
  have hksymm : (affineTopologicalMackeyQuotientLpEquiv hxi).symm f = k := by
    apply (affineTopologicalMackeyQuotientLpEquiv hxi).injective
    rw [(affineTopologicalMackeyQuotientLpEquiv hxi).apply_symm_apply, hk]
  rw [hksymm]
  exact Lp.coeFn_compMeasurePreserving f
    (affineTopologicalMackeyQuotient_symm_measurePreserving hxi)

/-- The canonical `L²` identification between the full frequency space and its conull nonzero
orbit model. -/
noncomputable def affineDualOrbitLpEquiv :
    Lp ℂ 2 (volume : Measure E) ≃ₗᵢ[ℂ] Lp ℂ 2 (affineDualOrbitMeasure (E := E)) := by
  rw [affineDualOrbitMeasure_eq_volume]
  exact LinearIsometryEquiv.refl ℂ _

/-- The explicit Fourier-side affine representation transported to the intrinsic `L²` space on
the nonzero-frequency subtype. -/
noncomputable def affineTopologicalOrbitLpUnitaryRepresentation :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :=
  (affineTopologicalFourierLpUnitaryRepresentation (E := E)).conjugate
    (affineDualOrbitSubtypeLpEquiv (E := E))

/-- The transported intrinsic-orbit representation retains the explicit
character-times-determinant-corrected dual pullback formula. -/
theorem affineTopologicalOrbitLpUnitaryRepresentation_apply_ae
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
        (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
    ((↑(affineTopologicalOrbitLpUnitaryRepresentation (E := E) g) :
        Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) →L[ℂ]
          Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) f) =ᵐ[
            affineDualOrbitSubtypeMeasure (E := E)]
      fun eta ↦ affineFrequencyPhase
          (AffineEquiv.topologicalSemidirectProductEquiv E g) eta.1 *
        (((affineTopologicalJacobian g).sqrt : ℂ) * f (g⁻¹ • eta)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  let e := affineDualOrbitSubtypeLpEquiv (E := E)
  let k := e.symm f
  let u := Unitary.linearIsometryEquiv
    (affineTopologicalFourierLpUnitaryRepresentation (E := E) g) k
  have hout := affineDualOrbitRestrictionLpLinearIsometry_apply_ae u
  have hout' :
      ((↑(affineTopologicalOrbitLpUnitaryRepresentation (E := E) g) :
          Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E)) →L[ℂ]
            Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) f) =ᵐ[
              affineDualOrbitSubtypeMeasure (E := E)] fun eta ↦ u eta.1 := by
    exact hout
  have hfull := affineFourierLpUnitaryRepresentation_apply_ae
    (AffineEquiv.topologicalSemidirectProductEquiv E g) k
  have hfull' := affineDualOrbitSubtype_measurePreserving.quasiMeasurePreserving.ae_eq hfull
  have hk := (affineDualOrbitSubtype_quasiMeasurePreserving g).ae_eq
    (affineDualOrbitSubtypeLpEquiv_symm_apply_ae f)
  filter_upwards [hout', hfull', hk] with eta houteta hfulleta hketa
  rw [houteta]
  change
    (Unitary.linearIsometryEquiv
      (affineFourierLpUnitaryRepresentation
        (AffineEquiv.topologicalSemidirectProductEquiv E g)) k) eta.1 = _
  simp only [Function.comp_apply] at hfulleta hketa
  rw [hfulleta]
  change k
      ((AffineEquiv.topologicalSemidirectProductEquiv E g).linear.adjoint eta.1) =
    f (g⁻¹ • eta) at hketa
  rw [hketa]
  rfl

/-- The explicit affine representation in its homogeneous-space `L²(G/H)` model.  It is
transported through the quotient-orbit homeomorphism, so no representative or measurable section
of `G/H` is chosen. -/
noncomputable def affineTopologicalMackeyQuotientLpUnitaryRepresentation {xi : E}
    (hxi : xi ≠ 0) :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :=
  (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).conjugate
    (affineTopologicalMackeyQuotientLpEquiv hxi)

/-- The independently transported homogeneous-space representation has the same explicit action
as the character-twisted quasi-regular construction. -/
theorem affineTopologicalMackeyQuotientLpUnitaryRepresentation_apply_ae
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi g) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ affineTopologicalMackeyQuotientPhase hxi g q *
        (((affineTopologicalJacobian g).sqrt : ℂ) * f (g⁻¹ • q)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  let e := affineTopologicalMackeyQuotientLpEquiv hxi
  let k := e.symm f
  let u := Unitary.linearIsometryEquiv
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E) g) k
  have hout := affineTopologicalMackeyQuotientLpLinearIsometry_apply_ae hxi u
  have hout' :
      ((↑(affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi g) :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
              affineTopologicalMackeyQuotientMeasure hxi]
        fun q ↦ u (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q) := by
    exact hout
  have horbit := affineTopologicalOrbitLpUnitaryRepresentation_apply_ae g k
  have horbit0 :
      (Unitary.linearIsometryEquiv
        (affineTopologicalOrbitLpUnitaryRepresentation (E := E) g) k :
          Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) =ᵐ[
            affineDualOrbitSubtypeMeasure (E := E)]
        fun eta ↦ affineFrequencyPhase
            (AffineEquiv.topologicalSemidirectProductEquiv E g) eta.1 *
          (((affineTopologicalJacobian g).sqrt : ℂ) * k (g⁻¹ • eta)) := by
    exact horbit
  have horbit' :=
    (affineTopologicalMackeyQuotient_measurePreserving hxi).quasiMeasurePreserving.ae_eq
      horbit0
  have hk := affineTopologicalMackeyQuotientLpEquiv_symm_apply_ae hxi f
  have hk' :=
    (affineTopologicalMackeyQuotient_measurePreserving hxi).quasiMeasurePreserving.ae_eq hk
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi) g
  have hk'' := hqmp.ae_eq hk'
  filter_upwards [hout', horbit', hk''] with q houtq horbitq hkq
  rw [houtq]
  simp only [Function.comp_apply] at horbitq hkq
  change
    (Unitary.linearIsometryEquiv
      (affineTopologicalOrbitLpUnitaryRepresentation (E := E) g) k)
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q) = _
  rw [horbitq]
  rw [affineTopologicalMackeyQuotientPhase]
  have he := affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul hxi g⁻¹ q
  rw [← he]
  change k (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi (g⁻¹ • q)) = _ at hkq
  have hkq' : k (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi (g⁻¹ • q)) =
      f (g⁻¹ • q) := by
    simpa only [Homeomorph.symm_apply_apply] using hkq
  rw [hkq']

/-- The character-twisted quasi-regular representation is exactly the homogeneous-space model
obtained independently by transporting the explicit Fourier representation. -/
theorem
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_eq_transported
    {xi : E} (hxi : xi ≠ 0) :
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation hxi =
      affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi := by
  ext g f
  have htwisted :=
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_apply_ae_explicit
      hxi g f
  have htransported := affineTopologicalMackeyQuotientLpUnitaryRepresentation_apply_ae hxi g f
  exact htwisted.trans htransported.symm

/-- The normalized-section induced model is exactly the independently transported Fourier
representation on the homogeneous quotient. -/
theorem affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_transported
    {xi : E} (hxi : xi ≠ 0) :
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi =
      affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi :=
  (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_quotient hxi).trans
    (affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_eq_transported hxi)

/-- The full frequency-space/orbit-space identification as a bounded intertwiner. -/
noncomputable def affineDualOrbitIntertwiningMap :
    (affineTopologicalFourierLpUnitaryRepresentation (E := E)).toContRepresentation →ⁱL
      (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).toContRepresentation :=
  UnitaryRepresentation.conjugateIntertwiningMap
    (affineTopologicalFourierLpUnitaryRepresentation (E := E))
    (affineDualOrbitSubtypeLpEquiv (E := E))

/-- The inverse orbit/full-frequency identification as a bounded intertwiner. -/
noncomputable def affineDualOrbitInverseIntertwiningMap :
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).toContRepresentation →ⁱL
      (affineTopologicalFourierLpUnitaryRepresentation (E := E)).toContRepresentation :=
  UnitaryRepresentation.conjugateInverseIntertwiningMap
    (affineTopologicalFourierLpUnitaryRepresentation (E := E))
    (affineDualOrbitSubtypeLpEquiv (E := E))

/-- The orbit/homogeneous-space identification as a bounded intertwiner. -/
noncomputable def affineTopologicalMackeyQuotientIntertwiningMap {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).toContRepresentation →ⁱL
      (affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi).toContRepresentation :=
  UnitaryRepresentation.conjugateIntertwiningMap
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E))
    (affineTopologicalMackeyQuotientLpEquiv hxi)

/-- The inverse homogeneous-space/orbit identification as a bounded intertwiner. -/
noncomputable def affineTopologicalMackeyQuotientInverseIntertwiningMap {xi : E}
    (hxi : xi ≠ 0) :
    (affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi).toContRepresentation →ⁱL
      (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).toContRepresentation :=
  UnitaryRepresentation.conjugateInverseIntertwiningMap
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E))
    (affineTopologicalMackeyQuotientLpEquiv hxi)

@[simp]
theorem affineDualOrbitIntertwiningMap_apply (f : Lp ℂ 2 (volume : Measure E)) :
    affineDualOrbitIntertwiningMap (E := E) f =
      affineDualOrbitSubtypeLpEquiv (E := E) f := rfl

@[simp]
theorem affineDualOrbitInverseIntertwiningMap_apply
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    affineDualOrbitInverseIntertwiningMap (E := E) f =
      (affineDualOrbitSubtypeLpEquiv (E := E)).symm f := rfl

@[simp]
theorem affineTopologicalMackeyQuotientIntertwiningMap_apply {xi : E} (hxi : xi ≠ 0)
    (f : Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :
    affineTopologicalMackeyQuotientIntertwiningMap hxi f =
      affineTopologicalMackeyQuotientLpEquiv hxi f := rfl

@[simp]
theorem affineTopologicalMackeyQuotientInverseIntertwiningMap_apply {xi : E} (hxi : xi ≠ 0)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    affineTopologicalMackeyQuotientInverseIntertwiningMap hxi f =
      (affineTopologicalMackeyQuotientLpEquiv hxi).symm f := rfl

/-- The orbit-measure representation is strongly continuous. -/
theorem affineTopologicalOrbitLpUnitaryRepresentation_isStronglyContinuous :
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).IsStronglyContinuous :=
  affineTopologicalFourierLpUnitaryRepresentation_isStronglyContinuous.conjugate
    (affineDualOrbitSubtypeLpEquiv (E := E))

/-- The homogeneous-space representation is strongly continuous. -/
theorem affineTopologicalMackeyQuotientLpUnitaryRepresentation_isStronglyContinuous
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi).IsStronglyContinuous :=
  affineTopologicalOrbitLpUnitaryRepresentation_isStronglyContinuous.conjugate
    (affineTopologicalMackeyQuotientLpEquiv hxi)

/-- The normalized-section induced representation is strongly continuous. -/
theorem affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isStronglyContinuous
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).IsStronglyContinuous := by
  rw [affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_transported hxi]
  exact affineTopologicalMackeyQuotientLpUnitaryRepresentation_isStronglyContinuous hxi

/-- Folland's compactly supported convolution smoothing, expressed intrinsically as a Haar-
integrated vector of the normalized-section induced representation. -/
noncomputable def affineMackeySmoothedVector
    {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).haarIntegratedVector ψ f

/-- The orbit-kernel defining affine Mackey smoothing is Bochner integrable. -/
theorem affineMackey_smoothing_integrable
    {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    Integrable (fun g ↦ ψ g •
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) Measure.haar :=
  UnitaryRepresentation.haarIntegratedVector_integrable
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isStronglyContinuous hxi) ψ f

/-- Haar convolution smoothing preserves every closed subspace invariant under the induced
representation. -/
theorem affineMackeySmoothedVector_mem
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    {f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)} (hf : f ∈ K) :
    affineMackeySmoothedVector hxi ψ f ∈ K := by
  apply UnitaryRepresentation.haarIntegratedVector_mem
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isStronglyContinuous hxi)
    K _ ψ hf
  exact (UnitaryRepresentation.isInvariant_iff_starProjection_commutes
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi) K).mpr hrepresentation

/-- Every vector in an invariant closed subspace is the `L²` limit of Haar-smoothed vectors in
the same subspace, using compactly supported nonnegative probability kernels whose supports shrink
to the identity.  This is the approximate-identity part of Folland Lemma 6.29. -/
theorem affineMackey_exists_smoothing_mem_tendsto
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    {f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)} (hf : f ∈ K) :
    ∃ ψ : ℕ → C_c(AffineEquiv.TopologicalSemidirectProduct E, ℝ),
      (∀ n g, 0 ≤ ψ n g) ∧
      (∀ n, ∫ g, ψ n g ∂Measure.haar = 1) ∧
      (∀ U ∈ nhds (1 : AffineEquiv.TopologicalSemidirectProduct E),
        ∀ᶠ n in Filter.atTop, tsupport (ψ n) ⊆ U) ∧
      (∀ n, affineMackeySmoothedVector hxi
        (UnitaryRepresentation.complexKernel (ψ n)) f ∈ K) ∧
      Filter.Tendsto
        (fun n ↦ affineMackeySmoothedVector hxi
          (UnitaryRepresentation.complexKernel (ψ n)) f)
        Filter.atTop (nhds f) := by
  obtain ⟨ψ, hnonneg, hintegral, hsupport, htendsto⟩ :=
    UnitaryRepresentation.exists_haarApproximateIdentity_tendsto_integratedVector
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isStronglyContinuous hxi) f
  refine ⟨ψ, hnonneg, hintegral, hsupport, ?_, ?_⟩
  · intro n
    exact affineMackeySmoothedVector_mem hxi K hrepresentation
      (UnitaryRepresentation.complexKernel (ψ n)) hf
  · simpa only [affineMackeySmoothedVector] using htendsto

/-- Haar smoothing of the normalized-section induced model has a continuous representative on the
homogeneous quotient.  A measurable representative of the quotient class lifts to the group so that
the smoothing integral becomes a compact-kernel group convolution: the convolution is continuous by
`LeanRidgelet.continuous_affineMackeySmoothingIntegral`, its slices over the finite-measure parts
of the quotient are integrable by
`LeanRidgelet.integrable_uncurry_affineMackeySmoothingIntegrand`, and
`MeasureTheory.integral_L2_coeFn_ae_of_restrict` therefore identifies the `L²`-valued Bochner
integral defining the smoothed vector with that pointwise integral.  The subsequent compact cutoff
and density argument is proved below. -/
theorem affineMackeySmoothedVector_exists_continuousRepresentative
    {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ∃ g : AffineTopologicalMackeyQuotient xi → ℂ,
      Continuous g ∧ MemLp g 2 (affineTopologicalMackeyQuotientMeasure hxi) ∧
        (affineMackeySmoothedVector hxi ψ f :
          AffineTopologicalMackeyQuotient xi → ℂ) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi] g := by
  obtain ⟨f₀, hf₀sm, hf₀ae⟩ := Lp.aestronglyMeasurable f
  have hf₀meas : Measurable f₀ := hf₀sm.measurable
  have hf₀mem : MemLp f₀ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
    (Lp.memLp f).ae_eq hf₀ae
  have hcont : Continuous (affineMackeySmoothingIntegral ψ f₀) :=
    continuous_affineMackeySmoothingIntegral hxi ψ
      (locallyIntegrable_affineMackeyLiftFun_inv hxi hf₀meas hf₀mem)
  have hae : (affineMackeySmoothedVector hxi ψ f :
      AffineTopologicalMackeyQuotient xi → ℂ) =ᵐ[affineTopologicalMackeyQuotientMeasure hxi]
      affineMackeySmoothingIntegral ψ f₀ := by
    refine integral_L2_coeFn_ae_of_restrict (affineMackey_smoothing_integrable hxi ψ f)
      (fun s hs hfin ↦ integrable_uncurry_affineMackeySmoothingIntegrand hxi ψ hf₀meas
        hf₀ae.symm hs hfin)
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g ↦ ?_)
    exact (Lp.coeFn_smul _ _).trans
      (affineMackeySmoothingIntegrand_ae_eq hxi ψ hf₀ae.symm g).symm
  exact ⟨affineMackeySmoothingIntegral ψ f₀, hcont, (Lp.memLp _).ae_eq hae, hae⟩

/-- The orbit-measure, Fourier, and physical affine models are topologically irreducible
simultaneously. -/
theorem affineTopologicalOrbitLpUnitaryRepresentation_isTopologicallyIrreducible_iff :
    (affineTopologicalOrbitLpUnitaryRepresentation (E := E)).IsTopologicallyIrreducible ↔
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure E)).IsTopologicallyIrreducible := by
  simpa only [affineTopologicalOrbitLpUnitaryRepresentation,
    affineTopologicalFourierLpUnitaryRepresentation,
    UnitaryRepresentation.conjugate_isTopologicallyIrreducible_iff] using
      (affineTopologicalLpUnitaryRepresentation_isTopologicallyIrreducible_iff
        (volume : Measure E))

/-- The homogeneous-space, orbit, Fourier, and physical affine models are topologically
irreducible simultaneously. -/
theorem
    affineTopologicalMackeyQuotientLpUnitaryRepresentation_isTopologicallyIrreducible_iff
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeyQuotientLpUnitaryRepresentation hxi).IsTopologicallyIrreducible ↔
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure E)).IsTopologicallyIrreducible := by
  rw [affineTopologicalMackeyQuotientLpUnitaryRepresentation,
    UnitaryRepresentation.conjugate_isTopologicallyIrreducible_iff]
  exact affineTopologicalOrbitLpUnitaryRepresentation_isTopologicallyIrreducible_iff

/-- Mackey irreducibility for the normalized-section induced model is exactly the remaining
irreducibility statement for the physical affine representation. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible_iff
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).IsTopologicallyIrreducible ↔
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure E)).IsTopologicallyIrreducible := by
  rw [affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_transported hxi]
  exact affineTopologicalMackeyQuotientLpUnitaryRepresentation_isTopologicallyIrreducible_iff hxi

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- In topological semidirect-product coordinates, a pure translation has identity linear
coordinate. -/
@[simp]
theorem affineTopologicalTranslation_right (b : E) :
    ((AffineEquiv.topologicalSemidirectProductEquiv E).symm
      (affineTranslation b)).right = 1 := by
  change (ContinuousLinearEquiv.unitsEquiv ℝ E).symm
      (affineTranslation b).linear.toContinuousLinearEquiv = 1
  apply Units.ext
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The translation subgroup acts trivially on the affine homogeneous quotient.  This is the
quotient-side form of the fact that the orbit map retains only the linear coordinate of an affine
transformation. -/
theorem affineTopologicalMackeyQuotient_translation_smul {xi : E} (hxi : xi ≠ 0) (b : E)
    (q : AffineTopologicalMackeyQuotient xi) :
    ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)) • q = q := by
  apply (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).injective
  rw [affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul hxi]
  apply Subtype.ext
  change affineTopologicalDualAction
      ((AffineEquiv.topologicalSemidirectProductEquiv E).symm
        (affineTranslation b)).right _ = _
  rw [affineTopologicalTranslation_right]
  exact affineTopologicalDualAction_one _

/-- The restriction of the normalized-section induced representation to translations is the
pointwise translation-character representation on the frequency orbit.  In particular, both the
homogeneous-space motion and the Radon--Nikodym factor disappear; only the character at the
frequency represented by the coset remains. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_apply_ae
    {xi : E} (hxi : xi ≠ 0) (b : E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi
        ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b))) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ (affineTranslationCharacter
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 b : ℂ) * f q := by
  let g : AffineEquiv.TopologicalSemidirectProduct E :=
    (AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)
  have haction :=
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit hxi g f
  filter_upwards [haction] with q hq
  rw [hq, affineTopologicalMackeySectionPhase_eq_quotientPhase hxi,
    affineTopologicalMackeyQuotientPhase_translation hxi]
  have hsmul : g⁻¹ • q = q := by
    apply (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).injective
    rw [affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul hxi]
    apply Subtype.ext
    change affineTopologicalDualAction (g⁻¹).right _ = _
    have hright : (g⁻¹).right = 1 := by simp [g]
    rw [hright]
    exact affineTopologicalDualAction_one _
  have hjac : affineTopologicalJacobian g = 1 := by
    simp [g, affineTopologicalJacobian]
  rw [hsmul, hjac]
  simp

/-- The quotient-orbit coordinate, regarded as a measurable embedding into the ambient frequency
space. -/
noncomputable def affineTopologicalMackeyFrequencyEmbedding {xi : E} (hxi : xi ≠ 0) :
    AffineTopologicalMackeyQuotient xi → E :=
  fun q ↦ (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1

omit [Nontrivial E] in
/-- The quotient-orbit coordinate is a measurable embedding. -/
theorem affineTopologicalMackeyFrequencyEmbedding_measurableEmbedding {xi : E} (hxi : xi ≠ 0) :
    MeasurableEmbedding (affineTopologicalMackeyFrequencyEmbedding hxi) := by
  exact (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit).comp
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).measurableEmbedding

/-- Multiplication by the character through which a pure translation acts on the Mackey
quotient.  Bundling this operator separately makes the spectral-projection step independent of
the group-representation implementation: its only input is commutation with these concrete
Fourier-character multipliers. -/
noncomputable def affineTopologicalMackeyTranslationMultiplier {xi : E} (hxi : xi ≠ 0)
    (b : E) :
    Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  MeasureTheory.fourierCharacterLpMultiplier
    (μ := affineTopologicalMackeyQuotientMeasure hxi)
    (affineTopologicalMackeyFrequencyEmbedding hxi)
    (affineTopologicalMackeyFrequencyEmbedding_measurableEmbedding hxi).measurable b

omit [Nontrivial E] in
/-- The bundled Mackey translation multiplier has the expected pointwise representative. -/
theorem affineTopologicalMackeyTranslationMultiplier_apply_ae {xi : E} (hxi : xi ≠ 0)
    (b : E) (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    affineTopologicalMackeyTranslationMultiplier hxi b f =ᵐ[
        affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ (affineTranslationCharacter
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 b : ℂ) * f q := by
  simpa only [affineTopologicalMackeyTranslationMultiplier,
    MeasureTheory.fourierCharacterMultiplierPhase, affineTopologicalMackeyFrequencyEmbedding,
    affineTranslationCharacter_apply] using
      (MeasureTheory.fourierCharacterLpMultiplier_apply_ae
        (μ := affineTopologicalMackeyQuotientMeasure hxi)
        (affineTopologicalMackeyFrequencyEmbedding hxi)
        (affineTopologicalMackeyFrequencyEmbedding_measurableEmbedding hxi).measurable b f)

/-- On the translation subgroup, the normalized-section induced representation is the concrete
Mackey character multiplier. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_eq_multiplier
    {xi : E} (hxi : xi ≠ 0) (b : E) :
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi
        ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)) :
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =
      (affineTopologicalMackeyTranslationMultiplier hxi b :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_apply_ae
    hxi b f).trans (affineTopologicalMackeyTranslationMultiplier_apply_ae hxi b f).symm

/-- An operator in the commutant of the induced affine representation commutes, in particular,
with every member of its translation restriction.  Together with the preceding pointwise formula,
this is the operator-theoretic input to the spectral-projection step. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translation
    {xi : E} (hxi : xi ≠ 0)
    (T : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (hT : (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes T)
    (b : E) :
    T.comp
        (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi
          ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)) :
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
              Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi
          ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)) :
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
              Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)).comp T := by
  exact hT _

/-- An operator in the affine commutant therefore commutes with every concrete translation
character multiplier. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translationMultiplier
    {xi : E} (hxi : xi ≠ 0)
    (T : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (hT : (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes T)
    (b : E) :
    T.comp (affineTopologicalMackeyTranslationMultiplier hxi b :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =
      (affineTopologicalMackeyTranslationMultiplier hxi b :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)).comp T := by
  rw [← affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_eq_multiplier
    hxi b]
  exact
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translation hxi T hT b

omit [Nontrivial E] in
/-- Specialization of the commutant criterion in Folland Theorem 4.44 to the translation
restriction of the affine induced model.  Since translations act by the characters displayed in
`affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_apply_ae`, their spectral
projections are the canonical measurable-set multiplication operators on the quotient orbit. -/
theorem
    affineMackey_commutes_indicator_of_commutes_translation
    {xi : E} (hxi : xi ≠ 0)
    (T : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (htranslation : ∀ b : E,
      T.comp (affineTopologicalMackeyTranslationMultiplier hxi b :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =
        (affineTopologicalMackeyTranslationMultiplier hxi b :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)).comp T)
    (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s) :
    T.comp (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
        (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs) =
      (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
        (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs).comp T := by
  exact ContinuousLinearMap.commutes_indicatorLp_of_commutes_fourierCharacter
    (affineTopologicalMackeyFrequencyEmbedding hxi)
    (affineTopologicalMackeyFrequencyEmbedding_measurableEmbedding hxi) T htranslation s hs

omit [Nontrivial E] in
/-- A system-invariant closed subspace is stable under every quotient-orbit indicator
projection.  This is the elementary range-of-projection consequence used before the regular
section argument of Folland Lemma 6.29. -/
theorem affineMackey_indicatorLp_mem
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      K.toSubmodule.starProjection.comp
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection)
    (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s)
    {f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)} (hf : f ∈ K) :
    MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
      (μ := affineTopologicalMackeyQuotientMeasure hxi)
      (E := ℂ) (𝕜 := ℂ) s hs f ∈ K := by
  exact MeasureTheory.indicatorLp_mem_of_starProjection_commute K s hs
    (hindicator s hs) hf

/-- A closed subspace whose star projection commutes with the induced representation is stable
under the induced action. -/
theorem affineMackey_representation_mem
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    {f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)} (hf : f ∈ K) :
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f ∈ K := by
  have hK := (UnitaryRepresentation.isInvariant_iff_starProjection_commutes
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi) K).mpr hrepresentation
  exact hK g hf

omit [Nontrivial E] in
/-- A compactly supported continuous scalar section on the homogeneous quotient belongs to
`L²`. -/
theorem affineMackey_regularSection_memLp
    {xi : E} (hxi : xi ≠ 0)
    (f : C_c(AffineTopologicalMackeyQuotient xi, ℂ)) :
    MemLp f 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  compactlySupportedContinuous_memLp f

/-- The linear map sending a regular quotient section to its `L²` class. -/
noncomputable def affineMackeyRegularSectionToLp
    {xi : E} (hxi : xi ≠ 0) :
    C_c(AffineTopologicalMackeyQuotient xi, ℂ) →ₗ[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
  compactlySupportedContinuousToLp

/-- Evaluation of a regular section at the identity coset. -/
def affineMackeyRegularSectionEvaluation
    {xi : E} : C_c(AffineTopologicalMackeyQuotient xi, ℂ) →ₗ[ℂ] ℂ where
  toFun f := f (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E))
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Regular sections whose `L²` classes belong to a fixed closed system-invariant subspace. -/
noncomputable def affineMackeyRegularSectionsIn
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))) :
    Submodule ℂ C_c(AffineTopologicalMackeyQuotient xi, ℂ) :=
  K.toSubmodule.comap (affineMackeyRegularSectionToLp hxi)

/-- The inducing fiber extracted from a closed subspace: take the closed linear span of the
values at the identity coset of its regular sections.  This is the concrete scalar specialization
of the fiber `M` constructed in Folland Lemma 6.30. -/
noncomputable def affineMackeyInducingFiber
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))) :
    ClosedSubmodule ℂ ℂ :=
  (Submodule.map affineMackeyRegularSectionEvaluation
    (affineMackeyRegularSectionsIn hxi K)).closure

/-- Folland Lemma 6.29 in the normalized quotient model: regular sections belonging to a closed
subspace invariant under the system of imprimitivity are dense in that subspace. -/
theorem affineMackey_regularSection_dense
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      K.toSubmodule.starProjection.comp
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection) :
    Dense (Set.range fun f : affineMackeyRegularSectionsIn hxi K ↦
      (⟨affineMackeyRegularSectionToLp hxi f, f.property⟩ : K)) := by
  intro f
  rw [mem_closure_iff_seq_limit]
  obtain ⟨ψ, _hnonneg, _hintegral, _hsupport, hψK, hψtendsto⟩ :=
    affineMackey_exists_smoothing_mem_tendsto hxi K hrepresentation f.property
  let u : ℕ → K := fun n ↦
    ⟨affineMackeySmoothedVector hxi
      (UnitaryRepresentation.complexKernel (ψ n)) f, hψK n⟩
  have hutendsto : Filter.Tendsto
      (fun n ↦ (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
      Filter.atTop (nhds (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))) := by
    simpa only [u] using hψtendsto
  have hregular : ∀ n, ∃ r : C_c(AffineTopologicalMackeyQuotient xi, ℂ),
      affineMackeyRegularSectionToLp hxi r ∈ K ∧
        dist (affineMackeyRegularSectionToLp hxi r)
          (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) <
            (1 : ℝ) / (n + 1) := by
    intro n
    obtain ⟨g, hgcontinuous, hgmem, hug⟩ :=
      affineMackeySmoothedVector_exists_continuousRepresentative hxi
        (UnitaryRepresentation.complexKernel (ψ n)) f
    have heq : hgmem.toLp g =
        (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) := by
      apply Lp.ext
      exact hgmem.coeFn_toLp.trans hug.symm
    have hgindicator : ∀ (t : Set (AffineTopologicalMackeyQuotient xi))
        (ht : MeasurableSet t),
        MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi)
          (E := ℂ) (𝕜 := ℂ) t ht (hgmem.toLp g) ∈ K := by
      intro t ht
      rw [heq]
      exact affineMackey_indicatorLp_mem hxi K hindicator t ht (u n).property
    obtain ⟨r, hrK, hrdist⟩ :=
      MeasureTheory.exists_compactlySupportedContinuousToLp_mem_dist_lt
        K hgcontinuous hgmem hgindicator
        (show 0 < (1 : ℝ) / (n + 1) by positivity)
    refine ⟨r, ?_, ?_⟩
    · simpa only [affineMackeyRegularSectionToLp] using hrK
    · rw [← heq]
      simpa only [affineMackeyRegularSectionToLp] using hrdist
  choose r hrK hrdist using hregular
  let v : ℕ → K := fun n ↦ ⟨affineMackeyRegularSectionToLp hxi (r n), hrK n⟩
  have hvtendsto : Filter.Tendsto v Filter.atTop (nhds f) := by
    rw [tendsto_subtype_rng]
    rw [tendsto_iff_dist_tendsto_zero]
    have hudist : Filter.Tendsto
        (fun n ↦ dist
          (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
          (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
        Filter.atTop (nhds 0) := tendsto_iff_dist_tendsto_zero.mp hutendsto
    have huppers : Filter.Tendsto
        (fun n ↦ (1 : ℝ) / (n + 1) + dist
          (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
          (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
        Filter.atTop (nhds 0) := by
      simpa only [zero_add] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add hudist
    apply squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (dist_triangle
        (v n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
        (u n : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
        (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))).trans
          (add_le_add (le_of_lt (hrdist n)) le_rfl))
      huppers
  refine ⟨v, ?_, hvtendsto⟩
  intro n
  let rn : affineMackeyRegularSectionsIn hxi K := ⟨r n, hrK n⟩
  exact ⟨rn, rfl⟩

/-- Translating a compactly supported continuous quotient section by the induced action.  The
phase and the Radon--Nikodym constant are unit-modulus and positive, so the translate is again a
compactly supported continuous section. -/
noncomputable def affineMackeyRegularSectionSMul {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ)) :
    C_c(AffineTopologicalMackeyQuotient xi, ℂ) where
  toFun q := affineTopologicalMackeySectionPhase g q *
    (((affineTopologicalJacobian g).sqrt : ℂ) * r (g⁻¹ • q))
  continuous_toFun :=
    (continuous_affineTopologicalMackeySectionPhase hxi g).mul
      (continuous_const.mul (r.continuous.comp (continuous_const_smul g⁻¹)))
  hasCompactSupport' := by
    have h : HasCompactSupport
        (fun q : AffineTopologicalMackeyQuotient xi ↦ r (g⁻¹ • q)) :=
      r.hasCompactSupport.comp_homeomorph (Homeomorph.smul g⁻¹)
    have heq : (fun q : AffineTopologicalMackeyQuotient xi ↦
          affineTopologicalMackeySectionPhase g q *
            (((affineTopologicalJacobian g).sqrt : ℂ) * r (g⁻¹ • q))) =
        (fun q : AffineTopologicalMackeyQuotient xi ↦
          affineTopologicalMackeySectionPhase g q *
            ((affineTopologicalJacobian g).sqrt : ℂ)) *
          fun q : AffineTopologicalMackeyQuotient xi ↦ r (g⁻¹ • q) := by
      funext q
      simp only [Pi.mul_apply, mul_assoc]
    rw [heq]
    exact h.mul_left

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem affineMackeyRegularSectionSMul_apply {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    (q : AffineTopologicalMackeyQuotient xi) :
    affineMackeyRegularSectionSMul hxi g r q =
      affineTopologicalMackeySectionPhase g q *
        (((affineTopologicalJacobian g).sqrt : ℂ) * r (g⁻¹ • q)) := rfl

omit [Nontrivial E] in
/-- A compactly supported continuous section represents its own `L²` class. -/
theorem affineMackeyRegularSectionToLp_coeFn_ae {xi : E} (hxi : xi ≠ 0)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ)) :
    (affineMackeyRegularSectionToLp hxi r :
        AffineTopologicalMackeyQuotient xi → ℂ) =ᵐ[
      affineTopologicalMackeyQuotientMeasure hxi] r := by
  change ((compactlySupportedContinuous_memLp
      (μ := affineTopologicalMackeyQuotientMeasure hxi) r).toLp
        (r : AffineTopologicalMackeyQuotient xi → ℂ) :
      AffineTopologicalMackeyQuotient xi → ℂ) =ᵐ[
        affineTopologicalMackeyQuotientMeasure hxi] r
  exact MemLp.coeFn_toLp _

set_option maxHeartbeats 1000000 in
-- Comparing the section translate with the fully instantiated general twist unfolds the same long
-- chain of `Lp` isometries as the explicit action formula itself.
/-- The `L²` class of a translated section is the induced action applied to the `L²` class of the
section. -/
theorem affineMackeyRegularSectionToLp_smul {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ)) :
    affineMackeyRegularSectionToLp hxi (affineMackeyRegularSectionSMul hxi g r) =
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
        (affineMackeyRegularSectionToLp hxi r) := by
  apply Lp.ext
  have haction :=
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit hxi g
      (affineMackeyRegularSectionToLp hxi r)
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi) g
  have hshift := hqmp.ae_eq (affineMackeyRegularSectionToLp_coeFn_ae hxi r)
  filter_upwards [affineMackeyRegularSectionToLp_coeFn_ae hxi
      (affineMackeyRegularSectionSMul hxi g r), haction, hshift]
    with q hq hactionq hshiftq
  rw [hq, hactionq]
  simp only [Function.comp_apply] at hshiftq
  rw [affineMackeyRegularSectionSMul_apply, hshiftq]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The phase and Radon--Nikodym factors of the section model never vanish, so a translated section
vanishes exactly where the original section does. -/
theorem affineMackeyRegularSectionSMul_ne_zero {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    {q : AffineTopologicalMackeyQuotient xi} (hq : r (g⁻¹ • q) ≠ 0) :
    affineMackeyRegularSectionSMul hxi g r q ≠ 0 := by
  rw [affineMackeyRegularSectionSMul_apply]
  have hphase : affineTopologicalMackeySectionPhase g q ≠ 0 := by
    rw [← norm_ne_zero_iff, affineTopologicalMackeySectionPhase_norm_one hxi g q]
    exact one_ne_zero
  have hjac : ((affineTopologicalJacobian g).sqrt : ℂ) ≠ 0 := by
    have h1 : (affineTopologicalJacobian g).sqrt ≠ 0 := by
      simpa using affineTopologicalJacobian_ne_zero g
    simpa using h1
  exact mul_ne_zero hphase (mul_ne_zero hjac hq)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Vanishing of a translated section at the identity coset means vanishing of the section at the
translated coset. -/
theorem affineMackeyRegularSection_eq_zero_of_smul_eq_zero {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    {q : AffineTopologicalMackeyQuotient xi}
    (h : affineMackeyRegularSectionSMul hxi g r q = 0) :
    r (g⁻¹ • q) = 0 := by
  by_contra hne
  exact affineMackeyRegularSectionSMul_ne_zero hxi g r hne h

omit [Nontrivial E] in
/-- The inducing fiber is trivial exactly when every regular section of the subspace vanishes at
the identity coset. -/
theorem affineMackeyInducingFiber_eq_bot_iff {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))) :
    affineMackeyInducingFiber hxi K = ⊥ ↔
      ∀ r : C_c(AffineTopologicalMackeyQuotient xi, ℂ),
        affineMackeyRegularSectionToLp hxi r ∈ K →
          r (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) = 0 := by
  constructor
  · intro hbot r hr
    have hmem : affineMackeyRegularSectionEvaluation r ∈
        affineMackeyInducingFiber hxi K := by
      rw [affineMackeyInducingFiber, Submodule.mem_closure_iff]
      exact Submodule.le_topologicalClosure _
        (Submodule.mem_map_of_mem (Submodule.mem_comap.mpr hr))
    rw [hbot] at hmem
    simpa [affineMackeyRegularSectionEvaluation] using hmem
  · intro h
    have hmap : Submodule.map (affineMackeyRegularSectionEvaluation (xi := xi))
        (affineMackeyRegularSectionsIn hxi K) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro x ⟨r, hr, rfl⟩
      exact h r (Submodule.mem_comap.mp hr)
    rw [affineMackeyInducingFiber, hmap,
      ← ClosedSubmodule.toSubmodule_bot (R := ℂ) (M := ℂ)]
    exact Submodule.closure_eq

omit [Nontrivial E] in
/-- One regular section of the subspace that does not vanish at the identity coset already spans
the whole one-dimensional inducing fiber. -/
theorem affineMackeyInducingFiber_eq_top_of_ne_zero {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    (hr : affineMackeyRegularSectionToLp hxi r ∈ K)
    (hr0 : r (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) ≠ 0) :
    affineMackeyInducingFiber hxi K = ⊤ := by
  have hmem : affineMackeyRegularSectionEvaluation r ∈
      Submodule.map (affineMackeyRegularSectionEvaluation (xi := xi))
        (affineMackeyRegularSectionsIn hxi K) :=
    Submodule.mem_map_of_mem (Submodule.mem_comap.mpr hr)
  have hmap : Submodule.map (affineMackeyRegularSectionEvaluation (xi := xi))
      (affineMackeyRegularSectionsIn hxi K) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hsmul := Submodule.smul_mem _ (x / affineMackeyRegularSectionEvaluation r) hmem
    rwa [smul_eq_mul, div_mul_cancel₀ x
      (show affineMackeyRegularSectionEvaluation r ≠ 0 from hr0)] at hsmul
  rw [affineMackeyInducingFiber, hmap,
    ← ClosedSubmodule.toSubmodule_top (R := ℂ) (M := ℂ)]
  exact Submodule.closure_eq

/-- If the inducing fiber is trivial, then every regular section of the subspace vanishes
identically: the induced action moves the identity coset onto every coset, so the fiber condition
propagates along the orbit. -/
theorem affineMackey_regularSection_eq_zero_of_inducingFiber_eq_bot {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hfiber : affineMackeyInducingFiber hxi K = ⊥)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    (hr : affineMackeyRegularSectionToLp hxi r ∈ K)
    (q : AffineTopologicalMackeyQuotient xi) :
    r q = 0 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (AffineEquiv.TopologicalSemidirectProduct E)
    (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) q
  have hRK : affineMackeyRegularSectionToLp hxi
      (affineMackeyRegularSectionSMul hxi g⁻¹ r) ∈ K := by
    rw [affineMackeyRegularSectionToLp_smul]
    exact affineMackey_representation_mem hxi K hrepresentation g⁻¹ hr
  have h0 := (affineMackeyInducingFiber_eq_bot_iff hxi K).mp hfiber _ hRK
  have hq := affineMackeyRegularSection_eq_zero_of_smul_eq_zero hxi g⁻¹ r h0
  rwa [inv_inv, hg] at hq

/-- A subspace with trivial inducing fiber is trivial.  Every regular section it contains vanishes
identically, and regular sections are dense in it by the Folland-6.29 density theorem. -/
theorem affineMackey_eq_bot_of_inducingFiber_eq_bot {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hregular : Dense (Set.range fun f : affineMackeyRegularSectionsIn hxi K ↦
      (⟨affineMackeyRegularSectionToLp hxi f, f.property⟩ : K)))
    (hfiber : affineMackeyInducingFiber hxi K = ⊥) :
    K = ⊥ := by
  have hsectionzero : ∀ f : affineMackeyRegularSectionsIn hxi K,
      affineMackeyRegularSectionToLp hxi (f : C_c(AffineTopologicalMackeyQuotient xi, ℂ)) = 0 := by
    intro f
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [affineMackeyRegularSectionToLp_coeFn_ae hxi
      (f : C_c(AffineTopologicalMackeyQuotient xi, ℂ))] with q hq
    rw [hq]
    exact affineMackey_regularSection_eq_zero_of_inducingFiber_eq_bot hxi K hrepresentation
      hfiber _ (Submodule.mem_comap.mp f.property) q
  have hrange : (Set.range fun f : affineMackeyRegularSectionsIn hxi K ↦
      (⟨affineMackeyRegularSectionToLp hxi f, f.property⟩ : K)) ⊆ {0} := by
    rintro y ⟨f, rfl⟩
    simp only [Set.mem_singleton_iff]
    exact Subtype.ext (hsectionzero f)
  have huniv : (Set.univ : Set K) ⊆ {0} := by
    rw [← hregular.closure_eq]
    exact isClosed_singleton.closure_subset_iff.mpr hrange
  apply SetLike.ext
  intro x
  simp only [ClosedSubmodule.mem_bot]
  refine ⟨fun hx ↦ ?_, fun hx ↦ by rw [hx]; exact zero_mem K⟩
  have hmem := huniv (Set.mem_univ (⟨x, hx⟩ : K))
  rw [Set.mem_singleton_iff] at hmem
  have hcoe := congrArg
    (fun y : K ↦ (y : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))) hmem
  simpa only [ZeroMemClass.coe_zero] using hcoe

/-- A subspace containing one regular section that does not vanish at the identity coset is
everything.  Orthogonality to the subspace forces a vector to vanish almost everywhere on the
nonvanishing set of every translate of that section, and countably many translates already cover the
homogeneous quotient. -/
theorem affineMackey_eq_top_of_regularSection_ne_zero {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      K.toSubmodule.starProjection.comp
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection)
    (r : C_c(AffineTopologicalMackeyQuotient xi, ℂ))
    (hr : affineMackeyRegularSectionToLp hxi r ∈ K)
    (hr0 : r (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) ≠ 0) :
    K = ⊤ := by
  have horthogonal : K.toSubmoduleᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    set U : Set (AffineTopologicalMackeyQuotient xi) := {q | r q ≠ 0} with hUdef
    have hUopen : IsOpen U := isOpen_compl_singleton.preimage r.continuous
    set V : AffineEquiv.TopologicalSemidirectProduct E →
        Set (AffineTopologicalMackeyQuotient xi) :=
      fun g ↦ (fun q ↦ g⁻¹ • q) ⁻¹' U with hVdef
    have hVopen : ∀ g, IsOpen (V g) := fun g ↦ hUopen.preimage (continuous_const_smul g⁻¹)
    have hVcover : (⋃ g, V g) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (AffineEquiv.TopologicalSemidirectProduct E)
        (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) q
      refine Set.mem_iUnion.mpr ⟨g, ?_⟩
      have hgq : g⁻¹ • q = QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E) := by
        rw [← hg, inv_smul_smul]
      change r (g⁻¹ • q) ≠ 0
      rw [hgq]
      exact hr0
    have hkey : ∀ g, ∀ᵐ q ∂ affineTopologicalMackeyQuotientMeasure hxi,
        q ∈ V g → (v : AffineTopologicalMackeyQuotient xi → ℂ) q = 0 := by
      intro g
      have hRK : affineMackeyRegularSectionToLp hxi
          (affineMackeyRegularSectionSMul hxi g r) ∈ K := by
        rw [affineMackeyRegularSectionToLp_smul]
        exact affineMackey_representation_mem hxi K hrepresentation g hr
      have hind : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
          MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
              (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs
              (affineMackeyRegularSectionToLp hxi
                (affineMackeyRegularSectionSMul hxi g r)) ∈ K.toSubmodule :=
        fun s hs ↦ affineMackey_indicatorLp_mem hxi K hindicator s hs hRK
      have hae := MeasureTheory.ae_eq_zero_of_mem_orthogonal_of_indicatorLp_mem hind hv
      filter_upwards [hae, affineMackeyRegularSectionToLp_coeFn_ae hxi
        (affineMackeyRegularSectionSMul hxi g r)] with q hq hrep hqV
      apply hq
      rw [hrep]
      exact affineMackeyRegularSectionSMul_ne_zero hxi g r hqV
    obtain ⟨T, hTcountable, hTunion⟩ := TopologicalSpace.isOpen_iUnion_countable V hVopen
    have hall : ∀ᵐ q ∂ affineTopologicalMackeyQuotientMeasure hxi,
        ∀ g ∈ T, q ∈ V g → (v : AffineTopologicalMackeyQuotient xi → ℂ) q = 0 :=
      (MeasureTheory.ae_ball_iff hTcountable).mpr fun g _ ↦ hkey g
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hall] with q hq
    have hmem : q ∈ ⋃ g ∈ T, V g := by
      rw [hTunion, hVcover]
      exact Set.mem_univ q
    obtain ⟨g, hgT, hgq⟩ := Set.mem_iUnion₂.mp hmem
    exact hq g hgT hgq
  have htop : K.toSubmodule = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horthogonal
  apply SetLike.ext
  intro x
  simp only [ClosedSubmodule.mem_top, iff_true]
  have hx : x ∈ K.toSubmodule := by rw [htop]; exact Submodule.mem_top
  exact hx

/-- Folland Lemma 6.30, restricted to the two conclusions needed for the one-dimensional affine
inducing fiber.  The regular-section fiber is zero exactly when the induced closed subspace is
zero, and it is the whole scalar fiber exactly when that subspace is the whole `L²` space.

Both directions are assembled from the four lemmas above: identity-coset evaluation of translated
sections for the zero case, together with the density hypothesis supplied by Folland 6.29, and
orthogonal-complement vanishing along a countable subcover of translates for the full case. -/
theorem affineMackey_closedSubspace_extreme_iff_inducingFiber_extreme
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      K.toSubmodule.starProjection.comp
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection)
    (hregular : Dense (Set.range fun f : affineMackeyRegularSectionsIn hxi K ↦
      (⟨affineMackeyRegularSectionToLp hxi f, f.property⟩ : K))) :
    (K = ⊥ ↔ affineMackeyInducingFiber hxi K = ⊥) ∧
      (K = ⊤ ↔ affineMackeyInducingFiber hxi K = ⊤) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hK
    rw [affineMackeyInducingFiber_eq_bot_iff]
    intro r hr
    rw [hK, ClosedSubmodule.mem_bot] at hr
    have hae : (r : AffineTopologicalMackeyQuotient xi → ℂ) =ᵐ[
        affineTopologicalMackeyQuotientMeasure hxi] 0 := by
      have h1 := affineMackeyRegularSectionToLp_coeFn_ae hxi r
      rw [hr] at h1
      exact h1.symm.trans (Lp.coeFn_zero ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    have hfun := (Continuous.ae_eq_iff_eq (affineTopologicalMackeyQuotientMeasure hxi)
      r.continuous continuous_const).mp hae
    exact congrFun hfun _
  · intro hfiber
    exact affineMackey_eq_bot_of_inducingFiber_eq_bot hxi K hrepresentation hregular hfiber
  · intro hK
    obtain ⟨f, hf1, -, hfsupport, -⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_singleton (x := QuotientGroup.mk
        (1 : AffineEquiv.TopologicalSemidirectProduct E)
        (s := (affineTopologicalMackeySubgroup xi).toSubgroup)))
      isClosed_empty (Set.disjoint_empty _)
    refine affineMackeyInducingFiber_eq_top_of_ne_zero hxi K
      ⟨⟨fun q ↦ (f q : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
        hfsupport.comp_left (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero⟩ ?_ ?_
    · rw [hK]
      exact ClosedSubmodule.mem_top
    · have hone : f (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) = 1 :=
        hf1 rfl
      change ((f (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) : ℝ) : ℂ) ≠ 0
      rw [hone]
      exact one_ne_zero
  · intro hfiber
    have hex : ∃ r : C_c(AffineTopologicalMackeyQuotient xi, ℂ),
        affineMackeyRegularSectionToLp hxi r ∈ K ∧
          r (QuotientGroup.mk (1 : AffineEquiv.TopologicalSemidirectProduct E)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hbot := (affineMackeyInducingFiber_eq_bot_iff hxi K).mpr hcon
      rw [hfiber] at hbot
      have hone : (1 : ℂ) ∈ (⊥ : ClosedSubmodule ℂ ℂ) := by
        rw [← hbot]
        exact ClosedSubmodule.mem_top
      rw [ClosedSubmodule.mem_bot] at hone
      exact one_ne_zero hone
    obtain ⟨r, hr, hr0⟩ := hex
    exact affineMackey_eq_top_of_regularSection_ne_zero hxi K hrepresentation hindicator r hr hr0

/-- Folland Lemmas 6.29--6.30 for the canonical affine system with one-dimensional inducing
fiber. A closed subspace whose orthogonal projection commutes with both the induced action and all
quotient-orbit indicator projections is zero or the whole `L²` space.

The regular-section density theorem above is a completed consequence of the named
measurable-lift/product-integrability/convolution-formula placeholder, and the inducing-fiber
correspondence is now proved. This theorem combines them with the proved classification of closed
complex subspaces of the one-dimensional inducing fiber and contains no `sorry` of its own. -/
theorem affineMackey_systemInvariant_closedSubspace_eq_bot_or_top
    {xi : E} (hxi : xi ≠ 0)
    (K : ClosedSubmodule ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)))
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      K.toSubmodule.starProjection.comp
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
            (μ := affineTopologicalMackeyQuotientMeasure hxi)
            (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection) :
    K = ⊥ ∨ K = ⊤ := by
  have hregular := affineMackey_regularSection_dense hxi K hrepresentation hindicator
  have hextreme := affineMackey_closedSubspace_extreme_iff_inducingFiber_extreme
    hxi K hrepresentation hindicator hregular
  rcases UnitaryRepresentation.closedSubmodule_complex_eq_bot_or_top
      (affineMackeyInducingFiber hxi K) with hbot | htop
  · exact Or.inl (hextreme.1.mpr hbot)
  · exact Or.inr (hextreme.2.mpr htop)

/-- A self-adjoint member of the canonical affine-system commutant is scalar. A hypothetical
non-scalar member supplies a nontrivial continuous-functional-calculus spectral subspace; its
orthogonal projection still commutes with the full system, contradicting the specialized
Folland-6.29--6.30 classification above. -/
theorem affineMackey_exists_scalar_of_isSelfAdjoint
    {xi : E} (hxi : xi ≠ 0)
    (A : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (hA : IsSelfAdjoint A)
    (hrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes A)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      A.comp (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs).comp A) :
    ∃ c : ℂ, A = c • ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) := by
  by_contra hscalar
  obtain ⟨K, hKbot, hKtop, hKcomm⟩ :=
    UnitaryRepresentation.exists_nontrivial_spectralSubspace_of_isSelfAdjoint_not_scalar
      A hA hscalar
  have hKrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes
        K.toSubmodule.starProjection := by
    intro g
    exact hKcomm _ (hrepresentation g)
  have hKindicator :
      ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
        K.toSubmodule.starProjection.comp
            (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
              (μ := affineTopologicalMackeyQuotientMeasure hxi)
              (E := ℂ) (𝕜 := ℂ) s hs) =
          (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
              (μ := affineTopologicalMackeyQuotientMeasure hxi)
              (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection := by
    intro s hs
    exact hKcomm _ (hindicator s hs)
  rcases affineMackey_systemInvariant_closedSubspace_eq_bot_or_top
      hxi K hKrepresentation hKindicator with hK | hK
  · exact hKbot hK
  · exact hKtop hK

set_option maxHeartbeats 400000 in
-- The expanded Mackey section types make the final `module` normalization exceed the default.
/-- Specialization of Folland Theorem 6.28 to the canonical affine system of imprimitivity.
Commutation with the induced action and all quotient-orbit indicator projections identifies `T`
with an operator in the commutant of the one-dimensional inducing character, hence with a scalar.

The only unproved input is the Folland-6.29 smoothed-vector continuous-representative theorem
used by the completed regular-section density argument. The spectral-subspace argument, the
inducing-fiber correspondence, and the decomposition into two self-adjoint operators are proved
here. -/
theorem
    affineMackey_scalar_of_commutes_indicators
    {xi : E} (hxi : xi ≠ 0)
    (T : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (hT : (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes T)
    (hindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s),
      T.comp (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs).comp T) :
    ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) := by
  let A : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
    ((2 : ℂ)⁻¹) • (T + star T)
  let S : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) :=
    ((2 : ℂ)⁻¹) • (T - star T)
  let B : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) := Complex.I • S
  have hstar :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes (star T) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hT.adjoint
  have hArepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes A := by
    simpa [A] using (hT.add hstar).smul ((2 : ℂ)⁻¹)
  have hSrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes S := by
    simpa [S, sub_eq_add_neg] using (hT.add (hstar.smul (-1))).smul ((2 : ℂ)⁻¹)
  have hBrepresentation :
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).Commutes B :=
    hSrepresentation.smul Complex.I
  have hAindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi))
      (hs : MeasurableSet s),
      A.comp (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs).comp A := by
    intro s hs
    let P := MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
      (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs
    have hTP : Commute T P := hindicator s hs
    have hstarTP : Commute (star T) P := by
      have h := hTP.star_star
      rw [(MeasureTheory.indicatorLp_isSelfAdjoint s hs).star_eq] at h
      exact h
    have hAP : Commute A P := by
      simpa [A] using (hTP.add_left hstarTP).smul_left ((2 : ℂ)⁻¹)
    exact hAP.eq
  have hBindicator : ∀ (s : Set (AffineTopologicalMackeyQuotient xi))
      (hs : MeasurableSet s),
      B.comp (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs) =
        (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs).comp B := by
    intro s hs
    let P := MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
      (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs
    have hTP : Commute T P := hindicator s hs
    have hstarTP : Commute (star T) P := by
      have h := hTP.star_star
      rw [(MeasureTheory.indicatorLp_isSelfAdjoint s hs).star_eq] at h
      exact h
    have hSP : Commute S P := by
      simpa [S, sub_eq_add_neg] using
        (hTP.add_left (hstarTP.smul_left (-1 : ℂ))).smul_left ((2 : ℂ)⁻¹)
    exact (hSP.smul_left Complex.I).eq
  have hAself : IsSelfAdjoint A := by
    rw [isSelfAdjoint_iff]
    simp [A, star_smul, add_comm]
  have hBself : IsSelfAdjoint B := by
    rw [isSelfAdjoint_iff]
    simp [B, S, star_smul, smul_smul]
    module
  obtain ⟨a, ha⟩ := affineMackey_exists_scalar_of_isSelfAdjoint
    hxi A hAself hArepresentation hAindicator
  obtain ⟨b, hb⟩ := affineMackey_exists_scalar_of_isSelfAdjoint
    hxi B hBself hBrepresentation hBindicator
  refine ⟨a + (-Complex.I) * b, ?_⟩
  have hdecomp : A + S = T := by
    dsimp only [A, S]
    module
  have hS : S = (-Complex.I) • B := by
    ext x
    simp [B, smul_smul]
  calc
    T = A + S := hdecomp.symm
    _ = (a • ContinuousLinearMap.id ℂ _) +
        (-Complex.I) • (b • ContinuousLinearMap.id ℂ _) := by rw [ha, hS, hb]
    _ = (a + (-Complex.I) * b) • ContinuousLinearMap.id ℂ _ := by module

/-- The assembled commutant form of the Mackey irreducibility step for the normalized-section
induced model. An operator commuting with the induced affine action first commutes with the
spectral projections of the translation subgroup, hence belongs to the commutant of the canonical
system of imprimitivity; the imprimitivity commutant theorem then identifies it with the commutant
of the inducing one-dimensional character, so it is scalar.

All group, orbit, quotient-measure, section-cocycle, continuity, inducing-character,
translation-spectral, and inducing-fiber inputs have already been constructed above. The remaining
analytic input is the named Folland-6.29 smoothed-vector continuous-representative theorem used by
the completed density argument; this assembly contains no source-level placeholder and uses no
induction or imprimitivity assumptions structure.
-/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_hasSchurProperty
    {xi : E} (hxi : xi ≠ 0) :
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi).HasSchurProperty := by
  intro T hT
  apply affineMackey_scalar_of_commutes_indicators hxi T hT
  intro s hs
  apply affineMackey_commutes_indicator_of_commutes_translation hxi T _ s hs
  intro b
  exact
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translationMultiplier
      hxi T hT b

/-- Folland Theorem 6.39, irreducibility direction, for the normalized-section affine induced
model.  Once its commutant is scalar, the converse direction of the unitary Schur lemma turns the
commutant statement into topological irreducibility. -/
theorem affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible
    {xi : E} (hxi : xi ≠ 0) :
    UnitaryRepresentation.IsTopologicallyIrreducible
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi) := by
  letI : Nontrivial (Lp ℂ 2 (volume : Measure E)) :=
    MeasureTheory.nontrivial_Lp_of_exists_measurableSet
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure E)) (E := ℂ)
      (by norm_num) (by norm_num) (Metric.closedBall (0 : E) 1)
      measurableSet_closedBall
      (Metric.measure_closedBall_pos (volume : Measure E) 0 zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  letI : Nontrivial (Lp ℂ 2 (affineDualOrbitSubtypeMeasure (E := E))) :=
    (affineDualOrbitSubtypeLpEquiv (E := E)).injective.nontrivial
  letI : Nontrivial (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :=
    (affineTopologicalMackeyQuotientLpEquiv hxi).injective.nontrivial
  apply UnitaryRepresentation.isTopologicallyIrreducible_of_hasSchurProperty
  exact affineTopologicalMackeySectionInducedLpUnitaryRepresentation_hasSchurProperty hxi

/-- Theorem 2.5 of arXiv:2405.13682: the scalar quasi-regular representation of the full affine
group is topologically irreducible.

The Fourier-conjugated representation has now been transported first to the intrinsic `L²` space
on the conull nonzero-frequency subtype and then, through
`affineTopologicalMackeyQuotientHomeomorphDualOrbit`, to the actual homogeneous-space
`L²(G/H)`. Both transports have explicit inverse bounded intertwiners, and the homeomorphism is
proved equivariant for left translation and the dual action. The closed locally compact inducing
subgroup and its strongly continuous irreducible character representation are
`affineTopologicalMackeySubgroup` and `affineTopologicalMackeyUnitaryRepresentation`, with the
required translation and little-group restriction formulas.

The normalized equivariant-section realization of unitary induction is now constructed explicitly:
its reentry cocycle is `s(q)⁻¹ g s(g⁻¹q)`, its character phase is proved equal to the Fourier
phase, and the resulting unitary representation is proved equal to the transported homogeneous
model. The paper endpoint is derived from the commutant form of Folland Theorem 6.39 above. Its
translation-spectral, spectral-subspace, compact-kernel convolution continuity, compact-cutoff,
regular-section density, and 6.30 inducing-fiber inputs are complete, while its Folland-6.29
measurable lift with product integrability and convolution formula is the one remaining HA
placeholder. Mathlib's algebraic
`Representation.ind` is not the quasi-invariant Hilbert-space construction and Mathlib has no
imprimitivity theorem.
-/
theorem affineDataLpUnitaryRepresentation_isTopologicallyIrreducible :
    UnitaryRepresentation.IsTopologicallyIrreducible
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)) := by
  obtain ⟨xi, hxi⟩ : ∃ xi : E, xi ≠ 0 := exists_ne 0
  exact
    (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible_iff
      hxi).mp
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible
        hxi)


end LeanRidgelet
