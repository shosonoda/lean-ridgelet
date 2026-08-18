import LeanRidgelet.HA.BochnerIntertwining
import LeanRidgelet.HA.InducedRepresentation
import LeanRidgelet.HA.JointEquivariance
import LeanRidgelet.ToMathlib.LieGroup.Schur
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
-- Verso directive headers and display mathematics must stay on one physical line.
set_option linter.style.longLine false
set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Harmonic-analysis method: representations and intertwiners" =>
%%%
file := "ha-representations"
%%%

This chapter and the two that follow describe the implementation of the harmonic-analysis method in
Lean dependency order; the publication-order roadmap is the `overview-ha` chapter. The Lean project
separates `OverviewHA` from the detail import carrier `LeanRidgelet.HA`, the modules under
`LeanRidgelet/HA/`, and the Mathlib-only Schur development under `LeanRidgelet/ToMathlib/LieGroup/`.
This chapter covers the layers that precede any concrete architecture: unitary representations and
Schur's lemma, pointwise joint equivariance, induced $`L^2` representations, and the Bochner
integral identities that turn them into intertwining operators.

*Unitary representations and the Hilbert-space Schur lemma*

:::definition "ha_unitary_representation_detail" (lean := "UnitaryRepresentation, UnitaryRepresentation.toContRepresentation, UnitaryRepresentation.IsInvariant, UnitaryRepresentation.IsTopologicallyIrreducible")
*The representation layer.* A unitary representation is a monoid homomorphism into the unitary
group of bounded operators. Forgetting unitarity produces Mathlib's `ContRepresentation`; closed
submodules state topological irreducibility without strengthening it to algebraic irreducibility.
:::

:::theorem "ha_schur_detail" (lean := "UnitaryRepresentation.Commutes, UnitaryRepresentation.isInvariant_iff_starProjection_commutes, UnitaryRepresentation.Commutes.adjoint, UnitaryRepresentation.exists_nonzero_orthogonal_cutoffs_of_isSelfAdjoint_not_scalar, UnitaryRepresentation.exists_nontrivial_spectralSubspace_of_isSelfAdjoint_not_scalar, UnitaryRepresentation.exists_scalar_of_isSelfAdjoint_of_commutes, UnitaryRepresentation.closedSubmodule_complex_eq_bot_or_top, UnitaryRepresentation.hasSchurProperty_of_isTopologicallyIrreducible, UnitaryRepresentation.isTopologicallyIrreducible_of_hasSchurProperty, UnitaryRepresentation.isTopologicallyIrreducible_iff_hasSchurProperty") (uses := "ha_unitary_representation_detail")
*The upstream candidate.* Folland's proof is split into mechanically checkable pieces: invariant
closed subspaces correspond to commuting orthogonal projections, the commutant is adjoint-closed,
and real and imaginary self-adjoint parts are scalar. The nontrivial spectral subspace is the range
closure of a continuous positive-part cutoff. A second orthogonal nonzero cutoff proves that this
closure is proper, while continuous-functional-calculus commutation makes its projection belong to
the commutant. Conversely, on a nontrivial Hilbert space the Schur property makes the orthogonal projection onto
every invariant closed subspace scalar; idempotence forces that scalar to be zero or one. Hence
topological irreducibility and scalarity of the commutant are equivalent.
:::

*Joint-equivariant maps before analysis*

:::definition "ha_joint_equivariance_detail" (lean := "LeanRidgelet.IsJointEquivariant, LeanRidgelet.IsEquivariant")
*The pointwise predicate.* This layer assumes only group actions and contains no topology, measure,
or integrability. It therefore exposes the algebra shared by all architectures without committing
to a particular $`L^2` realization.
:::

:::lemma_ "ha_joint_equivariance_constructors" (lean := "LeanRidgelet.IsEquivariant.isJointEquivariant_of_fixed, LeanRidgelet.orbitFeature, LeanRidgelet.isJointEquivariant_orbitFeature, LeanRidgelet.jointCascade, LeanRidgelet.IsJointEquivariant.jointCascade") (uses := "ha_joint_equivariance_detail")
*Constructors.* Fixed parameters recover ordinary equivariance, an arbitrary seed produces an
orbit feature, and binary cascade preserves joint equivariance.
:::

*Induced $`L^2` representations and Bochner intertwiners*

:::definition "ha_induced_l2_detail" (lean := "LeanRidgelet.quasiRegularAction, LeanRidgelet.quasiRegularAction_mul, LeanRidgelet.radonNikodymWeight, LeanRidgelet.radonNikodymWeight_mul, LeanRidgelet.invariantLpUnitaryRepresentation, LeanRidgelet.invariantLpUnitaryRepresentation_apply_ae, LeanRidgelet.quasiRegularAction_lintegral_enorm_sq, LeanRidgelet.quasiRegularAction_eLpNorm_two, LeanRidgelet.quasiRegularAction_memLp_two, LeanRidgelet.quasiInvariantLpLinearIsometry, LeanRidgelet.quasiInvariantLpUnitaryRepresentation, LeanRidgelet.quasiInvariantLpUnitaryRepresentation_apply_ae, LeanRidgelet.twistedQuasiInvariantLpLinearIsometryEquiv, LeanRidgelet.twistedQuasiInvariantLpLinearIsometryEquivMonoidHom, LeanRidgelet.twistedQuasiInvariantLpUnitaryRepresentation, LeanRidgelet.twistedQuasiInvariantLpUnitaryRepresentation_apply_ae") (uses := "ha_unitary_representation_detail")
*Measure layer.* Mathlib's measure-preserving composition API gives the invariant-measure unitary
representation on `Lp`. Folland's square-root Radon--Nikodym multiplier is defined and its group
law follows from the cocycle. For the strongly quasi-invariant case, the `withDensity` lintegral
formula proves norm preservation, `Measure.QuasiMeasurePreserving` controls representatives under
composition, `MemLp.toLp` descends the action, and the inverse group element proves surjectivity.
For a measurable unimodular multiplier cocycle, Mathlib's `Lp` multiplier isometry composes with
this pullback; a.e. representative formulas prove the group law and give the corresponding
character-twisted unitary representation.
:::

:::lemma_ "ha_bochner_intertwining_detail" (lean := "MeasureTheory.integral_eq_integral_smul_comp_smul_of_map_eq_withDensity, LeanRidgelet.bochnerSynthesis, LeanRidgelet.bochnerRidgelet, LeanRidgelet.bochnerSynthesis_intertwines, LeanRidgelet.bochnerRidgelet_intertwines, LeanRidgelet.bochnerSynthesis_quasi_intertwines, LeanRidgelet.bochnerRidgelet_quasi_intertwines, LeanRidgelet.bochnerSynthesisIntertwiningMap, LeanRidgelet.bochnerRidgeletIntertwiningMap, LeanRidgelet.bochnerSynthesisQuasiIntertwiningMap, LeanRidgelet.bochnerRidgeletQuasiIntertwiningMap, LeanRidgelet.bochnerReconstructionQuasiIntertwiningMap, LeanRidgelet.bochnerSynthesis_quasi_intertwines_of_character, LeanRidgelet.bochnerRidgelet_quasi_intertwines_of_character, LeanRidgelet.bochnerReconstruction_quasi_intertwines_of_character, LeanRidgelet.bochnerReconstruction_commutes_of_character, LeanRidgelet.character_eq_one_of_balance_of_mul_self_eq_one") (uses := "ha_induced_l2_detail, ha_joint_equivariance_constructors, mathlib_quasi_invariant_integral")
*Integral-to-operator bridge.* Measure-preserving changes of variables give the invariant Bochner
synthesis and ridgelet identities. For a strongly quasi-invariant measure, a general `withDensity`
change-of-variables theorem inserts the Jacobian; its product with the inverse square-root
representation weight leaves the complementary square root, which the explicit data/parameter
balance identifies with the weight on the other side. Joint equivariance then turns both pointwise
identities, and any bounded coordinate realization of them, into Mathlib continuous intertwining
maps. A separate constructor starts with a bounded extension of the pointwise *composite* and
proves that it is an endomorphism intertwiner without requiring either intermediate integral
operator to be bounded.
:::

The balance hypothesis of the quasi-invariant identities — that the parameter density is the reciprocal of the data density — is exactly what the affine ridge feature satisfies and the quadratic feature of Section 7 does not. Replacing it by a balance up to a scalar character shows what goes wrong. Both the synthesis and the ridgelet then pick up the *same* factor, not reciprocal ones, because the factor is the product of the two square-root densities in either order; so the composite carries its square rather than cancelling it. Requiring that square to be one forces the character itself to be one, which is the exactly balanced case again, and that implication is proved here rather than asserted. The consequence is negative and worth recording: for a feature whose densities are out of balance, the composite of synthesis with ridgelet is not a commutant element of the data representation, and the reconstruction argument does not apply to it.
