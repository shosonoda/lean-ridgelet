import LeanRidgelet.OverviewHA
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

#doc (Manual) "Harmonic-analysis method: arXiv:2405.13682 implementation map" =>
%%%
file := "overview-ha"
%%%

This chapter follows Sonoda--Hashimoto--Ishikawa--Ikeda, *Deep Ridgelet Transform and Unified
Universality Theorem for Deep and Shallow Joint-Group-Equivariant Machines*
(arXiv:2405.13682), in publication order. It records article-facing coverage only; the next
chapter explains helper constructions and proofs in Lean dependency order. A node without a Lean
link is a deferred target and creates no assumption in the Lean project.

The formalized discovery principle is
$`\text{joint equivariance}\Rightarrow\text{intertwiners}\Rightarrow\text{commutant}
\Rightarrow\text{Schur scalarity}\Rightarrow\text{reconstruction}`.

*Section 2: the classical ridgelet formula and irreducibility*

:::definition "ha_depth_two_machine" (lean := "LeanRidgelet.affineRidgeArgument, LeanRidgelet.affineFeature, LeanRidgelet.affineFeature_jointInvariant, LeanRidgelet.affineBochnerSynthesis_intertwines, LeanRidgelet.affineBochnerRidgelet_intertwines")
*Definitions 2.1 and 2.2.* The affine ridge argument, the depth-two feature, its joint invariance,
and the synthesis/ridgelet Bochner covariance formulas are formalized. The bounded Euclidean
operators themselves are reused from the L2 theory.
:::

:::theorem "ha_classical_reconstruction" (lean := "LeanRidgelet.bochnerSynthesis_affineFeature_eq_euclideanDualRidgeletTransform, LeanRidgelet.bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform, LeanRidgelet.bochnerSynthesis_affineFeature_eq_classicalSynthesisIntegral, LeanRidgelet.affineBochner_reconstruction_of_euclidean, LeanRidgelet.networkSynthesis_ae_eq_bochnerSynthesis_affineFeature") (uses := "ha_depth_two_machine, ha_affine_classical_comparison_detail")
*Theorem 2.3.* At homogeneity index zero the affine depth-two Bochner synthesis and ridgelet are
the classical Euclidean dual ridgelet transform and ridgelet transform on the nose, and the
classical synthesis integral of the L2 track is the same Bochner integral. Any Euclidean
reconstruction identity therefore reconstructs the harmonic-analysis composite with the same
scalar. That identity enters as a hypothesis, as it does on the Fourier-slice side.
:::

:::definition "ha_unitary_irreducibility" (lean := "UnitaryRepresentation, UnitaryRepresentation.IsInvariant, UnitaryRepresentation.IsTopologicallyIrreducible")
*Unitary representations and topological irreducibility.* Closed invariant subspaces, rather than
algebraic subrepresentations, express the article's infinite-dimensional notion.
:::

:::theorem "ha_schur_lemma" (lean := "UnitaryRepresentation.hasSchurProperty_of_isTopologicallyIrreducible, UnitaryRepresentation.isTopologicallyIrreducible_of_hasSchurProperty, UnitaryRepresentation.isTopologicallyIrreducible_iff_hasSchurProperty") (uses := "ha_unitary_irreducibility")
*Theorem 2.4.* The infinite-dimensional unitary Schur lemma and its converse are proved. Continuous
positive-part spectral cutoffs produce a nontrivial closed invariant subspace without introducing
a Borel spectral-projection hypothesis.
:::

:::definition "ha_affine_representations" (lean := "LeanRidgelet.affineDataJacobian, LeanRidgelet.affineParameterJacobian, LeanRidgelet.affineDataLpUnitaryRepresentation, LeanRidgelet.affineParameterLpUnitaryRepresentation") (uses := "ha_unitary_irreducibility")
*Affine representations.* Data and parameter Lebesgue measures have reciprocal determinant
densities. Their square-root-corrected pullbacks give the two unitary $`L^2` representations.
*Deviation.* The article's invariant-measure presentation is extended to the quasi-invariant
affine measures actually used by the example.
:::

:::theorem "ha_affine_irreducibility" (lean := "LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_indicator_covariant, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_apply_ae, LeanRidgelet.affineTopologicalMackeyTranslationMultiplier, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_eq_multiplier, MeasureTheory.ContinuousLinearMap.commutes_indicatorLp_of_commutes_fourierCharacter, LeanRidgelet.affineMackey_commutes_indicator_of_commutes_translation, LeanRidgelet.affineMackeySmoothedVector_exists_continuousRepresentative, LeanRidgelet.affineMackey_regularSection_dense, LeanRidgelet.affineMackeyRegularSectionToLp_smul, LeanRidgelet.affineMackeyInducingFiber_eq_bot_iff, LeanRidgelet.affineMackeyInducingFiber_eq_top_of_ne_zero, LeanRidgelet.affineMackey_eq_bot_of_inducingFiber_eq_bot, LeanRidgelet.affineMackey_eq_top_of_regularSection_ne_zero, LeanRidgelet.affineMackey_closedSubspace_extreme_iff_inducingFiber_extreme, LeanRidgelet.affineMackey_systemInvariant_closedSubspace_eq_bot_or_top, LeanRidgelet.affineMackey_scalar_of_commutes_indicators, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_hasSchurProperty, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible, LeanRidgelet.affineDataLpUnitaryRepresentation_isTopologicallyIrreducible") (uses := "ha_affine_representations, ha_schur_lemma, mathlib_group_convolution_continuity, mathlib_bochner_integral_l2")
*Theorem 2.5.* The physical affine representation is related by invertible bounded intertwiners to
its Fourier, conull-orbit, homogeneous-space, and normalized-section induced models. The inducing
subgroup and its irreducible character, the quotient-orbit homeomorphism, the quasi-invariant
measure, the explicit induced action, its translation-character restriction, the equality with a
bundled Fourier-character multiplier, and the canonical indicator covariance are proved.
Finite-character density for an arbitrary finite measure and the resulting general $`L^2`
multiplier form of Theorem 4.44 are proved, upgrading the translation commutant to indicator
spectral projections. The continuous-functional-calculus and self-adjoint decomposition part of
Theorem 6.28 is also proved. For Lemma 6.29, compactly supported Haar probability kernels shrinking
to the identity are constructed, and their smoothing stays in an invariant closed subspace and
converges in `L²`. Indicator stability is upgraded to compactly supported continuous multiplier
stability; Urysohn cutoff and a diagonal argument then prove regular-section density from a
continuous representative of each smoothed vector. Compact-kernel group-convolution continuity and
the pointwise-representative theorem for `L²`-valued Bochner integrals are proved generally. The
needed part of Lemma 6.30, identifying the extreme cases of a system-invariant closed subspace with
those of the extracted inducing fiber, is proved from translated sections, transitivity, and a
countable subcover of nonvanishing sets. The Lemma 6.29 measurable lift, the slice integrability of
its smoothing integrand, and the identification of the resulting pointwise convolution with the
Bochner-smoothed class are proved as well, so the chapter has no named `sorry` root. The
one-dimensional fiber classification and the combination of the two lemmas are proved. Schur's converse derives induced irreducibility and the
transports derive the article theorem. The group is the full $`GL(m)` affine group: positive
dilations alone would leave two frequency orbits in dimension one.
:::

*Section 3: joint equivariance and the reconstruction theorem*

:::definition "ha_induced_representations" (lean := "LeanRidgelet.invariantLpUnitaryRepresentation, LeanRidgelet.quasiInvariantLpUnitaryRepresentation, LeanRidgelet.twistedQuasiInvariantLpUnitaryRepresentation") (uses := "ha_unitary_irreducibility")
*Definition 3.1.* Invariant and strongly quasi-invariant pullbacks are bundled on Bochner $`L^2`;
the latter use the square-root Radon--Nikodym correction. A measurable unimodular cocycle supplies
the character-twisted form used by the affine induced model.
:::

:::definition "ha_joint_equivariance" (lean := "LeanRidgelet.IsJointEquivariant")
*Definition 3.2.* A feature $`\phi:X\times\Xi\to Y` is joint-$`G`-equivariant when the simultaneous
action on input and parameter agrees with the output action.
:::

:::lemma_ "ha_classical_equivariance" (lean := "LeanRidgelet.IsEquivariant, LeanRidgelet.IsEquivariant.isJointEquivariant_of_fixed") (uses := "ha_joint_equivariance")
*Remark 3.3.* Ordinary equivariance is the special case of a fixed parameter.
:::

:::lemma_ "ha_orbit_feature" (lean := "LeanRidgelet.orbitFeature, LeanRidgelet.isJointEquivariant_orbitFeature") (uses := "ha_joint_equivariance")
*Lemma 3.4.* An arbitrary seed produces a joint-equivariant orbit feature.
:::

:::lemma_ "ha_deep_feature" (lean := "LeanRidgelet.jointCascade, LeanRidgelet.IsJointEquivariant.jointCascade, LeanRidgelet.DeepParameters, LeanRidgelet.deepFeature, LeanRidgelet.isJointEquivariant_deepFeature") (uses := "ha_joint_equivariance")
*Lemma 3.5.* Binary cascade preserves joint equivariance, and a dependent finite tuple extends the
calculation to heterogeneous depth.
:::

:::definition "ha_joint_machine" (lean := "LeanRidgelet.JointEquivariantMachine") (uses := "ha_induced_representations, ha_joint_equivariance")
*Definition 3.6.* A bounded machine is a continuous intertwining map from the parameter
representation to the data representation.
:::

:::lemma_ "ha_machine_intertwines" (lean := "LeanRidgelet.bochnerSynthesis_intertwines, LeanRidgelet.bochnerSynthesis_quasi_intertwines, LeanRidgelet.bochnerSynthesisIntertwiningMap, LeanRidgelet.bochnerSynthesisQuasiIntertwiningMap") (uses := "ha_joint_machine")
*Lemma 3.7.* Bochner change of variables and joint equivariance make synthesis an intertwiner.
The quasi-invariant form records the reciprocal Jacobian balance required by affine actions.
:::

:::definition "ha_ridgelet_transform" (lean := "LeanRidgelet.JointEquivariantRidgelet") (uses := "ha_induced_representations, ha_joint_equivariance")
*Definition 3.8.* A bounded ridgelet transform is a continuous intertwining map in the reverse
direction.
:::

:::lemma_ "ha_ridgelet_intertwines" (lean := "LeanRidgelet.bochnerRidgelet_intertwines, LeanRidgelet.bochnerRidgelet_quasi_intertwines, LeanRidgelet.bochnerRidgeletIntertwiningMap, LeanRidgelet.bochnerRidgeletQuasiIntertwiningMap") (uses := "ha_ridgelet_transform")
*Lemma 3.9.* The corresponding invariant or quasi-invariant change of variables makes ridgelet
analysis an intertwiner.
:::

:::theorem "ha_main_reconstruction" (lean := "LeanRidgelet.bochnerReconstructionQuasiIntertwiningMap, LeanRidgelet.ha_reconstruction_of_hasSchurProperty, LeanRidgelet.ha_reconstruction_formula") (uses := "ha_schur_lemma, ha_machine_intertwines, ha_ridgelet_intertwines")
*Theorem 3.10.* The composite $`M_\phi R_\psi` belongs to the commutant and is therefore
$`c_{\phi,\psi}\,\mathrm{id}`. The formalization covers both individually bounded intertwiners and
the weaker hypothesis that only the pointwise composite has a bounded extension. *Deviation.* Over
$`\mathbb C`, the displayed scalar is sesquilinear rather than bilinear in the two features.
:::

:::theorem "ha_normalized_right_inverse" (lean := "LeanRidgelet.ha_normalizedRidgelet_rightInverse") (uses := "ha_main_reconstruction")
*Remark 3.11.* A nonzero reconstruction scalar gives the normalized ridgelet right inverse.
:::

*Sections 4--8: architectures and discussion*

:::corollary "ha_deep_ridgelet" (lean := "LeanRidgelet.deepRidgelet_reconstruction_formula, LeanRidgelet.deepRidgelet_normalized_rightInverse") (uses := "ha_deep_feature, ha_main_reconstruction")
*Corollary 4.1.* The reconstruction theorem applies to a heterogeneous finite cascade.
:::

:::definition "ha_fully_connected_feature" (lean := "LeanRidgelet.deepFullyConnectedFeature, LeanRidgelet.deepFullyConnectedFeature_endpoint_equivariant") (uses := "ha_deep_feature")
*Section 5 feature covariance.* The affine input action is absorbed by the first parameter and the
output action by the final readout; both identities propagate through arbitrary finite depth.
:::

:::lemma_ "ha_vector_affine_irreducibility" (lean := "LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation, LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation_apply_ae, LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation_isTopologicallyIrreducible_of") (uses := "ha_affine_irreducibility, ha_fully_connected_feature")
*Lemma 5.1.* The concrete complexified $`O(m)\times\operatorname{Aff}(m)` action on vector-valued
$`L^2` is implemented. Finite coordinate reconstruction and two Schur arguments prove the needed
finite-output product irreducibility, conditional only on the scalar affine endpoint.
:::

:::theorem "ha_group_convolution_reconstruction" (lean := "LeanRidgelet.groupConvolutionalFeature, LeanRidgelet.groupConvolutionalFeature_equivariant, LeanRidgelet.groupConvolutional_synthesis_ridgelet") (uses := "ha_deep_ridgelet")
*Theorem 6.1.* The group-convolutional orbit lift reduces at the identity to the base machine, so a
base reconstruction identity transports to the group-valued output.
:::

:::definition "ha_quadratic_feature" (lean := "LeanRidgelet.QuadraticParameter, LeanRidgelet.quadraticFeature, LeanRidgelet.quadraticParameterLinearEquiv, LeanRidgelet.quadraticArgument_invariant, LeanRidgelet.quadraticFeature_invariant, LeanRidgelet.quadraticParameterMulAction, LeanRidgelet.det_quadraticParameterLinearEquiv, LeanRidgelet.quadraticParameterJacobian, LeanRidgelet.quadraticParameterJacobian_cocycle, LeanRidgelet.quadraticParameter_group_map_eq_withDensity, LeanRidgelet.quadraticParameterLpUnitaryRepresentation, LeanRidgelet.quadraticRelativeMeasure, LeanRidgelet.quadraticRelativeParameterLpUnitaryRepresentation, LeanRidgelet.quadraticRelativeBochnerSynthesis_intertwines, LeanRidgelet.quadraticRelativeBochnerRidgelet_intertwines, LeanRidgelet.quadratic_reconstruction") (uses := "ha_joint_equivariance, ha_main_reconstruction")
*Section 7.* A quadratic form followed by an arbitrary activation, with symmetric coefficients
represented as self-adjoint continuous endomorphisms. The parameter action of the affine group is
linear, the scalar argument of the activation is invariant under the data and parameter actions
together, and the action law follows because a parameter is determined by its scalar functional.
The parameter determinant factors through the congruence on symmetric coefficients; that factor is
kept abstract, since only its non-vanishing is used, and it is exactly the Radon--Nikodym density
of the parameter action, so the quasi-invariant parameter measure and its `L²` representation are
obtained from it. That measure is then replaced by a relatively invariant one, weighted by a power of
the determinant of the symmetric coefficient, which restores the balance the quasi-invariant Bochner
identities need; with it the synthesis and ridgelet identities hold in their untwisted form, and
Schur's lemma applied to the proved irreducibility of the data representation gives the
reconstruction scalar and the right inverse. Boundedness of the two operators is the one input.
:::

Section 8 discusses scope and consequences and adds no numbered formal target.

*Appendices A--E*

:::lemma_ "ha_induced_unitarity" (lean := "LeanRidgelet.invariantLpUnitaryRepresentation, LeanRidgelet.quasiInvariantLpUnitaryRepresentation") (uses := "ha_induced_representations")
*Lemmas A.1 and A.2.* The invariant and strongly quasi-invariant $`L^2` constructions supply the
unitary representations used in the main text.
:::

:::lemma_ "ha_tensor_irreducibility" (lean := "LeanRidgelet.fullyConnectedLpUnitaryRepresentation_isTopologicallyIrreducible_of") (uses := "ha_vector_affine_irreducibility")
*Lemma A.3.* The finite-dimensional-output case needed in Section 5 is proved directly on Bochner
$`L^2`. A general completed-Hilbert-tensor theorem remains optional upstream work.
:::

:::lemma_ "ha_group_convolution_reduction" (lean := "LeanRidgelet.groupConvolutionalSynthesis_eq_orbit, LeanRidgelet.groupConvolutionalRidgelet_eq_base") (uses := "ha_group_convolution_reconstruction")
*Lemmas A.4 and A.5.* Synthesis is the orbit lift of base synthesis, and the identity-component
ridgelet is the base ridgelet.
:::

:::definition "ha_appendix_depth_two" (uses := "ha_depth_two_machine, ha_classical_reconstruction")
*Appendix B.* The depth-two fully-connected example expands the definitions and reconstruction
calculation used in Section 2; the comparison of Theorem 2.3 above now covers it at homogeneity
index zero.
:::

:::lemma_ "ha_bochner_preliminaries"
*Lemmas C.1--C.3.* Mathlib's Bochner integrability and dominated/bounded convergence results will
be cited directly rather than restated.
:::

:::theorem "ha_uniform_discretization" (uses := "ha_joint_machine, ha_bochner_preliminaries")
*Theorem C.4.* Uniform approximation of a compactly supported Bochner integral by finite networks
remains to be formalized with a valid bounded-continuous or compact-domain norm.
:::

:::lemma_ "ha_boundedness_criteria" (uses := "ha_joint_machine, ha_ridgelet_transform")
*Lemmas D.1 and D.2.* The remaining Hilbert--Schmidt-type boundedness criteria are deferred. The
Euclidean network needed in the main examples already uses the stronger existing L2 theory.
:::

:::theorem "ha_affine_appendix" (uses := "ha_affine_irreducibility")
*Lemma E.1 and Theorem E.2.* Their affine irreducibility conclusion is reached through the Mackey
model above. The approximate identity, invariant-subspace convergence, compact-kernel convolution
continuity, quotient cutoff, and density needed by Folland 6.29 are formalized, together with the
measurable lift, the slice integrability of its smoothing integrand, and the convolution formula
that complete the lemma, as is the exact 6.30 inducing-fiber correspondence.
:::
