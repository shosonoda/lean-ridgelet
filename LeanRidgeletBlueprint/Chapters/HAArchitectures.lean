import LeanRidgelet.HA.Deep
import LeanRidgelet.HA.FullyConnected
import LeanRidgelet.HA.FullyConnectedIrreducibility
import LeanRidgelet.HA.GroupConvolution
import LeanRidgelet.HA.L2Bridge
import LeanRidgelet.HA.Operators
import LeanRidgelet.HA.ClassicalComparison
import LeanRidgelet.HA.L2BridgeEquivariance
import LeanRidgelet.HA.Reconstruction
import LeanRidgelet.HA.AdjointReconstruction
import LeanRidgelet.HA.BochnerAdjoint
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

#doc (Manual) "Harmonic-analysis method: reconstruction and architectures" =>
%%%
file := "ha-architectures"
%%%

Once the intertwining operators of the representation layer are available, the reconstruction theorem is a short Schur argument, and every architecture of the article whose parameter space is a copy of the data space is an instance of it. This chapter covers the commutant reduction and the normalized right inverse, the finite cascade, the fully-connected and group-convolutional networks, the reuse of the existing $`L^2` operator layer, the comparison with the classical transforms, and the analytic comparisons that remain. Section 7, whose parameter space is the space of symmetric coefficients, has its own chapter.

*Intertwiners and the commutant*

:::definition "ha_intertwiner_operators" (lean := "LeanRidgelet.JointEquivariantMachine, LeanRidgelet.JointEquivariantRidgelet") (uses := "ha_bochner_intertwining_detail")
*Bounded operator API.* Synthesis and ridgelet transforms are continuous intertwining maps in
opposite directions. The preceding constructors supply values of these types once bounded maps
with the displayed coordinate formulas have been proved.
:::

:::lemma_ "ha_reconstruction_commutant" (lean := "LeanRidgelet.jointReconstructionOperator, LeanRidgelet.jointReconstructionOperator_apply, LeanRidgelet.jointReconstructionOperator_commutes") (uses := "ha_intertwiner_operators")
*Composition.* The composite of the two intertwiners is a bounded endomorphism of the data space,
and the intertwining laws prove that it commutes with every represented group element.
:::

:::theorem "ha_reconstruction_detail" (lean := "LeanRidgelet.ha_reconstruction_of_hasSchurProperty_of_intertwiner, LeanRidgelet.ha_reconstruction_of_intertwiner, LeanRidgelet.ha_reconstruction_of_hasSchurProperty, LeanRidgelet.ha_reconstruction_formula, LeanRidgelet.ha_normalizedRidgelet_rightInverse") (uses := "ha_schur_detail, ha_reconstruction_commutant")
*Schur reduction and normalization.* The theorem with `HasSchurProperty` as an explicit hypothesis
is proved without placeholders, for both an arbitrary bounded endomorphism intertwiner and a
composition of two bounded intertwiners. The topological-irreducibility endpoints are derived from
the Schur declaration, and a nonzero scalar gives the normalized ridgelet right inverse by
linearity.
:::

*Architectures after the abstract reconstruction theorem*

:::theorem "ha_adjoint_reconstruction_detail" (lean := "LeanRidgelet.UnitaryRepresentation.adjoint_coe, LeanRidgelet.adjointIntertwiner, LeanRidgelet.adjointIntertwiner_toContinuousLinearMap, LeanRidgelet.adjointReconstructionOperator, LeanRidgelet.adjointReconstructionOperator_apply, LeanRidgelet.inner_adjointReconstructionOperator, LeanRidgelet.ha_adjoint_reconstruction, LeanRidgelet.ha_adjoint_reconstruction_of_ne_zero, LeanRidgelet.bochnerSynthesis_eq_adjoint_bochnerRidgelet") (uses := "ha_reconstruction_detail, ha_intertwiner_operators")
*Reconstruction from the adjoint.* Take the machine to be the adjoint of the ridgelet transform. Then the composite is positive, Schur makes it a scalar, and the scalar is $`\|Rf\|^2/\|f\|^2` — real, nonnegative, and nonzero as soon as the transform is. One datum with nonzero transform gives the reconstruction formula outright.
:::

This is how coorbit theory and the theory of generalized wavelet transforms get their reconstruction formula, and it dissolves the compactness obstruction recorded below rather than working around it. That obstruction came from treating the synthesis and the analysis as *independent* integral operators, each with its own square-integrable kernel; here there is no independent synthesis operator, so no kernel is assumed square integrable, and a composite equal to a nonzero multiple of the identity makes the transform a multiple of an isometry, which in infinite dimensions is simply not compact.

Three facts carry it. The adjoint of an intertwiner of unitary representations is an intertwiner the other way — take adjoints in the intertwining law and the group element inverts, which costs nothing since a group element ranges over the group with its inverse. Pairing the composite with a datum gives the squared norm of the datum's transform, which is what makes the scalar real and nonnegative. And Schur applies to the composite because it is an intertwining endomorphism of the data representation, whose topological irreducibility is proved in this development.

In the notation of Berge's *A Primer on Coorbit Theory* (arXiv:2101.05232), the analysis operator is the wavelet transform $`\mathcal{W}_g f(x)=\langle f,\pi(x)g\rangle`, its adjoint is the weak integral $`\mathcal{W}_g^*(F)=\int F(x)\pi(x)g\,dx` of Proposition 2.33 there, and the reconstruction formula is Corollary 2.34. What supplies the constant there is the Duflo--Moore orthogonality relation for a square-integrable representation; here Schur's lemma supplies it, so neither square integrability of the representation nor an admissible vector is assumed.

The cost is that the machine is the adjoint rather than an independently chosen synthesis integral, and the identification that makes it precise is also proved here: for a *single* feature the Bochner synthesis integral and the Bochner ridgelet transform are adjoint to each other, by one exchange of the order of integration — both pairings are the double integral of $`\overline{\gamma(\xi)}\,\overline{\varphi(x,\xi)}\,f(x)`, one taken parameter-first and the other data-first. So the abstract adjoint *is* the network's own synthesis integral, provided the synthesis feature is the analysis feature. With a different synthesis feature the two are not adjoint, which is the precise sense in which this route reconstructs with the network whose activation is the analysis feature. Fixing the activation in advance is the harder problem, and it is the one the boundedness appendix is about.

:::lemma_ "ha_deep_cascade_detail" (lean := "LeanRidgelet.DeepParameters, LeanRidgelet.DeepParameters.smul, LeanRidgelet.DeepParameters.smul_nil, LeanRidgelet.DeepParameters.smul_snoc, LeanRidgelet.deepFeature, LeanRidgelet.deepFeature_zero, LeanRidgelet.deepFeature_succ, LeanRidgelet.isJointEquivariant_deepFeature, LeanRidgelet.deepRidgelet_reconstruction_formula, LeanRidgelet.deepRidgelet_normalized_rightInverse") (uses := "ha_joint_equivariance_constructors, ha_reconstruction_detail")
*Finite heterogeneous cascades.* A snoc-indexed dependent tuple stores exactly one parameter per
layer while allowing every intermediate type to change. Its componentwise group action is a
`MulAction`; induction lifts binary joint equivariance to the full cascade. Corollary 4.1 then
reuses the abstract bounded-intertwiner reconstruction and normalization results.
:::

:::definition "ha_l2_operator_bridge_detail" (lean := "LeanRidgelet.l2NetworkSynthesisMachine, LeanRidgelet.l2RidgeletIntertwiningMap, LeanRidgelet.norm_l2NetworkSynthesisMachine_le, LeanRidgelet.l2_jointReconstructionOperator_eq") (uses := "ha_intertwiner_operators, ha_deep_cascade_detail")
*L2 boundedness reuse.* Given covariance under chosen representations, the existing L2
`networkSynthesis` and `ridgeletOperator` become HA continuous intertwiners. Their concrete norm
bound and exact `networkSynthesis ∘ ridgeletOperator` identity are inherited directly; no second
Bochner boundedness proof or assumption structure is introduced.
:::

:::lemma_ "ha_fully_connected_detail" (lean := "LeanRidgelet.FullyConnectedParameter, LeanRidgelet.fullyConnectedFeature, LeanRidgelet.fullyConnectedInputParameterTransform, LeanRidgelet.fullyConnectedFeature_input_invariant, LeanRidgelet.fullyConnectedOutputParameterTransform, LeanRidgelet.fullyConnectedFeature_output_equivariant, LeanRidgelet.DeepParameters.mapFirst, LeanRidgelet.DeepParameters.mapLast, LeanRidgelet.deepFeature_mapFirst, LeanRidgelet.deepFeature_mapLast, LeanRidgelet.deepFullyConnectedFeature, LeanRidgelet.deepFullyConnectedFeature_endpoint_equivariant") (uses := "ha_deep_cascade_detail")
*Fully-connected endpoint covariance.* Linear maps replace matrices. Direct cancellation proves
that `(Lx+t, A L⁻¹, b+A L⁻¹t)` leaves the first layer unchanged, while composing the last readout
with the output linear equivalence transforms the final value. Separate first/last tuple maps and
two induction lemmas propagate these identities through every depth.
:::

:::lemma_ "ha_fully_connected_l2_representation_detail" (lean := "LeanRidgelet.affineDataLpUnitaryRepresentation_apply_ae_vector, LeanRidgelet.compLpL_intertwines_affineData, LeanRidgelet.lpPointwise_commute_affineData, LeanRidgelet.fullyConnectedLpUnitaryRepresentation, LeanRidgelet.fullyConnectedLpUnitaryRepresentation_apply_ae, LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation, LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation_apply_ae, LeanRidgelet.fullyConnectedLpUnitaryRepresentation_isTopologicallyIrreducible_of, LeanRidgelet.standardOrthogonalAffineLpUnitaryRepresentation_isTopologicallyIrreducible_of") (uses := "ha_fully_connected_detail, ha_affine_mackey_detail, mathlib_unitary_lp, mathlib_orthogonal_complexification")
*The Section 5 representation and Lemma 5.1 boundary.* The output representation is lifted
pointwise to Bochner $`L^2`; it commutes with the affine weighted pullback because a complex-linear
unitary commutes with the scalar Radon--Nikodym factor. Their commuting product gives the actual
representation on $`L^2(E;Y)` and its article-level a.e. formula. Entrywise complexification of
real orthogonal matrices now supplies the concrete standard $`O(m)` output factor, whose
irreducibility is proved independently; substituting it gives the article's
$`O(m)\times\operatorname{Aff}(m)` representation and matrix-level formula. Naturality of the
affine pullback under pointwise coordinate embeddings and projections lets Schur act on every
scalar matrix coefficient of an invariant orthogonal projection. Finite coordinate
reconstruction makes that projection the lift of a fixed output operator, to which output Schur
applies. This closes the Folland-7.12 finite-output step without a completed Hilbert tensor
product; the concrete conclusion now depends only on the separate scalar affine
induced-system convolution-regularity placeholder.
:::

:::theorem "ha_group_convolution_detail" (lean := "LeanRidgelet.groupConvolutionalFeature, LeanRidgelet.IsGroupConvolutionEquivariant, LeanRidgelet.groupConvolutionalFeature_equivariant, LeanRidgelet.groupConvolutionalSynthesis, LeanRidgelet.groupConvolutionalSynthesis_eq_orbit, LeanRidgelet.groupConvolutionalRidgelet, LeanRidgelet.groupConvolutionalRidgelet_eq_base, LeanRidgelet.groupConvolutional_reconstruction, LeanRidgelet.groupConvolutional_synthesis_ridgelet") (uses := "ha_fully_connected_l2_representation_detail, ha_l2_operator_bridge_detail")
*Group-convolution reduction.* The function-valued feature is the orbit lift
$`g\mapsto υ(g)[φ(g^{-1}x,ξ)]`. Representation multiplication proves equivariance; a linear
isometry commutes through the Bochner integral to identify GCN synthesis with the orbit lift of
base synthesis. The ridgelet reads only the identity component, and the two identities transport
base reconstruction to Theorem 6.1.
:::
:::theorem "ha_affine_classical_comparison_detail" (lean := "LeanRidgelet.bochnerSynthesis_affineFeature_eq_euclideanDualRidgeletTransform, LeanRidgelet.bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform, LeanRidgelet.bochnerSynthesis_affineFeature_eq_classicalSynthesisIntegral, LeanRidgelet.affineBochner_reconstruction_of_euclidean, LeanRidgelet.networkSynthesis_ae_eq_bochnerSynthesis_affineFeature, LeanRidgelet.isAddHaarMeasure_volume_ridgeParameter, LeanRidgelet.quasiMeasurePreserving_affineData_inv, LeanRidgelet.quasiUnitaryPullbackAction_affineData_congr_ae, LeanRidgelet.affineSchwartzParameterAction, LeanRidgelet.affineSchwartzParameterAction_coe, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_ae_intertwines, LeanRidgelet.euclideanRidgeletTransform_intertwines, LeanRidgelet.classicalRidgeletIntegral_eq_euclideanRidgeletTransform, LeanRidgelet.classicalRidgeletIntegral_intertwines") (uses := "ha_affine_jacobian_detail, ha_l2_operator_bridge_detail")
*Comparison with the classical transforms.* The affine depth-two Bochner pair, the Euclidean ridgelet pair of the L1 track at homogeneity index zero, and the classical synthesis integral of the L2 track are the same integrals.
:::

Nothing is transported: the ridgelet parameter space of the classical development and the affine parameter space of this one are the same type, and the ridge argument of the feature is syntactically the inner product minus the offset. At index zero the classical weight is one, so even the measures agree, and each of the three identifications is definitional up to that weight. There is no Fourier-normalization gap here, because the depth-two formula contains no Fourier transform; the convention enters only the reconstruction constants, whose comparison already exists between the L1 and Fourier-slice tracks.

The reconstruction identity itself is a hypothesis rather than a conclusion, matching the Fourier-slice group-convolution theorem, and for the same reason: the L1 endpoints are stated at homogeneity index one as limits of transforms truncated to annuli, whereas the Bochner synthesis is one absolutely convergent integral, and the dominated-convergence step between them fails for the admissible pairs the L1 track constructs, where the ridgelet transform is only square-integrable against the weighted parameter measure. Given the hypothesis, the composite is reconstructed with the same scalar. The last identification ties the bounded operator of the L2 bridge to the Bochner formula, and transporting the affine intertwining identity through it gives the equivariance of the classical network synthesis on the Schwartz compatibility domain, together with the exact equivariance of the classical ridgelet integral. It does not, however, discharge the equivariance hypotheses the L2 bridge carries. Those are stated over the transported-coordinate parameter space, where the bias variable has been replaced by the fiber frequency, and the affine parameter action lives on functions of the direction and the bias; the two are different Hilbert spaces and no unitary identification of them exists here, since a translation of the bias becomes a modulation in the fiber. Two smaller mismatches compound it: the bridge quantifies over every square-integrable class while the comparison reaches only the Schwartz domain, and there is no ridgelet-side comparison for the transported operator at all.
:::theorem "ha_l2_integral_detail" (uses := "ha_affine_jacobian_detail, ha_l2_operator_bridge_detail")
*Remaining analytic comparison.* Identify the L2 transported-coordinate operators with each
classical affine/deep Bochner realization on the appropriate compatibility domain. Architectures
with genuinely different parameter spaces continue to use the explicit bounded-extension bridge.
:::

:::theorem "ha_architecture_detail" (uses := "ha_l2_integral_detail, ha_group_convolution_detail, ha_affine_mackey_detail")
*Remaining architectures and approximation.* The general Hilbert--Schmidt criterion and the
finite-sum discretization are now proved in the Mathlib candidate layer; what remains is to
instantiate them at the parameter spaces the L2 bridge does not cover, and to derive the quadratic
synthesis and ridgelet pair from its parameter representation. Difficult endpoints remain named
declarations rather than assumption objects.
:::
