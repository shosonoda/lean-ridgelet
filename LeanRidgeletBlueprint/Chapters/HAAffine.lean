import LeanRidgelet.HA.Affine
import LeanRidgelet.HA.AffineFourier
import LeanRidgelet.HA.AffineFrequency
import LeanRidgelet.HA.AffineIrreducibility
import LeanRidgelet.HA.AffineMackey
import LeanRidgelet.HA.AffineMackeyInduction
import LeanRidgelet.HA.AffineGroupHaar
import LeanRidgelet.HA.AffineMackeyLift
import LeanRidgelet.HA.AffineMackeySmoothing
import LeanRidgelet.HA.AffineMackeyMeasure
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

#doc (Manual) "Harmonic-analysis method: the affine Mackey model" =>
%%%
file := "ha-affine"
%%%

The affine group is the concrete instance that Theorem 2.5 of arXiv:2405.13682 needs, and it is
also where the analysis is hardest. This chapter follows the Lean dependency order of the affine
layer: the Jacobian and the two quasi-invariant $`L^2` representations, the explicit frequency
action, the group and orbit input of the Mackey machine, the homogeneous-space model and its
quasi-invariant character twist, the normalized-section realization of unitary induction, and the
inducing fiber of the imprimitivity argument.

:::theorem "ha_affine_jacobian_detail" (lean := "LeanRidgelet.affineParameterLinearEquiv, LeanRidgelet.affineRidgeArgument_invariant, LeanRidgelet.det_affineParameterLinearEquiv, LeanRidgelet.affineDataJacobian, LeanRidgelet.affineParameterJacobian, LeanRidgelet.affine_synthesis_radonNikodym_balance, LeanRidgelet.affine_ridgelet_radonNikodym_balance, LeanRidgelet.affineDataLpUnitaryRepresentation, LeanRidgelet.affineParameterLpUnitaryRepresentation, LeanRidgelet.affineBochnerSynthesis_intertwines, LeanRidgelet.affineBochnerRidgelet_intertwines") (uses := "ha_bochner_intertwining_detail, mathlib_affine_haar")
*Concrete affine instance.* Writing $`g(x)=Lx+t`, the parameter action is the block
lower-triangular map $`(a,b)\mapsto(L^{-T}a,b+\langle t,L^{-T}a\rangle)`. Its determinant is
`$(\det L)^{-1}`. Additive Haar measure therefore has reciprocal data/parameter densities
`$\lVert\det L\rVert` and $`\lVert\det L\rVert^{-1}`; their square roots give both balance laws.
The generic quasi-invariant construction now yields the two unitary $`L^2` representations and
the synthesis/ridgelet Bochner intertwining identities for the affine feature.
:::

:::theorem "ha_affine_frequency_detail" (lean := "LeanRidgelet.affineDualAction, LeanRidgelet.affineDualJacobian, LeanRidgelet.affineDualAction_map_eq_withDensity, LeanRidgelet.affineDualPullbackLpUnitaryRepresentation, LeanRidgelet.affineDualPullbackLpUnitaryRepresentation_apply_ae, LeanRidgelet.affineFrequencyPhase, LeanRidgelet.affineFrequencyPhase_translation, LeanRidgelet.affineFrequencyPhase_cocycle, LeanRidgelet.affineFrequencyPhaseMultiplier, LeanRidgelet.affineFrequencyLinearIsometryEquiv, LeanRidgelet.affineFrequencyLinearIsometryEquiv_apply_ae, LeanRidgelet.affineFourierLpUnitaryRepresentation_schwartz_input_ae, LeanRidgelet.affineFrequencyLinearIsometryEquiv_eq_fourierRepresentation, LeanRidgelet.affineFourierLpUnitaryRepresentation_apply_ae") (uses := "ha_affine_jacobian_detail, mathlib_fourier_affine, mathlib_lp_unimodular_multiplier, mathlib_unitary_conjugation")
*The explicit frequency action on all of `L²`.* The contragredient action has reciprocal
determinant density, so its corrected pullback is $`f(\xi)\mapsto |\det L|^{1/2}f(L^T\xi)`.
Multiplication by the norm-one translation character is a second unitary operator. Their composite
therefore exists directly on `Lp` classes and has the expected almost-everywhere representative.
The Fourier covariance calculation first proves equality with the Plancherel conjugate on
Schwartz functions; continuity and Schwartz density extend it to every `L²` class.
:::

:::theorem "ha_affine_mackey_detail" (lean := "LeanRidgelet.affineTopologicalLpUnitaryRepresentation, LeanRidgelet.affineTopologicalLpUnitaryRepresentation_isStronglyContinuous, LeanRidgelet.affineTopologicalFourierLpUnitaryRepresentation, LeanRidgelet.affinePlancherelIntertwiningMap, LeanRidgelet.affinePlancherelInverseIntertwiningMap, LeanRidgelet.affineDualOrbit, LeanRidgelet.affineDualOrbit_transitive, LeanRidgelet.affineTopologicalMackeySubgroup, LeanRidgelet.affineTopologicalMackeyCharacter, LeanRidgelet.affineTopologicalMackeyUnitaryRepresentation, LeanRidgelet.affineTopologicalMackeyUnitaryRepresentation_isTopologicallyIrreducible, LeanRidgelet.affineTopologicalMackeyQuotientHomeomorphDualOrbit, LeanRidgelet.affineDualOrbitSubtypeMeasure, LeanRidgelet.affineDualOrbitSubtypeLpEquiv, LeanRidgelet.affineTopologicalOrbitLpUnitaryRepresentation, LeanRidgelet.affineDualOrbitIntertwiningMap, LeanRidgelet.affineDualOrbitInverseIntertwiningMap, LeanRidgelet.affineTopologicalOrbitLpUnitaryRepresentation_isTopologicallyIrreducible_iff") (uses := "ha_affine_frequency_detail, mathlib_affine_semidirect, mathlib_const_density_strong_continuity, mathlib_general_linear_orbit, mathlib_unitary_character")
*Group, Fourier, and orbit input for Mackey induction.* The affine group is realized as a locally
compact topological semidirect product, and the determinant-corrected physical representation is
strongly continuous. Plancherel conjugation gives an equivalent frequency representation with
bounded intertwiners in both directions; the explicit dual-pullback and character model agrees
with it on all of `L²`. The contragredient action has one conull nonzero orbit. At a chosen
frequency, the translation group semidirect the little group is a closed locally compact inducing
subgroup carrying a continuous irreducible character. The orbit map descends to an equivariant
homeomorphism from its left-coset space to that orbit. Pullback to the orbit subtype is a
surjective `L²` isometry, so physical, frequency, and intrinsic-orbit irreducibility are
equivalent. The measure, section, and commutant layers are separated below. The full linear group
is essential: positive dilations alone leave two frequency half-lines.
:::

:::theorem "ha_affine_homogeneous_l2_detail" (lean := "LeanRidgelet.instIsClosedAffineTopologicalMackeySubgroup, LeanRidgelet.instSecondCountableTopologyAffineTopologicalMackeyQuotient, LeanRidgelet.affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul, LeanRidgelet.AffineTopologicalMackeyQuotient, LeanRidgelet.affineTopologicalMackeyQuotientMeasure, LeanRidgelet.instIsFiniteMeasureOnCompactsAffineDualOrbitSubtypeMeasure, LeanRidgelet.instIsFiniteMeasureOnCompactsAffineTopologicalMackeyQuotientMeasure, LeanRidgelet.affineTopologicalMackeyQuotient_measurePreserving, LeanRidgelet.affineTopologicalMackeyQuotient_symm_measurePreserving, LeanRidgelet.affineTopologicalMackeyQuotientLpLinearIsometry, LeanRidgelet.affineTopologicalMackeyQuotientLpLinearIsometry_apply_ae, LeanRidgelet.affineTopologicalMackeyQuotientLpLinearIsometry_surjective, LeanRidgelet.affineTopologicalMackeyQuotientLpEquiv, LeanRidgelet.affineTopologicalMackeyQuotientLpEquiv_apply, LeanRidgelet.affineTopologicalMackeyQuotientLpUnitaryRepresentation, LeanRidgelet.affineTopologicalMackeyQuotientIntertwiningMap, LeanRidgelet.affineTopologicalMackeyQuotientInverseIntertwiningMap, LeanRidgelet.affineTopologicalMackeyQuotientIntertwiningMap_apply, LeanRidgelet.affineTopologicalMackeyQuotientInverseIntertwiningMap_apply, LeanRidgelet.affineTopologicalMackeyQuotientLpUnitaryRepresentation_isStronglyContinuous, LeanRidgelet.affineTopologicalMackeyQuotientLpUnitaryRepresentation_isTopologicallyIrreducible_iff") (uses := "ha_affine_mackey_detail")
*The homogeneous-space `L²` model.* The quotient-orbit homeomorphism intertwines left
translation on $`G/H` with the affine dual action. The affine semidirect product is Polish and the
closed subgroup quotient is second countable and Borel. Transporting the intrinsic orbit measure
back through the homeomorphism gives a measure on the actual left-coset space; the homeomorphism
and its inverse are measure preserving. Both transported measures are finite on compact sets, so
compactly supported continuous sections belong to `L²`. Mathlib's composition API gives an onto linear
isometry between orbit $`L^2` and homogeneous-space $`L^2`, with inverse pullback supplying the
surjectivity proof. Conjugation transports the explicit orbit representation to $`L^2(G/H)` and
bundles the equivalence and inverse as bounded intertwiners. Strong continuity and equivalence of
irreducibility with the physical model follow without a measurable section. The normalized-section
realization is constructed in the next node; only its spectral/commutant theorem remains afterward.
:::

:::definition "ha_affine_homogeneous_quasiregular_detail" (lean := "LeanRidgelet.affineTopologicalDualJacobian, LeanRidgelet.affineTopologicalDualJacobian_eq_inv, LeanRidgelet.measurable_affineTopologicalDualOrbit_smul, LeanRidgelet.affineDualOrbitSubtypeMeasure_map_inv_smul, LeanRidgelet.affineDualOrbitSubtype_quasiMeasurePreserving, LeanRidgelet.affineTopologicalMackeyQuotientJacobian, LeanRidgelet.measurable_affineTopologicalMackeyQuotient_smul, LeanRidgelet.affineTopologicalMackeyQuotientMeasure_map_inv_smul, LeanRidgelet.affineTopologicalMackeyQuotientJacobian_measurable, LeanRidgelet.affineTopologicalMackeyQuotientJacobian_ne_zero, LeanRidgelet.affineTopologicalMackeyQuotientJacobian_one, LeanRidgelet.affineTopologicalMackeyQuotientJacobian_cocycle, LeanRidgelet.affineTopologicalMackeyQuotientMeasure_map_eq_withDensity, LeanRidgelet.affineTopologicalMackeyQuotientRadonNikodymWeight, LeanRidgelet.affineTopologicalMackeyQuotientPhase, LeanRidgelet.affineTopologicalMackeyQuotientPhase_cocycle, LeanRidgelet.affineTopologicalMackeyQuotientPhase_norm_one, LeanRidgelet.continuous_affineTopologicalMackeyQuotientPhase, LeanRidgelet.affineTopologicalMackeyQuotientPhase_translation, LeanRidgelet.affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation, LeanRidgelet.affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation_apply_ae, LeanRidgelet.affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation_apply_ae_explicit, LeanRidgelet.affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation, LeanRidgelet.affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_apply_ae_explicit, LeanRidgelet.affineDualOrbitSubtypeLpEquiv_symm_apply_ae, LeanRidgelet.affineTopologicalMackeyQuotientLpEquiv_symm_apply_ae, LeanRidgelet.affineTopologicalOrbitLpUnitaryRepresentation_apply_ae, LeanRidgelet.affineTopologicalMackeyQuotientLpUnitaryRepresentation_apply_ae, LeanRidgelet.affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_eq_transported") (uses := "ha_affine_homogeneous_l2_detail, ha_induced_l2_detail")
*Quasi-invariance and the character twist.* Injectivity of measure pushforward through the
measurable orbit inclusion first transfers the ambient determinant formula to the intrinsic
orbit. Equivariance of the quotient-orbit homeomorphism then gives the quotient formula both as a
constant scalar multiple and as `withDensity`. The general quasi-invariant construction produces
the untwisted quasi-regular unitary representation, whose representative is
$`|\det L|^{1/2} f(g^{-1}q)`. The separately defined character phase is continuous, pointwise
unimodular, satisfies the multiplier cocycle law, and restricts on translations to the frequency
character. The general twisting construction bundles their product and proves its explicit a.e.
action formula. The inverse transport equivalences are also identified a.e.; quasi-measure-
preserving composition then proves equality with the independently transported Fourier model.
:::

:::theorem "ha_affine_section_induction_detail" (lean := "LeanRidgelet.affineTopologicalMackeySection, LeanRidgelet.affineTopologicalMackeySection_rightInverse, LeanRidgelet.affineTopologicalMackeySectionCocycle, LeanRidgelet.affineTopologicalMackeySectionPhase, LeanRidgelet.affineTopologicalMackeyQuotientHomeomorphDualOrbit_eq_out, LeanRidgelet.affineTopologicalMackeySectionPhase_eq_quotientPhase, LeanRidgelet.affineTopologicalMackeySectionPhase_cocycle, LeanRidgelet.affineTopologicalMackeySectionPhase_one, LeanRidgelet.continuous_affineTopologicalMackeySectionPhase, LeanRidgelet.continuous_uncurry_affineTopologicalMackeySectionPhase, LeanRidgelet.affineTopologicalMackeySectionPhase_norm_one, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_quotient, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_transported, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isStronglyContinuous, LeanRidgelet.affineMackeySmoothedVector, LeanRidgelet.affineMackey_smoothing_integrable, LeanRidgelet.affineMackeySmoothedVector_mem, LeanRidgelet.affineMackey_exists_smoothing_mem_tendsto, LeanRidgelet.affineMackeySmoothedVector_exists_continuousRepresentative, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible_iff, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_indicator_covariant, LeanRidgelet.affineTopologicalTranslation_right, LeanRidgelet.affineTopologicalMackeyQuotient_translation_smul, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_apply_ae, LeanRidgelet.affineTopologicalMackeyFrequencyEmbedding, LeanRidgelet.affineTopologicalMackeyFrequencyEmbedding_measurableEmbedding, LeanRidgelet.affineTopologicalMackeyTranslationMultiplier, LeanRidgelet.affineTopologicalMackeyTranslationMultiplier_apply_ae, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_translation_eq_multiplier, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translation, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_commutes_translationMultiplier, LeanRidgelet.affineMackey_commutes_indicator_of_commutes_translation, LeanRidgelet.affineMackey_indicatorLp_mem, LeanRidgelet.affineMackey_representation_mem, LeanRidgelet.affineMackey_regularSection_memLp, LeanRidgelet.affineMackeyRegularSectionToLp, LeanRidgelet.affineMackeyRegularSectionEvaluation, LeanRidgelet.affineMackeyRegularSectionsIn, LeanRidgelet.affineMackeyInducingFiber, LeanRidgelet.affineMackey_regularSection_dense, LeanRidgelet.affineMackeyRegularSectionSMul, LeanRidgelet.affineMackeyRegularSectionSMul_apply, LeanRidgelet.affineMackeyRegularSectionToLp_coeFn_ae, LeanRidgelet.affineMackeyRegularSectionToLp_smul, LeanRidgelet.affineMackeyRegularSectionSMul_ne_zero, LeanRidgelet.affineMackeyRegularSection_eq_zero_of_smul_eq_zero, LeanRidgelet.affineMackeyInducingFiber_eq_bot_iff, LeanRidgelet.affineMackeyInducingFiber_eq_top_of_ne_zero, LeanRidgelet.affineMackey_regularSection_eq_zero_of_inducingFiber_eq_bot, LeanRidgelet.affineMackey_eq_bot_of_inducingFiber_eq_bot, LeanRidgelet.affineMackey_eq_top_of_regularSection_ne_zero, LeanRidgelet.affineMackey_closedSubspace_extreme_iff_inducingFiber_extreme, LeanRidgelet.affineMackey_systemInvariant_closedSubspace_eq_bot_or_top, LeanRidgelet.affineMackey_scalar_of_commutes_indicators, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_hasSchurProperty, LeanRidgelet.affineTopologicalMackeySectionInducedLpUnitaryRepresentation_isTopologicallyIrreducible, LeanRidgelet.affineDataLpUnitaryRepresentation_isTopologicallyIrreducible") (uses := "ha_affine_homogeneous_quasiregular_detail, mathlib_homogeneous_section_cocycle, mathlib_integrated_unitary_representation, mathlib_group_convolution_continuity, mathlib_bochner_integral_l2, mathlib_lp_indicator, mathlib_lp_compact_multiplier, mathlib_fourier_character_multiplier")
*Normalized-section unitary induction.* Since the inducing subgroup contains every translation,
the choice-based quotient representative can be normalized by discarding its translation
coordinate without changing its coset. This gives a right inverse $`s:G/H\to G` and hence the
reentry cocycle $`s(q)^{-1}g s(g^{-1}q)` in the inducing subgroup. Applying the inducing character
to this cocycle is proved, by the adjoint identity for the linear coordinate of `s(q)`, to equal
the independently constructed Fourier phase. The resulting quasi-invariant `L²` representation
is therefore exactly both the character-twisted quotient model and the transported Fourier model;
it is strongly continuous, and its irreducibility is equivalent to Theorem 2.5. No measurability
of the raw choice function is assumed: regularity is obtained from the proved phase equality.
Measurable-set indicator operators form its canonical projection family and satisfy
$`P_s\pi(g)=\pi(g)P_{g^{-1}s}`. Pure translations fix the quotient and have unit Jacobian, so their
restriction is proved a.e. to be multiplication by the orbit-frequency character. The quotient
coordinate is a measurable embedding into frequency space, and the translation restriction is
identified with the general bundled Fourier-character multiplier. The derived affine Theorem-4.44
step is source-level complete: finite-character density in $`L^2` of an arbitrary finite measure is
proved in the Mathlib candidate layer by characteristic-function uniqueness. The spectral-subspace
and self-adjoint-decomposition remainder of Theorem 6.28 is proved as well. Compactly supported
continuous scalar sections are bundled into `L²`; their identity-coset values define the extracted
closed inducing fiber. Haar-integrated smoothing is defined for this affine representation. A
sequence of nonnegative compactly supported Haar probability kernels is constructed with supports
shrinking to the identity; the smoothed vectors stay in the invariant closed subspace and converge
in `L²` to the input. The compact-kernel group-convolution formula is now proved continuous in the
Mathlib candidate layer by reduction to additive convolution on the opposite group. Once a
smoothed vector has a continuous quotient representative, the general compact-multiplier API keeps
its Urysohn cutoffs in the same subspace, and a diagonal sequence proves regular-section density.
The general theorem identifying a Bochner integral in scalar `L²` with a family of pointwise
representatives integrable over the finite-measure slices is also proved, and applying it to the
measurable induced-model lift finishes Lemma 6.29: the smoothed vector agrees almost everywhere
with the pointwise convolution, which is continuous. Indicator and representation
stability, as well as the classification of closed complex subspaces of the one-dimensional fiber,
are proved. The extreme-subspace part of Lemma 6.30 is now proved as well.
:::

*Inducing fiber.* Translating a compactly supported continuous section by the induced action gives
another such section, because the phase is continuous and unimodular, the Radon--Nikodym factor is a
positive constant, and the shifted support is the homeomorphic image of a compact set; its $`L^2`
class is the induced action applied to the original class. Since the transported quotient measure is
positive on nonempty open sets, a section whose class vanishes vanishes identically, so a trivial
subspace has a trivial fiber; conversely, if the fiber is trivial then evaluating translated
sections at the identity coset kills a section at every coset, because the group acts transitively
on the quotient, and regular-section density then forces the subspace to be trivial. A Urysohn bump
provides a section with value one at the identity coset, so the full subspace has full fiber. If some
section of the subspace does not vanish at the identity coset, then every vector orthogonal to the
subspace vanishes almost everywhere on the nonvanishing set of each translate, by the indicator test
of the Mathlib candidate layer; those nonvanishing sets are open and cover the quotient, second
countability extracts a countable subcover, and the orthogonal complement is therefore zero. The
combination of the two lemmas, the assembled Schur property, Schur's converse, and the model
transports contain no further source-level `sorry` and derive the paper theorem.

*Haar measure of the affine group along the orbit map*

:::theorem "ha_affine_group_haar_detail" (lean := "LeanRidgelet.affineLinearDeterminantCharacter, LeanRidgelet.affineLinearDeterminantCharacter_apply, LeanRidgelet.affineLinearDeterminantCharacter_ne_zero, LeanRidgelet.continuous_affineLinearDeterminantCharacter_real, LeanRidgelet.measurable_affineLinearDeterminantCharacter, LeanRidgelet.exists_affineLinearDeterminantCharacter_le_of_isCompact, LeanRidgelet.affine_map_orbitMap_haar_restrict_le, LeanRidgelet.affineTopologicalMackeyOrbitMap_inv, LeanRidgelet.affine_map_adjointOrbitMap_haar_restrict_le") (uses := "ha_affine_mackey_detail, mathlib_semidirect_haar, mathlib_general_linear_haar")
*Quotient-integral input for the smoothing estimate.* Local integrability of the lift of a quotient $`L^2` class needs an integral over a compact set of group elements to become an integral over a compact set of frequencies. The estimate proved here does exactly that: the image of a compactly restricted Haar measure of the affine group under the orbit map $`x\mapsto (x_{\mathrm{right}}^{-1})^\dagger\xi` is dominated by a finite multiple of Lebesgue measure of frequency space, restricted to a compact set.
:::

The same bound is proved for the orbit map composed with inversion, that is for the adjoint orbit map $`x\mapsto x_{\mathrm{right}}^\dagger\xi`; that is the form the group-convolution continuity theorem consumes, since its local-integrability hypothesis is stated for the inverse-composed integrand. The proof instantiates the general semidirect-product factorization at the affine group and composes it with the contragredient-orbit estimate. The translation factor `Multiplicative E` is the additive group of `E` written multiplicatively, so its Haar measure *is* Lebesgue measure and the linear action rescales it by the reciprocal absolute determinant; that determinant is the multiplicative character of the factorization, continuous and nonvanishing, hence bounded on compact sets, which converts the relatively invariant measure of the linear factor back to Haar measure there. Borel structures on the two factors are introduced inside the proof rather than as global instances, since neither factor appears in the statement.

*The equivariant lift to the group*

:::definition "ha_affine_lift_detail" (lean := "LeanRidgelet.affineMackeyLiftPhase, LeanRidgelet.affineMackeyLiftPhase_norm_one, LeanRidgelet.affineMackeyLiftPhase_ne_zero, LeanRidgelet.continuous_affineMackeyLiftPhase, LeanRidgelet.affineMackeyLiftPhase_mul, LeanRidgelet.affineMackeyLiftFun, LeanRidgelet.affineMackeyLiftFun_apply, LeanRidgelet.norm_affineMackeyLiftFun, LeanRidgelet.affineMackeyLiftFun_inv_mul, LeanRidgelet.measurable_affineMackeyLiftFun, LeanRidgelet.affine_map_quotientMk_inv_haar_restrict_le, LeanRidgelet.locallyIntegrable_affineMackeyLiftFun_inv_of_bound, LeanRidgelet.locallyIntegrable_affineMackeyLiftFun_inv, LeanRidgelet.affineMackeySmoothingKernel, LeanRidgelet.affineMackeySmoothingKernel_apply, LeanRidgelet.affineMackeySmoothingIntegrand, LeanRidgelet.measurable_uncurry_affineMackeySmoothingIntegrand, LeanRidgelet.affineMackeySmoothingIntegrand_ae_eq, LeanRidgelet.integrable_uncurry_affineMackeySmoothingIntegrand, LeanRidgelet.affineMackeySmoothingIntegral, LeanRidgelet.affineMackeySmoothingIntegral_quotientMk, LeanRidgelet.continuous_affineMackeySmoothingIntegral") (uses := "ha_affine_section_induction_detail, ha_affine_group_haar_detail, mathlib_bochner_integral_l2")
*Lifting a quotient class to the group.* Folland realizes an induced representation on functions over the group that transform by the inducing character, which turns smoothing into an ordinary group convolution. Here the lift multiplies a function on the quotient by the inverse section phase at the point itself, $`F(x)=P(x)^{-1}f(xH)` with $`P(x)=\mathrm{phase}(x,xH)`.
:::

The gauge $`P` is unimodular, nowhere zero, and continuous — although the normalized section is only set-theoretic, its character equals the explicit Fourier phase, and that phase is continuous in both arguments. The cocycle law of the section phase gives $`P(x)=\mathrm{phase}(g,xH)\,P(g^{-1}x)`, hence the translation identity
$$`F(g^{-1}x)=P(x)^{-1}\bigl(\mathrm{phase}(g,xH)\,f(g^{-1}\cdot xH)\bigr),`
whose right-hand side is exactly the integrand of the induced action at the coset of `x`, up to the factor $`P(x)^{-1}` that does not depend on the integration variable. Convolving with a compactly supported kernel therefore reproduces the smoothed vector along the quotient map, and continuity of the convolution transfers to the quotient because the quotient map is a topological quotient map. Absolute values of the lift are those of the original function, which is what the local-integrability estimate consumes.

The estimate and the lift combine into continuity of the smoothing integral. Transporting the frequency-space Haar bound along the quotient-orbit homeomorphism gives the same bound on the homogeneous quotient, and Cauchy--Schwarz on a finite-measure set turns it into local integrability of the lift composed with inversion — exactly the hypothesis of the compact-kernel group-convolution theorem. Along the quotient map the smoothing integral is that convolution, of the compactly supported kernel $`ψ\cdot\sqrt{\det}` with the lift, corrected by the continuous unimodular gauge; hence it is continuous on the group, and it descends because the quotient map of a topological group by a subgroup is a quotient map.

What is left for Lemma 6.29 is to know that this pointwise integral is the representative of the Bochner-integrated vector, and that is a slice-integrability question. Each slice of the smoothing integrand in the group variable is, almost everywhere, the value of the kernel times the induced action applied to the class of the data, so all slices have the same $`L^2` norm; on a set of finite measure Hölder's inequality turns that into a uniform bound on their $`L^1` norms, and the compactly supported kernel dominates the group variable. The integrand is jointly measurable because the section phase is jointly continuous in the group element and the coset. The family is therefore integrable on the product of the group with every finite-measure part of the quotient, which is exactly the hypothesis of the slice form of the pointwise-representative theorem: a measurable representative of the data yields a continuous representative of the smoothed vector, and the Lemma 6.29 root is closed.
