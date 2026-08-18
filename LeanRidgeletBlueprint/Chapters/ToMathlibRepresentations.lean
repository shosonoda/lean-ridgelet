import LeanRidgeletBlueprint.Chapters.ToMathlibMeasureLp
import LeanRidgelet.ToMathlib.LieGroup.GroupConvolution
import LeanRidgelet.ToMathlib.LieGroup.HaarApproximateIdentity
import LeanRidgelet.ToMathlib.LieGroup.IntegratedRepresentation
import LeanRidgelet.ToMathlib.LieGroup.UnitaryConjugation
import LeanRidgelet.ToMathlib.LieGroup.UnitaryLp
import LeanRidgelet.ToMathlib.LieGroup.OrthogonalComplexification
import LeanRidgelet.ToMathlib.LieGroup.UnitaryCharacter
import LeanRidgelet.ToMathlib.LieGroup.HomogeneousSection
import LeanRidgelet.ToMathlib.LieGroup.StronglyContinuousConstDensity
import LeanRidgelet.ToMathlib.LieGroup.PolishUnits
import LeanRidgelet.ToMathlib.LieGroup.TopologicalSemidirectProduct
import LeanRidgelet.ToMathlib.LieGroup.AffineSemidirect
import LeanRidgelet.ToMathlib.LieGroup.GeneralLinearOrbit
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

#doc (Manual) "Mathlib candidates: unitary representations and groups" =>
%%%
file := "representations"
%%%

Reusable representation-theoretic and topological-group infrastructure, including conjugation, pointwise `Lp` actions, homogeneous-space cocycles, semidirect products, and the affine orbit.

*Unitary equivalence of representations*

:::theorem "mathlib_unitary_conjugation" (lean := "UnitaryRepresentation.restrict, UnitaryRepresentation.IsStronglyContinuous, UnitaryRepresentation.IsStronglyContinuous.restrict, UnitaryRepresentation.restrict_isInvariant_iff_of_surjective, UnitaryRepresentation.restrict_isTopologicallyIrreducible_iff_of_surjective, UnitaryRepresentation.conjugateLinearIsometryEquivMonoidHom, UnitaryRepresentation.conjugate, UnitaryRepresentation.linearIsometryEquiv_conjugate_apply, UnitaryRepresentation.IsStronglyContinuous.conjugate, UnitaryRepresentation.conjugateIntertwiningMap, UnitaryRepresentation.conjugateInverseIntertwiningMap, UnitaryRepresentation.conjugate_symm, UnitaryRepresentation.conjugate_isTopologicallyIrreducible, UnitaryRepresentation.conjugate_isTopologicallyIrreducible_iff")
*Transporting a unitary representation across a Hilbert-space equivalence.* A linear isometric
equivalence $`U:H\simeq K` conjugates every unitary representation by
$`\widehat\pi(g)=U\pi(g)U^{-1}`. The maps `U` and `U⁻¹` are bundled as continuous intertwiners in
the two directions; conjugating back recovers the original representation, and topological
irreducibility is therefore equivalent on the two sides. Restriction along a surjective group
homomorphism likewise preserves and reflects invariant closed subspaces and irreducibility. Since
Mathlib's `ContRepresentation` does not impose continuity in the group variable, strong continuity
is recorded separately as continuity of every orbit map and is preserved by restriction along a
continuous homomorphism. These are the abstract steps that turn a
Plancherel transform into a representation equivalence without making any pointwise choice of
$`L^2` representatives.
:::

:::theorem "mathlib_integrated_unitary_representation" (lean := "UnitaryRepresentation.integratedVector, UnitaryRepresentation.integratedVector_integrable, UnitaryRepresentation.integratedVector_mem, UnitaryRepresentation.tendsto_setIntegral_peak_smul_orbit, UnitaryRepresentation.haarIntegratedVector, UnitaryRepresentation.haarIntegratedVector_integrable, UnitaryRepresentation.haarIntegratedVector_mem, UnitaryRepresentation.complexKernel, UnitaryRepresentation.complexKernel_apply, UnitaryRepresentation.exists_haarProbabilityBump, UnitaryRepresentation.exists_haarApproximateIdentity, UnitaryRepresentation.exists_haarApproximateIdentity_tendsto_smul_orbit, UnitaryRepresentation.exists_haarApproximateIdentity_tendsto_integratedVector") (uses := "mathlib_unitary_conjugation")
*Integrated vectors of strongly continuous unitary representations.* A compactly supported
continuous scalar kernel times a strongly continuous unitary orbit is Bochner integrable for every
measure finite on compact sets. The integral remains in each closed invariant subspace containing
the input vector, by commuting the orthogonal projection with the integral. For a family of
nonnegative kernels concentrating at the identity, Mathlib's peak-function convergence theorem is
specialized to prove convergence of the corresponding local orbit integrals back to the input
vector. Urysohn bump functions and an antitone countable neighborhood basis then construct
nonnegative compactly supported Haar probability kernels whose supports shrink to the identity.
Their integrated vectors converge to the input vector, both in real-scalar integral form and via
the bundled complex Haar-integrated-vector API. This proves the abstract smoothing and convergence
step used in Folland Lemma 6.29 without adding an approximate-identity assumption object.
:::

:::theorem "mathlib_group_convolution_continuity" (lean := "MeasureTheory.continuous_integral_compact_mul_right")
*Continuity of compact-kernel group convolution.* On a noncommutative topological group, the
function
$`x\mapsto\int L(f(y^{-1}),g(xy))\,d\mu(y)` is continuous when $`f\circ\mathrm{inv}` is locally
integrable and $`g` is continuous with compact support. The proof transports the formula to
Mathlib's additive convolution on the opposite group `Additive Gᵐᵒᵖ`; therefore it works for an
arbitrary measure and needs no Haar-invariance assumption. This supplies the continuity step in
Folland Lemma 6.29 independently of the quotient-model representative problem.
:::

:::theorem "mathlib_unitary_lp" (lean := "UnitaryRepresentation.lpPointwiseLinearIsometry, UnitaryRepresentation.lpPointwiseLinearIsometry_apply_ae, UnitaryRepresentation.lpPointwiseLinearIsometry_surjective, UnitaryRepresentation.lpPointwiseLinearIsometryEquiv, UnitaryRepresentation.lpPointwiseLinearIsometryEquiv_apply_ae, UnitaryRepresentation.lpPointwiseLinearIsometryEquiv_mul_apply, UnitaryRepresentation.lpPointwiseLinearIsometryEquivMonoidHom, UnitaryRepresentation.lpPointwise, UnitaryRepresentation.lpPointwise_apply_ae, UnitaryRepresentation.prodOfCommute, UnitaryRepresentation.prodOfCommute_apply, UnitaryRepresentation.prodOfCommute_isTopologicallyIrreducible_of_finiteDimensional") (uses := "mathlib_unitary_conjugation, mathlib_lp_functor")
*Pointwise unitaries on Bochner $`L^2` and product groups.* A value-space linear isometric
equivalence acts pointwise on an `Lp` class through Mathlib's `ContinuousLinearMap.compLp`. Its
norm preservation, inverse, composition law, and a.e. representative are proved before it is
bundled as a unitary representation on Bochner $`L^2`. Two unitary representations on the same
Hilbert space whose images commute then combine, via Mathlib's noncommutative coproduct of monoid
homomorphisms, into a representation of the product group. No Hilbert tensor product is needed for
these constructions. For a finite-dimensional value representation, the commuting product is
also proved irreducible when the scalar action is irreducible and is natural under coordinate
embeddings and projections. The proof applies infinite-dimensional Schur twice: first to the
matrix coefficients of an invariant projection, then to its reconstructed value-space operator.
:::

:::theorem "mathlib_orthogonal_complexification" (lean := "Matrix.realToComplexStarMonoidHom, Matrix.orthogonalComplexificationMatrix, Matrix.standardComplexOrthogonalRepresentation, Matrix.standardComplexOrthogonalRepresentation_apply, Matrix.coordinateReflection, Matrix.coordinatePermutation, Matrix.coordinateReflection_mulVec, Matrix.coordinatePermutation_mulVec, Matrix.standardComplexOrthogonalRepresentation_coordinateReflection, Matrix.standardComplexOrthogonalRepresentation_coordinatePermutation, Matrix.standardComplexOrthogonalRepresentation_isTopologicallyIrreducible") (uses := "mathlib_unitary_conjugation")
*The irreducible standard complexification of the orthogonal group.* Entrywise inclusion sends a
real orthogonal matrix to a complex unitary matrix, and Mathlib's star-algebra equivalence between
matrices and operators on `EuclideanSpace` gives the standard complex unitary representation.
For a nonempty finite index type, any nonzero invariant complex subspace contains a standard basis
vector: subtracting its image under a coordinate sign reflection isolates a nonzero coordinate.
Permutation matrices then put every standard basis vector in the subspace, proving irreducibility.
This finite coordinate model avoids introducing a general complexification structure.
:::

:::theorem "mathlib_unitary_character" (lean := "circleComplexLinearIsometryEquiv, UnitaryRepresentation.closedSubmodule_complex_eq_bot_or_top, UnitaryRepresentation.complex_isTopologicallyIrreducible, UnitaryRepresentation.ofCircleCharacter, UnitaryRepresentation.ofCircleCharacter_apply, UnitaryRepresentation.ofCircleCharacter_isStronglyContinuous, UnitaryRepresentation.ofCircleCharacter_isTopologicallyIrreducible") (uses := "mathlib_unitary_conjugation")
*Circle characters as one-dimensional unitary representations.* Multiplication by an element of
the complex unit circle is bundled as a complex-linear isometric equivalence. Consequently every
multiplicative character $`\chi:G\to\mathbb T` gives a unitary representation on $`\mathbb C` by
$`\pi_\chi(g)z=\chi(g)z`. A continuous character gives a strongly continuous representation, and
every such representation is topologically irreducible because every closed complex subspace of
the complex line is proved to be zero or the whole space. This is the general one-dimensional
input used by Mackey induction.
:::

:::theorem "mathlib_homogeneous_section_cocycle" (lean := "QuotientGroup.leftCosetSection, QuotientGroup.mk_leftCosetSection, QuotientGroup.leftCosetSectionCocycleOf, QuotientGroup.leftCosetSectionCocycleOf_one, QuotientGroup.leftCosetSectionCocycleOf_mul, QuotientGroup.leftCosetSectionCocycle, QuotientGroup.leftCosetSectionCocycle_one, QuotientGroup.leftCosetSectionCocycle_mul, QuotientGroup.leftCosetSectionMultiplierOf, QuotientGroup.leftCosetSectionMultiplierOf_one, QuotientGroup.leftCosetSectionMultiplierOf_mul, QuotientGroup.leftCosetSectionMultiplier, QuotientGroup.leftCosetSectionMultiplier_one, QuotientGroup.leftCosetSectionMultiplier_mul")
*Section cocycles on homogeneous spaces.* For a subgroup $`H\leq G`, any right inverse
$`s:G/H\to G` of the left-coset quotient map gives an $`H`-valued reentry cocycle
$`c(g,q)=s(q)^{-1}g s(g^{-1}q)`. It satisfies
$`c(gh,q)=c(g,q)c(h,g^{-1}q)`. Composing with a multiplicative character of `H` gives the
multiplier cocycle used by the section realization of an induced representation. Mathlib's
choice-based `Quotient.out` is provided as a canonical set-theoretic specialization; no
measurability of that choice is asserted.
:::

:::theorem "mathlib_const_density_strong_continuity" (lean := "UnitaryRepresentation.isStronglyContinuous_of_const_density") (uses := "mathlib_constant_density_preimage, mathlib_unitary_conjugation")
*Strong continuity of constant-density pullback representations.* Let $`r_g:X\to X` vary
continuously in the compact-open topology and satisfy $`(r_g)_*\mu=c_g\mu`, where $`c_g>0` varies
continuously. If a unitary representation acts almost everywhere by
$`f\mapsto c_g^{-1/2}f\circ r_g`, then all of its orbit maps on scalar $`L^2(\mu)` are continuous.
The proof establishes continuity on indicators from symmetric-difference convergence of their
preimages, extends it by induction to `Lp` simple functions, and then uses density together with
the uniform Lipschitz bound supplied by unitarity.
:::

*Topological semidirect products and the affine group*

:::theorem "mathlib_polish_units" (lean := "Units.instPolishSpaceOfNormedRing")
*Polish topology on unit groups.* The units of a normed ring with summable geometric series form
an open subspace of the ring. Hence the unit group is Polish whenever the ambient ring is Polish,
with its existing topology rather than a newly installed one. This supplies the standard-Borel
input for homogeneous spaces whose linear factor is a general linear group.
:::

:::theorem "mathlib_affine_semidirect" (lean := "SemidirectProduct.homeomorphProd, SemidirectProduct.instMeasurableSpace, SemidirectProduct.instBorelSpace, SemidirectProduct.continuous_left, SemidirectProduct.continuous_right, SemidirectProduct.instSecondCountableTopology, SemidirectProduct.instPolishSpace, SemidirectProduct.instLocallyCompactSpace, SemidirectProduct.isTopologicalGroupOfContinuous, AffineEquiv.linearMultiplicativeActionHom, AffineEquiv.semidirectProductEquiv, AffineEquiv.continuousLinearMultiplicativeActionHom, AffineEquiv.continuous_continuousLinearMultiplicativeAction, AffineEquiv.instIsTopologicalGroupTopologicalSemidirectProduct, AffineEquiv.continuousLinearUnitsEquivLinearEquiv, AffineEquiv.topologicalSemidirectProductEquiv, AffineEquiv.topologicalSemidirectProductEquiv_linear, AffineEquiv.det_topologicalSemidirectProductEquiv_linear, AffineEquiv.topologicalSemidirectProductInverseContinuousMap, AffineEquiv.continuous_topologicalSemidirectProductInverseContinuousMap") (uses := "mathlib_polish_units")
*The affine group as a locally compact semidirect product.* Mathlib's semidirect product is
algebraic, so the product topology and its Borel structure are transported through its canonical
equivalence with the product of the two factors. A jointly continuous action then makes this a
topological group, while second countability, Polishness, and local compactness are inherited from
the product. Algebraically, translations and the general
linear group give $`E\rtimes GL(E)\simeq\operatorname{Aff}(E)`. For a finite-dimensional real
normed space, the topological model instead uses the units of the normed algebra $`E\to_L E`;
joint continuity follows from bounded bilinear evaluation, its units are locally compact, and
forgetting continuity identifies the resulting semidirect product with the same affine
automorphism group. Its inverse affine transformations form a continuous map from this group into
the compact-open space $`C(E,E)`, and their determinant density is read directly from the linear
factor. This supplies both the locally compact group input and the continuous family of changes of
variables needed for Mackey theory without putting a nonstandard topology on Mathlib's algebraic
`LinearEquiv`.
:::

*The general linear orbit*

:::theorem "mathlib_general_linear_orbit" (lean := "LinearEquiv.exists_apply_eq_of_ne_zero, LinearEquiv.adjoint_adjoint, LinearEquiv.contragredientHom, LinearEquiv.exists_symm_adjoint_apply_eq_of_ne_zero, MeasureTheory.setOf_ne_zero_ae_eq_univ")
*The nonzero vectors form one conull orbit of the general linear group.* A reflection maps a
nonzero vector to the rescaling of a target vector having the same norm, and a final invertible
scalar map corrects the norm. Hence both the ordinary action $`Lx` and the contragredient action
$`L^{-T}x` are transitive away from zero. For any additive Haar measure on a nontrivial
finite-dimensional real normed space, the omitted singleton is null. These are the elementary
orbit inputs for a Mackey-machine proof of affine irreducibility; they do not depend on the
ridgelet theory.
:::
