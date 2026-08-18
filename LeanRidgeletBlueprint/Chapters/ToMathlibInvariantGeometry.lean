import LeanRidgeletBlueprint.Chapters.ToMathlibIntegralFourierTools
import LeanRidgeletBlueprint.Chapters.ToMathlibFiniteEuclidean
import LeanRidgelet.ToMathlib.LieGroup.OrthogonalGroup
import LeanRidgelet.ToMathlib.LieGroup.SphereInvariantMeasure
import LeanRidgelet.ToMathlib.LieGroup.MatrixPolar
import LeanRidgelet.ToMathlib.LieGroup.StiefelCodimOne
import LeanRidgelet.ToMathlib.LieGroup.SingularValueDecomposition
import LeanRidgelet.ToMathlib.LieGroup.UnitsHaar
import LeanRidgelet.ToMathlib.LieGroup.SemidirectProductHaar
import LeanRidgelet.ToMathlib.LieGroup.HaarAutomorphism
import LeanRidgelet.ToMathlib.LieGroup.GeneralLinearHaar
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

#doc (Manual) "Mathlib candidates: invariant geometry and integration" =>
%%%
file := "invariant-geometry"
%%%

The orthogonal group, invariant measures on Stiefel manifolds and spheres, the matrix polar formula, the codimension-one specialization, singular value decomposition, and Haar measure on the unit group of a finite-dimensional algebra and on a semidirect product.

*The orthogonal group and the Stiefel manifold*

:::theorem "mathlib_orthogonal_group" (lean := "ContinuousLinearMap.instContinuousStar, ContinuousLinearMap.norm_le_one_of_mem_unitary, ContinuousLinearMap.isCompact_unitary, ContinuousLinearMap.instCompactSpaceUnitary, ContinuousLinearMap.orthogonalHaar, ContinuousLinearMap.instIsProbabilityMeasureOrthogonalHaar, ContinuousLinearMap.instTopologicalSpaceLinearIsometry, ContinuousLinearMap.continuous_toContinuousLinearMap, ContinuousLinearMap.unitaryIsometry, ContinuousLinearMap.stiefelAct, ContinuousLinearMap.stiefelAct_mul, ContinuousLinearMap.continuous_stiefelAct_left, ContinuousLinearMap.continuous_stiefelAct_right, ContinuousLinearMap.stiefelMeasure, ContinuousLinearMap.map_stiefelAct_stiefelMeasure, ContinuousLinearMap.instIsMulRightInvariantOrthogonalHaar, ContinuousLinearMap.isometryEquivOfIsometry, ContinuousLinearMap.unitaryOfIsometryEquiv, ContinuousLinearMap.exists_stiefelAct_eq, ContinuousLinearMap.stiefelMeasure_eq, ContinuousLinearMap.map_comp_right_stiefelMeasure") (uses := "mathlib_dplane_transform")
*The orthogonal group is a compact group, and the Stiefel manifold carries an invariant measure.* Mathlib has the orthogonal group only as linear algebra — `Matrix.orthogonalGroup` is a submonoid of matrices with no topology, no compactness and no measure — but it does have the unitary group of a C\*-algebra as a topological group whenever the star operation is continuous, and it identifies the elements of `unitary (E →L[𝕜] E)` with the linear isometry equivalences of `E`. That is the orthogonal group in coordinate-free form, and what is missing from it is supplied here: the adjoint is continuous because it is an isometry, so the group is topological; a unitary has operator norm at most one, so the group is bounded; it is closed, and in finite dimensions the operator space is proper, so it is *compact* by Heine--Borel; hence it carries a Haar measure, which is a *probability* measure because the group is compact.
:::

The Stiefel manifold of orthonormal `k`-frames is the space of linear isometries $`\mathbb R^k\to E`, which Mathlib leaves without a topology, a Borel structure or a measure. All three are given here, the topology induced from the continuous linear maps, and the *invariant measure* is defined as the pushforward of the Haar probability measure along the action of the orthogonal group on a fixed frame. Defining it this way makes invariance hold by construction rather than by a uniqueness theorem — which is what a construction by iterated sphere measures would need, since the recursion there privileges the first vector of the frame and the dependent family of orthogonal complements admits no global measurable trivialization.

Two further properties are what the matrix polar integration formula in codimension greater than one needs, and both are here. *Independence of the base frame*: the action is transitive on frames, because the map $`L'\circ L^{-1}` defined on the range of `L` extends to an isometry of all of `E` and in finite dimensions such an isometry is surjective, hence unitary; so the two pushforwards differ by a right translation of the group. That translation is invisible to the Haar measure because the group is *unimodular* — right translation of a left invariant measure is again left invariant, hence a scalar multiple of the Haar measure by uniqueness, and the scalar is the total mass, which compactness makes `1` on both sides. Mathlib derives right from left invariance only for abelian groups.

*Invariance under the right action* $`L\mapsto L\circ V` of the isometries of $`\mathbb R^k` then needs no separate argument: precomposing by `V` only replaces the frame the measure is built from, and by the previous paragraph every frame gives the same measure. This is the property that makes the direction integral of the matrix polar formula independent of the point of $`\mathbb S^{k-1}` it is read at.

*The sphere*

:::theorem "mathlib_sphere_invariant_measure" (lean := "MeasureTheory.sphereAct, MeasureTheory.continuous_sphereAct, MeasureTheory.coe_image_preimage_sphereAct, MeasureTheory.smul_set_preimage_isometryEquiv, MeasureTheory.map_sphereAct_toSphere, MeasureTheory.unitVectorIsometry, MeasureTheory.exists_sphereAct_eq, MeasureTheory.sphereOrbitMeasure, MeasureTheory.sphereOrbitMeasure_apply, MeasureTheory.sphereOrbitMeasure_eq, MeasureTheory.toSphere_eq_smul_sphereOrbitMeasure, MeasureTheory.sphereOrbitMeasure_eq_smul_toSphere, MeasureTheory.frameDirection, MeasureTheory.continuous_frameDirection, MeasureTheory.map_frameDirection_stiefelMeasure") (uses := "mathlib_orthogonal_group, mathlib_polar_coordinates")
*The rotation-invariant measure on the unit sphere is unique.* Mathlib records how `Measure.toSphere` is computed but none of its symmetries. *Invariance* under the orthogonal group is the first declaration group: `Measure.toSphere_apply'` computes $`\mu_{\mathbb S}(s)` as $`\dim E` times the Lebesgue measure of the open cone $`(0,1)\cdot s`, a rotation carries that cone to the cone over the rotated set, and Lebesgue measure does not see a rotation. *Uniqueness* is the averaging argument: the orbit measure of a unit vector — the pushforward of the Haar probability measure along $`Q\mapsto Qv` — does not depend on `v`, because the action is transitive and the Haar measure is unimodular; and averaging the invariance of the surface measure over the group, then exchanging the two integrals, identifies the surface measure with its total mass times that orbit measure. Transitivity on the sphere is the $`k=1` case of transitivity on frames, a unit vector being a linear isometry of the line.
:::

The consequence the matrix polar integration formula needs is the last declaration: *the direction of a random frame is uniform on the sphere.* For a fixed unit vector $`\boldsymbol\omega` of the frame space, the pushforward of the invariant measure on the Stiefel manifold along $`U\mapsto U\boldsymbol\omega` is the normalized surface measure, whichever $`\boldsymbol\omega` is chosen and whichever frame the Stiefel measure was built from. Both halves of the proof are what the two constructions were for: the orbit map of a *frame* composed with the direction map is the orbit map of a *vector*, and the orbit measure of a vector is the normalized surface measure by uniqueness.

*The matrix polar integration formula*

:::theorem "mathlib_matrix_polar" (lean := "MeasureTheory.toSphere_real_smul_integral_directionAverage, MeasureTheory.toSphere_real_smul_integral_stiefelMeasure, MeasureTheory.radialIntegral, MeasureTheory.radialLIntegral, MeasureTheory.measurable_radialLIntegral, MeasureTheory.toSphere_mul_lintegral_directionAverage, MeasureTheory.toSphere_mul_lintegral_stiefelMeasure, MeasureTheory.continuous_frameApply, MeasureTheory.ae_integrable_weighted_frameSection, MeasureTheory.integrable_prod_radialIntegral, MeasureTheory.toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable") (uses := "mathlib_sphere_invariant_measure, mathlib_orthogonal_group, mathlib_polar_coordinates")
*The matrix polar integration formula.* Polar coordinates write an integral over $`\mathbb R^m` as an integral over $`\mathbb S^{m-1}\times(0,\infty)`; the matrix polar formula does the same with a `k`-frame in place of a direction,
$$`c_{m,k}\int_{\mathbb R^m}F=\int_{V_{m,k}\times\mathbb R^k}F(U\boldsymbol b)\,|U\boldsymbol b|^{m-k},`
and it is what the `d`-plane reconstruction formulas need in codimension greater than one. The proof is three reductions and no new analysis: polar coordinates on the frame space turn the weight $`|U\boldsymbol b|^{m-k}` together with the Jacobian $`r^{k-1}` into $`r^{m-1}`, which is the Jacobian of polar coordinates on $`\mathbb R^m`; the direction integral over frames becomes an integral over $`\mathbb S^{m-1}` because the direction of a random frame is uniform there; and polar coordinates on $`\mathbb R^m` put it back together.
:::

Since the invariant measure on the Stiefel manifold is normalized to a *probability* measure, the constant comes out as a ratio of sphere areas, $`|\mathbb S^{k-1}|/|\mathbb S^{m-1}|`, and the statement is written multiplied out so that no division appears. That form is independent of how the Stiefel manifold is normalized. In the classical normalization, where the Stiefel manifold carries total mass $`\sigma_{m,k}=\prod_{j<k}|\mathbb S^{m-1-j}|`, the constant becomes $`|\mathbb S^{k-1}|\cdot\sigma_{m-1,k-1}` — the article's $`c_{m,k}` with frames of the *orthogonal complement* of the direction rather than of the whole space. The two readings agree at $`k=1`, which is why the codimension-one development did not see the difference.

The middle move is stated separately as the *direction average*, the first declaration: averaging a function of the direction $`U\boldsymbol\omega` over frames and over unit vectors of the frame space is averaging it over $`\mathbb S^{m-1}`, up to the ratio of the two sphere areas. That is the shared core of the reconstruction formulas over the Stiefel manifold and over the similitude group — whatever the weight family, the derivation ends by reducing the parameter integral to this average — so it is worth having on its own rather than inlined.

Both reductions are Tonelli rather than Fubini when read for the lower Lebesgue integral, so the *unsigned* form of the formula needs no hypothesis but measurability — and there the frame section needs no almost-everywhere qualifier either, a frame being an isometry, so the weight $`|U\boldsymbol b|^{m-k}` is $`|\boldsymbol b|^{m-k}` and the reduction holds at every frame.

That is what discharges the absolute convergence of the signed formula, which the article carries as a standing assumption: for a *strongly measurable* integrand, both hypotheses — the weighted section along almost every frame, and the doubly iterated integrand on the product — follow from integrability, by computing the integral of the norm with the unsigned formula and reading off that almost every fibre is finite.

The measurability cannot be weakened to almost-everywhere measurability, and the reason is not a technicality. The left-hand side reads the integrand only along the ranges of the frames, each of which is a null set of `E` when $`k<m`; an integrable integrand may therefore be modified there — off a null set of `E`, so without disturbing the right-hand side — into one whose frame sections are not even measurable. What the unsigned formula does say is that a *measurable* null set is met in a null set by almost every frame, so the formula is insensitive to modifying a strongly measurable integrand on a null set even though no individual frame section is.

*Codimension one*

:::theorem "mathlib_stiefel_codim_one" (lean := "MeasureTheory.continuous_frameOfUnitVector, MeasureTheory.stiefelHomeomorphSphere, MeasureTheory.stiefelHomeomorphSphere_apply, MeasureTheory.measurePreserving_stiefelHomeomorphSphere, MeasureTheory.integral_stiefelMeasure_codimOne") (uses := "mathlib_sphere_invariant_measure, mathlib_dplane_transform")
*The Stiefel manifold at codimension one is the unit sphere.* The set-level identification is in `mathlib_dplane_transform` and the measure theory of the two sides is in `mathlib_sphere_invariant_measure`; this joins them. The identification is a *homeomorphism*: sending a frame to its unit vector is continuous because the topology on the Stiefel manifold is induced from the continuous linear maps, and sending a unit vector to the frame that scales it is continuous because that frame is the coordinate functional tensored with the vector, a bounded bilinear operation. Reading "the direction of a random frame is uniform on the sphere" through the identification then makes it *measure preserving*, onto the surface measure divided by its total mass — the only difference between the two sides being that the invariant measure on the Stiefel manifold is normalized to a probability measure and `Measure.toSphere` is not.
:::

The change of variables for integrals follows with no measurability hypothesis on the integrand, the substitution being along an equivalence. Its use is to make "the general codimension specializes to codimension one" a theorem about the two layers rather than a remark about two constructions that resemble each other.

*Matrix decompositions*

:::theorem "mathlib_svd" (lean := "MeasureTheory.linearMapOfFamily, MeasureTheory.linearMapOfFamily_apply, MeasureTheory.isometryOfOrthonormalFamily, MeasureTheory.isometryOfOrthonormalFamily_apply, MeasureTheory.isometryOfOrthonormalFamily_single, MeasureTheory.exists_svd") (uses := "mathlib_diagonal_scaling")
*Singular value decomposition of an injective linear map.* Mathlib has singular *values* — `LinearMap.singularValues`, the square roots of the eigenvalues of $`A^\top A` — but not the decomposition they are the values of. It is proved here in the case that integration over a matrix space needs: an injective $`A:\mathbb R^k\to E` factors as $`A=UDV^\top` with `U` an orthonormal `k`-frame, `V` a rotation of $`\mathbb R^k`, and `D` the coordinatewise scaling by `k` *positive* numbers.
:::

The proof is the spectral theorem and nothing else. $`T=A^\top A` is symmetric, and positive definite because `A` is injective; its orthonormal eigenbasis $`(b_i)` has eigenvalues $`\mu_i=\|Ab_i\|^2>0`; the vectors $`u_i=Ab_i/\sqrt{\mu_i}` are orthonormal in `E` because $`\langle Ab_i,Ab_j\rangle=\langle Tb_i,b_j\rangle=\mu_i\delta_{ij}`; and reading `A` in the two bases gives the factorization with $`d_i=\sqrt{\mu_i}` and `V` the basis change. One auxiliary construction is worth naming on its own: an orthonormal family indexed by `Fin k` *is* a linear isometry out of $`\mathbb R^k`, sending the standard basis to the family.

What is *not* here is the measure-theoretic half — the Jacobian $`\mathrm dA=\delta(D)\,\mathrm dD\,\mathrm dU\,\mathrm dV`, which is what turns an integral over the matrix space into one over the singular value coordinates. Its published proofs go through exterior differential forms, or through the Jacobian of the matrix polar decomposition together with Weyl's integration formula for real symmetric matrices, and Mathlib has none of those.

*Haar measure on the unit group of a finite-dimensional algebra*

:::theorem "mathlib_units_haar" (lean := "MeasureTheory.lmul_eq_mulLeft, MeasureTheory.continuous_algebraNorm, MeasureTheory.algebraNorm_units_ne_zero, MeasureTheory.unitsHaarDensity, MeasureTheory.unitsHaarDensity_apply, MeasureTheory.continuous_unitsHaarDensity_comp_units_val, MeasureTheory.measurable_unitsHaarDensity, MeasureTheory.unitsHaarDensity_mul, MeasureTheory.unitsHaarDensity_one, MeasureTheory.unitsHaarDensity_units_ne_zero, MeasureTheory.unitsHaarDensity_units_ne_top, MeasureTheory.unitsHaarDensity_units_inv_mul_units, MeasureTheory.exists_unitsHaarDensity_le_of_isCompact, MeasureTheory.map_mul_left_withDensity_unitsHaarDensity, MeasureTheory.Measure.unitsHaar, MeasureTheory.Measure.unitsHaar_apply, MeasureTheory.Measure.unitsHaar_apply_of_measurableSet, MeasureTheory.units_val_image_preimage_mul_left, MeasureTheory.Measure.isMulLeftInvariant_unitsHaar, MeasureTheory.Measure.isFiniteMeasureOnCompacts_unitsHaar, MeasureTheory.Measure.isOpenPosMeasure_unitsHaar, MeasureTheory.Measure.isHaarMeasure_unitsHaar, MeasureTheory.instLocallyCompactSpaceUnits, MeasureTheory.instSecondCountableTopologyUnits, MeasureTheory.Measure.exists_haar_eq_smul_unitsHaar, MeasureTheory.Measure.exists_map_units_val_haar_restrict_le")
*Haar measure of a unit group as a weighted Lebesgue measure.* The unit group of a finite-dimensional real normed algebra `A` is open in `A`, so its Haar measure should be an explicit weighted additive Haar measure of `A`. The weight is the reciprocal absolute algebra norm $`|N(a)|^{-1}`, where $`N(a)=\det(x\mapsto ax)` is Mathlib's `Algebra.norm`. Multiplicativity of the algebra norm — free, since `Algebra.norm` is a monoid homomorphism — makes the weighted measure invariant under left multiplication by units: substituting $`b=u^{-1}b'` rescales additive Haar measure by $`|N(u)|^{-1}` while the weight picks up the reciprocal factor $`|N(u^{-1})|^{-1}`, and the two cancel because $`N(u^{-1})N(u)=1`. No determinant power in $`\dim A` has to be evaluated.
:::

The weighted measure is finite on compact subsets of the unit group, because the weight is continuous there — the algebra norm is continuous, being the determinant of the continuous linear map $`x\mapsto ax`, and it does not vanish on units — and it is positive on nonempty open sets, because the weight is positive on units. Transporting it to the unit group along the open embedding gives a Haar measure, so uniqueness of Haar measure identifies the canonical Haar measure of the unit group with it up to a positive finite factor.

The consequence used downstream is a comparison: on a compact subset of the unit group, the image of Haar measure under the inclusion into `A` is dominated by a multiple of additive Haar measure of `A`. It converts local integrability statements on the algebra into local integrability statements on the group, which is what the quotient-integral estimate of an induced representation needs.

*Haar measure of a semidirect product*

:::theorem "mathlib_semidirect_haar" (lean := "MeasureTheory.map_mul_left_withDensity_monoidHom, SemidirectProduct.prodMeasure, SemidirectProduct.measurable_homeomorphProd_symm, SemidirectProduct.measurable_homeomorphProd, SemidirectProduct.prodMeasure_apply, SemidirectProduct.homeomorphProd_symm_comp_mul_left, SemidirectProduct.isMulLeftInvariant_prodMeasure, SemidirectProduct.isFiniteMeasureOnCompacts_prodMeasure, SemidirectProduct.isOpenPosMeasure_prodMeasure, SemidirectProduct.isHaarMeasure_prodMeasure, SemidirectProduct.exists_haar_eq_smul_prodMeasure, SemidirectProduct.exists_map_right_haar_restrict_le") (uses := "mathlib_units_haar")
*Left Haar measure of `N ⋊ G` as a product measure.* Haar measure of a semidirect product is Haar measure of the normal factor times a *relatively* invariant measure on the acting factor, the correction being exactly the factor $`χ(g)` by which the action of `g` rescales Haar measure of `N`. The proof is short because left translation by a fixed $`x_0` acts on the two product coordinates separately — the acting coordinate of $`x_0` is fixed, so its action on `N` does not depend on the point being translated — hence `Measure.map_prod_map` applies, and the two coordinate factors $`χ(x_0.\mathrm{right})` and $`χ(x_0.\mathrm{right}^{-1})` cancel by multiplicativity alone. No positivity or finiteness of the character is used.
:::

The relatively invariant measure on `G` comes from twisting Haar measure by the character: for a monoid homomorphism $`χ:G\to[0,∞]`, left translation rescales $`χ\,\mathrm dκ` by $`χ(g_0^{-1})`. Finiteness on compacts and positivity on open sets are inherited from the two factors through the product homeomorphism, so uniqueness of Haar measure identifies the canonical Haar measure of the semidirect product with the product measure up to a positive finite factor.

The estimate extracted for use downstream bounds, on a compact subset of the group, the image of Haar measure under the projection to the acting factor by the relatively invariant measure, with constant the Haar measure of the compact projection to the normal factor.

*Haar measure under a group automorphism*

:::theorem "mathlib_haar_automorphism" (lean := "MeasureTheory.exists_map_continuousMulEquiv_haar_eq_smul_haar, MeasureTheory.exists_map_continuousMulEquiv_haar_restrict_eq_smul_haar_restrict") (uses := "mathlib_semidirect_haar")
*Transporting Haar measure through an automorphism.* A continuous group automorphism with continuous inverse pushes Haar measure to a Haar measure, hence — by uniqueness — to a positive finite multiple of the original one. Restricted to a measurable set, the image measure is exactly that multiple of Haar measure restricted to the image set.
:::

This is the form in which a compactly supported estimate survives a coordinate change of the group. The case needed here is the contragredient map $`L\mapsto (L^\dagger)^{-1}` of a general linear group, which is an automorphism because it is the composition of two anti-automorphisms, inversion and the adjoint.

*Contragredient orbits of the general linear group*

:::theorem "mathlib_general_linear_haar" (lean := "ContinuousLinearMap.contragredientUnit, ContinuousLinearMap.contragredientUnit_val, ContinuousLinearMap.contragredientUnit_inv_val, ContinuousLinearMap.contragredientUnit_mul, ContinuousLinearMap.contragredientUnit_one, ContinuousLinearMap.contragredientUnit_involutive, ContinuousLinearMap.continuous_contragredientUnit_val, ContinuousLinearMap.continuous_contragredientUnit, ContinuousLinearMap.contragredientUnits, ContinuousLinearMap.contragredientUnits_apply, ContinuousLinearMap.evalLinearMap, ContinuousLinearMap.evalLinearMap_apply, ContinuousLinearMap.evalLinearMap_surjective, ContinuousLinearMap.exists_map_contragredientOrbit_haar_restrict_le, ContinuousLinearMap.adjointEvalLinearMap, ContinuousLinearMap.adjointEvalLinearMap_apply, ContinuousLinearMap.adjointEvalLinearMap_surjective, ContinuousLinearMap.exists_map_adjointOrbit_haar_restrict_le") (uses := "mathlib_haar_automorphism, mathlib_units_haar, mathlib_linear_surjection_haar")
*Contragredient orbit maps and Haar measure.* The contragredient map $`L\mapsto (L^{-1})^\dagger` is an automorphism of the group of invertible operators on a finite-dimensional real inner-product space: it composes the two anti-automorphisms $`L\mapsto L^{-1}` and $`L\mapsto L^\dagger`, and it is an involution, so it is its own inverse. Evaluation $`A\mapsto A\xi` at a nonzero vector is a surjective linear map, a rank-one operator realizing any prescribed value.
:::

Chaining the three preceding estimates along $`L\mapsto(L^{-1})^\dagger\mapsto\text{(inclusion into the algebra)}\mapsto A\xi` bounds, on a compact set of invertible operators, the image of Haar measure under a contragredient orbit map by a finite multiple of Lebesgue measure restricted to the compact image. Each of the three steps preserves the compact restriction, which is what makes the composite usable for functions that are only locally integrable.

The variant for the *adjoint* orbit map $`L\mapsto L^\dagger\xi` — the orbit map composed with inversion, which is the form a group convolution consumes — is cheaper: taking adjoints and evaluating are both linear on the operator algebra, so only the unit-group comparison and the linear pushforward bound are used, with no Haar transport along an automorphism.

The symmetric-space material that used to close this page — the abstract Helgason--Fourier layer and the two concrete models it is instantiated at — is now the `ToMathlib / Symmetric spaces` page.
