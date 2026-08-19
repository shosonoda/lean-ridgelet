import LeanRidgelet.ToMathlib.BochnerIntegralL2
import LeanRidgelet.ToMathlib.HaarProdAssoc
import LeanRidgelet.ToMathlib.HilbertSchmidtKernel
import LeanRidgelet.ToMathlib.RelativelyInvariantDensity
import LeanRidgelet.ToMathlib.SymmetricCongruenceDet
import LeanRidgelet.ToMathlib.WeightedSobolevOneDim
import LeanRidgelet.ToMathlib.LipschitzDiscretization
import LeanRidgelet.ToMathlib.LpIntegrableDense
import LeanRidgelet.ToMathlib.LpUnimodular
import LeanRidgelet.ToMathlib.QuasiInvariantIntegral
import LeanRidgelet.ToMathlib.ContinuousConstDensityPreimage
import LeanRidgelet.ToMathlib.AffineHaar
import LeanRidgelet.ToMathlib.LinearSurjectionHaar
import LeanRidgelet.ToMathlib.L2Duality
import LeanRidgelet.ToMathlib.LpOperatorOfPointwise
import LeanRidgelet.ToMathlib.ParametricIteratedDeriv
import LeanRidgelet.ToMathlib.LpFunctor
import LeanRidgelet.ToMathlib.LpIndicator
import LeanRidgelet.ToMathlib.LpCompactlySupportedMultiplier
import LeanRidgelet.ToMathlib.FourierCharacterMultiplier
import LeanRidgelet.ToMathlib.ProdShear
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

#doc (Manual) "Mathlib candidates: Lp and measure transport" =>
%%%
file := "measure-lp"
%%%

General measure-transport lemmas and bounded-operator infrastructure on Bochner `Lp` spaces. These declarations form a dependency boundary used by the Fourier and representation-theoretic pages.

*Lp spaces*

:::theorem "mathlib_lp_integrable_dense" (lean := "MeasureTheory.Lp.dense_setOf_integrable")
*Density of the integrable elements in `Lp`.* For an exponent $`1\le p<\infty`, the classes in $`L^p(\mu)` with an integrable representative — that is, $`L^1\cap L^p(\mu)` — form a dense subset of $`L^p(\mu)`. Mathlib provides the density of `Lp` simple functions (`MeasureTheory.Lp.simpleFunc.dense`) and the integrability of `Lp` simple functions (`MeasureTheory.SimpleFunc.memLp_iff_integrable`) separately, but not this combination, which is the standard entry point for extending an operator defined by an absolutely convergent integral on $`L^1\cap L^p` to all of $`L^p`.
:::

:::theorem "mathlib_lp_unimodular_multiplier" (lean := "MeasureTheory.MemLp.unimodular_mul, MeasureTheory.unimodularMultiplierLinearIsometry, MeasureTheory.unimodularMultiplierLinearIsometry_apply_ae, MeasureTheory.unimodularMultiplierLinearIsometry_surjective, MeasureTheory.unimodularMultiplierLinearIsometryEquiv, MeasureTheory.unimodularMultiplierLinearIsometryEquiv_apply_ae")
*Unimodular multiplication on `Lp`.* An almost-everywhere strongly measurable complex function
`u` with $`|u|=1` acts on every normed $`L^p(\mu)` by pointwise multiplication. The action is
bundled as a linear isometric equivalence, has $`u f` as its almost-everywhere representative,
and is onto because multiplication by $`\overline u` gives a preimage. The proof uses Mathlib's
`MemLp.congr_norm` and does not require a separate integrability estimate.
:::

*Quasi-invariant measure transport*

:::theorem "mathlib_quasi_invariant_integral" (lean := "MeasureTheory.integral_eq_integral_smul_comp_smul_of_map_eq_withDensity, NNReal.smul_inv_sqrt_smul")
*Bochner change of variables for a quasi-invariant measure.* If pushforward by $`x\mapsto g^{-1}x` has nonnegative density $`J_g` with respect to $`\mu`, then every Bochner integrand satisfies $`\int F\,d\mu=\int J_g(x)F(gx)\,d\mu`. The proof packages the action as a measurable equivalence, applies `integral_map_equiv`, and rewrites the resulting `withDensity` integral. The companion identity $`J\cdot J^{-1/2}y=J^{1/2}y` for nonzero $`J` is the algebraic cancellation needed by unitary Radon--Nikodym multipliers.
:::

:::theorem "mathlib_constant_density_preimage" (lean := "MeasureTheory.measure_preimage_eq_nnreal_smul, MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero_of_isOpen_of_map_eq_nnreal_smul, MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero_of_map_eq_nnreal_smul")
*Continuous preimages for constant-density maps.* Suppose continuous maps $`r_i:X\to Y`
converge in the compact-open topology, their pushforward measures are $`c_i\mu`, and the finite
nonnegative constants $`c_i` converge. Then the preimages of every finite-measure measurable set
converge in symmetric-difference measure. The proof first treats open sets using inner regularity
and compact-open convergence, then approximates a measurable set by an open set. This extends
Mathlib's corresponding measure-preserving result to the determinant-scaled maps required by
quasi-regular affine actions.
:::

:::theorem "mathlib_affine_haar" (lean := "LinearEquiv.adjoint, LinearMap.det_adjoint, LinearEquiv.det_adjoint, LinearEquiv.det_skewProd, MeasureTheory.Measure.map_affineEquiv_addHaar_eq_smul_addHaar, MeasureTheory.Measure.map_affineEquiv_symm_addHaar_eq_withDensity")
*Adjoints, block determinants, and affine Haar transport.* In finite-dimensional inner-product
spaces, the adjoint of a linear equivalence is bundled as an equivalence and its determinant is
the conjugate determinant. A block lower-triangular `LinearEquiv.skewProd` has the product of its
diagonal determinants. Finally, an affine equivalence $`x\mapsto Lx+t` pushes an additive Haar
measure forward by the scalar $`|\det L^{-1}|`; the inverse map has the constant `withDensity`
density $`\lVert\det L\rVert`. The proof combines Mathlib's linear Haar change of variables with
translation invariance.
:::

*Hilbert-space duality and `Lp` operators*

:::theorem "mathlib_l2_duality" (lean := "MeasureTheory.eLpNorm_two_eq_lintegral_enorm_sq, MeasureTheory.eLpNorm_two_sq_eq_lintegral_enorm_sq, MeasureTheory.lintegral_enorm_mul_le_eLpNorm_two_mul_eLpNorm_two, MeasureTheory.MemLp.norm_integral_mul_conj_le, MeasureTheory.MemLp.integrable_norm_sq, MeasureTheory.eLpNorm_two_le_of_forall_indicator_pairing_le, MeasureTheory.memLp_two_of_integrable_of_bound")
*Cauchy--Schwarz and an `L²` duality criterion.* Two elementary tools that Mathlib states only in `Lp`-space form. First, *Cauchy--Schwarz for Bochner integrals*: for square-integrable scalar `u`, `v`,
$$`\Big\|\int u\,\overline v\Big\|\le\Big(\int\|u\|^2\Big)^{1/2}\Big(\int\|v\|^2\Big)^{1/2},`
by Hölder's inequality for the norms. Second, an *`L²` duality criterion*: if `h` is measurable, the measurable sets $`s_n` increase to the whole space, every truncation $`1_{s_n}h` is square-integrable, and
$$`\Big|\int h\,\overline{1_{s_n}h}\Big|\le M\,\|1_{s_n}h\|_2\quad\text{for all }n,`
then `h` itself is square-integrable with $`\|h\|_2\le M`. This is the standard device for turning a duality bound $`|\langle h,g\rangle|\le M\|g\|_2` into a norm bound *without* knowing beforehand that `h` lies in `L²`: each truncation is square-integrable by construction, the displayed inequality reads $`t_n\le M\sqrt{t_n}` for $`t_n=\|1_{s_n}h\|_2^2`, and monotone convergence lifts the resulting uniform bound $`t_n\le M^2` to `h`. The auxiliary `lintegral` form of the `L²` seminorm — with and without the square root — the natural-power integrability of $`\|\cdot\|^2`, and the inclusion $`L^1\cap L^\infty\subseteq L^2` (an integrable function with a uniform bound is square-integrable) are provided alongside. So is the `lintegral` form of Cauchy--Schwarz, $`\int^-\|u\|_e\|v\|_e\le\|u\|_2\|v\|_2`, which needs no integrability hypothesis and allows the two targets to differ, so that it applies to a scalar coefficient paired against a vector-valued kernel.
:::

:::theorem "mathlib_parametric_iterated_deriv" (lean := "MeasureTheory.stronglyMeasurable_iteratedDeriv_succ, MeasureTheory.stronglyMeasurable_iteratedDeriv, MeasureTheory.parametricDeriv, MeasureTheory.parametricIteratedDeriv, MeasureTheory.parametricDeriv_slice, MeasureTheory.parametricIteratedDeriv_slice, MeasureTheory.parametricIteratedDeriv_zero, MeasureTheory.parametricIteratedDeriv_succ, MeasureTheory.parametricIteratedDeriv_succ', MeasureTheory.measurable_parametricDeriv_of_continuous, MeasureTheory.measurable_parametricIteratedDeriv_succ_of_continuous, MeasureTheory.contDiff_parametricDeriv, MeasureTheory.continuous_parametricIteratedDeriv, MeasureTheory.measurable_parametricIteratedDeriv, MeasureTheory.measurable_parametricIteratedDeriv_succ")
*Measurability of an iterated derivative in a parameter.* Mathlib knows that a single derivative is measurable with no differentiability assumption — for one variable because the derivative vanishes off the differentiability set and that set is Borel, and for a jointly continuous family by the same argument with a parameter — but neither statement iterates on its own, the parametric one consuming a joint continuity it does not produce. One variable is then free: iterating costs nothing, so an iterated derivative of positive order is strongly measurable for *every* function on the line. A parameter has content, and there are two routes. The *continuity route* supplies the missing induction: the derivative in the last variable of a jointly $`C^{m+1}` function of a pair is jointly $`C^m`, so an induction on the order gives joint continuity of the parametric iterated derivative. Feeding that back into the one-step lemma gains an order, so $`C^j` gives measurability of order $`j+1` rather than of order $`j`. The *limit route* is the one-step lemma itself, stated in this file's notation: joint continuity at order $`j` gives joint measurability at order $`j+1`, assuming no differentiability at all.
:::

:::theorem "mathlib_lp_operator_of_pointwise" (lean := "MeasureTheory.lpLinearMapOfPointwise, MeasureTheory.coeFn_lpLinearMapOfPointwise, MeasureTheory.lpOperatorOfPointwise, MeasureTheory.lpOperatorOfPointwise_apply, MeasureTheory.coeFn_lpOperatorOfPointwise, MeasureTheory.norm_lpOperatorOfPointwise_le")
*A bounded operator on $`L^2` from a pointwise formula.* An integral transform is given by a formula on functions; turning it into a bounded operator is always the same four steps, and this does them once.
:::

The four inputs are: the formula's value is square integrable, the formula is additive and homogeneous almost everywhere, and its $`L^2` norm is at most a constant times the input's. Out comes the operator, with its values represented by the formula and its operator norm bounded by that constant.

Additivity and homogeneity are hypotheses rather than consequences, and that is the point of the packaging. A formula linear on functions need not be linear on almost-everywhere classes: splitting the defining integral over a sum requires each piece to be integrable. So those two hypotheses are exactly where the integrability of an integral transform enters, and isolating them is what makes the rest mechanical.

:::theorem "mathlib_bochner_integral_l2" (lean := "MeasureTheory.integral_L2_coeFn_ae, MeasureTheory.integral_L2_coeFn_ae_of_restrict_of_aefinStronglyMeasurable, MeasureTheory.integral_L2_coeFn_ae_of_restrict, MeasureTheory.integral_norm_restrict_le_norm_mul_rpow")
*Pointwise representatives of `L²`-valued Bochner integrals.* Let $`\Phi(a)` be a scalar `L²`
class with representatives $`F(a,b)`. If $`\Phi` is Bochner integrable and $`F` is integrable on
the product measure, then
$$`\left(\int \Phi(a)\,d\mu(a)\right)(b)=\int F(a,b)\,d\mu(a)`
for almost every $`b`. The proof tests both sides against indicators of arbitrary finite-measure
sets. The resulting `L²` inner-product functional commutes with the Bochner integral, and Fubini
identifies the two set integrals. This is the bridge from an `L²`-valued integrated representation
to a pointwise convolution representative.
:::

Because equality of the two sides is detected by testing against indicators of finite-measure sets, product integrability over all of $`μ\otimesν` is more than the argument needs: integrability over each slice $`μ\otimes(ν|_s)` with $`ν(s)<∞` already justifies the Fubini step. The slice version is what a merely *locally* integrable pointwise integral admits; its price is that measurability of the pointwise integral must be assumed separately, and that $`ν` must be σ-finite for that measurability to yield the fin-strong measurability the test-set criterion consumes. The globally integrable statement is recovered as a corollary. The Hölder bound that makes a slice hypothesis checkable is proved here too: on a set of finite measure the integral of the norm of an `L²` class is at most its `L²` norm times the square root of the measure of the set, so a family whose slices are `L²` classes of a fixed norm is integrable on every finite-measure part.

:::theorem "mathlib_lp_functor" (lean := "MeasureTheory.nontrivial_Lp_of_exists_measurableSet, ContinuousLinearMap.zero_compLpL, ContinuousLinearMap.id_compLpL, ContinuousLinearMap.comp_compLpL, ContinuousLinearMap.sub_compLpL, ContinuousLinearMap.finsetSum_compLpL, ContinuousLinearMap.compLpL_injective, ContinuousLinearMap.lpCoordinateEmbedding, ContinuousLinearMap.lpCoordinateProjection, ContinuousLinearMap.lpCoordinateEmbedding_apply_ae, ContinuousLinearMap.lpCoordinateProjection_apply_ae, ContinuousLinearMap.rankOne_compLpL_eq_coordinate_comp, ContinuousLinearMap.sum_lpCoordinateEmbedding_comp_projection_eq_id, ContinuousLinearMap.exists_eq_compLpL_of_matrixCoefficient_scalar")
*Functoriality and finite coordinate reconstruction on Bochner $`L^p`.* Mathlib's
`ContinuousLinearMap.compLpL` applies a bounded value-space map pointwise, but its elementary
functor laws were absent. A measurable set of positive finite measure gives a nonzero indicator
and hence a nontrivial scalar or vector-valued $`L^p` space. The lift is proved to preserve zero,
identity, composition, subtraction, and finite sums; when scalar $`L^p` is nontrivial it is faithful. Coordinate
embeddings and projections along a finite orthonormal basis therefore give a resolution of the
identity on vector-valued $`L^p`. Consequently, if every matrix coefficient of a bounded
operator on vector-valued $`L^p` is a scalar operator on scalar $`L^p`, the operator is the
pointwise lift of one fixed bounded value-space operator. This is the finite-output substitute
for introducing a completed Hilbert tensor product.
:::

:::theorem "mathlib_lp_indicator" (lean := "MeasureTheory.indicatorMemLp, MeasureTheory.indicatorLpLinearMap, MeasureTheory.indicatorLpLinearMap_apply_ae, MeasureTheory.indicatorLp, MeasureTheory.indicatorLp_apply_ae, MeasureTheory.indicatorLp_comp_self, MeasureTheory.indicatorLp_univ, MeasureTheory.indicatorLp_empty, MeasureTheory.indicatorLp_isSelfAdjoint, MeasureTheory.indicatorLp_isStarProjection, MeasureTheory.indicatorLp_mem_of_starProjection_commute, MeasureTheory.ae_eq_zero_of_mem_orthogonal_of_indicatorLp_mem")
*Measurable-set projections on Bochner $`L^p`.* Multiplication by the indicator of a measurable
set descends to a contractive bounded linear operator on $`L^p`, with the expected almost-everywhere
representative. It is idempotent; the whole-space and empty-set operators are respectively the
identity and zero. On scalar $`L^2` these operators form the canonical projection family used by
systems of imprimitivity: the integral formula for the $`L^2` inner product proves that every
indicator operator is self-adjoint, so idempotence makes it an orthogonal star projection. If the
star projection onto a closed subspace commutes with an indicator operator, that indicator
preserves the subspace.
:::

If a submodule contains every indicator restriction of a fixed vector $`f`, then testing
orthogonality against those restrictions says that the integrable pointwise inner product
$`\langle f,v\rangle` has vanishing integral over every measurable set. Hence a vector orthogonal
to the submodule vanishes almost everywhere on the set where $`f` does not vanish.

:::theorem "mathlib_lp_compact_multiplier" (lean := "HasCompactSupport.exists_simpleFunc_approx, MeasureTheory.simpleFuncMultiplierLp, MeasureTheory.simpleFuncMultiplierLp_apply_ae, MeasureTheory.simpleFuncMultiplierLp_mem_of_indicatorLp_mem, MeasureTheory.compactlySupportedContinuous_memLp, MeasureTheory.compactlySupportedContinuousToLp, MeasureTheory.compactlySupportedContinuousMultiplierLp, MeasureTheory.compactlySupportedContinuousMultiplierLp_apply_ae, MeasureTheory.compactlySupportedContinuousMultiplierLp_mem_of_indicatorLp_mem, MeasureTheory.exists_compactlySupportedContinuousToLp_mem_dist_lt") (uses := "mathlib_lp_indicator")
*Compactly supported scalar multipliers on $`L^2`.* A compactly supported continuous scalar
function is uniformly approximated by measurable simple functions. Its simple multipliers are
finite linear combinations of indicator projections, so every closed subspace stable under all
measurable indicators is stable under compactly supported continuous multiplication. Combining
this with Mathlib's regular-measure approximation theorem and an Urysohn cutoff shows that a
continuous $`L^2` representative can be approximated by compactly supported continuous
representatives in the same closed subspace.
:::

:::theorem "mathlib_fourier_character_multiplier" (lean := "MeasureTheory.eLpNorm_mul_eq_eLpNorm_withDensity_enorm_sq, MeasureTheory.fourierCharacterMultiplierPhase, MeasureTheory.fourierCharacterMultiplierPhase_aestronglyMeasurable, MeasureTheory.fourierCharacterMultiplierPhase_norm_one, MeasureTheory.fourierCharacterLpMultiplier, MeasureTheory.fourierCharacterLpMultiplier_apply_ae, MeasureTheory.integrable_real_eq_zero_of_integral_fourierChar_inner, MeasureTheory.integrable_complex_eq_zero_of_integral_fourierChar_inner, MeasureTheory.exists_fourierCharacter_finset_approx_indicator_eLpNorm, MeasureTheory.exists_finsetSum_fourierCharacterLpMultiplier_approx_indicatorLp, MeasureTheory.ContinuousLinearMap.commutes_finsetSum_fourierCharacterLpMultiplier, MeasureTheory.ContinuousLinearMap.commutes_indicatorLp_of_commutes_fourierCharacter") (uses := "mathlib_lp_indicator")
*Fourier characters generate measurable multipliers on $`L^2`.* A measurable embedding into a
finite-dimensional real inner-product space pulls Mathlib's normalized Fourier characters back to
unitary multiplication operators. A bounded operator commuting with all these character
multipliers also commutes with every finite complex character sum. Finite character sums are dense
in $`L^2` of every finite measure: an orthogonal vector is first regarded as an integrable density;
the positive and negative parts of its real and imaginary components define finite measures, and
Mathlib's characteristic-function uniqueness theorem makes those measures equal. The weighted-
measure calculation then gives simultaneous approximation of two $`L^2` vectors, and a strong-limit
argument yields commutation with every indicator projection. No general projection-valued-measure
API is introduced.
:::

*Product measures*

:::theorem "mathlib_prod_shear" (lean := "MeasureTheory.measurePreserving_prodSwapRight, MeasureTheory.measurePreserving_skewDivLeft, MeasureTheory.measurePreserving_skewSubLeft, MeasureTheory.quasiMeasurePreserving_skewDivLeft, MeasureTheory.quasiMeasurePreserving_skewSubLeft, MeasureTheory.measurePreserving_skewDivRight, MeasureTheory.measurePreserving_skewSubRight, MeasureTheory.quasiMeasurePreserving_skewDivRight, MeasureTheory.quasiMeasurePreserving_skewSubRight")
*Parametrized shears and rearrangements of product measures.* Two elementary transports for iterated Fubini arguments: the rearrangement $`((a,b),c)\mapsto((a,c),b)` exchanging the two right factors of a left-nested triple product of s-finite measures preserves the product measures; and for a measurable parameter map `c` into a measurable group with an invariant fiber measure, the parametrized shears $`(w,b)\mapsto(w,c(w)/b)` and $`(w,b)\mapsto(w,b/c(w))` preserve `μ.prod ν`, with quasi-measure-preserving evaluations $`(w,b)\mapsto c(w)/b` and $`(w,b)\mapsto b/c(w)` (multiplicative and additive versions). The evaluations are the standard device for the joint measurability of kernels $`(w,b)\mapsto g(c(w)-b)` with `g` merely a.e. strongly measurable.
:::

*Relatively invariant densities and the congruence determinant*

:::theorem "mathlib_relatively_invariant_density" (lean := "MeasureTheory.Measure.map_withDensity_of_map_eq_smul, MeasureTheory.Measure.map_restrict_of_map_eq_smul") (uses := "mathlib_affine_haar")
*Weighting a relatively invariant measure.* If a map scales a measure by a constant and scales a weight by a constant, it scales the weighted measure by the product of the two reciprocals; and restricting to an invariant set changes nothing.
:::

The two statements are what turn a relative invariant of a group action into a parameter measure with a prescribed density. The first is stated for an arbitrary measure and an arbitrary scaling, not for a Haar measure and a linear automorphism, precisely so that the second can be composed with it: one restricts a Haar measure to the invariant complement of a degenerate locus, which keeps the scaling, and then weights it.

:::theorem "mathlib_symmetric_congruence_det" (lean := "Matrix.symmetricSubmodule, Matrix.symmetricBasis, Matrix.congrMap, Matrix.congrMap_mul, Matrix.det_congrMap_diagonal, Matrix.det_congrMap_transvection, Matrix.det_congrMap, ContinuousLinearMap.congrSelfAdjoint, ContinuousLinearMap.selfAdjointEquivSymmetric, ContinuousLinearMap.det_congrSelfAdjoint")
*The determinant of congruence.* On the symmetric matrices of size `n`, the map $`A\mapsto M^\top AM` has determinant $`(\det M)^{n+1}`; equivalently, on the self-adjoint endomorphisms of a finite-dimensional real inner product space, congruence has determinant the dimension-plus-one power of the determinant.
:::

Mathlib has the symmetric matrices as a predicate but not as a subspace, so the subspace, its basis indexed by the pairs `i ≤ j`, and the congruence map are built here. Congruence is an anti-homomorphism, so its determinant is multiplicative, and it suffices to compute on the generators of the invertible matrices. On a diagonal matrix the basis is an eigenbasis with eigenvalues the products of the two diagonal entries, and each index occurs in `n + 1` of those products, which gives the exponent. On a transvection the determinant is one, by an argument that avoids both nilpotence and continuity: conjugating a transvection by a diagonal matrix rescales its parameter, so the determinant is invariant under doubling the parameter, while it is also multiplicative in it; being nonzero, it is one. The singular case needs no generators: a vector killed by the transpose produces a nonzero symmetric matrix in the kernel, so both sides vanish. The basis-free form is transported along an orthonormal basis, under which the adjoint becomes the transpose and self-adjointness becomes symmetry.

*Factoring a Haar measure over the last coordinate*

:::theorem "mathlib_haar_prod_assoc" (lean := "MeasureTheory.Measure.map_withDensity_measurableEquiv, MeasureTheory.Measure.exists_map_prodAssoc_symm_eq_smul_prod, MeasureTheory.Measure.preimage_prodAssoc_symm_prod_univ, MeasureTheory.Measure.map_prodAssoc_symm_restrict_of_map_eq_smul, MeasureTheory.Measure.map_prodAssoc_symm_withDensity_of_map_eq_smul") (uses := "mathlib_affine_haar")
*Reassociating a triple product.* An additive Haar measure on a right-nested triple product becomes, after the associativity transport, a positive finite multiple of a product of additive Haar measures; and restricting to a set that reads only the first two coordinates, or weighting by a density that reads only those, commutes with the transport.
:::

Three ingredients and no analysis: a product of additive Haar measures is additive Haar, the pushforward of an additive Haar measure along a continuous additive equivalence is additive Haar, and two additive Haar measures on the same group differ by a positive finite scalar. Going through the additive equivalence rather than a linear one keeps the statements at the generality of second-countable locally compact additive groups, with no vector-space structure needed. The commutation with a density is stated separately because Mathlib has no lemma commuting a pushforward with `withDensity`; that gap is filled here.

This is the bookkeeping a Fubini step over the last coordinate of a parameter space needs when the measure is presented abstractly as a Haar measure rather than as a product.

*The weighted Sobolev identity in one variable*

:::theorem "mathlib_weighted_sobolev_one_dim" (lean := "MeasureTheory.Integrable.eLpNorm_fourier, MeasureTheory.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier, MeasureTheory.memLp_two_pow_smul_fourier, SchwartzMap.iteratedDeriv_eq_iterate_derivCLM, SchwartzMap.integrable_iteratedDeriv, SchwartzMap.memLp_two_iteratedDeriv, SchwartzMap.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier, SchwartzMap.memLp_two_pow_smul_fourier") (uses := "mathlib_l2_duality")
*Smoothness is decay.* The `L²` norm of the `k`-th derivative of a function on the line is the `L²` norm of its Fourier transform weighted by the `k`-th power of the frequency, and the weighted transform is square-integrable exactly when the derivative is.
:::

Two inputs and no analysis of its own: the Fourier transform of an iterated derivative is a power of the frequency times the transform, and Plancherel turns that into an identity of norms. The weight that comes out is the `k`-th power of `2π` times the absolute frequency, the factor being the modulus of the multiplier rather than a choice. For a Schwartz function every hypothesis is automatic, which is the form the application uses; the general form asks for the smoothness and the integrability of the derivatives that the multiplier identity needs.

This is the missing bridge for the boundedness route of the harmonic-analysis track. There a derivative in an additive parameter is moved onto the analysis feature, and the identity converts that into a bound in a frequency-weighted coefficient space — smoothness of the feature and of the data becoming decay of the transform.

*Bounded integral operators with a square-integrable kernel*

:::theorem "mathlib_hilbert_schmidt_kernel" (lean := "MeasureTheory.eLpNorm_rpow_toReal_eq_lintegral, MeasureTheory.lintegral_eLpNorm_rpow_prodMk_left, MeasureTheory.MemLp.prodMk_left, MeasureTheory.enorm_integral_mul_conj_le, MeasureTheory.integrable_mul_conj, MeasureTheory.integrable_mul_conj_kernel_ae, MeasureTheory.enorm_integral_mul_conj_kernel_le_ae, MeasureTheory.aestronglyMeasurable_integral_mul_conj_kernel, MeasureTheory.eLpNorm_integral_mul_conj_kernel_le, MeasureTheory.memLp_integral_mul_conj_kernel, MeasureTheory.eLpNorm_prod_swap, MeasureTheory.MemLp.prod_swap, MeasureTheory.eLpNorm_integral_feature_analysis_le, MeasureTheory.memLp_integral_feature_analysis, MeasureTheory.eLpNorm_integral_feature_composite_le, MeasureTheory.memLp_integral_feature_composite, MeasureTheory.hilbertSchmidtKernelLinearMap, MeasureTheory.coeFn_hilbertSchmidtKernelLinearMap, MeasureTheory.norm_hilbertSchmidtKernelLinearMap_le, MeasureTheory.hilbertSchmidtKernelOperator, MeasureTheory.coeFn_hilbertSchmidtKernelOperator, MeasureTheory.norm_hilbertSchmidtKernelOperator_le") (uses := "mathlib_l2_duality")
*Hilbert--Schmidt bound.* If the kernel `k` is square-integrable for the product measure, then $`f\mapsto\int f(y)\overline{k(\cdot,y)}\,dy` maps $`L^2` to $`L^2` with $`\|Tf\|_2\le\|k\|_{L^2(\mu\otimes\mu)}\|f\|_2`.
:::

Almost every slice of a square-integrable kernel is square-integrable — a `MemLp` slice lemma for product measures that Mathlib does not have, proved here for every exponent by Tonelli below infinity and by the essential-supremum bound at infinity. On such a slice, Cauchy--Schwarz makes the integrand integrable and bounds the integral by the product of the two `L²` norms; squaring that bound and integrating in the outer variable turns the slice norms back into the product-measure norm, again by Tonelli. The statement is left unbundled: the operator appears as the explicit integral rather than as a continuous linear map, so nothing has to be unfolded at the point of use. This is condition T1 of the article's boundedness appendix.

The kernel need not join a space to itself: the statement is proved between two measure spaces, which is what it was really proving all along, and only the measure integrated against has to be s-finite. Condition T2 of the same appendix follows by using it twice. The analysis map with feature `\psi` is the kernel operator from the data space to the parameter space, its kernel being the swap of `\psi`, and the synthesis map with feature `\varphi` is the kernel operator back; composing the two bounds gives the composite bound with the product of the two feature norms. Making the analysis half a literal instance needs `MemLp` to be stable under swapping the factors of a product measure, which Mathlib has only for measurability, so that is proved here too. The conjugate is placed on the feature map in the synthesis so that the instance is literal rather than up to a rewrite; the unconjugated reading is the same statement for the conjugate feature, which has the same norm.

The estimate is bundled as well, into a continuous linear map between the two scalar `L²` spaces whose operator norm is at most the `L²` norm of the kernel. Additivity is where the slice integrability is needed: splitting the integral of a sum requires each half to be integrable, which holds for almost every point of the outer variable, and that is exactly the almost-everywhere statement proved above. The bundled operator is what a reconstruction argument consumes, since the machine and the ridgelet transform there are bounded operators on `L²` and not merely pointwise integrals.

*Finite-sum discretization of a Bochner integral*

:::theorem "mathlib_lipschitz_discretization" (lean := "MeasureTheory.exists_fin_measurable_partition_subset_ball, MeasureTheory.integrable_of_lipschitzWith, MeasureTheory.exists_finsetSum_approx_integral_of_lipschitz, MeasureTheory.exists_finsetSum_approx_integral_boundedContinuous_of_lipschitz") (uses := "mathlib_bochner_integral_l2")
*Uniform approximation by finite sums.* A Lipschitz Banach-valued function on a compact metric space with a finite measure has a Bochner integral, and that integral is approximated in norm, to any accuracy, by finite sums $`\sum_i w_i\varphi(\xi_i)` with nonnegative weights.
:::

Compactness supplies a finite cover by balls of a chosen radius; disjointifying it gives a finite measurable partition, and the simple function taking the value of the integrand at the centre of each piece is within the Lipschitz constant times that radius of the integrand everywhere. Its integral is exactly the finite sum with weights the measures of the pieces, and the finiteness of the measure turns the pointwise bound into a bound on the difference of the integrals. Taking the value at the centre rather than at an arbitrary point of each piece halves the constant and removes the need to choose representatives, so the empty parameter space needs no separate treatment. Specializing the Banach space to the bounded continuous functions on an arbitrary topological space gives the article's uniform approximation of an integral representation by finite networks: no measure, compactness, or metric on the data space is involved.

*Pushing a compactly restricted Haar measure by a surjective linear map*

:::theorem "mathlib_linear_surjection_haar" (lean := "MeasureTheory.map_snd_restrict_prod_le, LinearMap.exists_map_restrict_addHaar_le_smul_addHaar") (uses := "mathlib_affine_haar")
*Compactly restricted pushforward bound.* Mathlib's `LinearMap.exists_map_addHaar_eq_smul_addHaar'` pushes a whole additive Haar measure forward along a surjective linear map, and its proportionality factor is infinite as soon as the map has a nontrivial kernel, since the fibers are unbounded. Restricting the source measure to a compact set removes the divergence: the image measure is dominated by a *finite* multiple of additive Haar measure of the target.
:::

The proof reuses Mathlib's decomposition. A complement `T` of the kernel `S` splits the source as $`S\times T`, so the map is the second projection followed by a linear equivalence, and Haar uniqueness turns both the source measure and the target measure into multiples of the corresponding product and pushforward measures. The remaining estimate is elementary and is isolated as its own lemma: the second projection of a product measure restricted to a set is dominated by the second factor, with the measure of the first projection of that set as the constant — finite exactly because the restriction set is compact.
