import LeanRidgelet
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

#doc (Manual) "Current manuscript implementation map" =>
%%%
file := "overview"
%%%

This chapter follows the publication order and single shared theorem-like counter of the
submitted manuscript snapshot `ghost20260718submit.pdf` (2026-07-19), corresponding to the active
LaTeX tree at revision `354ffde`. The paper first
derives the separated Fourier expression in the Introduction, isolates its abstract unitary
operator theory in Section 2, and only then constructs the concrete activation, coefficient, and
parameter spaces. Later sections treat adjoint ridgelet functions, finite-width consequences,
numerics, and parameter perturbations as distinct developments.

The Lean project completely implements the abstract unitary layer and its transported-coordinate
specialization. A few concrete analytic identifications still stop at the coefficient-vector
level; these boundaries are stated below rather than hidden behind assumptions. A declaration
containing `sorry` records a later manuscript result whose proof is still pending and is checked by
the assumption audit.

The Fourier expression method in Section 1.2 proposes
$$`\gamma^\sharp(\xi/\omega,\omega)=\widehat f(\xi)\overline{\rho^\sharp(\omega)}`
and separates one particular direction from homogeneous directions. Lean currently validates the
resulting unitary-coordinate and Hilbert-basis theory. It also reconstructs a ridgelet distribution
continuously from every completed coefficient vector, with the expected weighted spectrum on the
dense Schwartz core. On the Schwartz compatibility domain, the synthesis and ridgelet operators
now agree with the classical network and ridgelet integrals; the remaining classical boundaries
are the explicit Fourier formulas (32)--(33) and per-activation realization formulas.

*Section 2: Abstract Reconstruction Formula and Solution Geometry*

:::definition "abstract_synthesis_and_reconstruction" (lean := "LeanRidgelet.unitarySynthesis, LeanRidgelet.unitaryRidgelet")
*Abstract synthesis and reconstruction operators.* For a unitary
$`T:\mathcal G\to L^2(X,\mu;\mathcal H)` and $`L\in\mathcal H^*`, define
$$`S:=\widetilde L T,\qquad J_h[f](x):=f(x)h,\qquad R_h:=T^*J_h.`
These are `unitarySynthesis` and `unitaryRidgelet`; the coordinate-side names
`fiberSynthesis` and `fiberRidgelet` denote $`\widetilde L` and $`J_h`.
:::

:::theorem "abstract_reconstruction" (lean := "LeanRidgelet.unitarySynthesis_comp_unitaryRidgelet, LeanRidgelet.adjoint_unitarySynthesis, LeanRidgelet.unitarySynthesis_comp_adjoint, LeanRidgelet.norm_adjoint_unitarySynthesis_sq") (uses := "abstract_synthesis_and_reconstruction")
*Reconstruction from a unitary factorization.* If $`h_L` is the Riesz representer of
$`L` and $`c_L=\|h_L\|^2=\|L\|^2`, then
$$`SR_h=L[h]I,\qquad S^*=R_{h_L},\qquad SS^*=c_LI,\qquad \|S^*[f]\|^2=c_L\|f\|^2.`
No nonzero assumption on $`L` is needed for these identities.
:::

:::theorem "abstract_solution_geometry" (lean := "LeanRidgelet.unitaryMoorePenroseInverse, LeanRidgelet.unitaryParameterProjection, LeanRidgelet.unitaryMoorePenroseInverse_rightInverse, LeanRidgelet.isIdempotentElem_unitaryParameterProjection, LeanRidgelet.isSelfAdjoint_unitaryParameterProjection, LeanRidgelet.ker_unitaryParameterProjection, LeanRidgelet.range_unitaryParameterProjection, LeanRidgelet.map_ker_unitarySynthesis, LeanRidgelet.unitarySolution_iff_kernel_translate, LeanRidgelet.unitaryMoorePenroseInverse_pythagorean, LeanRidgelet.unitaryMoorePenroseInverse_unique_minimal") (uses := "abstract_reconstruction")
*Orthogonal geometry of the solution set.* For $`L\ne0`, put
$`S^\dagger=c_L^{-1}S^*` and $`P=S^\dagger S`. Then $`S^\dagger` is a right inverse, $`P` is the
canonical orthogonal parameter projection, and
$$`T[\ker S]=L^2(X,\mu;\ker L),\qquad \operatorname{im}P=(\ker S)^\perp.`
Every solution is $`S^\dagger[f]+\eta` with $`\eta\in\ker S`; the Pythagoras identity makes
$`S^\dagger[f]` the unique minimum-norm solution.
:::

:::theorem "abstract_basis_expansion" (lean := "LeanRidgelet.hasSum_unitaryRidgelet_coefficients, LeanRidgelet.eq_unitaryCoefficient_of_hasSum_unitaryRidgelet, LeanRidgelet.hasSum_norm_sq_unitaryCoefficient, LeanRidgelet.mem_ker_unitarySynthesis_iff_coefficients, LeanRidgelet.unitaryNullDoubleCoefficients, LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis") (uses := "abstract_solution_geometry")
*Hilbert-basis expansion in parameter space.* For any Hilbert basis
$`\{e_i\}_{i\in I}` of the target space,
$$`\gamma=\sum_{i\in I}R_{h_i[\gamma]}[e_i],\qquad \sum_{i\in I}\|h_i[\gamma]\|^2=\|\gamma\|^2.`
The coefficients are unique, and $`\gamma\in\ker S` exactly when every
$`h_i[\gamma]\in\ker L`. A Hilbert basis $`\{k_j\}_{j\in J}` of $`\ker L` gives an
unconditionally convergent double expansion with an actual $`\ell^2(I\times J)` coefficient.
:::

*Section 3: Neural-Network Specialization: Hilbert Spaces and Boundedness*

:::definition "activation_space" (lean := "LeanRidgelet.ActivationSpace, LeanRidgelet.activationDistribution")
*Activation space.* The manuscript defines the weighted Sobolev Hilbert space
$`\mathcal A_{s,t}=\langle\cdot\rangle^tH^s(\mathbb R)` through its Fourier--Bessel coordinate.
Lean realizes this space by its isometric $`L^2(\mathbb R)` coordinate together with the associated
tempered distribution.
:::

:::proposition "activation_hilbert_structure" (lean := "LeanRidgelet.l2_proposition_one_activation_hilbert_structure") (uses := "activation_space")
*Activation Hilbert structure.* The weighted Fourier--Bessel coordinate is an
isometric isomorphism from $`\mathcal A_{s,t}` onto $`L^2(\mathbb R)`; hence
$`\mathcal A_{s,t}` is a Hilbert space.
:::

:::definition "coefficient_space" (lean := "LeanRidgelet.fiberNormSq, LeanRidgelet.FiberSpace, LeanRidgelet.fiberDistribution, LeanRidgelet.fiberDistribution_coe")
*Coefficient space.* The coefficient Hilbert space $`\mathcal H_{s,t}` is the
completion of the Schwartz core for the sum of the dilation-Jacobian norm and the weighted
Bessel-potential norm. In Lean the historical identifier `FiberSpace` denotes this coefficient
space; an individual $`T[\gamma](x,\cdot)` is a coefficient vector, not a separate fiber. A
continuous map realizes completed coefficient vectors as tempered distributions and recovers the
original Schwartz function on the dense core.
:::

:::definition "activation_functional" (lean := "LeanRidgelet.activationFiberFunctional, LeanRidgelet.activationSpectrum, LeanRidgelet.activationRealization, LeanRidgelet.activationSpectrum_apply, LeanRidgelet.activationFiberFunctional_eq_spectrum") (uses := "activation_space, coefficient_space")
*Activation functional.* The distributional pairing with $`\sigma^\sharp` extends
to a bounded functional $`L_\sigma\in\mathcal H_{s,t}^*`, satisfying
$`\|L_\sigma\|\le (2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}}`.
Lean reconstructs the spectrum $`\sigma^\sharp` and the classical activation
$`\sigma=\mathcal F^{-1}[\sigma^\sharp]` from the activation coordinate and proves
$`L_\sigma[h]=(2\pi)^{m-1}\sigma^\sharp[h]` on the Schwartz core.
:::

:::definition "pointwise_coordinate_transform" (lean := "LeanRidgelet.fourierDilationTransformCore, LeanRidgelet.fourierDilationTransformFiberCore, LeanRidgelet.fourierDilationTransformCoreL2, LeanRidgelet.parameterSchwartzRealization")
*Coordinate transform on Schwartz parameters.* The pointwise formula is
$$`T_{\mathrm{pt}}[\gamma](x,\omega)=(2\pi)^{-m}\!\int\gamma(a,b)e^{i\omega(a\cdot x-b)}\,da\,db.`
It is compared with the Hilbert transform only on the natural compatibility domain
$`\mathcal S^T_{s,t}`. Lean keeps the required Bochner `MemLp` evidence as an explicit theorem
argument instead of placing it in an assumption object.
:::

:::lemma_ "weighted_dilation_identity" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul") (uses := "pointwise_coordinate_transform")
*Weighted dilation identity.* For nonnegative Borel $`g`,
$$`\int g(a,\omega)\,da\,d\omega=\int g(-\omega x,\omega)|\omega|^m\,dx\,d\omega.`
The exceptional slice $`\omega=0` is handled measure-theoretically rather than by claiming a
globally invertible change of variables.
:::

:::definition "parameter_space_and_unitary_transform" (lean := "LeanRidgelet.ParameterSpace, LeanRidgelet.parameterCoordinateEquiv, LeanRidgelet.fourierDilationTransform, LeanRidgelet.inverseFourierDilationTransform") (uses := "coefficient_space, pointwise_coordinate_transform, weighted_dilation_identity")
*Parameter space and unitary coordinate transform.* The manuscript uses the graph
domain $`\mathcal G_{s,t}` and its unitary map
$`T:\mathcal G_{s,t}\to L^2(\mathbb R^m;\mathcal H_{s,t})`. Lean currently defines the source by
transport from the Bochner coordinate model, so `ParameterSpace` and `parameterCoordinateEquiv`
provide the same Hilbert-space interface while the graph-domain analytic identification remains
separate.
:::

:::proposition "concrete_unitary_transform" (lean := "LeanRidgelet.fourierDilationTransform, LeanRidgelet.inverseFourierDilationTransform_apply_fourierDilationTransform, LeanRidgelet.fourierDilationCompatibilityDomain, LeanRidgelet.mem_fourierDilationCompatibilityDomain_iff_memLp, LeanRidgelet.fourierDilationTransform_parameterSchwartzRealization_apply_ae, LeanRidgelet.inverseFourierDilationTransformCore") (uses := "parameter_space_and_unitary_transform")
*Concrete unitary coordinate transform.* The graph-domain transform is unitary;
its inverse is first given by an integral on the dense algebraic tensor class
$`\mathcal E_{s,t}` and then extended by Hilbert-space limits. Lean proves the transported unitary
and natural-domain forward compatibility and defines the inverse core formula. The final equality
between that inverse integral and the transported inverse is still an analytic boundary.
:::

:::definition "hilbert_space_synthesis" (lean := "LeanRidgelet.networkSynthesis, LeanRidgelet.networkSynthesis_eq_unitarySynthesis, LeanRidgelet.networkSynthesis_apply_fourierDilation_ae, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_apply_ae, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_fourierPairing_ae") (uses := "activation_functional, concrete_unitary_transform, abstract_synthesis_and_reconstruction")
*Hilbert-space synthesis operator.* The completed operator is
$`S=\widetilde L_\sigma T`, equivalently
$`S[\gamma](x)=L_\sigma[T[\gamma](x,\cdot)]`. The classical parameter integral is the motivating
formula and is asserted only on its natural domain.
:::

:::theorem "bounded_synthesis" (lean := "LeanRidgelet.l2_theorem_one_bounded_synthesis, LeanRidgelet.norm_networkSynthesis_le, LeanRidgelet.classicalSynthesisIntegral, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae") (uses := "hilbert_space_synthesis")
*Boundedness of $`S`.* For $`\sigma\in\mathcal A_{s,t}`,
$$`\|S[\gamma]\|_2\le (2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}}\|\gamma\|_{\mathcal G_{s,t}}.`
The coordinate operator and estimate are formalized. On the Schwartz compatibility domain,
`networkSynthesis` agrees almost everywhere with the classical integral
$`\int\gamma(a,b)\,\sigma_{\mathrm{cl}}(a\cdot x-b)\,da\,db` whenever the classical integral is
defined and the realized activation acts by integration against $`\sigma_{\mathrm{cl}}`.
:::

*Section 4: Neural-Network Specialization: Ridgelet Reconstruction from the Fourier Expression*

:::definition "ridgelet_transform_and_pairing" (lean := "LeanRidgelet.ridgeletOperator, LeanRidgelet.ridgeletOperator_eq_unitaryRidgelet, LeanRidgelet.fiberBaseCoordinate, LeanRidgelet.ridgeletSpectrum, LeanRidgelet.ridgeletSpectrum_coe, LeanRidgelet.ridgeletFunction, LeanRidgelet.paperFourierDistribution_ridgeletFunction, LeanRidgelet.classicalRidgeletFunction, LeanRidgelet.classicalRidgeletIntegral, LeanRidgelet.ridgeletFunctionCore_apply_classical") (uses := "concrete_unitary_transform")
*Ridgelet transform and activation pairing.* For a compatible ridgelet function
$`\rho`, the coefficient vector is $`h_\rho=|\omega|^{-m}\overline{\rho^\sharp}` and the rigorous
operator is $`R[f;\rho]=T^*[f\otimes h_\rho]`. Lean implements the coefficient-vector operator
$`R_h`, the tempered-distribution realization of completed $`h`, and the continuous
conjugate-linear inverse construction $`h\mapsto\rho` with spectrum
$`\rho^\sharp=|\omega|^m\overline h`. This spectrum formula agrees pointwise on the Schwartz core,
and the reconstructed distribution acts by integration against the classical ridgelet function.
The completed function space $`\mathcal B_{s,t}` and the forward weighted Fourier map
$`\rho\mapsto h_\rho` are not yet bundled.
:::

:::lemma_ "fourier_expressions" (lean := "LeanRidgelet.l2_lemma_one_ridgelet_fiber_representation, LeanRidgelet.fourierDilationTransform_ridgeletOperator_apply_ae, LeanRidgelet.classicalRidgeletIntegral_eq_inverseTensorIntegral, LeanRidgelet.classicalRidgeletIntegral_eq_inverseFourierDilationTransformCore") (uses := "ridgelet_transform_and_pairing, bounded_synthesis")
*Fourier expressions for $`S` and $`R`.* The manuscript proves the bias-Fourier formulas
and the coordinate identity $`T[R[f;\rho]]=f\otimes h_\rho`. Lean proves the simple-tensor
coordinate identity, and that the classical ridgelet integral for the reconstructed classical
ridgelet function equals the inverse-coordinate integral formula on the tensor section
representing $`T[R_h[f]]`. The explicit bias/input Fourier formulas (32)--(33) are still pending.
:::

:::theorem "concrete_reconstruction" (lean := "LeanRidgelet.l2_theorem_two_reconstruction, LeanRidgelet.networkSynthesis_comp_ridgeletOperator") (uses := "fourier_expressions, abstract_reconstruction")
*Reconstruction formula.* For $`f\in L^2(\mathbb R^m)`, compatible $`\rho`, and
$`\sigma\in\mathcal A_{s,t}`,
$$`S[R[f;\rho]]=\langle\!\langle\sigma,\rho\rangle\!\rangle f.`
The coefficient-vector form $`S\circ R_h=L_\sigma[h]I` is fully formalized; the classical
$`\rho`-formula depends on the preceding unfinished identification.
:::

*Section 5: Neural-Network Specialization: Adjoint, Null Space, and Complete General Solution*

:::definition "adjoint_ridgelet_function" (lean := "LeanRidgelet.activationRieszRepresenter, LeanRidgelet.activationNormalization") (uses := "activation_functional, ridgelet_transform_and_pairing")
*Adjoint ridgelet function.* The Riesz vector $`h_\sigma` of $`L_\sigma` determines
$`\sigma_*^\sharp=|\omega|^m\overline{h_\sigma}` and
$`c_\sigma=\|h_\sigma\|^2=\|L_\sigma\|^2`. Lean implements $`h_\sigma` and $`c_\sigma`; the
distributional ridgelet function $`\sigma_*` itself is not yet constructed.
:::

:::lemma_ "concrete_adjoint" (lean := "LeanRidgelet.l2_lemma_two_adjoint, LeanRidgelet.adjoint_networkSynthesis, LeanRidgelet.networkSynthesis_comp_adjoint") (uses := "adjoint_ridgelet_function, abstract_reconstruction")
*Concrete adjoint and canonical ridgelet.* In coefficient coordinates,
$$`S^*=R_{h_\sigma},\qquad SS^*=c_\sigma I,\qquad \|S^*[f]\|^2=c_\sigma\|f\|^2.`
The manuscript writes the first identity as $`S^*[f]=R[f;\sigma_*]`.
:::

:::definition "canonical_solution_and_projection" (lean := "LeanRidgelet.normalizedNetworkRightInverse, LeanRidgelet.networkVisibleProjection, LeanRidgelet.normalizedNetworkRightInverse_rightInverse, LeanRidgelet.isSelfAdjoint_networkVisibleProjection") (uses := "concrete_adjoint, abstract_solution_geometry")
*Canonical solution and parameter projection.* Define
$`S^\dagger=c_\sigma^{-1}S^*` and $`P=S^\dagger S`. Lean retains the historical internal names
`normalizedNetworkRightInverse` and `networkVisibleProjection`, while the documentation uses the
manuscript terminology.
:::

:::theorem "concrete_null_space_and_general_solution" (lean := "LeanRidgelet.l2_theorem_three_null_space_and_general_solution, LeanRidgelet.mem_ker_networkSynthesis_iff_fourierDilation, LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient, LeanRidgelet.networkSolution_iff_kernel_translate, LeanRidgelet.normalizedNetworkRightInverse_unique_minimal, LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis") (uses := "canonical_solution_and_projection, abstract_basis_expansion, fourier_expressions")
*Ridgelet characterization of the null space and general solution.* The theorem
identifies $`T[\ker S]=L^2(\mathbb R^m;\ker L_\sigma)`, gives the unique coefficient expansion of
every null element, and writes every solution as a particular ridgelet solution plus that null
series. Lean proves the complete coefficient-vector expansion, affine solution set, double
$`\ell^2` expansion, and minimum-norm statement. Translating every coefficient vector back to a
classical ridgelet function $`\rho_i` still uses the unfinished analytic map from Definition 15.
:::

*Section 6: Examples of Adjoint Ridgelet Functions: ReLU, Sigmoidal, and Gaussian Activations*

The manuscript's Example 2 derives one-dimensional weak resolvent formulas for the adjoint
ridgelet functions of ReLU, tanh, the Gaussian cumulative distribution function, and the Gaussian
density. Lean currently formalizes membership and distributional realizations for several standard
activations, but not these explicit Riesz-resolvent formulas.

*Section 7: Further Developments: Finite-Width Approximation of Null Elements*

:::definition "measure_valued_synthesis"
*Measure-valued synthesis.* For a finite complex Radon measure $`\mu` and localized
data measure $`\nu`, the manuscript defines $`S_\nu[\mu]` as a Bochner integral under a finite
feature-energy condition. This measure-valued space is deliberately separate from
$`\mathcal G_{s,t}` and has not yet been formalized.
:::

:::theorem "normalized_finite_width_approximation" (lean := "LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation") (uses := "measure_valued_synthesis")
*Normalized finite-width approximation of a null measure.* A normalized nonzero null
measure admits width-$`N` atomic approximations with output error at most
$`E_\nu(\mu_0)^{1/2}N^{-1/2}`, exact mean-square rate $`E_\nu(\mu_0)/N`, and almost-sure weak-star
and output convergence. The current named Lean placeholder states the Hilbert-valued sampling core;
the full Radon-measure and convergence theorem remains open.
:::

:::corollary "discretizable_ridgelet_null_elements" (lean := "LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements") (uses := "normalized_finite_width_approximation, concrete_null_space_and_general_solution")
*Discretizable ridgelet null elements.* Under continuity, polynomial growth, and
compact data support, a nonzero Schwartz ridgelet null element produces a normalized null measure
to which Theorem 23 applies. The Lean placeholder currently records existence of a nonzero
coordinate-side null ridgelet candidate, not the full measure construction.
:::

:::proposition "exact_finite_null_relations" (lean := "LeanRidgelet.l2_proposition_two_exact_finite_null_relations")
*Exact finite null relations.* Odd and even activations give antipodal two-atom
relations, while ReLU admits the stated affine-cancellation family. This algebraic statement is
tracked by a named Lean placeholder.
:::

*Section 8: Further Developments: Numerical Illustration in Finite Networks*

This section is a numerical illustration rather than a formal theorem. It discretizes continuous
ridgelet null elements and distinguishes antipodal cancellation from a genuinely nontrivial null
relation. No structural result depends on the experiment.

*Section 9: Further Developments: Perturbative Readout of Null-Space Information*

:::theorem "null_space_encoding_and_perturbations" (lean := "LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout") (uses := "concrete_null_space_and_general_solution, canonical_solution_and_projection")
*Null-space encoding and parameter perturbations.* A square-summable family is encoded
in orthonormal null coefficient directions. Riesz-dual activations read individual entries, while
the minimum-norm additive perturbation $`S^\dagger[f_i-f_0]` changes the represented output and
preserves the stored null component. The current Lean declaration is a named placeholder for this
construction; its statement covers the encoding and invariant-null-component identities, while
the complete uniqueness and exact norm formula still require proof-level refinement.
:::

*Section 10: Discussion*

This section separates the proved continuous null-space structure, its finite-width traces, and
the interpretation of null-space information. It introduces no additional numbered mathematical
result.

*Section 11: Conclusion*

The conclusion summarizes the paper and likewise adds no numbered result.
