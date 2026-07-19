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

#doc (Manual) "L2 theory: current manuscript implementation map" =>
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
Let $`(X,\mu)` be a measure space, let $`\mathcal H` and $`\mathcal G` be complex Hilbert
spaces, let $`T:\mathcal G\simeq L^2(X,\mu;\mathcal H)` be unitary, and let
$`L:\mathcal H\to\mathbb C` be continuous and linear. Define
$$`S:=\widetilde L\,T:\mathcal G\to L^2(X,\mu),\qquad
R_h:=T^*J_h:L^2(X,\mu)\to\mathcal G,\qquad J_h[f](x):=f(x)h.`
Here `unitarySynthesis T L` is $`S`, and `unitaryRidgelet T h` is $`R_h`.
:::

:::theorem "abstract_reconstruction" (lean := "LeanRidgelet.unitarySynthesis_comp_unitaryRidgelet, LeanRidgelet.adjoint_unitarySynthesis, LeanRidgelet.unitarySynthesis_comp_adjoint, LeanRidgelet.norm_adjoint_unitarySynthesis_sq") (uses := "abstract_synthesis_and_reconstruction")
Under Definition 1, let $`h\in\mathcal H`, let $`h_L` be the Riesz vector determined by
$`L[h]=\langle h,h_L\rangle`, and put $`c_L:=\|h_L\|^2=\|L\|^2`. Then
$$`S\circ R_h=L[h]I,\qquad S^*=R_{h_L},\qquad S\circ S^*=c_LI,
\qquad \|S^*[f]\|^2=c_L\|f\|^2\quad(f\in L^2(X,\mu)).`
The four conclusions correspond, in order, to `unitarySynthesis_comp_unitaryRidgelet`,
`adjoint_unitarySynthesis`, `unitarySynthesis_comp_adjoint`, and
`norm_adjoint_unitarySynthesis_sq`. No hypothesis $`L\ne0` is required.
:::

:::theorem "abstract_solution_geometry" (lean := "LeanRidgelet.unitaryMoorePenroseInverse, LeanRidgelet.unitaryParameterProjection, LeanRidgelet.unitaryMoorePenroseInverse_rightInverse, LeanRidgelet.isIdempotentElem_unitaryParameterProjection, LeanRidgelet.isSelfAdjoint_unitaryParameterProjection, LeanRidgelet.ker_unitaryParameterProjection, LeanRidgelet.range_unitaryParameterProjection, LeanRidgelet.map_ker_unitarySynthesis, LeanRidgelet.unitarySolution_iff_kernel_translate, LeanRidgelet.unitaryMoorePenroseInverse_pythagorean, LeanRidgelet.unitaryMoorePenroseInverse_unique_minimal") (uses := "abstract_reconstruction")
Assume the data of Definition 1 and $`L\ne0`. Define
$$`S^\dagger:=c_L^{-1}S^*,\qquad P:=S^\dagger S.`
Then $`SS^\dagger=I`, $`P^2=P=P^*`, and
$$`\ker P=\ker S,\qquad \operatorname{ran}P=(\ker S)^\perp,
\qquad T[\ker S]=L^2(X,\mu;\ker L).`
Moreover, for $`f\in L^2(X,\mu)` and $`\gamma\in\mathcal G`,
$$`S[\gamma]=f\iff\gamma-S^\dagger[f]\in\ker S,`
and every such solution satisfies
$$`\|\gamma\|^2=\|S^\dagger[f]\|^2+\|\gamma-S^\dagger[f]\|^2.`
Thus $`S^\dagger[f]` is the unique minimum-norm solution. The linked declarations separately
implement the definitions, right-inverse law, projection laws, kernel/range identities, affine
solution formula, Pythagoras identity, and uniqueness statement in this displayed order.
:::

:::theorem "abstract_basis_expansion" (lean := "LeanRidgelet.hasSum_unitaryRidgelet_coefficients, LeanRidgelet.eq_unitaryCoefficient_of_hasSum_unitaryRidgelet, LeanRidgelet.hasSum_norm_sq_unitaryCoefficient, LeanRidgelet.mem_ker_unitarySynthesis_iff_coefficients, LeanRidgelet.unitaryNullDoubleCoefficients, LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis") (uses := "abstract_solution_geometry")
Assume Definition 1 and let $`(e_i)_{i\in I}` be a Hilbert basis of $`L^2(X,\mu)`. For
$`\gamma\in\mathcal G`, define $`h_i[\gamma]\in\mathcal H` by the partial inner product of
$`T[\gamma]` against $`e_i`. Then
$$`\gamma=\sum_{i\in I}R_{h_i[\gamma]}[e_i],\qquad
\sum_{i\in I}\|h_i[\gamma]\|^2=\|\gamma\|^2,`
and these coefficient vectors are unique. Furthermore,
$$`\gamma\in\ker S\iff(\forall i\in I)\;h_i[\gamma]\in\ker L.`
If $`(k_j)_{j\in J}` is a Hilbert basis of $`\ker L`, every $`\gamma\in\ker S` also has the
unconditionally convergent expansion
$$`\gamma=\sum_{(i,j)\in I\times J}c_{ij}\,R_{k_j}[e_i],
\qquad(c_{ij})\in\ell^2(I\times J).`
The linked declarations implement, respectively, existence, uniqueness, Parseval, the null-space
criterion, the $`\ell^2` coefficient, and the double expansion.
:::

*Section 3: Neural-Network Specialization: Hilbert Spaces and Boundedness*

:::definition "activation_space" (lean := "LeanRidgelet.ActivationSpace, LeanRidgelet.activationDistribution")
For $`s,t\in\mathbb R`, define the activation space
$$`\mathcal A_{s,t}:=\langle\cdot\rangle^tH^s(\mathbb R),`
represented by its Fourier--Bessel coordinate $`u\in L^2(\mathbb R)`. In Lean,
`ActivationSpace s t` is this coordinate Hilbert space and `activationDistribution s t u` is
the associated tempered distribution
$$`\sigma=\langle\cdot\rangle^t\langle\partial\rangle^{-s}[u].`
:::

:::proposition "activation_hilbert_structure" (lean := "LeanRidgelet.l2_proposition_one_activation_hilbert_structure") (uses := "activation_space")
For every $`s,t\in\mathbb R`, the coordinate map of Definition 5 is a linear isometric
equivalence
$$`\mathcal A_{s,t}\simeq L^2(\mathbb R).`
Consequently $`\mathcal A_{s,t}` is a complex Hilbert space.
:::

:::definition "coefficient_space" (lean := "LeanRidgelet.fiberNormSq, LeanRidgelet.FiberSpace, LeanRidgelet.fiberDistribution, LeanRidgelet.fiberDistribution_coe")
Let $`m\ge1` and $`s,t\in\mathbb R`. For $`h\in\mathcal S(\mathbb R)`, define
$$`\|h\|_{\mathcal H_{s,t}}^2:=C_m\int_{\mathbb R}|h(\omega)|^2|\omega|^m\,d\omega
+\int_{\mathbb R}|\langle\partial_\omega\rangle^t[h](\omega)|^2
\langle\omega\rangle^{-2s}\,d\omega.`
The coefficient space $`\mathcal H_{s,t}` is the Hilbert completion of this normed core.
`fiberNormSq` is the displayed quadratic form and `FiberSpace m s t` is its completion.
For every completed $`h\in\mathcal H_{s,t}`, `fiberDistribution m s t h` is a tempered
distribution; `fiberDistribution_coe` states that this realization equals the original Schwartz
function on the dense core.
:::

:::definition "activation_functional" (lean := "LeanRidgelet.activationFiberFunctional, LeanRidgelet.activationSpectrum, LeanRidgelet.activationRealization, LeanRidgelet.activationSpectrum_apply, LeanRidgelet.activationFiberFunctional_eq_spectrum") (uses := "activation_space, coefficient_space")
Let $`m\ge1`, $`s,t\in\mathbb R`, and $`\sigma\in\mathcal A_{s,t}`. Define the spectrum
$`\sigma^\sharp:=\texttt{activationSpectrum}(\sigma)` and its inverse-Fourier realization
$`\sigma_{\mathrm{cl}}:=\mathcal F^{-1}[\sigma^\sharp]`. Then the pairing extends uniquely to
a continuous linear functional $`L_\sigma:\mathcal H_{s,t}\to\mathbb C` with
$$`\|L_\sigma\|\le(2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}},\qquad
L_\sigma[h]=(2\pi)^{m-1}\sigma^\sharp[h]`
for every Schwartz-core coefficient $`h`. `activationSpectrum` and `activationRealization`
define the two realizations; `activationSpectrum_apply` gives the spectrum action; and
`activationFiberFunctional_eq_spectrum` is the displayed pairing identity.
:::

:::definition "pointwise_coordinate_transform" (lean := "LeanRidgelet.fourierDilationTransformCore, LeanRidgelet.fourierDilationTransformFiberCore, LeanRidgelet.fourierDilationTransformCoreL2, LeanRidgelet.parameterSchwartzRealization")
Let $`m\ge1`, $`s,t\in\mathbb R`, and $`\gamma\in\mathcal S(\mathbb R^m\times\mathbb R)`.
Define
$$`T_{\mathrm{pt}}[\gamma](x,\omega):=(2\pi)^{-m}
\int_{\mathbb R^m\times\mathbb R}\gamma(a,b)e^{i\omega(a\cdot x-b)}\,da\,db.`
`fourierDilationTransformCore` is this scalar formula;
`fourierDilationTransformFiberCore` bundles $`\omega\mapsto T_{\mathrm{pt}}[\gamma](x,\omega)`
as a coefficient-core vector. If this fiber-valued map belongs to Bochner $`L^2`,
`fourierDilationTransformCoreL2` and `parameterSchwartzRealization` bundle it into the completed
coordinate and parameter spaces.
:::

:::lemma_ "weighted_dilation_identity" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul") (uses := "pointwise_coordinate_transform")
Let $`m\ge1` and let $`g:\mathbb R^m\times\mathbb R\to[0,\infty]` be Borel measurable. Then
$$`\int g(a,\omega)\,da\,d\omega=\int g(-\omega x,\omega)|\omega|^m\,dx\,d\omega.`
The exceptional slice $`\omega=0` is handled measure-theoretically rather than by claiming a
globally invertible change of variables.
:::

:::definition "parameter_space_and_unitary_transform" (lean := "LeanRidgelet.ParameterSpace, LeanRidgelet.parameterCoordinateEquiv, LeanRidgelet.fourierDilationTransform, LeanRidgelet.inverseFourierDilationTransform") (uses := "coefficient_space, pointwise_coordinate_transform, weighted_dilation_identity")
Let $`m\ge1` and $`s,t\in\mathbb R`. Define the parameter Hilbert space and its coordinate map by
$$`\mathcal G_{s,t}:=L^2(\mathbb R^m;\mathcal H_{s,t}),\qquad
T:\mathcal G_{s,t}\simeq L^2(\mathbb R^m;\mathcal H_{s,t}).`
In Lean, `ParameterSpace m s t` is the transported coordinate model,
`parameterCoordinateEquiv m s t` and `fourierDilationTransform m s t` are $`T`, and
`inverseFourierDilationTransform m s t` is $`T^{-1}`. The identification of this model with the
manuscript's concrete graph domain is treated separately on the compatibility domain.
:::

:::proposition "concrete_unitary_transform" (lean := "LeanRidgelet.fourierDilationTransform, LeanRidgelet.inverseFourierDilationTransform_apply_fourierDilationTransform, LeanRidgelet.fourierDilationCompatibilityDomain, LeanRidgelet.mem_fourierDilationCompatibilityDomain_iff_memLp, LeanRidgelet.fourierDilationTransform_parameterSchwartzRealization_apply_ae, LeanRidgelet.inverseFourierDilationTransformCore") (uses := "parameter_space_and_unitary_transform")
Let $`m\ge1`, $`s,t\in\mathbb R`, and let $`T` be Definition 11. Then $`T` is unitary and
$$`T^{-1}T=I.`
If $`\gamma\in\mathcal S(\mathbb R^m\times\mathbb R)` satisfies
$`T_{\mathrm{pt}}[\gamma]\in L^2(\mathbb R^m;\mathcal H_{s,t})`, then
$$`T[\gamma]=T_{\mathrm{pt}}[\gamma]\quad\text{a.e.}`
after embedding $`\gamma` by `parameterSchwartzRealization`. The inverse core is
$$`T^{-1}_{\mathrm{pt}}[u](a,b)=\frac1{2\pi}\int u(x,\omega)
e^{-i\omega(a\cdot x-b)}|\omega|^m\,dx\,d\omega.`
The linked declarations give $`T`, $`T^{-1}T=I`, the compatibility domain and its $`L^2`
criterion, the a.e. forward agreement, and the inverse-core formula, respectively. Equality of
the last integral with the transported inverse is not yet asserted.
:::

:::definition "hilbert_space_synthesis" (lean := "LeanRidgelet.networkSynthesis, LeanRidgelet.networkSynthesis_eq_unitarySynthesis, LeanRidgelet.networkSynthesis_apply_fourierDilation_ae, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_apply_ae, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_fourierPairing_ae") (uses := "activation_functional, concrete_unitary_transform, abstract_synthesis_and_reconstruction")
Let $`m\ge1`, $`s,t\in\mathbb R`, $`\sigma\in\mathcal A_{s,t}`, and let $`T` and
$`L_\sigma` be Definitions 11 and 8. Define
$$`S_\sigma:=\widetilde L_\sigma T:\mathcal G_{s,t}\to L^2(\mathbb R^m),\qquad
S_\sigma[\gamma](x):=L_\sigma[T[\gamma](x,\cdot)].`
`networkSynthesis` defines $`S_\sigma`; `networkSynthesis_eq_unitarySynthesis` gives the
factorization; the three remaining linked declarations give the a.e. coordinate formula and its
Schwartz-core and Fourier-pairing specializations.
:::

:::theorem "bounded_synthesis" (lean := "LeanRidgelet.l2_theorem_one_bounded_synthesis, LeanRidgelet.norm_networkSynthesis_le, LeanRidgelet.classicalSynthesisIntegral, LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae") (uses := "hilbert_space_synthesis")
Let $`m\ge1`, $`s,t\in\mathbb R`, $`\sigma\in\mathcal A_{s,t}`, and
$`\gamma\in\mathcal G_{s,t}`. Then
$$`\|S[\gamma]\|_2\le (2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}}\|\gamma\|_{\mathcal G_{s,t}}.`
This estimate is the second component of `l2_theorem_one_bounded_synthesis`. In addition, if
$`\gamma` lies in the Schwartz compatibility domain, the classical integral is absolutely
defined, and `activationRealization σ` acts by integration against a function
$`\sigma_{\mathrm{cl}}`, then
$$`S_\sigma[\gamma](x)=\int\gamma(a,b)\sigma_{\mathrm{cl}}(a\cdot x-b)\,da\,db
\quad\text{for a.e. }x.`
`classicalSynthesisIntegral` defines the right-hand side and
`networkSynthesis_parameterSchwartzRealization_classical_ae` proves this equality.
:::

*Section 4: Neural-Network Specialization: Ridgelet Reconstruction from the Fourier Expression*

:::definition "ridgelet_transform_and_pairing" (lean := "LeanRidgelet.ridgeletOperator, LeanRidgelet.ridgeletOperator_eq_unitaryRidgelet, LeanRidgelet.fiberBaseCoordinate, LeanRidgelet.ridgeletSpectrum, LeanRidgelet.ridgeletSpectrum_coe, LeanRidgelet.ridgeletFunction, LeanRidgelet.paperFourierDistribution_ridgeletFunction, LeanRidgelet.classicalRidgeletFunction, LeanRidgelet.classicalRidgeletIntegral, LeanRidgelet.ridgeletFunctionCore_apply_classical") (uses := "concrete_unitary_transform")
Let $`m\ge1`, $`s,t\in\mathbb R`, $`h\in\mathcal H_{s,t}`, and
$`f\in L^2(\mathbb R^m)`. Define
$$`R_h[f]:=T^*[f\otimes h],\qquad \rho_h^\sharp:=|\omega|^m\overline h,
\qquad \rho_h:=\mathcal F^{-1}[\rho_h^\sharp].`
`ridgeletOperator` is $`R_h` and `ridgeletOperator_eq_unitaryRidgelet` gives the displayed
factorization. `fiberBaseCoordinate`, `ridgeletSpectrum`, and `ridgeletFunction` construct the
completed distributional data; `ridgeletSpectrum_coe` proves the pointwise spectrum formula on
the Schwartz core; and `paperFourierDistribution_ridgeletFunction` proves
$`\rho_h^\sharp=\mathcal F[\rho_h]`. For Schwartz $`h`, `classicalRidgeletFunction` is a function
representing $`\rho_h`, and `classicalRidgeletIntegral` defines
$$`R[f;\rho_h](a,b):=\int f(x)\overline{\rho_h(a\cdot x-b)}\,dx.`
:::

:::lemma_ "fourier_expressions" (lean := "LeanRidgelet.l2_lemma_one_ridgelet_fiber_representation, LeanRidgelet.fourierDilationTransform_ridgeletOperator_apply_ae, LeanRidgelet.classicalRidgeletIntegral_eq_inverseTensorIntegral, LeanRidgelet.classicalRidgeletIntegral_eq_inverseFourierDilationTransformCore") (uses := "ridgelet_transform_and_pairing, bounded_synthesis")
Let $`m\ge1`, $`s,t\in\mathbb R`, $`h\in\mathcal H_{s,t}`, and
$`f\in L^2(\mathbb R^m)`. Then
$$`T[R_h[f]](x)=f(x)h\quad\text{for a.e. }x.`
This is `fourierDilationTransform_ridgeletOperator_apply_ae`; its compatibility wrapper is
`l2_lemma_one_ridgelet_fiber_representation`. If $`f` and $`h` are Schwartz and the classical
ridgelet integral of Definition 15 is integrable, then for every $`(a,b)` it equals
$$`\frac1{2\pi}\int f(x)h(\omega)e^{-i\omega(a\cdot x-b)}|\omega|^m\,dx\,d\omega.`
This is `classicalRidgeletIntegral_eq_inverseTensorIntegral`, and
`classicalRidgeletIntegral_eq_inverseFourierDilationTransformCore` identifies the same expression
with the inverse-transform core. The separate bias/input Fourier formulas (32)--(33) are not
asserted by these declarations.
:::

:::theorem "concrete_reconstruction" (lean := "LeanRidgelet.l2_theorem_two_reconstruction, LeanRidgelet.networkSynthesis_comp_ridgeletOperator") (uses := "fourier_expressions, abstract_reconstruction")
Let $`m\ge1`, $`s,t\in\mathbb R`, $`\sigma\in\mathcal A_{s,t}`, and
$`h\in\mathcal H_{s,t}`. Then
$$`S_\sigma\circ R_h=L_\sigma[h]I,`
that is, $`S_\sigma[R_h[f]]=L_\sigma[h]f` for every $`f\in L^2(\mathbb R^m)`.
This is `networkSynthesis_comp_ridgeletOperator`; `l2_theorem_two_reconstruction` is its
manuscript-numbered compatibility wrapper. If a classical ridgelet function $`\rho` has
$`h=|\omega|^{-m}\overline{\rho^\sharp}`, this becomes
$`S_\sigma[R[f;\rho]]=\langle\!\langle\sigma,\rho\rangle\!\rangle f`; bundling the forward map
$`\rho\mapsto h` remains outside the current statement.
:::

*Section 5: Neural-Network Specialization: Adjoint, Null Space, and Complete General Solution*

:::definition "adjoint_ridgelet_function" (lean := "LeanRidgelet.activationRieszRepresenter, LeanRidgelet.activationNormalization, LeanRidgelet.ridgeletFunction, LeanRidgelet.paperFourierDistribution_ridgeletFunction") (uses := "activation_functional, ridgelet_transform_and_pairing")
Let $`m\ge1`, $`s,t\in\mathbb R`, and $`\sigma\in\mathcal A_{s,t}`. Define the Riesz vector
$`h_\sigma\in\mathcal H_{s,t}` and normalization $`c_\sigma` by
$$`L_\sigma[h]=\langle h,h_\sigma\rangle,qquad
c_\sigma:=\|h_\sigma\|^2=\|L_\sigma\|^2.`
Define the adjoint ridgelet distribution $`\sigma_*:=\rho_{h_\sigma}`; equivalently,
$$`\sigma_*^\sharp=|\omega|^m\overline{h_\sigma}.`
`activationRieszRepresenter` and `activationNormalization` define $`h_\sigma` and
$`c_\sigma`; `ridgeletFunction` constructs $`\sigma_*`; and
`paperFourierDistribution_ridgeletFunction` proves its spectrum formula.
:::

:::lemma_ "concrete_adjoint" (lean := "LeanRidgelet.l2_lemma_two_adjoint, LeanRidgelet.adjoint_networkSynthesis, LeanRidgelet.networkSynthesis_comp_adjoint") (uses := "adjoint_ridgelet_function, abstract_reconstruction")
Under Definition 18, for every $`f\in L^2(\mathbb R^m)`,
$$`S_\sigma^*=R_{h_\sigma},\qquad
S_\sigma S_\sigma^*=c_\sigma I,\qquad
\|S_\sigma^*[f]\|^2=c_\sigma\|f\|^2.`
The first two identities are `adjoint_networkSynthesis` and `networkSynthesis_comp_adjoint` and
are bundled by `l2_lemma_two_adjoint`; the norm identity follows from the linked abstract
reconstruction theorem. With $`\sigma_*` from Definition 18, the manuscript writes the first
identity as $`S_\sigma^*[f]=R[f;\sigma_*]`.
:::

:::definition "canonical_solution_and_projection" (lean := "LeanRidgelet.normalizedNetworkRightInverse, LeanRidgelet.networkVisibleProjection, LeanRidgelet.normalizedNetworkRightInverse_rightInverse, LeanRidgelet.isSelfAdjoint_networkVisibleProjection") (uses := "concrete_adjoint, abstract_solution_geometry")
Let $`\sigma\in\mathcal A_{s,t}` satisfy $`\sigma\ne0`. Define
$$`S_\sigma^\dagger:=c_\sigma^{-1}S_\sigma^*,\qquad
P_\sigma:=S_\sigma^\dagger S_\sigma.`
Then $`S_\sigma S_\sigma^\dagger=I` and $`P_\sigma^*=P_\sigma`.
`normalizedNetworkRightInverse` and `networkVisibleProjection` define the two operators;
`normalizedNetworkRightInverse_rightInverse` and `isSelfAdjoint_networkVisibleProjection` prove
the two displayed properties.
:::

:::theorem "concrete_null_space_and_general_solution" (lean := "LeanRidgelet.l2_theorem_three_null_space_and_general_solution, LeanRidgelet.mem_ker_networkSynthesis_iff_fourierDilation, LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient, LeanRidgelet.networkSolution_iff_kernel_translate, LeanRidgelet.normalizedNetworkRightInverse_unique_minimal, LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis") (uses := "canonical_solution_and_projection, abstract_basis_expansion, fourier_expressions")
Let $`\sigma\in\mathcal A_{s,t}` satisfy $`\sigma\ne0`, let $`(e_i)_{i\in I}` be a Hilbert basis
of $`L^2(\mathbb R^m)`, and let $`\gamma\in\mathcal G_{s,t}`. Then
$$`\gamma\in\ker S_\sigma\iff
L_\sigma[T[\gamma](x,\cdot)]=0\ \text{for a.e. }x
\iff(\forall i)\;h_i[\gamma]\in\ker L_\sigma,`
and
$$`\gamma=\sum_iR_{h_i[\gamma]}[e_i]`
with unique coefficient vectors. For $`f\in L^2(\mathbb R^m)`, all solutions are exactly
$$`\{\gamma:S_\sigma[\gamma]=f\}=S_\sigma^\dagger[f]+\ker S_\sigma,`
and $`S_\sigma^\dagger[f]` is the unique minimum-norm solution. The linked concrete declarations
prove the pointwise criterion, series, affine formula, and minimum statement; the abstract
`hasSum_unitaryRidgelet_kernelBasis` supplies the double $`\ell^2` null expansion.
:::

*Section 6: Examples of Adjoint Ridgelet Functions: ReLU, Sigmoidal, and Gaussian Activations*

The manuscript's Example 2 derives one-dimensional weak resolvent formulas for the adjoint
ridgelet functions of ReLU, tanh, the Gaussian cumulative distribution function, and the Gaussian
density. Lean currently formalizes membership and distributional realizations for several standard
activations, but not these explicit Riesz-resolvent formulas.

*Section 7: Further Developments: Finite-Width Approximation of Null Elements*

:::definition "measure_valued_synthesis"
Let $`\mu` be a finite complex Radon measure on parameter space and let $`\nu` be a finite data
measure. If the feature map $`\theta\mapsto\sigma(a\cdot x-b)` has finite $`L^2(\nu)` energy
with respect to $`|\mu|`, define
$$`S_\nu[\mu]:=\int\sigma(a\cdot{\,\cdot\,}-b)\,d\mu(a,b)
\in L^2(\nu).`
This measure-valued domain is distinct from $`\mathcal G_{s,t}`. No Lean declaration is linked
because the Radon-measure construction has not yet been formalized.
:::

:::theorem "normalized_finite_width_approximation" (lean := "LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation") (uses := "measure_valued_synthesis")
Let $`(\Theta,\mu)` be a probability space, let $`H` be a complex Hilbert space, and let
$`\Phi:\Theta\to H` and $`u:\Theta\to\mathbb C` satisfy
$$`|u(\theta)|=1\ \text{a.e.},\qquad
\int\|\Phi(\theta)\|^2d\mu(\theta)<\infty,\qquad
\int u(\theta)\Phi(\theta)d\mu(\theta)=0.`
Then for every integer $`N\ge1` there exist $`\theta_1,\ldots,\theta_N\in\Theta` such that
$$`\left\|\frac1N\sum_{j=1}^Nu(\theta_j)\Phi(\theta_j)\right\|
\le\sqrt{\frac{\int\|\Phi\|^2d\mu}{N}}.`
The linked Lean declaration states this Hilbert-valued sampling conclusion. The manuscript's
stronger Radon-measure, exact mean-square, and almost-sure convergence assertions are not part of
that Lean statement.
:::

:::corollary "discretizable_ridgelet_null_elements" (lean := "LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements") (uses := "normalized_finite_width_approximation, concrete_null_space_and_general_solution")
Let $`m\ge1`, $`s,t\in\mathbb R`, and let $`0\ne\sigma\in\mathcal A_{s,t}`. Then there exist
$`0\ne f\in L^2(\mathbb R^m)` and $`0\ne h\in\mathcal H_{s,t}` such that
$$`L_\sigma[h]=0,\qquad R_h[f]\in\ker S_\sigma.`
This is exactly the coordinate-level conclusion of the linked Lean declaration. The manuscript's
additional passage from a Schwartz ridgelet element to a normalized Radon measure, under
continuity, polynomial-growth, and compact-support assumptions, remains outside this statement.
:::

:::proposition "exact_finite_null_relations" (lean := "LeanRidgelet.l2_proposition_two_exact_finite_null_relations")
Let $`m\ge0`, $`a,x\in\mathbb R^m`, and $`b\in\mathbb R`. If $`\sigma` is odd, then
$$`\sigma(a\cdot x-b)+\sigma((-a)\cdot x-(-b))=0,`
and if $`\sigma` is even, the same two terms have difference zero. Moreover, for
$`c_j\in\mathbb R`, $`a_j\in\mathbb R^m`, and $`b_j\in\mathbb R` satisfying
$$`\sum_jc_ja_j=0,\qquad\sum_jc_jb_j=0,`
the ReLU features satisfy, for every $`x`,
$$`\sum_jc_j\bigl((a_j\cdot x-b_j)_+-((-a_j)\cdot x-(-b_j))_+\bigr)=0.`
These three algebraic conclusions are the three conjuncts of the linked Lean declaration.
:::

*Section 8: Further Developments: Numerical Illustration in Finite Networks*

This section is a numerical illustration rather than a formal theorem. It discretizes continuous
ridgelet null elements and distinguishes antipodal cancellation from a genuinely nontrivial null
relation. No structural result depends on the experiment.

*Section 9: Further Developments: Perturbative Readout of Null-Space Information*

:::theorem "null_space_encoding_and_perturbations" (lean := "LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout") (uses := "concrete_null_space_and_general_solution, canonical_solution_and_projection")
Let $`m\ge1`, $`s,t\in\mathbb R`, and let $`0\ne\sigma\in\mathcal A_{s,t}`. There exist
orthonormal $`(h_i)_{i\in\mathbb N}\subset\ker L_\sigma` and activations
$`(\tau_i)_{i\in\mathbb N}` satisfying
$$`L_{\tau_i}[h_j]=\delta_{ij}.`
For every $`f_0\in L^2(\mathbb R^m)` and every sequence $`(f_i)` with
$`\sum_i\|f_i\|^2<\infty`, there exists $`\gamma_{\mathrm{enc}}\in\mathcal G_{s,t}` such that
$$`S_\sigma[\gamma_{\mathrm{enc}}]=f_0,\qquad
\gamma_{\mathrm{enc}}-S_\sigma^\dagger[f_0]=\sum_iR_{h_i}[f_i],qquad
S_{\tau_i}[\gamma_{\mathrm{enc}}]=f_i.`
For $`\delta\gamma_i:=S_\sigma^\dagger[f_i-f_0]`, one further has
$$`S_\sigma[\gamma_{\mathrm{enc}}+\delta\gamma_i]=f_i,qquad
(I-P_\sigma)(\gamma_{\mathrm{enc}}+\delta\gamma_i)
=(I-P_\sigma)\gamma_{\mathrm{enc}}.`
These are precisely the existential data and conclusions collected by the linked Lean statement;
the manuscript's stronger uniqueness and exact-norm refinements are not asserted there.
:::

*Section 10: Discussion*

This section separates the proved continuous null-space structure, its finite-width traces, and
the interpretation of null-space information. It introduces no additional numbered mathematical
result.

*Section 11: Conclusion*

The conclusion summarizes the paper and likewise adds no numbered result.
