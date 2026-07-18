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

#doc (Manual) "L2 implementation map in current publication order" =>
%%%
file := "overview"
%%%

The current manuscript first proves the unitary operator theory for an arbitrary parameter Hilbert
space $`\mathcal G`, then specializes it to the graph-domain realization of integral-representation
networks. The first three nodes below follow that publication order and link directly to the new
unitary transport layer. Concrete nodes still use compatibility wrapper names where that keeps the
existing public API stable. A declaration containing `sorry` records a later main result whose
proof remains to be formalized; these placeholders are explicitly named and checked by the
assumption audit.

:::proposition "abstract_proposition_one" (lean := "LeanRidgelet.unitarySynthesis_comp_unitaryRidgelet")
*Proposition 1 (Synthesis and reconstruction in unitary coordinates).* For a unitary
$`T:\mathcal G\to L^2(X;\mathcal H)` and bounded $`L:\mathcal H\to\mathbb C`, define
$`S=\widetilde L T` and $`R_h=T^*J_h`. Then
$$`S\circ R_h=L[h]I,\qquad S^*=R_{h_L},\qquad SS^*=c_LI`,
where $`c_L=\|h_L\|^2=\|L\|^2`. The implementation also exposes the exact adjoint norm identity
$`\|S^*[f]\|^2=c_L\|f\|^2`.
:::

:::theorem "abstract_theorem_one" (lean := "LeanRidgelet.unitaryMoorePenroseInverse_pythagorean") (uses := "abstract_proposition_one")
*Theorem 1 (Orthogonal geometry of the solution set).* If $`L\ne0`, the normalized adjoint is a
right inverse, $`P=S^\dagger S` is the canonical orthogonal parameter projection, and
$$`T[\ker S]=L^2(X;\ker L)`.
Every solution is $`S^\dagger[f]+\eta` with $`\eta\in\ker S`, and satisfies the Pythagoras identity
$$`\|\gamma\|^2=\|S^\dagger[f]\|^2+\|\gamma-S^\dagger[f]\|^2`.
Thus the canonical solution is the unique minimum-norm solution.
:::

:::theorem "abstract_theorem_two" (lean := "LeanRidgelet.hasSum_unitaryRidgelet_coefficients, LeanRidgelet.eq_unitaryCoefficient_of_hasSum_unitaryRidgelet, LeanRidgelet.hasSum_norm_sq_unitaryCoefficient, LeanRidgelet.mem_ker_unitarySynthesis_iff_coefficients, LeanRidgelet.unitaryNullDoubleCoefficients, LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis") (uses := "abstract_theorem_one")
*Theorem 2 (Hilbert-basis expansion in parameter space).* For an arbitrary Hilbert basis
$`\{e_i\}_{i\in I}` of the target space, every parameter has a unique unconditional expansion
$$`\gamma=\sum_{i\in I}R_{h_i[\gamma]}[e_i]`,
and the coefficient vectors satisfy Parseval's identity
$$`\sum_{i\in I}\|h_i[\gamma]\|^2=\|\gamma\|^2`.
Lean also proves $`\gamma\in\ker S` iff every $`h_i[\gamma]\in\ker L`. Given a Hilbert basis
$`\{u_j\}_{j\in J}` of $`\ker L`, the null coefficients form an element of $`\ell^2(I\times J)`,
and the resulting flattened $`I\times J` ridgelet series converges unconditionally to $`\gamma`.
:::

:::proposition "l2_proposition_one" (lean := "LeanRidgelet.l2_proposition_one_activation_hilbert_structure")
*Proposition 2 (Activation Hilbert structure).* The activation space $`\mathcal A_{s,t}` is a
Hilbert space, and its weighted Bessel coordinate map is an isometric isomorphism onto
$`L^2(\mathbb R)`.
:::

:::lemma_ "weighted_dilation_identity" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul") (uses := "l2_proposition_one")
*Lemma 1 (Weighted dilation identity).* The Fourier--dilation pullback preserves the relevant
nonnegative weighted integral. The exceptional slice $`\omega=0` is handled measure-theoretically,
without treating the singular pullback as a globally invertible change of variables.
:::

:::proposition "concrete_unitary_transform" (lean := "LeanRidgelet.fourierDilationTransform") (uses := "weighted_dilation_identity")
*Proposition 3 (Concrete unitary coordinate transform).* The graph-domain transform is a unitary
map from the parameter Hilbert space to $`L^2(\mathbb R^m;\mathcal H_{s,t})`. In the current Lean
model the source is defined by transport along this coordinate equivalence.
:::

:::proposition "schwartz_compatibility" (lean := "LeanRidgelet.fourierDilationTransform_parameterSchwartzRealization") (uses := "concrete_unitary_transform")
*Proposition 4 (Compatibility on Schwartz parameters).* On the natural compatibility domain where
the pointwise Schwartz transform is a Bochner $`L^2` coordinate, the unitary transform agrees with
that pointwise formula almost everywhere. No inclusion of all Schwartz parameters is asserted.
:::

:::theorem "l2_theorem_one" (lean := "LeanRidgelet.l2_theorem_one_bounded_synthesis") (uses := "schwartz_compatibility, abstract_proposition_one")
*Theorem 3 (Boundedness of synthesis).* For $`\sigma\in\mathcal A_{s,t}`, the coordinate formula
$$`S_\sigma[\gamma](x)=L_\sigma[T[\gamma](x,\cdot)]`
defines a bounded operator $`S_\sigma:\mathcal G_{s,t}\to L^2(\mathbb R^m)` satisfying
$$`\|S_\sigma[\gamma]\|_2\le (2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}}\|\gamma\|_{\mathcal G_{s,t}}`.
The wrapper covers this Fourier--dilation coordinate statement; agreement with the classical
integral on its natural domain remains a separate formalization task.
:::

:::lemma_ "l2_lemma_one" (lean := "LeanRidgelet.l2_lemma_one_ridgelet_fiber_representation") (uses := "l2_theorem_one")
*Lemma 2 (Fourier expressions for $`S` and $`R`).* The manuscript gives the bias-Fourier formulas
for $`R[f;\rho]` and $`S_\sigma[\gamma]`, and the coordinate identity
$$`T[R[f;\rho]](x,\omega)=f(x)h_\rho(\omega)`.
The Lean wrapper records the implemented simple-tensor coordinate identity. The classical Fourier
formulas remain to be connected to it.
:::

:::theorem "l2_theorem_two" (lean := "LeanRidgelet.l2_theorem_two_reconstruction") (uses := "l2_lemma_one")
*Theorem 4 (Reconstruction formula).* For every compatible coefficient vector $`h`,
$$`S_\sigma\circ R_h=L_\sigma[h]I`.
In the manuscript notation this is $`S_\sigma[R[f;\rho]]=\langle\!\langle\sigma,\rho\rangle\!\rangle f`.
:::

:::lemma_ "l2_lemma_two" (lean := "LeanRidgelet.l2_lemma_two_adjoint") (uses := "l2_theorem_two")
*Lemma 3 (Concrete adjoint and canonical ridgelet).* If $`h_\sigma` is the Riesz representer and
$`c_\sigma=\|h_\sigma\|^2`, then
$$`S_\sigma^*=R_{h_\sigma},\qquad S_\sigma\circ S_\sigma^*=c_\sigma I`.
:::

:::corollary "l2_theorem_three" (lean := "LeanRidgelet.l2_theorem_three_null_space_and_general_solution") (uses := "l2_lemma_two, abstract_theorem_one, abstract_theorem_two")
*Corollary 1 (Concrete null-space structure and general solution).* In unitary coordinates,
$$`T[\ker S_\sigma]=L^2(\mathbb R^m;\ker L_\sigma)`.
Relative to a fixed Hilbert basis, every parameter has a unique ridgelet series. The null
parameters are exactly those whose coefficient vectors lie in $`\ker L_\sigma`, and every solution
of $`S_\sigma[\gamma]=f` is $`S_\sigma^\dagger[f]+\gamma_0` with
$`\gamma_0\in\ker S_\sigma`. The canonical solution $`S_\sigma^\dagger[f]` is the unique
minimum-norm solution.
:::

:::theorem "l2_theorem_five" (lean := "LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation")
*Theorem 5 (Normalized finite-width approximation).* A normalized nonzero null measure with
finite feature energy admits width-$`N` atomic approximations of total variation one whose output
error is at most $`E^{1/2}N^{-1/2}`. Independent sampling also gives the exact mean-square rate
$`E/N` and almost-sure convergence.
:::

:::corollary "l2_corollary_one" (lean := "LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements") (uses := "l2_theorem_three, l2_theorem_five")
*Corollary 2 (Discretizable ridgelet null elements).* For a continuous activation of at most
polynomial growth and compactly supported data measure, a nonzero Schwartz ridgelet null element
induces a normalized null measure to which Theorem 5 applies.
:::

:::proposition "l2_proposition_two" (lean := "LeanRidgelet.l2_proposition_two_exact_finite_null_relations")
*Proposition 5 (Exact finite null relations).* Odd and even activations give exact two-atom null
relations. For ReLU, every finite family satisfying the affine cancellation conditions
$`\sum_j c_j a_j=0` and $`\sum_j c_j b_j=0` gives an exact finite null relation.
:::

:::theorem "l2_theorem_four" (lean := "LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout") (uses := "l2_theorem_three")
*Theorem 6 (Encoding and perturbative readout).* A countable square-summable family of target
functions can be encoded isometrically in orthonormal null fibers. Dual activations read individual
functions, and a minimum-norm additive perturbation moves the selected function into the visible
component without changing the stored null component.
:::
