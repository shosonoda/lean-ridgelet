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

#doc (Manual) "Overview of the L2 main results" =>
%%%
file := "overview"
%%%

This chapter lists the numbered results of the L2 manuscript in publication order. A green Lean
declaration is a thin wrapper around the coordinate-based implementation already present in the
library. A declaration containing `sorry` records a main result whose proof remains to be
formalized; these placeholders are explicitly named and checked by the assumption audit.

:::proposition "l2_proposition_one" (lean := "LeanRidgelet.l2_proposition_one_activation_hilbert_structure")
*Proposition 1 (Activation Hilbert structure).* The activation space $`\mathcal A_{s,t}` is a
Hilbert space, and its weighted Bessel coordinate map is an isometric isomorphism onto
$`L^2(\mathbb R)`.
:::

:::theorem "l2_theorem_one" (lean := "LeanRidgelet.l2_theorem_one_bounded_synthesis") (uses := "l2_proposition_one")
*Theorem 1 (Boundedness of synthesis).* For $`\sigma\in\mathcal A_{s,t}`, the coordinate formula
$$`S_\sigma[\gamma](x)=L_\sigma[T[\gamma](x,\cdot)]`
defines a bounded operator $`S_\sigma:\mathcal G_{s,t}\to L^2(\mathbb R^m)` satisfying
$$`\|S_\sigma[\gamma]\|_2\le (2\pi)^{m-1}\|\sigma\|_{\mathcal A_{s,t}}\|\gamma\|_{\mathcal G_{s,t}}`.
The wrapper covers this Fourier--dilation coordinate statement; agreement with the classical
integral on its natural domain remains a separate formalization task.
:::

:::lemma_ "l2_lemma_one" (lean := "LeanRidgelet.l2_lemma_one_ridgelet_fiber_representation") (uses := "l2_theorem_one")
*Lemma 1 (Fourier and fiber representations).* The manuscript gives the bias-Fourier formulas
for $`R[f;\rho]` and $`S_\sigma[\gamma]`, and the fiber identity
$$`T[R[f;\rho]](x,\omega)=f(x)q_\rho(\omega)`.
The Lean wrapper records the implemented simple-tensor fiber identity. The classical Fourier
formulas remain to be connected to it.
:::

:::theorem "l2_theorem_two" (lean := "LeanRidgelet.l2_theorem_two_reconstruction") (uses := "l2_lemma_one")
*Theorem 2 (Reconstruction formula).* For every compatible ridgelet fiber $`q`,
$$`S_\sigma\circ R_q=L_\sigma[q]I`.
In the manuscript notation this is $`S_\sigma[R[f;\rho]]=\langle\!\langle\sigma,\rho\rangle\!\rangle f`.
:::

:::lemma_ "l2_lemma_two" (lean := "LeanRidgelet.l2_lemma_two_adjoint") (uses := "l2_theorem_two")
*Lemma 2 (Adjoint).* If $`q_\sigma` is the Riesz fiber and
$`c_\sigma=\|q_\sigma\|^2`, then
$$`S_\sigma^*=R_{q_\sigma},\qquad S_\sigma\circ S_\sigma^*=c_\sigma I`.
:::

:::theorem "l2_theorem_three" (lean := "LeanRidgelet.l2_theorem_three_null_space_and_general_solution") (uses := "l2_lemma_two")
*Theorem 3 (Structure of the null space and general solution).* In Fourier--dilation coordinates,
$$`T[\ker S_\sigma]=L^2(\mathbb R^m;\ker L_\sigma)`.
Relative to a fixed Hilbert basis, every parameter has a unique ridgelet series. The null
parameters are exactly those whose coefficient fibers lie in $`\ker L_\sigma`, and every solution
of $`S_\sigma[\gamma]=f` is $`S_\sigma^\dagger[f]+\gamma_0` with
$`\gamma_0\in\ker S_\sigma`. The canonical solution $`S_\sigma^\dagger[f]` is the unique
minimum-norm solution.
:::

:::theorem "l2_theorem_four" (lean := "LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout") (uses := "l2_theorem_three")
*Theorem 4 (Encoding and perturbative readout).* A countable square-summable family of target
functions can be encoded isometrically in orthonormal null fibers. Dual activations read individual
functions, and a minimum-norm additive perturbation moves the selected function into the visible
component without changing the stored null component.
:::

:::theorem "l2_theorem_five" (lean := "LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation")
*Theorem 5 (Normalized finite-width approximation).* A normalized nonzero null measure with
finite feature energy admits width-$`N` atomic approximations of total variation one whose output
error is at most $`E^{1/2}N^{-1/2}`. Independent sampling also gives the exact mean-square rate
$`E/N` and almost-sure convergence.
:::

:::corollary "l2_corollary_one" (lean := "LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements") (uses := "l2_theorem_three, l2_theorem_five")
*Corollary 1 (Discretizable ridgelet null elements).* For a continuous activation of at most
polynomial growth and compactly supported data measure, a nonzero Schwartz ridgelet null element
induces a normalized null measure to which Theorem 5 applies.
:::

:::proposition "l2_proposition_two" (lean := "LeanRidgelet.l2_proposition_two_exact_finite_null_relations")
*Proposition 2 (Exact finite null relations).* Odd and even activations give exact two-atom null
relations. For ReLU, every finite family satisfying the affine cancellation conditions
$`\sum_j c_j a_j=0` and $`\sum_j c_j b_j=0` gives an exact finite null relation.
:::
