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

#doc (Manual) "Further results from the source manuscript" =>
%%%
file := "further-results"
%%%

The following results appear in `05journal/body.tex` but lie beyond the current formalization of
Chapters 2--5. They are recorded as unformalized nodes with their dependencies made explicit.

:::theorem "encoding_and_perturbative_readout"
A countable family of $`L^2` functions can be encoded isometrically into an orthonormal sequence
in the null fiber. A suitable additive parameter perturbation reads a selected function into the
visible component without changing the null component, and this perturbation is the unique one of
minimum norm.
:::

:::definition "measure_valued_synthesis"
For a finite complex Radon measure $`\mu` and a localized data measure $`\nu`, define the
measure-valued synthesis $`S_\nu[\mu]` as the Bochner integral of the feature map.
:::

:::theorem "normalized_finite_width_null_approximation" (uses := "measure_valued_synthesis")
A null measure of total variation one can be approximated by an atomic measure of width $`N`,
whose output norm converges to zero at rate $`O(N^{-1/2})`.
:::

:::lemma_ "truncated_monte_carlo_quadrature" (uses := "measure_valued_synthesis")
Uniform Monte Carlo sampling on a bounded parameter domain for a finite measure separates the
truncation error from the sampling error, and the latter has mean square $`O(N^{-1})`.
:::

:::corollary "discretizable_ridgelet_null_elements" (uses := "normalized_finite_width_null_approximation")
For a continuous activation of at most polynomial growth and a compactly supported data measure,
every Schwartz ridgelet null element yields a finite-width null approximation.
:::

:::proposition "exact_finite_null_relations"
The parity of an activation gives an exact two-atom null relation. For ReLU, affine cancellation
conditions give further exact null relations among finitely many neurons.
:::
