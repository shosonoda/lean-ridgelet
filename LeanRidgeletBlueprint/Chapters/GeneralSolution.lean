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

#doc (Manual) "Null space and the general solution" =>
%%%
file := "general-solution"
%%%

:::definition "canonical_parameter_projection" (lean := "LeanRidgelet.networkVisibleProjection")
Define the canonical orthogonal parameter projection by
$`P=S_\sigma^\dagger\circ S_\sigma`.
:::

:::theorem "canonical_parameter_projection_properties" (lean := "LeanRidgelet.isIdempotentElem_networkVisibleProjection, LeanRidgelet.isSelfAdjoint_networkVisibleProjection")
If $`\sigma\ne0` then $`P^2=P=P^*`.
:::

:::theorem "canonical_parameter_projection_range_kernel" (lean := "LeanRidgelet.ker_networkVisibleProjection, LeanRidgelet.range_networkVisibleProjection")
The kernel and range of the canonical parameter projection are
$$`\ker P=\ker S_\sigma,\qquad\operatorname{ran}P=(\ker S_\sigma)^\perp`.
:::

:::theorem "pointwise_null_space" (lean := "LeanRidgelet.mem_ker_networkSynthesis_iff")
A parameter $`\gamma` belongs to the null space if and only if
$`L_\sigma[T[\gamma](x,\cdot)]=0` for almost every $`x`. In the current transported Lean model
$`T=I`. Equivalently,
$$`T[\ker S_\sigma]=L^2(\mathbb R^m;\ker L_\sigma)`.
:::

:::theorem "general_solution_kernel_translate" (lean := "LeanRidgelet.networkSolution_iff_kernel_translate")
Assume $`\sigma\ne0`. The complete solution set of $`S_\sigma[\gamma]=f` is
$$`S_\sigma^\dagger[f]+\ker S_\sigma`.
:::

:::theorem "minimum_norm_solution" (lean := "LeanRidgelet.normalizedNetworkRightInverse_unique_minimal")
$`S_\sigma^\dagger[f]` is the unique minimum-norm solution of
$`S_\sigma[\gamma]=f`.
:::

:::definition "coefficient_vector" (lean := "LeanRidgelet.fiberCoefficient")
For a Hilbert basis $`(e_i)` of $`L^2(\mathbb R^m)`, define the coefficient vector $`h_i[\gamma]`
of a parameter by a Bochner integral.
:::

:::theorem "ridgelet_series" (lean := "LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient")
Every parameter distribution has the ridgelet-series expansion
$$`\gamma=\sum_i R_{h_i[\gamma]}[e_i]`.
:::

:::theorem "null_ridgelet_coefficients" (lean := "LeanRidgelet.activationFiberFunctional_fiberCoefficient_eq_zero_of_mem_ker")
If $`\gamma\in\ker S_\sigma`, then every coefficient vector $`h_i[\gamma]` belongs to
$`\ker L_\sigma`.
:::

:::theorem "null_space_structure" (lean := "LeanRidgelet.mem_ker_networkSynthesis_iff, LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient, LeanRidgelet.networkSolution_iff_kernel_translate, LeanRidgelet.normalizedNetworkRightInverse_unique_minimal") (uses := "pointwise_null_space, ridgelet_series, null_ridgelet_coefficients, general_solution_kernel_translate, minimum_norm_solution")
Together, these results show that the null ridgelet series relative to a fixed Hilbert basis exists
and is unique, and that every solution is the sum of the canonical particular solution and an
arbitrary null series.
:::
