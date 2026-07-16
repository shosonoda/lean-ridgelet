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

:::definition "visible_projection" (lean := "LeanRidgelet.networkVisibleProjection")
parameter space の可視成分への作用素を
$`P=S_\sigma^\dagger S_\sigma` と定める。
:::

:::theorem "visible_projection_properties" (lean := "LeanRidgelet.isIdempotentElem_networkVisibleProjection, LeanRidgelet.isSelfAdjoint_networkVisibleProjection")
$`\sigma\ne0` なら $`P^2=P=P^*` である。
:::

:::theorem "visible_projection_range_kernel" (lean := "LeanRidgelet.ker_networkVisibleProjection, LeanRidgelet.range_networkVisibleProjection")
可視射影の kernel と range は
$$`\ker P=\ker S_\sigma,\qquad\operatorname{ran}P=(\ker S_\sigma)^\perp`
である。
:::

:::theorem "fiberwise_null_space" (lean := "LeanRidgelet.mem_ker_networkSynthesis_iff")
parameter $`\gamma` が null space に属することと、almost every $`x` で
$`L_\sigma[\gamma(x)]=0` となることは同値である。すなわち Fourier--dilation 座標で
$$`T(\ker S_\sigma)=L^2(\mathbb R^m;\ker L_\sigma)`
となる。
:::

:::theorem "general_solution_kernel_translate" (lean := "LeanRidgelet.networkSolution_iff_kernel_translate")
$`\sigma\ne0` とする。方程式 $`S_\sigma\gamma=f` の完全な解集合は
$$`S_\sigma^\dagger f+\ker S_\sigma`
である。
:::

:::theorem "minimum_norm_solution" (lean := "LeanRidgelet.normalizedNetworkRightInverse_unique_minimal")
$`S_\sigma^\dagger f` は $`S_\sigma\gamma=f` を満たす唯一の最小ノルム解である。
:::

:::definition "fiber_coefficient" (lean := "LeanRidgelet.fiberCoefficient")
$`L^2(\mathbb R^m)` の Hilbert basis $`(e_i)` に沿う parameter の fiber coefficient
$`q_i` を Bochner integral で定める。
:::

:::theorem "ridgelet_series" (lean := "LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient")
任意の parameter distribution は Hilbert basis に沿う ridgelet series
$$`\gamma=\sum_i R_{q_i}e_i`
に展開できる。
:::

:::theorem "null_ridgelet_coefficients" (lean := "LeanRidgelet.activationFiberFunctional_fiberCoefficient_eq_zero_of_mem_ker")
$`\gamma\in\ker S_\sigma` なら、その全ての coefficient fiber $`q_i` は
$`\ker L_\sigma` に属する。
:::

:::theorem "null_space_structure" (lean := "LeanRidgelet.mem_ker_networkSynthesis_iff, LeanRidgelet.hasSum_ridgeletOperator_fiberCoefficient, LeanRidgelet.networkSolution_iff_kernel_translate, LeanRidgelet.normalizedNetworkRightInverse_unique_minimal") (uses := "fiberwise_null_space, ridgelet_series, null_ridgelet_coefficients, general_solution_kernel_translate, minimum_norm_solution")
以上を合わせると、固定した Hilbert basis に関して null ridgelet series は存在し一意であり、
一般解は canonical particular solution と任意の null series の和として尽くされる。
:::
