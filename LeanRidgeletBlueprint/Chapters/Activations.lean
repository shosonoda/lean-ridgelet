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

#doc (Manual) "Standard activation functions" =>

:::proposition "gaussian_activation" (lean := "LeanRidgelet.gaussianActivation, LeanRidgelet.gaussianActivation_ne_zero")
Gaussian の Fourier coordinate $`e^{-\omega^2/2}` は $`L^2(\mathbb R)` に属し、
非零な $`\mathcal A_{0,0}` activation を与える。
:::

:::proposition "tanh_activation" (lean := "LeanRidgelet.memLp_tanhWeightedFn, LeanRidgelet.tanhTemperedDistribution_apply")
$`t>1/2` なら $`\langle x\rangle^{-t}\tanh x\in L^2(\mathbb R)` であり、
$`\tanh` は $`\mathcal A_{0,t}` の nonzero tempered distribution realization を持つ。
:::

:::proposition "relu_activation" (lean := "LeanRidgelet.memLp_reluWeightedFn, LeanRidgelet.reluTemperedDistribution_apply")
$`t>3/2` なら $`\langle x\rangle^{-t}x_+\in L^2(\mathbb R)` であり、
ReLU は $`\mathcal A_{0,t}` の nonzero tempered distribution realization を持つ。
:::

:::proposition "tanh_operator_theory" (lean := "LeanRidgelet.surjective_tanhSynthesis, LeanRidgelet.adjoint_tanhSynthesis, LeanRidgelet.tanhSolution_iff_kernel_translate")
$`t>1/2` の tanh synthesis は全射であり、adjoint ridgelet、一般解、
一意最小ノルム解を持つ。
:::

:::proposition "relu_operator_theory" (lean := "LeanRidgelet.surjective_reluSynthesis, LeanRidgelet.adjoint_reluSynthesis, LeanRidgelet.reluSolution_iff_kernel_translate")
$`t>3/2` の ReLU synthesis は全射であり、adjoint ridgelet、一般解、
一意最小ノルム解を持つ。
:::

:::theorem "activation_sobolev_inclusion"
$`s\le0` なら $`\mathcal A_{0,t}` から $`\mathcal A_{s,t}` への連続包含がある。
これにより tanh と ReLU の現在の $`s=0` 理論を source manuscript の範囲へ拡張できる。
:::

:::theorem "activation_distributional_fourier_formulas"
ReLU、tanh、Gaussian CDF、Gaussian の distributional Fourier 公式を、finite-part、
principal value、Dirac distribution を含めて同定する。
:::

:::theorem "standard_activation_riesz_resolvents"
各標準 activation の Riesz fiber は manuscript の one-dimensional weak resolvent
equation を満たし、それから adjoint ridgelet function の明示式が得られる。
:::
