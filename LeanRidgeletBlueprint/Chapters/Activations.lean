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
%%%
file := "activations"
%%%

:::proposition "gaussian_activation" (lean := "LeanRidgelet.gaussianActivation, LeanRidgelet.gaussianActivation_ne_zero")
The Gaussian Fourier coordinate $`e^{-\omega^2/2}` belongs to $`L^2(\mathbb R)` and defines a
nonzero activation in $`\mathcal A_{0,0}`.
:::

:::proposition "tanh_activation" (lean := "LeanRidgelet.memLp_tanhWeightedFn, LeanRidgelet.tanhActivation, LeanRidgelet.tanhActivation_ne_zero, LeanRidgelet.tanhTemperedDistribution_apply, LeanRidgelet.memActivationSpace_tanhTemperedDistribution")
If $`t>1/2`, then $`\langle x\rangle^{-t}\tanh x\in L^2(\mathbb R)`.  The nonzero activation
coordinate of $`\tanh` in $`\mathcal A_{0,t}` is the paper Fourier transform
$`(\langle\cdot\rangle^{-t}\tanh)^\sharp = \langle\partial_\omega\rangle^{-t}[\tanh^\sharp]`,
and its pairing-consistent classical realization acts by integration against $`\tanh`.
:::

:::proposition "relu_activation" (lean := "LeanRidgelet.memLp_reluWeightedFn, LeanRidgelet.reluActivation, LeanRidgelet.reluActivation_ne_zero, LeanRidgelet.reluTemperedDistribution_apply, LeanRidgelet.memActivationSpace_reluTemperedDistribution")
If $`t>3/2`, then $`\langle x\rangle^{-t}x_+\in L^2(\mathbb R)`.  The nonzero activation
coordinate of ReLU in $`\mathcal A_{0,t}` is the paper Fourier transform
$`(\langle\cdot\rangle^{-t}x_+)^\sharp = \langle\partial_\omega\rangle^{-t}[(x_+)^\sharp]`,
and its pairing-consistent classical realization acts by integration against ReLU.
:::

:::proposition "tanh_operator_theory" (lean := "LeanRidgelet.surjective_tanhSynthesis, LeanRidgelet.adjoint_tanhSynthesis, LeanRidgelet.tanhSolution_iff_kernel_translate")
For $`t>1/2`, tanh synthesis is surjective and admits an adjoint ridgelet operator, a complete
description of its solutions, and a unique minimum-norm solution.
:::

:::proposition "relu_operator_theory" (lean := "LeanRidgelet.surjective_reluSynthesis, LeanRidgelet.adjoint_reluSynthesis, LeanRidgelet.reluSolution_iff_kernel_translate")
For $`t>3/2`, ReLU synthesis is surjective and admits an adjoint ridgelet operator, a complete
description of its solutions, and a unique minimum-norm solution.
:::

:::theorem "activation_sobolev_inclusion"
If $`s\le0`, there is a continuous inclusion from $`\mathcal A_{0,t}` into
$`\mathcal A_{s,t}`. This extends the present $`s=0` theory of tanh and ReLU toward the range
treated in the source manuscript.
:::

:::theorem "activation_distributional_fourier_formulas"
Identify the distributional Fourier formulas for ReLU, tanh, the Gaussian CDF, and the Gaussian,
including finite-part, principal-value, and Dirac distributions.
:::

:::theorem "standard_activation_riesz_resolvents"
For each standard activation, the Riesz representer satisfies the one-dimensional weak resolvent equation
from the manuscript, from which an explicit adjoint ridgelet function can be derived.
:::
