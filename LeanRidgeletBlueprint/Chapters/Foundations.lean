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

#doc (Manual) "Fourier conventions and Hilbert spaces" =>

:::source_document "ghosts-l2"
%%%
title := "Ghosts in Neural Networks"
kind := .pdf
pdf := "00data/ghost20260715.pdf"
%%%
:::

This chapter reorganizes the notation from `head.tex` and the Hilbert-space framework from
`05journal/body.tex` according to the Lean dependency order. Inner products are linear in the
first argument.

:::definition "paper_fourier_convention" (lean := "LeanRidgelet.Fourier.paperFourierIntegralInner")
Let $`V` be a finite-dimensional real inner-product space. Define the paper-normalized Fourier
transform by
$$`\widehat f(\xi)=\int_V e^{-i\langle x,\xi\rangle}f(x)\,dx`.
Mathlib's Fourier character uses the $`2\pi` convention, so rescaling the frequency by
$`\xi/(2\pi)` relates the two conventions.
:::

:::theorem "paper_plancherel" (lean := "LeanRidgelet.Fourier.paper_plancherel_schwartz_inner, LeanRidgelet.Fourier.paper_plancherel_schwartz")
For every Schwartz function $`f`, the paper-normalized Plancherel identity is
$$`\|\widehat f\|_{L^2(V)}^2=(2\pi)^{\dim V}\|f\|_{L^2(V)}^2`.
:::

:::definition "japanese_bracket" (lean := "LeanRidgelet.japaneseBracketPow")
For a real exponent $`r`, define the Japanese bracket power by
$`\langle x\rangle^r=(1+\|x\|^2)^{r/2}`.
:::

:::definition "activation_space" (lean := "LeanRidgelet.ActivationSpace, LeanRidgelet.activationDistribution")
For $`s,t\in\mathbb R`, the activation Hilbert space $`\mathcal A_{s,t}` is modeled in
$`L^2(\mathbb R)` coordinates. The tempered-distribution realization of a coordinate $`u` is
$$`\sigma=\langle\cdot\rangle^t\langle\partial\rangle^{-s}[u]`.
Thus $`\mathcal A_{s,t}` is a coordinate model of
$`\langle\cdot\rangle^tH^s(\mathbb R)`.
:::

:::proposition "activation_hilbert_structure" (lean := "LeanRidgelet.activationCoordinateEquiv, LeanRidgelet.activationDistribution_injective")
$`\mathcal A_{s,t}` is a Hilbert space, and its $`L^2(\mathbb R)` coordinate map is a linear
isometric equivalence. Its realization in tempered distributions is injective.
:::

:::definition "fiber_space" (lean := "LeanRidgelet.fiberNormSq, LeanRidgelet.FiberSpace")
Let $`m>0`. On the Schwartz core, set
$$`\|q\|_{\mathcal H_{s,t}}^2=C_m\int_{\mathbb R}|q(\omega)|^2|\omega|^m\,d\omega+\int_{\mathbb R}|(\langle\partial_\omega\rangle^t[q])(\omega)|^2\langle\omega\rangle^{-2s}\,d\omega`.
The first term retains the dilation Jacobian, while the weighted Bessel term controls the
activation pairing. The fiber space $`\mathcal H_{s,t}` is the Hilbert completion of this core.
:::

:::proposition "fiber_inner_product" (lean := "LeanRidgelet.fiberInner_self_eq_zero, LeanRidgelet.denseRange_fiberCore_coe")
The preceding sesquilinear form is positive definite, and the Schwartz core embeds densely into
the completed fiber space.
:::

:::definition "activation_fiber_functional" (lean := "LeanRidgelet.activationFiberFunctional")
Each $`\sigma\in\mathcal A_{s,t}` induces a continuous linear functional on every fiber:
$$`L_\sigma[q]=C_m\int_{\mathbb R}q(\omega)\sigma^\sharp(\omega)\,d\omega`.
For distributional activations, this formula denotes the dual action mediated by the weighted
Bessel coordinates.
:::

:::theorem "activation_fiber_dual_bound" (lean := "LeanRidgelet.norm_activationFiberFunctional_le, LeanRidgelet.activationFiberDualMap")
$`L_\sigma` is bounded, and the assignment $`\sigma\mapsto L_\sigma` is a continuous linear
map from activations to the fiber dual.
:::

:::definition "parameter_space" (lean := "LeanRidgelet.ParameterSpace, LeanRidgelet.parameterCoordinateEquiv")
Define the parameter Hilbert space $`\mathcal G_{s,t}` through Fourier--dilation coordinates so
that
$$`\mathcal G_{s,t}\simeq L^2(\mathbb R^m;\mathcal H_{s,t})`.
The Lean development takes this Bochner $`L^2` space as its coordinate model.
:::
