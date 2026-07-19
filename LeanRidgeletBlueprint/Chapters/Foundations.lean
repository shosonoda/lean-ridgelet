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
%%%
file := "foundations"
%%%

:::source_document "ghosts-l2"
%%%
title := "Ghosts in Neural Networks"
kind := .pdf
pdf := "00data/ghost20260718submit.pdf"
%%%
:::

This chapter reorganizes the notation from `head.tex` and the Hilbert-space framework from the
active `05journal/02theory.tex` according to the Lean dependency order. The manuscript inner
product is linear in the first argument; Mathlib's is linear in the second, so Lean identities use
the reversed argument order. In particular, manuscript $`L[h]=\langle h,h_L\rangle` is represented
in Lean by $`\langle h_L,h\rangle=L[h]`.

The displayed symbols $`\mathcal A_{s,t}`, $`\mathcal H_{s,t}`, $`\mathcal G_{s,t}`,
$`L_\sigma`, $`T`, $`f^\sharp`, $`\langle x\rangle^r`, and
$`\langle\partial\rangle^t` correspond to the scoped Lean notations `𝓐 s t`, `𝓗 m s t`,
`𝓖 m s t`, `L[σ]`, `𝐓`, `f♯`, `⧼x⧽^r`, and `⧼∂⧽^t`. The linked declarations remain the
canonical API.

:::definition "paper_fourier_convention" (lean := "LeanRidgelet.Fourier.paperFourierIntegralInner, LeanRidgelet.Fourier.paperFourierDistribution, LeanRidgelet.Fourier.paperFourierInvDistribution")
Let $`V` be a finite-dimensional real inner-product space. Define the paper-normalized Fourier
transform by
$$`\widehat f(\xi)=\int_V e^{-i\langle x,\xi\rangle}f(x)\,dx`.
Mathlib's Fourier character uses the $`2\pi` convention, so rescaling the frequency by
$`\xi/(2\pi)` relates the two conventions. Lean also bundles the one-dimensional forward and
inverse transforms on tempered distributions and proves that they are mutual inverses.
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

:::definition "fiber_space" (lean := "LeanRidgelet.fiberNormSq, LeanRidgelet.FiberSpace, LeanRidgelet.fiberDistribution, LeanRidgelet.fiberDistribution_coe, LeanRidgelet.fiberBaseCoordinate, LeanRidgelet.fiberBaseCoordinate_coe")
Let $`m>0`. On the Schwartz core, set
$$`\|h\|_{\mathcal H_{s,t}}^2=C_m\int_{\mathbb R}|h(\omega)|^2|\omega|^m\,d\omega+\int_{\mathbb R}|(\langle\partial_\omega\rangle^t[h])(\omega)|^2\langle\omega\rangle^{-2s}\,d\omega`.
The first term retains the dilation Jacobian, while the weighted Bessel term controls the
activation pairing. The fiber space $`\mathcal H_{s,t}` is the Hilbert completion of this core.
Lean also realizes every completed coefficient vector as a tempered distribution by undoing its
weighted Bessel coordinate; this realization agrees with the original function on the Schwartz
core. The square-root dilation-Jacobian coordinate extends contractively to the completion as an
$`L^2` map and supplies the pairing used by the completed ridgelet spectrum.
:::

:::proposition "fiber_inner_product" (lean := "LeanRidgelet.fiberInner_self_eq_zero, LeanRidgelet.denseRange_fiberCore_coe")
The preceding sesquilinear form is positive definite, and the Schwartz core embeds densely into
the completed fiber space.
:::

:::definition "activation_fiber_functional" (lean := "LeanRidgelet.activationFiberFunctional, LeanRidgelet.activationSpectrum, LeanRidgelet.activationRealization, LeanRidgelet.activationSpectrum_apply, LeanRidgelet.activationFiberFunctional_eq_spectrum")
Each $`\sigma\in\mathcal A_{s,t}` induces a continuous linear functional on the coefficient space:
$$`L_\sigma[h]=C_m\int_{\mathbb R}h(\omega)\sigma^\sharp(\omega)\,d\omega`.
For distributional activations, this formula denotes the dual action mediated by the weighted
Bessel coordinates.
:::

:::theorem "activation_fiber_dual_bound" (lean := "LeanRidgelet.norm_activationFiberFunctional_le, LeanRidgelet.activationFiberDualMap")
$`L_\sigma` is bounded, and the assignment $`\sigma\mapsto L_\sigma` is a continuous linear
map from activations to the fiber dual.
:::

:::definition "parameter_space" (lean := "LeanRidgelet.ParameterSpace, LeanRidgelet.parameterCoordinateEquiv")
Define the parameter Hilbert space $`\mathcal G_{s,t}` through the unitary coordinates $`T` so
that
$$`\mathcal G_{s,t}\simeq L^2(\mathbb R^m;\mathcal H_{s,t})`.
The concrete construction of $`T` uses the full Fourier transform and a weighted dilation. The
Lean development currently takes the resulting Bochner $`L^2` space as its transported coordinate
model.
:::
