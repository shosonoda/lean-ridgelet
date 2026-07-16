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

この章は `head.tex` の記法と `05journal/body.tex` の Hilbert-space framework を、
Lean の依存順に並べ直したものである。内積は第一変数について線形とする。

:::definition "paper_fourier_convention" (lean := "LeanRidgelet.Fourier.paperFourierIntegralInner")
$`V` を有限次元実内積空間とする。論文規約の Fourier 変換を
$$`\widehat f(\xi)=\int_V e^{-i\langle x,\xi\rangle}f(x)\,dx`
で定める。Mathlib の Fourier character は $`2\pi` 規約なので、周波数を
$`\xi/(2\pi)` に変換して両規約を接続する。
:::

:::theorem "paper_plancherel" (lean := "LeanRidgelet.Fourier.paper_plancherel_schwartz_inner, LeanRidgelet.Fourier.paper_plancherel_schwartz")
Schwartz 関数 $`f` に対して、論文規約の Plancherel 公式
$$`\|\widehat f\|_{L^2(V)}^2=(2\pi)^{\dim V}\|f\|_{L^2(V)}^2`
が成り立つ。
:::

:::definition "japanese_bracket" (lean := "LeanRidgelet.japaneseBracketPow")
Japanese bracket の実数冪を
$`\langle x\rangle^r=(1+\|x\|^2)^{r/2}` と定める。
:::

:::definition "activation_space" (lean := "LeanRidgelet.ActivationSpace, LeanRidgelet.activationDistribution")
$`s,t\in\mathbb R` に対し、activation Hilbert space $`\mathcal A_{s,t}` は
$`L^2(\mathbb R)` 座標でモデル化する。座標 $`u` の tempered distribution 実現は
$$`\sigma=\langle\cdot\rangle^t\langle\partial\rangle^{-s}u`
で与える。したがって $`\mathcal A_{s,t}` は
$`\langle\cdot\rangle^tH^s(\mathbb R)` の座標モデルである。
:::

:::proposition "activation_hilbert_structure" (lean := "LeanRidgelet.activationCoordinateEquiv, LeanRidgelet.activationDistribution_injective")
$`\mathcal A_{s,t}` は Hilbert 空間であり、その $`L^2(\mathbb R)` 座標写像は
線形等長同型である。また、tempered distribution への実現は単射である。
:::

:::definition "fiber_space" (lean := "LeanRidgelet.fiberNormSq, LeanRidgelet.FiberSpace")
$`m>0` とする。Schwartz core 上で、dilation Jacobian を保持する項と activation
pairing を制御する weighted Bessel 項の和を
$$`\|q\|_{\mathcal H_{s,t}}^2=C_m\int_{\mathbb R}|q(\omega)|^2|\omega|^m\,d\omega+\int_{\mathbb R}|\langle\partial_\omega\rangle^tq(\omega)|^2\langle\omega\rangle^{-2s}\,d\omega`
と置き、その Hilbert completion を fiber space $`\mathcal H_{s,t}` とする。
:::

:::proposition "fiber_inner_product" (lean := "LeanRidgelet.fiberInner_self_eq_zero, LeanRidgelet.denseRange_fiberCore_coe")
上の sesquilinear form は正定値であり、Schwartz core は完成した fiber space に
稠密に埋め込まれる。
:::

:::definition "activation_fiber_functional" (lean := "LeanRidgelet.activationFiberFunctional")
$`\sigma\in\mathcal A_{s,t}` は各 fiber に連続線形汎関数
$$`L_\sigma[q]=C_m\int_{\mathbb R}q(\omega)\sigma^\sharp(\omega)\,d\omega`
を誘導する。分布の場合、この式は weighted Bessel 座標を介した双対作用と解釈する。
:::

:::theorem "activation_fiber_dual_bound" (lean := "LeanRidgelet.norm_activationFiberFunctional_le, LeanRidgelet.activationFiberDualMap")
汎関数 $`L_\sigma` は有界であり、activation から fiber dual への対応
$`\sigma\mapsto L_\sigma` は連続線形写像である。
:::

:::definition "parameter_space" (lean := "LeanRidgelet.ParameterSpace, LeanRidgelet.parameterCoordinateEquiv")
parameter Hilbert space $`\mathcal G_{s,t}` は Fourier--dilation 座標で
$$`\mathcal G_{s,t}\simeq L^2(\mathbb R^m;\mathcal H_{s,t})`
となるように定める。Lean ではこの Bochner $`L^2` 空間を座標モデルとして採用する。
:::
