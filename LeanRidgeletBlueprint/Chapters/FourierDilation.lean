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

#doc (Manual) "Fourier--dilation coordinates" =>

この章は `05journal/body.tex` の Fourier--dilation coordinate transform と
`05journal/supp.tex` の change-of-variables proof に対応する。

:::definition "fourier_dilation_core" (lean := "LeanRidgelet.fourierDilationTransformCore")
Schwartz parameter distribution $`\gamma` に対し、Fourier--dilation transform を
$$`T\gamma(x,\omega)=(2\pi)^{-m}\int_{\mathbb R^m\times\mathbb R}\gamma(a,b)e^{i\omega(a\cdot x-b)}\,da\,db`
で定める。
:::

:::definition "fourier_dilation_coordinate" (lean := "LeanRidgelet.frequencyDilation, LeanRidgelet.fourierDilationCoordinate")
周波数 dilation を $`D_\omega x=\omega x`、pullback 座標を
$`\kappa(x,\omega)=(-D_\omega x,\omega)` と定める。
:::

:::lemma_ "weighted_dilation_change_of_variables" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul")
$`\omega=0` の零集合を除き $`y=\omega x` と変数変換すると、Jacobian
$`|\omega|^m` を伴う weighted integral identity が得られる。
:::

:::theorem "fourier_dilation_core_plancherel" (lean := "LeanRidgelet.fourierDilationTransformCore_norm_sq")
Schwartz core 上で、論文規約の Plancherel 公式と dilation の変数変換を組み合わせると
$$`\int |T\gamma(x,\omega)|^2|\omega|^m\,dx\,d\omega=(2\pi)^{1-m}\|\gamma\|_{L^2}^2`
を得る。
:::

:::definition "fourier_dilation_unitary" (lean := "LeanRidgelet.fourierDilationTransform")
transported coordinate model 上の $`T` は
$`\mathcal G_{s,t}` から $`L^2(\mathbb R^m;\mathcal H_{s,t})` への線形等長同型である。
:::

:::definition "inverse_fourier_dilation_core" (lean := "LeanRidgelet.inverseFourierDilationTransformCore")
Schwartz 座標関数 $`q` に対する逆変換の積分核を
$$`T^{-1}q(a,b)=\frac1{2\pi}\int q(x,\omega)e^{-i\omega(a\cdot x-b)}|\omega|^m\,dx\,d\omega`
と定める。
:::

:::theorem "fourier_dilation_inverse" (lean := "LeanRidgelet.inverseFourierDilationTransform_apply_fourierDilationTransform")
Hilbert-space 座標上の逆変換は $`T^{-1}T=I` を満たす。
:::

:::theorem "core_transform_agrees_with_unitary"
Schwartz core の積分表示と transported unitary map が一致する。
この接続は現在の Lean 実装で未証明である。
:::
