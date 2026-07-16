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

#doc (Manual) "Synthesis, ridgelets, and reconstruction" =>

:::definition "network_synthesis" (lean := "LeanRidgelet.networkSynthesis")
activation $`\sigma\in\mathcal A_{s,t}` に対する synthesis operator を fiberwise に
$$`S_\sigma\gamma(x)=L_\sigma[\gamma(x)]`
と定める。Fourier--dilation 座標を戻せば depth-2 network の積分表現に対応する。
:::

:::theorem "bounded_network_synthesis" (lean := "LeanRidgelet.norm_networkSynthesis_le, LeanRidgelet.norm_networkSynthesis_apply_le")
$`S_\sigma:\mathcal G_{s,t}\to L^2(\mathbb R^m)` は有界線形作用素であり、
その作用素ノルムは activation--fiber dual bound から評価される。
:::

:::theorem "classical_synthesis_agreement"
Schwartz class で定義した古典積分
$$`\int\gamma(a,b)\sigma(a\cdot x-b)\,da\,db`
と coordinate synthesis $`S_\sigma` は一致する。この接続は現在未証明である。
:::

:::definition "ridgelet_operator" (lean := "LeanRidgelet.ridgeletOperator")
$`q\in\mathcal H_{s,t}` を固定し、ridgelet operator を Fourier--dilation 座標で
$`R_qf(x)=f(x)q` と定める。
:::

:::lemma_ "ridgelet_simple_tensor" (lean := "LeanRidgelet.ridgeletOperator_apply_ae")
ridgelet operator は almost everywhere に $`x\mapsto f(x)q` という simple tensor である。
:::

:::lemma_ "fourier_and_fiber_representations" (uses := "classical_synthesis_agreement, ridgelet_simple_tensor")
古典 ridgelet 式 $`R[f;\rho](a,b)=\int f(x)\overline{\rho(a\cdot x-b)}\,dx` の
bias Fourier 変換と、synthesis の Fourier 表現はそれぞれ
$$`R[f;\rho]^\sharp(a,\omega)=\widehat f(\omega a)\overline{\rho^\sharp(\omega)}`
および $`\widehat{S_\sigma\gamma}(\xi)=L_\sigma[T\gamma(\xi)]` である。
simple-tensor fiber 表現は形式化済みだが、古典積分式からの導出は現在未証明である。
:::

:::theorem "ridgelet_reconstruction" (lean := "LeanRidgelet.networkSynthesis_comp_ridgeletOperator")
任意の fiber $`q` に対して
$$`S_\sigma R_q=L_\sigma[q]I`
が成り立つ。従って $`L_\sigma[q]=1` なら $`R_q` は右逆であり、
$`L_\sigma[q]=0` ならその像は null space に含まれる。
:::

:::definition "activation_riesz_representer" (lean := "LeanRidgelet.activationRieszRepresenter")
Riesz 表現定理により、$`L_\sigma[q]=\langle q_\sigma,q\rangle` を満たす一意な
$`q_\sigma\in\mathcal H_{s,t}` を activation の可視 fiber とする。
:::

:::definition "activation_normalization" (lean := "LeanRidgelet.activationNormalization")
再構成定数を $`c_\sigma=\|q_\sigma\|^2` と定める。
:::

:::theorem "activation_normalization_positive" (lean := "LeanRidgelet.activationNormalization_pos")
$`\sigma\ne0` なら $`L_\sigma\ne0` であり、従って $`c_\sigma>0` である。
:::

:::theorem "adjoint_synthesis" (lean := "LeanRidgelet.adjoint_networkSynthesis, LeanRidgelet.networkSynthesis_comp_adjoint")
synthesis の Hilbert adjoint は Riesz fiber による ridgelet operator であり、
$$`S_\sigma^*=R_{q_\sigma},\qquad S_\sigma S_\sigma^*=c_\sigma I`
を満たす。
:::

:::definition "normalized_network_right_inverse" (lean := "LeanRidgelet.normalizedNetworkRightInverse")
正規化 adjoint $`S_\sigma^\dagger=c_\sigma^{-1}S_\sigma^*` を canonical right inverse
とする。
:::

:::theorem "normalized_network_right_inverse_spec" (lean := "LeanRidgelet.normalizedNetworkRightInverse_rightInverse, LeanRidgelet.surjective_networkSynthesis")
$`\sigma\ne0` なら $`S_\sigma S_\sigma^\dagger=I` であり、synthesis は全射である。
:::
