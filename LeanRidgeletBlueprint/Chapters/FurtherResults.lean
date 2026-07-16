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

以下は `05journal/body.tex` に並ぶが、現在の Ch.2--5 形式化の外側にあるため、
依存先を明示した未形式化 node として記録する。

:::theorem "encoding_and_perturbative_readout"
null fiber の正規直交列には可算個の $`L^2` 関数を等長に符号化できる。
適切な additive parameter perturbation は null component を変えずに選択した関数を
visible component へ読み出し、その perturbation は一意最小ノルムである。
:::

:::definition "measure_valued_synthesis"
有限複素 Radon measure $`\mu` と局所化した data measure $`\nu` に対し、
feature の Bochner integral として measure-valued synthesis $`S_\nu[\mu]` を定める。
:::

:::theorem "normalized_finite_width_null_approximation" (uses := "measure_valued_synthesis")
total variation が一の null measure は、width $`N` の atomic measure で近似でき、
output norm は $`O(N^{-1/2})` で 0 に収束する。
:::

:::lemma_ "truncated_monte_carlo_quadrature" (uses := "measure_valued_synthesis")
有限測度の bounded parameter domain 上で一様 Monte Carlo 標本を取ると、truncation error と
sampling error を分離でき、後者の mean-square は $`O(N^{-1})` で評価できる。
:::

:::corollary "discretizable_ridgelet_null_elements" (uses := "normalized_finite_width_null_approximation")
連続かつ高々多項式増大の activation と compactly supported data measure に対し、
Schwartz ridgelet null element から finite-width null approximation を構成できる。
:::

:::proposition "exact_finite_null_relations"
activation の parity は exact two-atom null relation を与える。ReLU ではさらに affine
cancellation 条件から有限個の neuron の exact null relation が得られる。
:::
