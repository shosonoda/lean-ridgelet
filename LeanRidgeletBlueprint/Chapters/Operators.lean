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
%%%
file := "operators"
%%%

:::definition "network_synthesis" (lean := "LeanRidgelet.networkSynthesis")
For an activation $`\sigma\in\mathcal A_{s,t}`, define the synthesis operator fiberwise by
$$`S_\sigma[\gamma](x)=L_\sigma[\gamma(x)]`.
After undoing the Fourier--dilation coordinates, this is the integral representation of a
depth-2 network.
:::

:::theorem "bounded_network_synthesis" (lean := "LeanRidgelet.norm_networkSynthesis_le, LeanRidgelet.norm_networkSynthesis_apply_le")
$`S_\sigma:\mathcal G_{s,t}\to L^2(\mathbb R^m)` is a bounded linear operator, and its operator
norm is controlled by the activation--fiber dual bound.
:::

:::theorem "classical_synthesis_agreement"
The classical integral on the Schwartz class,
$$`\int\gamma(a,b)\sigma(a\cdot x-b)\,da\,db`,
agrees with the coordinate synthesis $`S_\sigma`. This compatibility statement is not yet proved.
:::

:::definition "ridgelet_operator" (lean := "LeanRidgelet.ridgeletOperator")
For a fixed $`q\in\mathcal H_{s,t}`, define the ridgelet operator in Fourier--dilation
coordinates by $`R_q[f](x)=f(x)q`.
:::

:::lemma_ "ridgelet_simple_tensor" (lean := "LeanRidgelet.ridgeletOperator_apply_ae")
Almost everywhere, the ridgelet operator is the simple tensor $`x\mapsto f(x)q`.
:::

:::lemma_ "fourier_and_fiber_representations" (uses := "classical_synthesis_agreement, ridgelet_simple_tensor")
The bias Fourier transform of the classical ridgelet formula
$`R[f;\rho](a,b)=\int f(x)\overline{\rho(a\cdot x-b)}\,dx` and the Fourier representation of
synthesis are
$$`R[f;\rho]^\sharp(a,\omega)=\widehat f(\omega a)\overline{\rho^\sharp(\omega)}`
and $`\widehat{S_\sigma[\gamma]}(\xi)=L_\sigma[T[\gamma](\xi)]`, respectively.
The simple-tensor fiber representation is formalized, but its derivation from the classical
integral formula is not yet proved.
:::

:::theorem "ridgelet_reconstruction" (lean := "LeanRidgelet.networkSynthesis_comp_ridgeletOperator")
For every fiber $`q`,
$$`S_\sigma\circ R_q=L_\sigma[q]I`.
Consequently, if $`L_\sigma[q]=1` then $`R_q` is a right inverse, while if
$`L_\sigma[q]=0` then its range lies in the null space.
:::

:::definition "activation_riesz_representer" (lean := "LeanRidgelet.activationRieszRepresenter")
By the Riesz representation theorem, the activation has a unique visible fiber
$`q_\sigma\in\mathcal H_{s,t}` satisfying
$`L_\sigma[q]=\langle q_\sigma,q\rangle`.
:::

:::definition "activation_normalization" (lean := "LeanRidgelet.activationNormalization")
Define the reconstruction constant by $`c_\sigma=\|q_\sigma\|^2`.
:::

:::theorem "activation_normalization_positive" (lean := "LeanRidgelet.activationNormalization_pos")
If $`\sigma\ne0` then $`L_\sigma\ne0`, and hence $`c_\sigma>0`.
:::

:::theorem "adjoint_synthesis" (lean := "LeanRidgelet.adjoint_networkSynthesis, LeanRidgelet.networkSynthesis_comp_adjoint")
The Hilbert adjoint of synthesis is the ridgelet operator associated with the Riesz fiber, and
$$`S_\sigma^*=R_{q_\sigma},\qquad S_\sigma\circ S_\sigma^*=c_\sigma I`.
:::

:::definition "normalized_network_right_inverse" (lean := "LeanRidgelet.normalizedNetworkRightInverse")
Define the canonical right inverse to be the normalized adjoint
$`S_\sigma^\dagger=c_\sigma^{-1}S_\sigma^*`.
:::

:::theorem "normalized_network_right_inverse_spec" (lean := "LeanRidgelet.normalizedNetworkRightInverse_rightInverse, LeanRidgelet.surjective_networkSynthesis")
If $`\sigma\ne0` then $`S_\sigma\circ S_\sigma^\dagger=I`, so synthesis is surjective.
:::
