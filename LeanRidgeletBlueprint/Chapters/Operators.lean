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
For an activation $`\sigma\in\mathcal A_{s,t}`, the manuscript factorization is
$$`S_\sigma=\widetilde L_\sigma T,\qquad S_\sigma[\gamma](x)=L_\sigma[T[\gamma](x,\cdot)]`.
The current Lean `ParameterSpace` is the transported coordinate model, so $`T=I` there and
`networkSynthesis` is definitionally the pointwise lift $`\widetilde L_\sigma`.
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
For a fixed $`h\in\mathcal H_{s,t}`, define the coordinate-side tensor embedding by
$`J_h[f](x)=f(x)h`. On the original parameter space, the corresponding solution operator is
$`R_h=T^*J_h`.
:::

:::lemma_ "ridgelet_simple_tensor" (lean := "LeanRidgelet.ridgeletOperator_apply_ae")
Almost everywhere, the coordinate-side operator is the simple tensor $`x\mapsto f(x)h`.
:::

:::lemma_ "fourier_expressions" (uses := "classical_synthesis_agreement, ridgelet_simple_tensor")
The bias Fourier transform of the classical ridgelet formula
$`R[f;\rho](a,b)=\int f(x)\overline{\rho(a\cdot x-b)}\,dx` and the Fourier representation of
synthesis are
$$`R[f;\rho]^\sharp(a,\omega)=\widehat f(\omega a)\overline{\rho^\sharp(\omega)}`
and $`\widehat{S_\sigma[\gamma]}(\xi)=L_\sigma[T[\gamma](\xi)]`, respectively.
The simple-tensor coordinate representation is formalized, but its derivation from the classical
integral formula is not yet proved.
:::

:::theorem "ridgelet_reconstruction" (lean := "LeanRidgelet.networkSynthesis_comp_ridgeletOperator")
For every coefficient vector $`h`,
$$`S_\sigma\circ R_h=L_\sigma[h]I`.
Consequently, if $`L_\sigma[h]=1` then $`R_h` is a right inverse, while if
$`L_\sigma[h]=0` then its range lies in the null space.
:::

:::definition "activation_riesz_representer" (lean := "LeanRidgelet.activationRieszRepresenter")
By the Riesz representation theorem, the activation has a unique coefficient vector
$`h_\sigma\in\mathcal H_{s,t}` satisfying
$`L_\sigma[h]=\langle h,h_\sigma\rangle` in the manuscript convention.
:::

:::definition "activation_normalization" (lean := "LeanRidgelet.activationNormalization")
The manuscript defines the reconstruction constant by
$`c_\sigma=\|h_\sigma\|^2=\|L_\sigma\|^2`. The first equality is implemented; the named Lean
theorem for the operator-norm equality is tracked in M1A.
:::

:::theorem "activation_normalization_positive" (lean := "LeanRidgelet.activationNormalization_pos")
If $`\sigma\ne0` then $`L_\sigma\ne0`, and hence $`c_\sigma>0`.
:::

:::theorem "adjoint_synthesis" (lean := "LeanRidgelet.adjoint_networkSynthesis, LeanRidgelet.networkSynthesis_comp_adjoint")
The Hilbert adjoint of synthesis is the ridgelet operator associated with the Riesz representer,
and
$$`S_\sigma^*=R_{h_\sigma},\qquad S_\sigma\circ S_\sigma^*=c_\sigma I`.
:::

:::definition "normalized_network_right_inverse" (lean := "LeanRidgelet.normalizedNetworkRightInverse")
Define the canonical right inverse to be the normalized adjoint
$`S_\sigma^\dagger=c_\sigma^{-1}S_\sigma^*`.
:::

:::theorem "normalized_network_right_inverse_spec" (lean := "LeanRidgelet.normalizedNetworkRightInverse_rightInverse, LeanRidgelet.surjective_networkSynthesis")
If $`\sigma\ne0` then $`S_\sigma\circ S_\sigma^\dagger=I`, so synthesis is surjective.
:::
