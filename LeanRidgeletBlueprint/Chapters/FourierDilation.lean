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

This chapter corresponds to the Fourier--dilation coordinate transform in `05journal/body.tex`
and the change-of-variables proof in `05journal/supp.tex`.

:::definition "fourier_dilation_core" (lean := "LeanRidgelet.fourierDilationTransformCore")
For a Schwartz parameter distribution $`\gamma`, define the Fourier--dilation transform by
$$`T[\gamma](x,\omega)=(2\pi)^{-m}\int_{\mathbb R^m\times\mathbb R}\gamma(a,b)e^{i\omega(a\cdot x-b)}\,da\,db`.
:::

:::definition "fourier_dilation_coordinate" (lean := "LeanRidgelet.frequencyDilation, LeanRidgelet.fourierDilationCoordinate")
Define frequency dilation by $`D_\omega[x]=\omega x` and the pullback coordinate by
$`\kappa(x,\omega)=(-D_\omega[x],\omega)`.
:::

:::lemma_ "weighted_dilation_change_of_variables" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul")
Away from the null set $`\omega=0`, the substitution $`y=\omega x` gives a weighted integral
identity with Jacobian $`|\omega|^m`.
:::

:::theorem "fourier_dilation_core_plancherel" (lean := "LeanRidgelet.fourierDilationTransformCore_norm_sq")
Combining the paper-normalized Plancherel identity with the dilation change of variables yields,
on the Schwartz core,
$$`\int |T[\gamma](x,\omega)|^2|\omega|^m\,dx\,d\omega=(2\pi)^{1-m}\|\gamma\|_{L^2}^2`.
:::

:::definition "fourier_dilation_unitary" (lean := "LeanRidgelet.fourierDilationTransform")
On the transported coordinate model, $`T` is a linear isometric equivalence from
$`\mathcal G_{s,t}` to $`L^2(\mathbb R^m;\mathcal H_{s,t})`.
:::

:::definition "inverse_fourier_dilation_core" (lean := "LeanRidgelet.inverseFourierDilationTransformCore")
For a Schwartz coordinate function $`q`, define the inverse-transform kernel by
$$`T^{-1}[q](a,b)=\frac1{2\pi}\int q(x,\omega)e^{-i\omega(a\cdot x-b)}|\omega|^m\,dx\,d\omega`.
:::

:::theorem "fourier_dilation_inverse" (lean := "LeanRidgelet.inverseFourierDilationTransform_apply_fourierDilationTransform")
On Hilbert-space coordinates, the inverse transform satisfies $`T^{-1}\circ T=I`.
:::

:::theorem "core_transform_agrees_with_unitary"
The integral representation on the Schwartz core agrees with the transported unitary map.
This compatibility statement is not yet proved in the Lean development.
:::
