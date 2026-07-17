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

#doc (Manual) "Unitary coordinates and their Fourier construction" =>
%%%
file := "fourier-dilation"
%%%

This chapter corresponds to the unitary coordinate transform in the active
`05journal/02theory02.tex` and its construction and proof in `05journal/supp02.tex`.
“Fourier--dilation” describes the construction; the operator's formal manuscript name is the
unitary coordinate transform $`T`.

:::definition "fourier_dilation_core" (lean := "LeanRidgelet.fourierDilationTransformCore, LeanRidgelet.fourierDilationTransformFiberCore, LeanRidgelet.fourierDilationTransformCoreL2")
For a Schwartz parameter distribution $`\gamma`, construct the unitary coordinate transform by
$$`T[\gamma](x,\omega)=(2\pi)^{-m}\int_{\mathbb R^m\times\mathbb R}\gamma(a,b)e^{i\omega(a\cdot x-b)}\,da\,db`.
For every fixed $`x`, this formula is bundled as a Schwartz element of the fiber core.
Once the resulting fiber-valued function is in Bochner $`L^2`, it is bundled as the corresponding
Hilbert-space coordinate.
:::

:::definition "fourier_dilation_coordinate" (lean := "LeanRidgelet.frequencyDilation, LeanRidgelet.fourierDilationCoordinate")
Define frequency dilation by $`D_\omega[x]=\omega x` and the pullback coordinate by
$`\kappa(x,\omega)=(-D_\omega[x],\omega)`.
:::

:::lemma_ "weighted_dilation_change_of_variables" (lean := "LeanRidgelet.integral_fourierDilationCoordinate_mul, LeanRidgelet.integrable_fourierDilationCoordinate_mul")
Away from the null set $`\omega=0`, the substitution $`y=\omega x` gives a weighted integral
identity with Jacobian $`|\omega|^m`.
:::

:::theorem "fourier_dilation_core_plancherel" (lean := "LeanRidgelet.fourierDilationTransformCore_norm_sq, LeanRidgelet.integral_fiberBaseNormSq_fourierDilationTransformFiberCore")
Combining the paper-normalized Plancherel identity with the dilation change of variables yields,
on the Schwartz core,
$$`\int |T[\gamma](x,\omega)|^2|\omega|^m\,dx\,d\omega=(2\pi)^{1-m}\|\gamma\|_{L^2}^2`.
:::

:::definition "fourier_dilation_unitary" (lean := "LeanRidgelet.fourierDilationTransform")
On the transported coordinate model, the unitary coordinate transform $`T` is a linear isometric
equivalence from
$`\mathcal G_{s,t}` to $`L^2(\mathbb R^m;\mathcal H_{s,t})`.
For the concrete core formula, the base part of the fiber norm is already integrable; after
strong measurability, Bochner $`L^2` membership is equivalent to integrability of the remaining
Sobolev term.
:::

:::definition "inverse_fourier_dilation_core" (lean := "LeanRidgelet.inverseFourierDilationTransformCore")
For a Schwartz coordinate test function $`u`, define the inverse-transform Fourier expression by
$$`T^{-1}[u](a,b)=\frac1{2\pi}\int u(x,\omega)e^{-i\omega(a\cdot x-b)}|\omega|^m\,dx\,d\omega`.
:::

:::theorem "fourier_dilation_inverse" (lean := "LeanRidgelet.inverseFourierDilationTransform_apply_fourierDilationTransform")
On Hilbert-space coordinates, $`T^*=T^{-1}` and $`T^{-1}\circ T=I`.
:::

:::theorem "core_transform_agrees_with_unitary" (lean := "LeanRidgelet.fourierDilationTransform_parameterSchwartzRealization") (uses := "fourier_dilation_core, fourier_dilation_unitary")
If the fiber-valued integral formula associated with a parameter Schwartz function belongs to
Bochner $`L^2`, its inverse-unitary realization is mapped back to that concrete core coordinate.
Thus the integral representation agrees with the transported unitary on its natural domain.
:::
