import LeanRidgeletBlueprint.Chapters.ToMathlibMeasureLp
import LeanRidgelet.ToMathlib.RadonTransform
import LeanRidgelet.ToMathlib.FourierPlancherel
import LeanRidgelet.ToMathlib.FourierAffine
import LeanRidgelet.ToMathlib.FourierInversion
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

#doc (Manual) "Mathlib candidates: Radon and Fourier transforms" =>
%%%
file := "radon-fourier"
%%%

The Radon transform, its `L¹` theory and slice theorem, together with the Fourier-analysis bridges that Mathlib's integral and `L²` APIs currently lack.

*Radon transform*

:::definition "mathlib_radon_transform" (lean := "MeasureTheory.radonTransform, MeasureTheory.dualRadonTransform, MeasureTheory.lineOrthogonalSplit")
*Radon transform, dual Radon transform, and the line–hyperplane splitting.* On a finite-dimensional real inner product space $`E` with values in a normed space,
$$`\mathscr Rf(u,p)=\int_{(\mathbb Ru)^\perp}f(pu+y)\,dy,\qquad \mathscr R^\dagger\Phi(x)=\int_{\mathbb S}\Phi(u,\langle u,x\rangle)\,du,`
where the hyperplane carries its canonical Lebesgue measure and the unit sphere the surface measure `volume.toSphere`. For a unit vector `u`, the parametrization $`(p,y)\mapsto pu+y` of $`E` by the line $`\mathbb Ru` and its orthogonal complement is packaged as a measurable equivalence, assembled from the `WithLp 2` product coordinates and the orthogonal decomposition $`E\simeq\mathbb Ru\times_2(\mathbb Ru)^\perp`.
:::

:::theorem "mathlib_radon_l1_theory" (lean := "MeasureTheory.measurePreserving_lineOrthogonalSplit, MeasureTheory.integrable_comp_lineOrthogonalSplit, MeasureTheory.ae_integrable_radonTransform_section, MeasureTheory.integrable_radonTransform, MeasureTheory.integral_radonTransform, MeasureTheory.integral_norm_radonTransform_le") (uses := "mathlib_radon_transform")
*`L¹` theory of the Radon transform.* The line–hyperplane splitting preserves Lebesgue measure. Consequently, for integrable `f` and every unit direction `u` — a fixed-direction strengthening of the almost-every-direction statement quoted in the tomography literature — almost every hyperplane section of `f` is integrable, the Radon transform $`\mathscr Rf(u,\cdot)` is integrable on $`\mathbb R`, and
$$`\int_{\mathbb R}\mathscr Rf(u,p)\,dp=\int_Ef(x)\,dx,\qquad \|\mathscr Rf(u,\cdot)\|_{L^1(\mathbb R)}\le\|f\|_{L^1(E)}.`
:::

:::theorem "mathlib_fourier_slice" (lean := "MeasureTheory.fourier_slice_radonTransform") (uses := "mathlib_radon_transform, mathlib_radon_l1_theory")
*Fourier slice theorem.* For integrable `f` on `E` with values in a complex normed space, a unit vector `u`, and every frequency $`\omega`,
$$`\mathcal F f(\omega u)=\mathcal F(\mathscr Rf(u,\cdot))(\omega),`
where the left-hand side is the Fourier transform on `E` and the right-hand side the one-dimensional Fourier transform, both in the Mathlib `2π` convention (`𝓕`). Also known as the projection-slice or central-slice theorem.
:::

*Fourier analysis*

:::theorem "mathlib_fourier_plancherel" (lean := "MeasureTheory.Integrable.fourier_toLp_ae_eq, MeasureTheory.Integrable.memLp_fourier, MeasureTheory.Integrable.integral_norm_fourier_sq, MeasureTheory.Integrable.lintegral_enorm_fourier_sq, MeasureTheory.MemLp.integrable_mul_conj, MeasureTheory.Integrable.integral_inner_fourier, MeasureTheory.Integrable.integral_fourier_mul_conj_fourier")
*Plancherel's theorem on `L¹ ∩ L²`.* Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ` provides the Fourier transform on `L²` of a finite-dimensional real inner product space as a linear isometry, with Schwartz and tempered-distribution compatibility, but no statement that on `L¹ ∩ L²` the isometry is computed by the Fourier integral. That bridge is proved here: for integrable, square-integrable `f`, the Fourier integral `𝓕 f` is an almost-everywhere representative of the `L²` Fourier transform of the class of `f`; it is square-integrable; and
$$`\int\|\mathcal Ff(\xi)\|^2\,d\xi=\int\|f(x)\|^2\,dx`
in both Bochner and `lintegral` form. The proof pairs the `L²` transform against Schwartz functions through the tempered-distribution compatibility, rewrites with the self-adjointness of the Fourier integral, and identifies the representatives with `ae_eq_of_integral_contDiff_smul_eq`. The polarized companions (last three declarations) provide the integrability of pointwise products of `L²` functions and *Parseval's relation on `L¹ ∩ L²`*, $`\int\langle\mathcal Ff,\mathcal Fg\rangle=\int\langle f,g\rangle` (with the scalar mul-conjugate form), by transporting the unitarity of `MeasureTheory.Lp.fourierTransformₗᵢ` through the `L¹ ∩ L²` representation.
:::

:::theorem "mathlib_fourier_affine" (lean := "MeasureTheory.integral_comp_linearEquiv_symm, MeasureTheory.fourier_comp_linearEquiv_symm, MeasureTheory.fourier_comp_sub, MeasureTheory.affineEquiv_symm_apply, MeasureTheory.fourier_comp_affineEquiv_symm, MeasureTheory.fourier_weighted_comp_affineEquiv_symm") (uses := "mathlib_affine_haar")
*Fourier covariance under affine changes of variables.* For an invertible real linear map `L`,
pullback by `L⁻¹` contributes the determinant and applies `Lᵀ` to frequency. Translation
contributes the corresponding Fourier character. Combining the two gives
$$`\mathcal F[f\circ g^{-1}](\xi)=|\det L|\,\mathbf e(-\langle g(0),\xi\rangle)\,\mathcal Ff(L^T\xi).`
For the unitary affine pullback with coefficient $`|\det L|^{-1/2}`, the remaining frequency-side
coefficient is $`|\det L|^{1/2}`. The proof uses the additive-Haar determinant formula and the
Bochner `integral_map_equiv` API; it is valid for arbitrary finite-dimensional real inner-product
spaces and does not depend on ridgelets.
:::

:::theorem "mathlib_fourier_inversion_ae" (lean := "MeasureTheory.Integrable.fourierInv_fourier_ae_eq")
*Almost-everywhere Fourier inversion.* Mathlib's inversion theorem (`MeasureTheory.Integrable.fourierInv_fourier_eq`) recovers an integrable function with integrable Fourier transform at its continuity points; the almost-everywhere counterpart with no continuity hypothesis is absent. It is proved here: for `f` integrable on a finite-dimensional real inner product space with `𝓕 f` integrable, $`\mathcal F^{-1}[\mathcal F f]=f` almost everywhere. The proof pairs both sides against Schwartz functions — a Fubini swap computes the pairing of $`\mathcal F^{-1}\mathcal F f` against $`\varphi` as the pairing of $`\mathcal F f` against $`\mathcal F^{-1}\varphi`, the multiplication formula (`VectorFourier.integral_fourierIntegral_smul_eq_flip`) moves the transform back to `f`, and the Schwartz inversion closes the circle — and concludes with `ae_eq_of_integral_contDiff_smul_eq`.
:::

