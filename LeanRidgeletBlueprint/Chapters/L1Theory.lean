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

#doc (Manual) "L1 theory: formalization details" =>
%%%
file := "l1-theory"
%%%

The machinery behind the main results of the previous chapter, organized by Lean dependency
rather than by publication order. Each section corresponds to one file of `LeanRidgelet/L1/`; the three files whose results are
already stated in full in the overview chapter — `L1.Balancing`, `L1.StructureTheorem` and
`L1.Radon` — have no section of their own here.
The general-purpose analytic input — the Radon transform, Young's inequality, the Hilbert
transform, polar coordinates, weighted `L¹` smoothing, the `L²` duality criterion — is stated in
Mathlib generality in the upstream-candidates chapter and only specialized here.

*`L1.Defs`, `L1.FourierExpression`: the two identities the theory runs on*

:::theorem "l1_fourier_slice_angular" (lean := "LeanRidgelet.angularFourier_slice_radonTransform") (uses := "mathlib_radon_l1_theory, mathlib_fourier_slice, l1_parameter_space")
*Fourier slice theorem in the article convention.* For $`f\in L^1(\mathbb R^m)` and every unit direction $`\boldsymbol{u}`, the slice identity $`\widehat f(\omega\boldsymbol{u})=\widehat{\mathscr Rf(\boldsymbol{u},\cdot)}(\omega)` holds in the article Fourier convention, bridging the $`m`-dimensional and one-dimensional transforms. The article quotes the slice theorem and the Fubini corollary $`\int\mathscr Rf(\boldsymbol{u},p)\,dp=\int f` without proof; both are proved, the latter in the upstream chapter, for every unit direction rather than almost every.
:::

:::theorem "l1_fourier_expression" (lean := "LeanRidgelet.integrable_ridgelet_bias_kernel, LeanRidgelet.integrable_euclideanRidgeletTransform_bias, LeanRidgelet.memLp_two_euclideanRidgeletTransform_bias, LeanRidgelet.angularFourier1D_euclideanRidgeletTransform") (uses := "l1_ridgelet_transforms, l1_parameter_space")
*Fourier expression of the ridgelet transform (`eq:fstridge`).* For $`f\in L^1(\mathbb R^m)`, $`\psi\in L^1(\mathbb R)`, every weight $`\boldsymbol{a}` and bias frequency $`\zeta`,
$$`\widehat{\mathscr R_\psi f(\boldsymbol{a},\cdot)}(\zeta)=\widehat f(\zeta\boldsymbol{a})\,\overline{\widehat\psi(\zeta)}\,\|\boldsymbol{a}\|^s,`
where the hat on the left is the one-dimensional article Fourier transform in the bias. In the bias-frequency domain the ridgelet transform is the Fourier slice data $`\widehat f(\zeta\boldsymbol{a})` weighted by the conjugate activation spectrum. This is the bridge between the L1 transform and the unitary Fourier--dilation coordinates $`T` of the L2 theory, and the engine behind `thm:parseval` and `thm:L2`. The proof uses the measure-preserving preactivation shear $`(\boldsymbol{a},z)\mapsto(\boldsymbol{a},\langle\boldsymbol{a},x\rangle-z)` and a one-dimensional reflected translation. The first three declarations are the accompanying `L¹` and `L²` bias-section estimates.
:::

*`L1.Lizorkin`: the quotient at function level*

:::lemma_ "l1_lizorkin_moment_vanishing" (lean := "LeanRidgelet.integral_pow_mul_angularFourier1D_eq_zero, LeanRidgelet.integral_polynomial_mul_angularFourier1D_eq_zero") (uses := "l1_fourier_away_from_origin, mathlib_lizorkin_space")
*Moments of a spectrum supported away from the origin.* All moments $`\int\zeta^n\widehat\varphi(\zeta)\,d\zeta` of the Fourier transform of a Schwartz function $`\varphi` with $`0\notin\operatorname{tsupport}\varphi` vanish, hence so does the pairing against any polynomial. Since moments are the derivatives of the Fourier transform at the origin (`mathlib_lizorkin_space`), this is the analytic heart of the invisibility of polynomials, and gives `l1_lizorkin_quotient_invariance`.
:::

*`L1.TruncatedPower`: the Gel'fand--Shilov pairing*

:::lemma_ "l1_gelfand_shilov_pairing" (lean := "LeanRidgelet.angularFourier1D_deriv, LeanRidgelet.setIntegral_Ioi_angularFourier1D, LeanRidgelet.truncatedPowerFourier_pairing") (uses := "l1_standard_activations, mathlib_schwartz_aux")
*The pairing identity for the truncated powers.* The identity $`\int_0^\infty z^k\widehat\varphi(z)\,dz=\int k!/(i\zeta)^{k+1}\varphi(\zeta)\,d\zeta` for test functions supported away from the origin is proved by induction on $`k`. The base case computes the half-line integral of an angular Fourier transform through finite truncations, Fubini's theorem and the Riemann--Lebesgue lemma (second declaration); the inductive step trades one power of $`z` for one derivative of the test function through the angular derivative rule $`\widehat{\varphi'}(\zeta)=i\zeta\widehat\varphi(\zeta)` (first declaration) and integrates by parts on the real line.
:::

*`L1.PairingExtension`: absolute convergence and step T4*

:::lemma_ "l1_reconstruction_moment_layer" (lean := "LeanRidgelet.integrable_reflectedConjConvolution_integrand, LeanRidgelet.norm_reflectedConjConvolution_le, MeasureTheory.integral_pow_mul_conj_comp_sub_eq_zero, LeanRidgelet.integral_euclideanRidgeletTransform_mul_activation") (uses := "l1_ridgelet_transforms, l1_radon_backprojection")
*Absolute-convergence layer for the reconstruction.* For an activation with $`\|\eta(z)\|\le C_\eta(1+|z|)^k` and a ridgelet function with finite $`k`-th moment, the convolution kernel $`w=\overline{\widetilde\psi}*\eta` converges absolutely at every point with growth $`\|w(z)\|\le C_\eta\,(\int(1+|s|)^k\|\psi(s)\|ds)\,(1+|z|)^k` (first and second declarations), and for a signal with finite $`k`-th moment the bias pairing of the ridgelet transform factors through it (`eq:convdz` in Euclidean coordinates, fourth declaration):
$$`\int_{\mathbb R}\mathscr R_\psi f(\boldsymbol{a},b)\,\eta(t-b)\,db=\|\boldsymbol{a}\|\int_{\mathbb R^m}f(\boldsymbol{y})\,w(t-\langle\boldsymbol{a},\boldsymbol{y}\rangle)\,d\boldsymbol{y}.`
Vanishing moments of $`\psi` up to $`k` are inherited by every shifted conjugate section $`r\mapsto\overline{\psi(r-c)}` (third declaration, stated in Mathlib generality in the upstream chapter), the mechanism hiding the polynomial part of the activation.
:::

:::lemma_ "l1_pairing_extension" (lean := "LeanRidgelet.hasFourierAwayFromOrigin_pairing_extension") (uses := "l1_fourier_away_from_origin, l1_reconstruction_moment_layer, mathlib_weighted_l1_smoothing")
*Pairing extension for Fourier data away from the origin (step T4).* For an activation of growth degree $`k` with Fourier data $`F_\eta` and a weighted-`L¹` function $`\Xi` with vanishing moments up to $`k`,
$$`\int\eta(z)\,\Xi(z)\,dz=\frac1{2\pi}\int_{\zeta\ne0}F_\eta(\zeta)\,\widehat\Xi(-\zeta)\,d\zeta,`
provided the right-hand side converges absolutely. The polynomial part of $`\eta` is invisible on both sides — on the right because the integral omits the origin, on the left by the vanishing moments — realizing the dual pairing of the Lizorkin quotient at function level. The proof feeds the Schwartz test functions $`\varphi_{n,\ell}=c_n\cdot(\kappa_\ell*\chi)` — with $`\chi(\zeta)=\widehat\Xi(-\zeta)`, a compactly supported mollifier $`\kappa_\ell`, and a smooth cutoff $`c_n=b(\zeta/n)-b(n\zeta)` vanishing near the origin — to the defining pairing; the transform identity $`\widehat{\varphi_{n,\ell}}(z)=\int\Xi(r)\widehat\kappa_\ell(r)\widehat c_n(z-r)\,dr` holds by two absolutely convergent Fubini computations. As $`\ell\to\infty` both sides converge by dominated convergence; as $`n\to\infty`, the splitting $`\widehat c_n(s)=n\widehat b(ns)-n^{-1}\widehat b(s/n)` sends the taper term to $`2\pi\int\eta\,\Xi` by the weighted approximate identity and kills the low-cut term by the vanishing-moment cancellation, both proved in the upstream chapter (`mathlib_weighted_l1_smoothing`).
:::

*`L1.ReconstructionSection`, `L1.Reconstruction`: steps T1--T3 and T5--T6*

:::lemma_ "l1_reconstruction_section" (lean := "LeanRidgelet.truncatedReconstructionSection, LeanRidgelet.truncatedDualRidgeletTransform_eq_section_pairing, LeanRidgelet.aestronglyMeasurable_truncatedReconstructionSection, LeanRidgelet.integrable_weight_truncatedReconstructionSection, LeanRidgelet.integral_pow_mul_truncatedReconstructionSection_eq_zero, LeanRidgelet.truncatedSpectralFactor, LeanRidgelet.angularFourier1D_truncatedReconstructionSection, LeanRidgelet.norm_truncatedSpectralFactor_le, LeanRidgelet.norm_truncatedSpectralFactor_le_of_ne") (uses := "l1_ridgelet_transforms, l1_reconstruction_moment_layer, mathlib_prod_shear")
*The reconstruction section and its spectral data (steps T1--T3).* The truncated reconstruction is the pairing of the activation against the section $`\Xi_{x,\varepsilon,\delta}(r)=\int_{\varepsilon\le\|a\|\le\delta}\int f(y)\,\overline{\psi(r-\langle a,x-y\rangle)}\,dy\,da`:
$$`\mathscr R^\dagger_\eta[\mathscr R_\psi f](x;\varepsilon,\delta)=\int\eta(r)\,\Xi_{x,\varepsilon,\delta}(r)\,dr,`
absolutely convergent under matched $`k`-th moments (step T1; the proof substitutes $`b\leftarrow\langle a,x\rangle-r` fibrewise and swaps the scale and pairing integrals through a triple-kernel layer built from the parametrized skew shears). The section is measurable, lies in the $`(1+|r|)^k`-weighted $`L^1`, and inherits the vanishing moments of $`\psi`: $`\int r^j\,\Xi_{x,\varepsilon,\delta}(r)\,dr=0` for $`j\le k` (step T3 — the integrated form of the shifted-conjugate moment lemma, placing $`\Xi` in the domain of the pairing extension). Its Fourier data is computed by the spectral factor $`H_{x,\varepsilon,\delta}(\zeta)=\int_{\varepsilon\le\|a\|\le\delta}\widehat f(\zeta a)e^{i\zeta\langle a,x\rangle}da`:
$$`\widehat\Xi(\zeta)=\overline{\widehat\psi(-\zeta)}\,H(-\zeta),\qquad \|H(\zeta)\|\le\min\bigl(\|f\|_1\,\mathrm{vol}(A_{\varepsilon,\delta}),\ |\zeta|^{-m}\|\widehat f\|_1\bigr),`
the two bounds — uniform near the origin, dilation-decaying at infinity — that make the admissibility pairing of step T5 absolutely convergent.
:::

:::lemma_ "l1_spectral_pairing" (lean := "LeanRidgelet.truncatedSpectralWindow, LeanRidgelet.truncatedSpectralWindow_eq, LeanRidgelet.integrable_truncatedReconstructionSection, LeanRidgelet.integrableOn_fourierData_truncatedReconstructionSection, LeanRidgelet.setIntegral_fourierData_truncatedReconstructionSection, LeanRidgelet.truncatedDualRidgeletTransform_eq_spectral_pairing") (uses := "l1_reconstruction_section, l1_pairing_extension")
*The spectral pairing of the truncated reconstruction (step T5).* The spectral window $`G_{x,\varepsilon,\delta}(\zeta)=\int_{|\zeta|\varepsilon\le\|\xi\|\le|\zeta|\delta}\widehat f(\xi)e^{i\langle\xi,x\rangle}d\xi` is the $`|\zeta|^m`-rescaled spectral factor, $`G(\zeta)=|\zeta|^mH(\zeta)`, by the dilation $`\xi=\zeta a`. The dilation bound $`\|H(\zeta)\|\le|\zeta|^{-m}\|\widehat f\|_1` dominates the pairing integrand of the extension theorem by the admissibility density $`u(\zeta)=\overline{\widehat\psi(\zeta)}F_\eta(\zeta)/|\zeta|^m`, giving the absolute convergence $`\|F_\eta(\zeta)\widehat\Xi(-\zeta)\|\le\|u(\zeta)\|\,\|\widehat f\|_1` demanded by the pairing extension — the point where the integrability half of admissibility enters. Combining T1--T5:
$$`\mathscr R^\dagger_\eta[\mathscr R_\psi f](x;\varepsilon,\delta)=\frac1{2\pi}\int_{\zeta\ne0}u(\zeta)\,G_{x,\varepsilon,\delta}(\zeta)\,d\zeta.`
:::

:::lemma_ "l1_truncation_limit" (lean := "LeanRidgelet.norm_truncatedSpectralWindow_le, LeanRidgelet.continuous_truncatedSpectralFactor, LeanRidgelet.tendsto_truncatedSpectralWindow, LeanRidgelet.tendsto_truncatedDualRidgeletTransform, LeanRidgelet.ae_integral_angularFourier_mul_exp, LeanRidgelet.integral_angularFourier_mul_exp_of_continuousAt") (uses := "l1_spectral_pairing, mathlib_fourier_inversion_ae, angular_plancherel")
*The truncation limit (step T6).* At every nonzero frequency the spectral window converges to the full inverse spectral integral along the truncation filter $`\varepsilon\to0^+`, $`\delta\to\infty` (dominated convergence over the dilated annuli, majorant $`\|\widehat f\|_1`; the origin is null for $`m\ge1`). A second dominated convergence with majorant $`\|u\|\,\|\widehat f\|_1` — uniform in the truncation — passes the limit through the spectral pairing:
$$`\mathscr R^\dagger_\eta[\mathscr R_\psi f](x;\varepsilon,\delta)\longrightarrow K_{\psi,\eta}\,(2\pi)^{-m}\int\widehat f(\xi)e^{i\langle\xi,x\rangle}d\xi,`
and the inverse spectral integral equals $`(2\pi)^mf(x)` almost everywhere (by almost-everywhere Fourier inversion) and at continuity points (by Mathlib's inversion theorem), through the angular bridge of the foundations chapter. This proves `l1_reconstruction`.
:::

*`L1.LambdaOperator`: the multiplier property*

:::theorem "l1_lambda_multiplier" (lean := "LeanRidgelet.lambda_symbol_even, LeanRidgelet.lambda_symbol_odd, LeanRidgelet.lambdaOperatorPow_eq_fourier_multiplier, LeanRidgelet.angularSchwartz, LeanRidgelet.lambdaOperatorPow_eq_angular, LeanRidgelet.hasFourierAwayFromOrigin_angularFourierInv, LeanRidgelet.hasFourierAwayFromOrigin_lambdaOperatorPow, LeanRidgelet.integrable_lambdaOperatorPow_of_even, LeanRidgelet.integral_iteratedDeriv_schwartz_eq_zero, LeanRidgelet.integrable_lambdaOperatorPow, LeanRidgelet.angularFourier1D_lambdaOperatorPow") (uses := "l1_radon_backprojection, mathlib_hilbert_symbol, mathlib_schwartz_aux, mathlib_lizorkin_space")
*The Lambda operator as a Fourier multiplier (plan item A-3).* On Schwartz functions the standard Lambda-operator power $`\Lambda^m` acts as the Fourier multiplier $`|2\pi\xi|^m`, i.e. the article's $`|\omega|^m` in the angular convention $`\omega=2\pi\xi`:
$$`\Lambda^m\varphi(z)=\int|2\pi\xi|^m\,\mathcal F\varphi(\xi)\,e^{2\pi iz\xi}\,d\xi.`
The even case is Fourier inversion together with the derivative rule $`\mathcal F[\partial^m\varphi]=(2\pi i\xi)^m\mathcal F\varphi` and the identity $`(-1)^{m/2}(2\pi i\xi)^m=|2\pi\xi|^m`; the odd case additionally uses the Fourier symbol $`-i\,\mathrm{sign}\,\xi` of the principal-value Hilbert transform (upstream-candidate `mathlib_hilbert_symbol`) and the identity $`(-1)^{\lfloor m/2\rfloor}(-i\,\mathrm{sign}\,\xi)(2\pi i\xi)^m=|2\pi\xi|^m`. The angular form (fifth declaration) exhibits $`\Lambda^m\varphi` as the inverse angular Fourier transform of the integrable multiplier $`|\zeta|^m\widehat\varphi`, and a general lemma — the inverse angular Fourier transform of an integrable function carries that function as its Fourier data away from the origin (sixth declaration) — yields the Fourier data of $`\Lambda^m\varphi` (seventh), which is what the spectral form of `thm:eq.ac` needs. The sixth declaration is also the function-level substitute for the duality $`\mathcal O_M\cong\mathcal O_C'` in the necessity half of `l1_structure_theorem`, its witness being bounded and continuous rather than slowly increasing and smooth. *Integrability of the filtered function.* For even $`m` it is Schwartz (eighth declaration); for odd $`m` it is $`\pm\mathscr H\varphi^{(m)}`, whose integral vanishes because it is a derivative (ninth declaration), so the $`L^1` estimate of `mathlib_hilbert_symbol` applies and $`\Lambda^m\varphi\in L^1` for every $`m\ge1` (tenth declaration). Angular Fourier inversion then upgrades the Fourier data to the honest Fourier integral at every frequency (eleventh declaration), which is what `l1_construction_admissible` needs. This chain is also the analytic prerequisite of Radon's inversion formula for even $`m`.
:::

*`L1.FourierData`: uniqueness and the convolution theorem away from the origin*

:::lemma_ "l1_fourier_data_convolution" (lean := "LeanRidgelet.angularFourier1D_apply, LeanRidgelet.integrable_mul_of_tsupport_subset_compl_singleton, LeanRidgelet.hasFourierAwayFromOrigin_ae_eq, LeanRidgelet.HasFourierAwayFromOrigin.congr_data, LeanRidgelet.angularFourier1D_mul_conj_angularFourier1D, LeanRidgelet.hasFourierAwayFromOrigin_reflectedConjConvolution") (uses := "l1_fourier_away_from_origin, l1_reconstruction_moment_layer, mathlib_prod_shear, mathlib_polynomial_growth")
*Uniqueness of Fourier data, and the convolution theorem away from the origin.* Two representatives of the Fourier transform of the same function away from the origin agree almost everywhere on $`\mathbb R\setminus\{0\}`: a smooth bump compactly supported there is a legitimate test function, so the fundamental lemma of the calculus of variations applies on that open set (third declaration; the second supplies the integrability that makes the defining pairing an honest Bochner integral). If $`\eta` carries the Fourier data $`F_\eta` and $`\psi` is Schwartz, then $`\overline{\widetilde\psi}\ast\eta` carries the Fourier data $`\overline{\widehat\psi}F_\eta` (last declaration). The proof pairs against a test function $`\theta` supported away from the origin, moves $`\overline{\widehat\psi}` onto $`\theta` — the product $`\theta\,\overline{\widehat\psi}` is again Schwartz and again supported away from the origin — and uses the identity
$$`\widehat{\theta\,\overline{\widehat\psi}}(s)=\int\overline{\psi(s-z)}\,\widehat\theta(z)\,dz`
(fourth declaration; the factor $`(2\pi)^{-1}` of the product-convolution theorem cancels against the factor $`2\pi` of the double transform). Fubini's theorem then exchanges the two iterated integrals: the dominating function factorizes after $`1+|z-t|\le(1+|z|)(1+|t|)`, and the shear $`(z,t)\mapsto(z,z-t)` of `mathlib_prod_shear` carries one iterated order to the other. Together with `l1_lambda_multiplier` this is what turns the backprojection equation of `thm:eq.ac` into its spectral form; the fourth declaration records that Fourier data depends only on its values away from the origin, which is what lets the two forms be compared.
:::

*`L1.Plancherel`, `L1.ReconstructionL2`: the `L²` layer*

:::lemma_ "l1_plancherel_lintegral" (lean := "LeanRidgelet.aestronglyMeasurable_euclideanRidgeletTransform, LeanRidgelet.aestronglyMeasurable_euclideanRidgeletTransform_parameterMeasure, LeanRidgelet.lintegral_enorm_euclideanRidgeletTransform_sq, LeanRidgelet.memLp_two_euclideanRidgeletTransform") (uses := "l1_fourier_expression, mathlib_fourier_plancherel")
*Strong measurability and the `lintegral` form of Plancherel's identity.* The ridgelet transform is strongly measurable on parameter space, for the Lebesgue and the weighted measure and for every homogeneity index. Plancherel's identity is proved first in `lintegral` form — `eq:fstridge` factors the fibre, the fibrewise `L¹ ∩ L²` Plancherel identity in the angular convention evaluates it, the weight $`\|a\|^{-2}` cancels against $`\|a\|^2`, Tonelli's theorem and the dilation change of variables $`\xi=\zeta a` reduce it to the $`m`-dimensional Plancherel identity, and $`K_{\psi,\psi}=1` closes it. Square-integrability $`\mathscr R_\psi f\in L^2(\mathbb Y^{m+1})` follows, and drives both `l1_parseval_plancherel` and the bounded extension `l1_L2_extension`.
:::

:::lemma_ "l1_l2_duality_steps" (lean := "LeanRidgelet.integral_norm_euclideanRidgeletTransform_bias_le, LeanRidgelet.integrable_weight_indicator_euclideanRidgeletTransform, LeanRidgelet.norm_truncatedDualRidgeletTransform_le, LeanRidgelet.aestronglyMeasurable_truncatedDualRidgeletTransform, LeanRidgelet.setIntegral_annulus_ridgeletTransform_mul_conj, LeanRidgelet.eLpNorm_truncatedDualRidgeletTransform_sub_le, LeanRidgelet.tendsto_setIntegral_compl_annulus_norm_sq") (uses := "l1_dual_operator, l1_parseval_plancherel, mathlib_l2_duality")
*The three quantitative steps of `thm:formula.L2`.* (i) *Truncated duality*: the identity `thm:dual`, applied to the data $`1_A\mathscr R_\psi f` truncated to the annulus $`A=\{\varepsilon\le\|a\|\le\delta\}` — whose weighted form is integrable because $`\|\mathscr R_\psi f(a,\cdot)\|_1\le\|f\|_1\|\psi\|_1\|a\|` — identifies $`\langle\mathscr R^\dagger_\eta[\mathscr R_\psi f](\cdot;\varepsilon,\delta),g\rangle` with $`\langle\mathscr R_\psi f,\mathscr R_\eta g\rangle_{L^2(A)}`. (ii) *Error bound*: subtracting Parseval's relation, the error pairs with $`g` as $`-\langle\mathscr R_\psi f,\mathscr R_\eta g\rangle_{L^2(A^c)}`, which Cauchy--Schwarz and the Plancherel identity for $`\eta` bound by $`\|\mathscr R_\psi f\|_{L^2(A^c)}\|g\|_2`; since the truncated reconstruction is bounded and measurable, the upstream `L²` duality criterion — testing against the truncations of the error to an exhausting sequence of balls — converts this into $`\|\mathscr R^\dagger_\eta[\mathscr R_\psi f](\cdot;\varepsilon,\delta)-f\|_2\le\|\mathscr R_\psi f\|_{L^2(A^c)}`, with no a priori `L²`-membership of the truncated reconstruction. (iii) *Vanishing tail*: dominated convergence along the truncation filter sends $`\|\mathscr R_\psi f\|_{L^2(A^c)}` to zero, because the annulus exhausts $`\mathbb Y^{m+1}` up to the null set of vanishing weights.
:::

*`L1.BumpRidgelet`: the explicit witness*

:::lemma_ "l1_bump_ridgelet_construction" (lean := "LeanRidgelet.spectrumBump, LeanRidgelet.bumpRidgeletSchwartz, LeanRidgelet.bumpAdmissibilityDensity, LeanRidgelet.admissibilityIntegrand_bumpRidgelet, LeanRidgelet.integral_bumpAdmissibilityDensity_pos, LeanRidgelet.admissibilityConstant_bumpRidgelet_ne_zero, LeanRidgelet.integrable_weight_bumpRidgelet, LeanRidgelet.norm_truncatedPower_one_le") (uses := "l1_standard_activations, l1_truncated_power_fourier")
*Construction of the explicit admissible ridgelet function.* Take a smooth bump supported in $`(5\pi/2,7\pi/2)`, positive at its centre $`3\pi`, as the spectrum, and let $`\psi` be its inverse Fourier transform; it is Schwartz, hence integrable with all weighted moments finite. Against the Fourier data $`k!/(i\zeta)^{k+1}` of the truncated power the admissibility integrand becomes a fixed nonzero constant times the nonnegative continuous compactly supported density $`\zeta\mapsto\widehat\psi(\zeta)/(\zeta^{k+1}|\zeta|^m)` on the positive half-line, so it is integrable and its integral is strictly positive; hence $`K_{\psi,z_+^k}\ne0`. All moments of $`\psi` vanish because its spectrum vanishes near the origin. The last declaration records the ReLU growth bound $`\|z_+\|\le1+|z|` used when the pair is fed into the reconstruction formula.
:::
