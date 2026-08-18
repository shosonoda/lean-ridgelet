import LeanRidgeletBlueprint.Chapters.ToMathlibRadonFourier
import LeanRidgelet.ToMathlib.PolarCoordinates
import LeanRidgelet.ToMathlib.DirichletIntegral
import LeanRidgelet.ToMathlib.GaussianSchwartz
import LeanRidgelet.ToMathlib.HilbertTransform
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

#doc (Manual) "Mathlib candidates: integral and Fourier tools" =>
%%%
file := "integral-fourier-tools"
%%%

Analytic tools that support Radon inversion and invariant integration: Schwartz sections, polar coordinates, the Dirichlet integral, Gaussian Schwartz estimates, and the Hilbert-transform symbol.

*Integral and Fourier tools*

:::theorem "mathlib_radon_schwartz_section" (lean := "MeasureTheory.schwartz_norm_le_one_add_norm_rpow, MeasureTheory.continuous_radonTransform_schwartz, MeasureTheory.radonSchwartzSection, MeasureTheory.fourier_radonSchwartzSection, MeasureTheory.radonTransform_eq_radonSchwartzSection") (uses := "mathlib_fourier_slice, mathlib_fourier_inversion_ae")
*Radon sections of Schwartz functions are Schwartz.* For a Schwartz function `f` on `E` and a unit direction `u`, the section $`\mathscr Rf(u,\cdot)` *equals* the Schwartz function $`\mathcal F^{-1}[\omega\mapsto\mathcal Ff(\omega u)]` (last declaration). The slice $`\omega\mapsto\mathcal Ff(\omega u)` is Schwartz because the ray map $`\omega\mapsto\omega u` is temperate and antilipschitz (`SchwartzMap.compCLMOfAntilipschitz`), so its inverse Fourier transform is Schwartz; the Fourier slice theorem identifies the two Fourier transforms, almost-everywhere Fourier inversion (upstream-candidate `mathlib_fourier_inversion_ae`) turns this into almost-everywhere equality, and continuity of both sides upgrades it to equality everywhere. Continuity of the section (second declaration) is dominated convergence with the Japanese-bracket dominator, available uniformly in the offset because a point of the line $`\mathbb Ru` and a point of $`(\mathbb Ru)^\perp` are orthogonal, whence $`\|pu+y\|\ge\|y\|`; the Schwartz decay is used in the form $`\|f(x)\|\le C(1+\|x\|)^{-k}` (first declaration). This is what makes one-dimensional Schwartz theory — in particular Fourier multipliers such as the filter of filtered backprojection — available on Radon sections.
:::

:::theorem "mathlib_polar_coordinates" (lean := "MeasureTheory.integral_eq_integral_prod_toSphere, MeasureTheory.integrable_prod_toSphere_of_integrable, MeasureTheory.integrable_volumeIoiPow_iff, MeasureTheory.ae_integrableOn_Ioi_of_integrable, MeasureTheory.integral_eq_integral_toSphere_integral_Ioi, MeasureTheory.sphereNeg, MeasureTheory.map_sphereNeg_toSphere, MeasureTheory.integral_sphereNeg, MeasureTheory.integral_eq_integral_toSphere_integral_Iio, MeasureTheory.ae_integrableOn_Iio_of_integrable, MeasureTheory.ae_integrable_radial_of_integrable, MeasureTheory.integral_eq_integral_toSphere_integral_two_sided, MeasureTheory.lintegral_eq_lintegral_prod_toSphere, MeasureTheory.lintegral_volumeIoiPow, MeasureTheory.lintegral_eq_lintegral_toSphere_lintegral_Ioi")
*Polar coordinates for the Bochner integral.* Mathlib's `Measure.toSphere` and `Measure.measurePreserving_homeomorphUnitSphereProd` give the polar decomposition of an additive Haar measure, but the integral formula is recorded only for *radial* integrands (`integral_fun_norm_addHaar`). The general formula
$$`\int_EF\,d\mu=\int_{\mathbb S}\int_0^\infty r^{d-1}F(ru)\,dr\,d\mu_{\mathbb S}(u),\qquad d=\dim E,`
is proved here by the same route: restrict to `E∖{0}`, transport along the polar homeomorphism (product form, first declaration), transport integrability (second declaration), and unwind the density of `Measure.volumeIoiPow` after Fubini (iterated form).
:::

The same two forms hold for the *lower Lebesgue integral*, and there the product form needs no hypothesis at all and the iterated form only measurability, both reductions being Tonelli rather than Fubini. That is the form an absolute convergence *statement* has to be proved with: deciding whether a product integrand is integrable means computing the integral of its norm, and that computation may not presuppose what it is meant to establish.

The fibrewise counterpart is here too: for an integrable $`F`, almost every radial section $`r\mapsto|r|^{d-1}F(ru)` is itself integrable on $`\mathbb R`. It follows from the product integrability by Fubini on the positive half-line, and on the negative half-line by transporting along $`r\mapsto-r` together with invariance of the sphere measure under the antipodal map. This is what keeps the iterated formulas free of any hypothesis beyond integrability of $`F`, and in particular it is what makes the two-sided form below unconditional.

Invariance of the sphere measure under the antipodal map is itself missing from Mathlib, which records how `Measure.toSphere` is computed but none of its symmetries. It is what turns the polar formula above, whose radial variable runs over $`(0,\infty)`, into the two-sided form whose radial variable runs over all of $`\mathbb R` at the cost of a factor $`2` — the double cover $`(r,u)\mapsto ru` of $`E\setminus\{0\}`. That two-sided form is the one that matches a scale parameter ranging over a full Euclidean space, and it is what the $`d`-plane reconstruction formula at codimension one evaluates its direction integral with.

:::theorem "mathlib_dirichlet_integral" (lean := "MeasureTheory.tendsto_intervalIntegral_sin_div_atTop, MeasureTheory.abs_intervalIntegral_sin_div_le, MeasureTheory.sinDivTail, MeasureTheory.tendsto_intervalIntegral_sin_div_atTop_left, MeasureTheory.abs_sinDivTail_le, MeasureTheory.tendsto_sinDivTail_nhds_zero, MeasureTheory.intervalIntegral_sin_mul_div_eq")
*The Dirichlet integral.* Mathlib knows `Real.sinc` and its elementary bounds but not the *Dirichlet integral*
$$`\int_0^\infty\frac{\sin t}{t}\,dt=\frac\pi2,`
which exists only as an improper integral. It is proved here (first declaration) by the Laplace representation $`1/t=\int_0^\infty e^{-ut}\,du`, Fubini on $`(0,R]\times(0,\infty)` (absolutely convergent because $`|\sin t|\le t`), the elementary primitive of $`t\mapsto e^{-ut}\sin t`, the arctangent integral $`\int_0^\infty du/(1+u^2)=\pi/2`, and the $`O(1/R)` bound on the error term. Conditionally convergent Fourier computations need two companions, also proved here: the *uniform bound* $`|\int_a^b\sin u/u\,du|\le3` for all $`0\le a\le b` (second declaration; short intervals by $`|\sin u/u|\le1`, long ones by integration by parts, which gives $`\le2/a` for $`a\ge1`), and the *tail* $`\int_a^\infty\sin u/u\,du` as the explicit function $`\pi/2-\int_0^a\sin u/u\,du` with its limit description, uniform bound and limit $`\pi/2` as $`a\to0` (remaining declarations, including the scaling and oddness relation in the frequency variable).
:::

:::theorem "mathlib_gaussian_schwartz" (lean := "Real.pow_mul_exp_neg_le_factorial, Real.abs_pow_mul_exp_neg_sq_div_two_le, Real.one_add_abs_pow_mul_exp_neg_sq_div_two_le, Real.exists_bound_polynomial_eval, Real.exists_polynomial_iteratedDeriv_gaussian, Real.gaussianSchwartz")
*The Gaussian as a Schwartz function.* Mathlib has the Gaussian integral and the Fourier transform of a Gaussian, but no realization of $`z\mapsto e^{-z^2/2}` as an element of Schwartz space. Two ingredients: every derivative is a polynomial multiple of the Gaussian, $`G^{(n)}=p_nG` with $`p_0=1` and $`p_{n+1}=p_n'-Xp_n` (fifth declaration, by induction on the product rule); and every power is dominated by the Gaussian, $`|x|^de^{-x^2/2}\le1+2^dd!` (second declaration, from $`x^d/d!\le e^x`), whence $`(1+|x|)^Ne^{-x^2/2}\le2^N(1+2^NN!)` (third). With the crude polynomial bound $`|p(z)|\le C(1+|z|)^d` (fourth) these give the Schwartz seminorm estimates directly, since in one variable the norm of the iterated Fréchet derivative is the norm of the iterated derivative.
:::

:::theorem "mathlib_hilbert_symbol" (lean := "MeasureTheory.pvHilbertTransform, MeasureTheory.setIntegral_hilbert_eq_Ioi, MeasureTheory.intervalIntegral_hilbert_eq_fourier, MeasureTheory.setIntegral_hilbert_eq_fourier_tail, MeasureTheory.pvHilbertTransform_schwartz, MeasureTheory.pvHilbertTransform_schwartz_eq_fourierInv, MeasureTheory.integrableOn_schwartz_oddDiff, MeasureTheory.pvHilbertTransform_schwartz_eq_oddIntegral, MeasureTheory.coord_mul_pvHilbertTransform, MeasureTheory.memLp_two_pvHilbertTransform, MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero") (uses := "mathlib_dirichlet_integral, mathlib_fourier_plancherel")
*The Hilbert transform and its Fourier symbol.* Mathlib has no Hilbert transform. Defined here in the classical normalization $`\mathscr Hg(x)=\frac1\pi\,\mathrm{p.v.}\int g(t)/(x-t)\,dt` (so $`\mathscr H^2=-1`), with its *Fourier symbol* on Schwartz functions,
$$`\mathscr Hg=\mathcal F^{-1}\big[-i\,\mathrm{sign}(\xi)\,\mathcal Fg\big]`
(the symbol is homogeneous of degree `0`, hence identical in every Fourier normalization). Three steps. The truncated integral is first rewritten as the absolutely convergent integral of the odd difference quotient $`(g(x-s)-g(x+s))/s` over $`(\varepsilon,\infty)`. Next, on a *doubly* truncated domain $`\varepsilon<s<R` — the outer cut-off is unavoidable, since the Hilbert kernel is not integrable at infinity and Fubini would fail — Fourier inversion and Fubini produce the partial Dirichlet integral $`\int_\varepsilon^R\sin(2\pi s\xi)/s\,ds` as symbol. Two dominated-convergence passes against the uniform Dirichlet bound then send $`R\to\infty` (symbol: the Dirichlet tail) and $`\varepsilon\to0` (symbol: $`-i\,\mathrm{sign}\,\xi`, by the Dirichlet integral). In particular the principal-value limit exists at every point of a Schwartz function. *Integrability.* The last four declarations prove that $`\mathscr Hg\in L^1` whenever $`g` is Schwartz with $`\int g=0` — the transform is only $`O(1/x)` in general, so the hypothesis is needed. Taking the limit $`\varepsilon\to0` in the first step exhibits $`\mathscr Hg` as an absolutely convergent integral of the odd difference quotient over $`(0,\infty)`, and from that form the *commutator identity*
$$`x\,\mathscr Hg(x)=\mathscr H\big(t\mapsto t\,g(t)\big)(x)+\tfrac1\pi\int g`
is the pointwise algebra $`xg(t)/(x-t)=tg(t)/(x-t)+g(t)`. With $`\int g=0` it says that $`x\,\mathscr Hg` is again the Hilbert transform of a Schwartz function; both are square-integrable because the symbol is unimodular and Plancherel applies, and away from the origin $`\|\mathscr Hg(x)\|=|x|^{-1}\|x\,\mathscr Hg(x)\|\le(1+x^2)^{-1}+\|x\,\mathscr Hg(x)\|^2` by the arithmetic--geometric mean inequality.
:::
