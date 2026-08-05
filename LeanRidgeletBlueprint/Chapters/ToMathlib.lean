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

#doc (Manual) "Mathlib upstream candidates" =>
%%%
file := "to-mathlib"
%%%

This development-only chapter collects the general-purpose analytic results developed for the
ridgelet formalization that are staged for upstreaming to Mathlib. They live under
`LeanRidgelet/ToMathlib/`, import only Mathlib, and carry no dependence on — or reference to —
the ridgelet theory. Statements are given on an arbitrary finite-dimensional real inner product
space with its canonical Lebesgue measure, or on a measurable additive commutative group with
an invariant σ-finite measure.

A survey of the pinned Mathlib version confirmed the gaps these files fill. Mathlib has no
Radon transform (`Mathlib.MeasureTheory` only carries Radon--Nikodym derivatives and Radon
measures), no Fourier slice theorem, no Hilbert transform, no Young convolution inequality
beyond the `L¹ ⋆ L¹` case (`MeasureTheory.Integrable.integrable_convolution` in
`Mathlib.Analysis.Convolution`), and no continuous Minkowski integral inequality
(`Mathlib.MeasureTheory.Integral.MeanInequalities` has only the two-function version).
`Mathlib.MeasureTheory.Function.LpSpace` contains no convolution results, and
`Mathlib.Analysis.CStarAlgebra.lpSpace` concerns the sequence spaces `lp A ∞` rather than
convolution on `L^p(G)`. The Young inequality proved here deliberately bypasses the missing
Minkowski integral inequality through the Hölder splitting described below.

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

:::theorem "mathlib_fourier_inversion_ae" (lean := "MeasureTheory.Integrable.fourierInv_fourier_ae_eq")
*Almost-everywhere Fourier inversion.* Mathlib's inversion theorem (`MeasureTheory.Integrable.fourierInv_fourier_eq`) recovers an integrable function with integrable Fourier transform at its continuity points; the almost-everywhere counterpart with no continuity hypothesis is absent. It is proved here: for `f` integrable on a finite-dimensional real inner product space with `𝓕 f` integrable, $`\mathcal F^{-1}[\mathcal F f]=f` almost everywhere. The proof pairs both sides against Schwartz functions — a Fubini swap computes the pairing of $`\mathcal F^{-1}\mathcal F f` against $`\varphi` as the pairing of $`\mathcal F f` against $`\mathcal F^{-1}\varphi`, the multiplication formula (`VectorFourier.integral_fourierIntegral_smul_eq_flip`) moves the transform back to `f`, and the Schwartz inversion closes the circle — and concludes with `ae_eq_of_integral_contDiff_smul_eq`.
:::

*Lp spaces*

:::theorem "mathlib_lp_integrable_dense" (lean := "MeasureTheory.Lp.dense_setOf_integrable")
*Density of the integrable elements in `Lp`.* For an exponent $`1\le p<\infty`, the classes in $`L^p(\mu)` with an integrable representative — that is, $`L^1\cap L^p(\mu)` — form a dense subset of $`L^p(\mu)`. Mathlib provides the density of `Lp` simple functions (`MeasureTheory.Lp.simpleFunc.dense`) and the integrability of `Lp` simple functions (`MeasureTheory.SimpleFunc.memLp_iff_integrable`) separately, but not this combination, which is the standard entry point for extending an operator defined by an absolutely convergent integral on $`L^1\cap L^p` to all of $`L^p`.
:::

*Product measures*

:::theorem "mathlib_radon_schwartz_section" (lean := "MeasureTheory.schwartz_norm_le_one_add_norm_rpow, MeasureTheory.continuous_radonTransform_schwartz, MeasureTheory.radonSchwartzSection, MeasureTheory.fourier_radonSchwartzSection, MeasureTheory.radonTransform_eq_radonSchwartzSection") (uses := "mathlib_fourier_slice, mathlib_fourier_inversion_ae")
*Radon sections of Schwartz functions are Schwartz.* For a Schwartz function `f` on `E` and a unit direction `u`, the section $`\mathscr Rf(u,\cdot)` *equals* the Schwartz function $`\mathcal F^{-1}[\omega\mapsto\mathcal Ff(\omega u)]` (last declaration). The slice $`\omega\mapsto\mathcal Ff(\omega u)` is Schwartz because the ray map $`\omega\mapsto\omega u` is temperate and antilipschitz (`SchwartzMap.compCLMOfAntilipschitz`), so its inverse Fourier transform is Schwartz; the Fourier slice theorem identifies the two Fourier transforms, almost-everywhere Fourier inversion (upstream-candidate `mathlib_fourier_inversion_ae`) turns this into almost-everywhere equality, and continuity of both sides upgrades it to equality everywhere. Continuity of the section (second declaration) is dominated convergence with the Japanese-bracket dominator, available uniformly in the offset because a point of the line $`\mathbb Ru` and a point of $`(\mathbb Ru)^\perp` are orthogonal, whence $`\|pu+y\|\ge\|y\|`; the Schwartz decay is used in the form $`\|f(x)\|\le C(1+\|x\|)^{-k}` (first declaration). This is what makes one-dimensional Schwartz theory — in particular Fourier multipliers such as the filter of filtered backprojection — available on Radon sections.
:::

:::theorem "mathlib_polar_coordinates" (lean := "MeasureTheory.integral_eq_integral_prod_toSphere, MeasureTheory.integrable_prod_toSphere_of_integrable, MeasureTheory.integral_eq_integral_toSphere_integral_Ioi")
*Polar coordinates for the Bochner integral.* Mathlib's `Measure.toSphere` and `Measure.measurePreserving_homeomorphUnitSphereProd` give the polar decomposition of an additive Haar measure, but the integral formula is recorded only for *radial* integrands (`integral_fun_norm_addHaar`). The general formula
$$`\int_EF\,d\mu=\int_{\mathbb S}\int_0^\infty r^{d-1}F(ru)\,dr\,d\mu_{\mathbb S}(u),\qquad d=\dim E,`
is proved here by the same route: restrict to `E∖{0}`, transport along the polar homeomorphism (product form, first declaration), transport integrability (second declaration), and unwind the density of `Measure.volumeIoiPow` after Fubini (iterated form, third declaration).
:::

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

:::theorem "mathlib_l2_duality" (lean := "MeasureTheory.eLpNorm_two_eq_lintegral_enorm_sq, MeasureTheory.MemLp.norm_integral_mul_conj_le, MeasureTheory.MemLp.integrable_norm_sq, MeasureTheory.eLpNorm_two_le_of_forall_indicator_pairing_le, MeasureTheory.memLp_two_of_integrable_of_bound")
*Cauchy--Schwarz and an `L²` duality criterion.* Two elementary tools that Mathlib states only in `Lp`-space form. First, *Cauchy--Schwarz for Bochner integrals*: for square-integrable scalar `u`, `v`,
$$`\Big\|\int u\,\overline v\Big\|\le\Big(\int\|u\|^2\Big)^{1/2}\Big(\int\|v\|^2\Big)^{1/2},`
by Hölder's inequality for the norms. Second, an *`L²` duality criterion*: if `h` is measurable, the measurable sets $`s_n` increase to the whole space, every truncation $`1_{s_n}h` is square-integrable, and
$$`\Big|\int h\,\overline{1_{s_n}h}\Big|\le M\,\|1_{s_n}h\|_2\quad\text{for all }n,`
then `h` itself is square-integrable with $`\|h\|_2\le M`. This is the standard device for turning a duality bound $`|\langle h,g\rangle|\le M\|g\|_2` into a norm bound *without* knowing beforehand that `h` lies in `L²`: each truncation is square-integrable by construction, the displayed inequality reads $`t_n\le M\sqrt{t_n}` for $`t_n=\|1_{s_n}h\|_2^2`, and monotone convergence lifts the resulting uniform bound $`t_n\le M^2` to `h`. The auxiliary `lintegral` form of the `L²` seminorm, the natural-power integrability of $`\|\cdot\|^2`, and the inclusion $`L^1\cap L^\infty\subseteq L^2` (an integrable function with a uniform bound is square-integrable) are provided alongside.
:::

:::theorem "mathlib_prod_shear" (lean := "MeasureTheory.measurePreserving_prodSwapRight, MeasureTheory.measurePreserving_skewDivLeft, MeasureTheory.measurePreserving_skewSubLeft, MeasureTheory.quasiMeasurePreserving_skewDivLeft, MeasureTheory.quasiMeasurePreserving_skewSubLeft, MeasureTheory.measurePreserving_skewDivRight, MeasureTheory.measurePreserving_skewSubRight, MeasureTheory.quasiMeasurePreserving_skewDivRight, MeasureTheory.quasiMeasurePreserving_skewSubRight")
*Parametrized shears and rearrangements of product measures.* Two elementary transports for iterated Fubini arguments: the rearrangement $`((a,b),c)\mapsto((a,c),b)` exchanging the two right factors of a left-nested triple product of s-finite measures preserves the product measures; and for a measurable parameter map `c` into a measurable group with an invariant fiber measure, the parametrized shears $`(w,b)\mapsto(w,c(w)/b)` and $`(w,b)\mapsto(w,b/c(w))` preserve `μ.prod ν`, with quasi-measure-preserving evaluations $`(w,b)\mapsto c(w)/b` and $`(w,b)\mapsto b/c(w)` (multiplicative and additive versions). The evaluations are the standard device for the joint measurability of kernels $`(w,b)\mapsto g(c(w)-b)` with `g` merely a.e. strongly measurable.
:::

*Weighted `L¹` smoothing*

:::theorem "mathlib_weighted_l1_smoothing" (lean := "abs_pow_sub_pow_le_mul, norm_sub_taylorSum_le, MeasureTheory.tendsto_setIntegral_norm_abs_gt, MeasureTheory.tendsto_integral_norm_sub_comp_sub_right, MeasureTheory.tendsto_integral_weight_norm_sub_comp_sub_right, MeasureTheory.integrable_weight_norm_comp_sub, MeasureTheory.integrable_weight_norm_sub_comp_sub, MeasureTheory.continuous_integral_weight_norm_sub, MeasureTheory.integral_comp_sub_div_smul, MeasureTheory.tendsto_integral_weight_norm_smoothing_sub, MeasureTheory.tendsto_integral_mul_smoothing_of_vanishing_moments")
*Polynomial-weighted `L¹` smoothing estimates.* The estimates driving the function-level pairing theory of tempered distributions modulo polynomials: a Lipschitz bound $`|x^n-y^n|\le nM^{n-1}|x-y|` on $`[0,M]`; a uniform Taylor remainder bound $`\|f(a+h)-\sum_{j\le k}(h^j/j!)f^{(j)}(a)\|\le C|h|^{k+1}/k!` on unordered intervals (both endpoints of Mathlib's `taylor_mean_remainder_bound`, through reflection); the vanishing of integral tails $`\int_{|r|>c}\|g\|\to0`; the continuity of translation in `L¹(ℝ)` — obtained from `MeasureTheory.Lp.compMeasurePreserving_continuous`, which Mathlib provides without this classical corollary — together with its polynomially weighted form; the weighted integrability and continuity of the translation modulus $`\omega(s)=\int(1+|z|)^k\|\Xi(z-s)-\Xi(z)\|dz`; an `E`-valued affine change of variables $`\int F((w-r)/c)\,dw=c\cdot\int F`; the *scaled approximate identity in weighted `L¹`* ($`\int(1+|z|)^k\|\int K(u)\Xi(z-u/c)\,du-\Xi(z)\|dz\to0` as $`c\to\infty` for kernels `K` of unit integral and finite `k`-th moment, by a Tonelli swap and dominated convergence against the modulus $`\omega`); and the *vanishing-moment cancellation for wide smoothing* (last declaration): if $`\Xi` has a finite `k`-th moment and vanishing moments up to `k` and $`\eta` is strongly measurable with growth at most $`(1+|z|)^k`, then $`\int\Xi(r)\,c^{-1}\!\int\eta(w)\theta((w-r)/c)\,dw\,dr\to0` as `c → ∞` for every Schwartz kernel $`\theta`. The proof Taylor-expands the kernel to order `k`, splits the line at $`|r|=c`, bounds the outside by the integral tail, converts the truncated Taylor moments into tails through the vanishing moments, and dominates the remainder by $`\min(1,|r|/c)`; exactly `k` moments suffice.
:::

*Schwartz space*

:::definition "mathlib_lizorkin_space" (lean := "IsLizorkin, LizorkinSpace, mem_lizorkinSpace_iff, integrable_pow_smul_schwartz, Real.fourier_apply_zero, Real.iteratedDeriv_fourier_zero, mem_lizorkinSpace_iff_fourier_flat, integral_polynomial_mul_eq_zero_of_mem_lizorkinSpace, LizorkinDistribution")
*The Lizorkin space and Lizorkin distributions.* Mathlib has the Schwartz space and its Fourier theory but not the *Lizorkin space* $`\mathcal S_0(\mathbb R)`, the submodule of Schwartz functions all of whose moments vanish. It is defined here, together with the identity `moments = derivatives of the Fourier transform at the origin`, whence the *Fourier characterization*: a Schwartz function is Lizorkin exactly when its Fourier transform vanishes to infinite order at the origin. *Polynomials annihilate it*, the precise form of the statement that a point mass $`\delta^{(j)}` at the origin is invisible. The *Lizorkin distributions* $`\mathcal S_0'(\mathbb R)=\mathcal S_0(\mathbb R)\to_L\mathbb C` are tempered distributions modulo polynomials.
:::

:::theorem "mathlib_polynomial_growth" (lean := "MeasureTheory.PolynomiallyBounded, MeasureTheory.polynomiallyBounded_nonneg_const, MeasureTheory.PolynomiallyBounded.add, MeasureTheory.polynomiallyBounded_polynomial_eval, MeasureTheory.PolynomiallyBounded.integrable_mul_schwartz, one_add_abs_add_le_mul, MeasureTheory.integrable_one_add_abs_pow_mul_schwartz, MeasureTheory.integral_pow_mul_conj_comp_sub_eq_zero")
*Polynomially bounded functions.* Mathlib has `Function.HasTemperateGrowth`, which additionally demands smoothness with polynomially bounded derivatives of every order, but no bare growth predicate $`\|f(z)\|\le C(1+|z|)^k` for merely measurable functions — the classical criterion, together with local integrability, for defining a tempered distribution. It is introduced here with its closure under addition, its validity for polynomials, and the resulting integrability against every Schwartz function. Alongside: submultiplicativity $`1+|z+t|\le(1+|z|)(1+|t|)` of the weight, weighted integrability $`(1+|s|)^k\|\varphi(s)\|\in L^1` of Schwartz functions, and the invariance of vanishing moments under shift and conjugation, $`\int r^j\overline{\psi(r-c)}\,dr=0` for $`j\le k`.
:::

:::theorem "mathlib_schwartz_aux" (lean := "coe_iterate_schwartz_derivCLM, iteratedDeriv_eq_zero_of_tsupport_subset_compl, exists_pos_le_abs_of_tsupport_subset, MeasureTheory.integrable_mul_of_bound_on_tsupport, hasTemperateGrowth_const_mul, antilipschitzWith_const_mul")
*Auxiliary lemmas on Schwartz functions and supports.* Iterating `SchwartzMap.derivCLM` computes `iteratedDeriv`; all derivatives of a Schwartz function supported away from a point vanish at that point; a function supported away from the origin is uniformly separated from it; multiplying an integrable function by a factor bounded on its support preserves integrability; and the scaling $`\zeta\mapsto c\zeta` is of temperate growth and, for $`c\ne0`, antilipschitz — the two hypotheses of `SchwartzMap.compCLMOfAntilipschitz`, which is how a Fourier rescaling is recognized as an endomorphism of the Schwartz space.
:::

*Convolution*

:::theorem "mathlib_young_convolution" (lean := "MeasureTheory.enorm_integral_mul_sub_le, MeasureTheory.lintegral_lintegral_mul_comp_sub, MeasureTheory.eLpNorm_convolution_le, MeasureTheory.Integrable.convolution_memLp")
*Young's convolution inequality `L¹ ⋆ L^p ⊆ L^p`.* On a measurable additive commutative group with an invariant σ-finite measure, $`\|f\ast g\|_{L^p}\le\|f\|_{L^1}\|g\|_{L^p}` for $`1\le p\le\infty` with no finiteness hypotheses, and the convolution of an integrable function with an $`L^p` function is in $`L^p`. The proof avoids the (also missing) continuous Minkowski integral inequality through the Hölder splitting $`\|f(t)\|\,\|g(x-t)\|=\|f(t)\|^{1/q}\cdot(\|f(t)\|^{1/p}\|g(x-t)\|)`, the two-function Hölder inequality `ENNReal.lintegral_mul_le_Lp_mul_Lq`, Tonelli's theorem, and translation invariance.
:::
