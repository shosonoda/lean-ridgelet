import LeanRidgelet.ToMathlib.WeightedL1Smoothing
import LeanRidgelet.ToMathlib.Lizorkin
import LeanRidgelet.ToMathlib.PolynomialGrowth
import LeanRidgelet.ToMathlib.SchwartzAux
import LeanRidgelet.ToMathlib.YoungConvolution
import LeanRidgelet.ToMathlib.TemperateGrowth
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

#doc (Manual) "Mathlib candidates: Schwartz space and convolution" =>
%%%
file := "schwartz-convolution"
%%%

Weighted smoothing, Lizorkin and Schwartz-space auxiliaries, Young's convolution inequality, and a reusable temperate-growth closure theorem.

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

:::theorem "mathlib_temperate_growth_rpow" (lean := "Function.norm_iteratedFDerivWithin_rpow_le, Function.HasTemperateGrowth.rpow_of_le")
*A real power of a temperate function bounded away from zero has temperate growth.* Mathlib has this for the Bessel potential multiplier $`x\mapsto(1+\|x\|^2)^a`, whose proof composes $`u\mapsto u^a` — temperate on any ray bounded away from the origin — with the inner function $`1+\|x\|^2`, whose *range* is bounded away from the origin; its own comment observes that the argument works for any such ray. That generalization is proved here: if `q` has temperate growth and $`q\geq c` for some $`c>0`, so does $`q^a`, for every real `a`.
:::

What the generalization buys is the freedom to *choose* the inner function, which is what a multiplier with a singularity at the origin needs: $`\|x\|^a` is not of temperate growth — for `a` non-even it is not smooth at the origin, and for `a` negative not even bounded there — but outside a ball it agrees with $`q^{a/2}` for a `q` that is $`\|x\|^2` corrected by a bump, and that is temperate by the statement here. The correction goes *inside* the ball, where the multiplier is not needed, rather than on the multiplier itself.

The estimate is separated out as the first declaration, and it is the only analytic content: the `n`-th derivative of $`u^a` is a descending Pochhammer factor times $`u^{a-n}`, which on a ray $`u>b>0` is bounded by a fixed power of $`1+u` when $`a-n\geq0` and by a constant when $`a-n<0`.
