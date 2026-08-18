import LeanRidgelet.OverviewL1
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

#doc (Manual) "L1 theory: arXiv:1505.03654v2 implementation map" =>
%%%
file := "overview-l1"
%%%

This chapter lists the definitions and the main results of Sonoda--Murata, *Neural network with
unbounded activation functions is universal approximator* (arXiv:1505.03654v2), in the
publication order of the article, each linked to the Lean declaration that carries it. It is the
place to check *what* is formalized; the machinery behind the proofs is the following chapter,
organized by Lean dependency. It corresponds to plan milestone M7.

The pass is at function level. The parameter space is realized in Euclidean coordinates
$`(\boldsymbol{a},b)\in\mathbb R^m\times\mathbb R`; the polar coordinates
$`(\boldsymbol{u},\alpha,\beta)` of the article enter through the Radon transform. The ridgelet
function is integrable rather than Schwartz, and the distributional Fourier transform of an
activation $`\eta` is carried by a function $`F_\eta` representing $`\widehat\eta` away from the
origin, so that point masses at the origin — the polynomial part of $`\eta`, i.e. the kernel of
the Lizorkin quotient $`\mathcal S'(\mathbb R)/\mathcal P\cong\mathcal S_0'(\mathbb R)` — are
invisible.

Wherever the formalized statement differs from the article, the node says so in one sentence and
the reason is recorded in the docstring of the declaration and in the module docstring of the
file holding it, under the heading *Deviations from the article*. A node without a Lean link
records deferred mathematical scope and creates no Lean assumption. **Every linked declaration
is proved: the L1 development contains no `sorry`.**

*Section 2--3: coordinates, transforms, and the Lizorkin quotient*

:::definition "l1_parameter_space" (lean := "LeanRidgelet.RidgeletParameterSpace, LeanRidgelet.ridgeletParameterMeasure, LeanRidgelet.angularFourier1D, LeanRidgelet.angularFourier1D_eq_mathlib")
*Parameter space and reference measure.* The parameter space $`\mathbb Y^{m+1}=\mathbb R^m\times\mathbb R` carries the measure $`\|\boldsymbol{a}\|^{-2}\,d\boldsymbol{a}\,db`, the Euclidean expression of the article's fixed measure $`\alpha^{-m}\,d\alpha\,d\beta\,d\boldsymbol{u}` under $`\boldsymbol{a}=\boldsymbol{u}/\alpha`, $`b=\beta/\alpha`. The one-dimensional article Fourier convention $`\widehat\psi(\zeta)=\int\psi(z)e^{-iz\zeta}\,dz` is the $`V=\mathbb R` case of the shared convention module, with the rescaling bridge $`\widehat g(\zeta)=\mathcal Fg(\zeta/2\pi)` to Mathlib's transform.
:::

:::definition "l1_ridgelet_transforms" (lean := "LeanRidgelet.euclideanRidgeletTransform, LeanRidgelet.euclideanDualRidgeletTransform, LeanRidgelet.truncatedDualRidgeletTransform, LeanRidgelet.ridgeletTruncationFilter") (uses := "l1_parameter_space")
*Ridgelet and dual ridgelet transforms (`eq:eucrid`).* With homogeneity index $`s` (the article fixes $`s=1` from Section 4 on),
$$`\mathscr R_\psi f(\boldsymbol{a},b)=\int f(\boldsymbol{x})\overline{\psi(\boldsymbol{a}\cdot\boldsymbol{x}-b)}\,\|\boldsymbol{a}\|^s\,d\boldsymbol{x},\qquad \mathscr R^\dagger_\eta T(\boldsymbol{x})=\int T(\boldsymbol{a},b)\,\eta(\boldsymbol{a}\cdot\boldsymbol{x}-b)\,\|\boldsymbol{a}\|^{-s}\,d\boldsymbol{a}\,db.`
The truncated dual transform integrates over the annulus $`\varepsilon\le\|\boldsymbol{a}\|\le\delta`, and the reconstruction limit is taken along the product filter $`\varepsilon\to0^+`, $`\delta\to\infty`. Scoped Lean notation: `𝓡[s; ψ]`, `𝓡†[s; η]`.
:::

:::definition "l1_weak_ridgelet" (lean := "LeanRidgelet.weakRidgeletTransform") (uses := "l1_ridgelet_transforms, mathlib_radon_transform")
*Weak ridgelet transform (Definition 4.1).* For a locally integrable ridgelet function,
$$`\mathscr R_\psi f(\boldsymbol{u},\alpha,\beta)=\int_{\mathbb R}\mathscr Rf(\boldsymbol{u},\alpha z+\beta)\,\overline{\psi(z)}\,dz.`
*Deviation.* The article reads the integral as the action of a distribution $`\psi\in\mathcal S'(\mathbb R)`; that reading is deferred with the distributional pass.
:::

:::definition "l1_radon_backprojection" (lean := "MeasureTheory.pvHilbertTransform, LeanRidgelet.lambdaOperatorPow, LeanRidgelet.reflectedConjConvolution") (uses := "mathlib_radon_transform, mathlib_hilbert_symbol")
*The filter of filtered backprojection (`eq:bp`).* Formalized as the $`m`-th power of the standard *Lambda operator* $`\Lambda=\sqrt{-d^2/dz^2}` (in tomography also the fractional Laplacian or the Calderón operator; Natterer's Riesz potential $`I^{-m}`; the ramp filter $`|\omega|` for $`m=1`): $`\Lambda^m=(-1)^{\lfloor m/2\rfloor}\partial_z^m` for even $`m` and $`(-1)^{\lfloor m/2\rfloor}\mathscr H\partial_z^m` for odd $`m`, with intended Fourier multiplier $`|\omega|^m`. Scoped Lean notation: `Λ^m`. *Deviation.* This corrects the article, whose filter `eq:bp` ($`\partial_p^m` / $`H\partial_p^m` with $`H=i\mathscr H`) equals $`i^m\Lambda^m` and carries the spurious phase $`i^m`; see the docstring of `lambdaOperatorPow`. The affected statements (`thm:eq.ac`, `cor:const.ap`, `thm:formula.radon`, Section 6.2) are equivalent up to a nonzero scalar, except that the sign of the inversion formula is fixed.
:::

:::definition "l1_fourier_away_from_origin" (lean := "MeasureTheory.PolynomiallyBounded, LeanRidgelet.HasFourierAwayFromOrigin") (uses := "l1_parameter_space, mathlib_lizorkin_space")
*Fourier data away from the origin (Section 2.3, function-level form).* A locally integrable, polynomially bounded activation $`\eta` has Fourier data $`F_\eta` away from the origin when $`\int F_\eta\varphi=\int\eta\widehat\varphi` for every Schwartz $`\varphi` supported away from $`0`. *Deviation.* The article takes $`\eta\in\mathcal S_0'(\mathbb R)`; this predicate is the function-level realization of the same quotient, and is exactly the pairing a Lizorkin distribution sees. The Lizorkin space itself is available as a type in the upstream-candidates chapter (`mathlib_lizorkin_space`).
:::

:::definition "l1_admissibility" (lean := "LeanRidgelet.admissibilityConstant, LeanRidgelet.IsAdmissiblePair, LeanRidgelet.IsSelfAdmissible, LeanRidgelet.IsEquivalentPair, LeanRidgelet.IsAdmissiblyDecomposable") (uses := "l1_fourier_away_from_origin")
*Admissibility (`eq:defK`, Section 5.3).* The pair $`(\psi,\eta)` with Fourier data $`F_\eta` is admissible when $`\psi` is integrable, the integrand of
$$`K_{\psi,\eta}=(2\pi)^{m-1}\int_{\mathbb R\setminus\{0\}}\frac{\overline{\widehat\psi(\zeta)}\,F_\eta(\zeta)}{|\zeta|^m}\,d\zeta`
is integrable on $`\mathbb R\setminus\{0\}`, and $`K_{\psi,\eta}\ne0`. Self-admissible, equivalent, and admissibly decomposable pairs are as in Section 5.3, with equivalence expressed on the Fourier side. Scoped Lean notation: `K[m; ψ, Fη]`. The article motivates excising the origin with its Examples 5.2 and 5.3; see `l1_admissibility_examples`.
:::

:::proposition "l1_admissibility_examples" (lean := "LeanRidgelet.l1_hasFourierAwayFromOrigin_polynomial, LeanRidgelet.l1_polynomial_not_isAdmissiblePair, LeanRidgelet.l1_step_not_isAdmissiblePair_lambdaOperatorPow") (uses := "l1_admissibility, l1_lizorkin_quotient_invariance, l1_construction_admissible, l1_truncated_power_fourier")
*Examples 5.2 and 5.3: where admissibility fails.* The article exhibits two pairs for which the naive product $`\overline{\widehat\psi}\,\widehat\eta\,|\zeta|^{-m}` of tempered distributions is not associative, the two groupings of $`\mathrm{p.v.}(1/|\zeta|)\times|\zeta|G(\zeta)\times\delta(\zeta)` differing by $`G(0)`, and uses them to motivate excising the origin in `eq:defK`. At function level no such ambiguity can arise: $`F_\eta` is a function on $`\mathbb R\setminus\{0\}` and the admissibility density is a pointwise product of complex numbers. What survives is the verdict, and it agrees with the article's. **Example 5.2** ($`\eta(z)=z`, $`\psi=\Lambda G`): a polynomial activation is never admissible, since its Fourier data away from the origin vanishes (second declaration, from the first) and hence $`K_{\psi,\eta}=0` for every $`\psi`. This is why activations are taken in $`\mathcal S'(\mathbb R)/\mathcal P\cong\mathcal S_0'(\mathbb R)`. **Example 5.3** ($`\eta(z)=z_+^0+(2\pi)^{-1}e^{iz}`, $`\psi=\Lambda G`): removing the origin is not by itself enough. The unit step is inadmissible with any filtered ridgelet function $`\Lambda^m\varphi` whose window satisfies $`\widehat\varphi(0)\ne0`, because by `l1_construction_admissible` the density is $`\overline{\widehat\varphi(\zeta)}/(i\zeta)`, which is not absolutely integrable at the origin (third declaration). The second summand of the article's $`\eta` puts a point mass of $`\widehat\eta` away from the origin and lies outside the function-level framework, but it is not the source of the divergence.
:::

:::definition "l1_standard_activations" (lean := "LeanRidgelet.truncatedPower, LeanRidgelet.truncatedPowerFourier, LeanRidgelet.gaussianWindow")
*Standard unbounded activations (Section 6).* The truncated powers $`z_+^k` contain the step function ($`k=0`) and the ReLU ($`k=1`); their distributional Fourier transforms away from the origin are $`k!/(i\zeta)^{k+1}`. The Gaussian window generates the admissible ridgelet functions of Section 6.2. *Deviation.* `truncatedPower` is defined by cases rather than as $`(\max(z,0))^k`, which would be the constant $`1` at $`k=0` instead of the unit step.
:::

:::definition "l1_lizorkin_spaces"
*Distribution classes on the half-space (deferred).* The classes $`\mathcal S(\mathbb H)`, $`\mathcal S'(\mathbb H)` and $`\mathcal D'(\mathbb Y^{m+1})` on the open half-space, needed to state the transforms as distribution actions, remain to be formalized as types for the distributional pass.
:::

*Section 4: well-definedness and duality*

:::theorem "l1_balancing_theorem" (lean := "LeanRidgelet.l1_ridgelet_pointwise_convergent_L1_bounded, LeanRidgelet.l1_weakRidgeletTransform_eq_euclidean, LeanRidgelet.l1_balancing_weakRidgeletTransform_memLp") (uses := "l1_weak_ridgelet, l1_ridgelet_transforms, mathlib_radon_l1_theory, mathlib_young_convolution, l1_fourier_slice_angular")
*Balancing theorem (`thm:existence`), formalized rows.* For $`f\in L^1(\mathbb R^m)` and a bounded continuous $`\psi`, the ridgelet integral converges absolutely at every parameter with $`\|\mathscr R_\psi f(\boldsymbol{a},b)\|\le\|f\|_1\|\psi\|_\infty\|\boldsymbol{a}\|^s`, and the weak (Radon) definition agrees with the strong Euclidean one at $`s=1`. For continuous $`\psi\in L^p(\mathbb R)`, the weak transform lies in $`L^p` in the shift $`\beta`, for every direction and scale. *Deviation.* The $`L^p` row adds $`1\le p`, implicit in the article's use of $`L^p` as a Banach space; the conclusion holds for every direction, not almost every.
:::

:::theorem "l1_balancing_distributional_rows" (uses := "l1_lizorkin_spaces, l1_balancing_theorem")
*Balancing theorem, remaining rows (deferred).* The rows $`\mathcal D\times\mathcal D'`, $`\mathcal E'\times\mathcal D'`, $`\mathcal S\times\mathcal S'`, $`\mathcal O_C'\times\mathcal S'`, and $`\mathcal D_{L^1}'\times\mathcal D_{L^p}'` of the article's Table 3 require the distribution classes on $`\mathbb Y^{m+1}`.
:::

:::proposition "l1_continuity_L1_Linfty" (lean := "LeanRidgelet.norm_euclideanRidgeletTransform_zero_le, LeanRidgelet.l1_ridgeletTransform_bounded_L1_Linfty") (uses := "l1_balancing_theorem")
*Continuity (`prop:conti.L1`).* For a Schwartz ridgelet function the ridgelet transform is bounded from $`L^1(\mathbb R^m)` to $`L^\infty(\mathbb Y^{m+1})`; the bound holds at every parameter point, with the explicit constant $`\|\psi\|_\infty` (the Schwartz seminorm $`(0,0)`) in the first declaration and the existential operator-norm form of the article in the second. *Deviation (author decision 2026-07-22).* The article states the proposition at $`s=1`, where its constant $`\sup_{r,\beta}|r\psi(r\beta)|` diverges and the statement is false even with vanishing-moment hypotheses; it is read here in the $`s=0` normalization (Murata's Euclidean normalization, the remark after `eq:eucrid`), and wherever boundedness matters the theory may be read at $`s=0` throughout, with $`d\boldsymbol{a}\,db` replacing $`\|\boldsymbol{a}\|^{-2}d\boldsymbol{a}\,db`. The counterexample is in the docstring.
:::

:::theorem "l1_dual_operator" (lean := "LeanRidgelet.l1_dualRidgeletTransform_pairing") (uses := "l1_ridgelet_transforms")
*Dual operator (`thm:dual`).* Under absolute integrability, the dual ridgelet transform is the dual of the ridgelet transform with respect to the pairing of $`L^2(\mathbb Y^{m+1},\|\boldsymbol{a}\|^{-2}d\boldsymbol{a}\,db)` and $`L^2(\mathbb R^m)`.
:::

*Section 5: admissible pairs and reconstruction*

:::proposition "l1_lizorkin_quotient_invariance" (lean := "LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial") (uses := "l1_fourier_away_from_origin, l1_lizorkin_moment_vanishing")
*Polynomial invisibility.* Adding a polynomial to the activation changes neither its Fourier data away from the origin nor the admissibility constant: admissibility is a property of the Lizorkin class of $`\eta`.
:::

:::theorem "l1_structure_theorem" (lean := "LeanRidgelet.l1_structure_theorem_admissible_pairs, LeanRidgelet.admissibilityConstant_of_backprojection, LeanRidgelet.l1_structure_theorem_sufficiency, LeanRidgelet.l1_structure_theorem_sufficiency_physical") (uses := "l1_admissibility, l1_radon_backprojection, l1_lambda_multiplier, l1_fourier_data_convolution, l1_lizorkin_quotient_invariance")
*Structure theorem for admissible pairs (`thm:eq.ac`).* The article characterizes admissibility of $`(\psi,\eta)` by the solvability of the backprojection equation $`\Lambda^mu=\overline{\widetilde\psi}\ast(\eta-Q)` with $`\int\widehat u\ne0`. *Proved* (first declaration), with the equation imposed on the Fourier data of both sides. Sufficiency is `l1_fourier_data_convolution` together with the admissibility constant $`K_{\psi,\eta}=(2\pi)^{m-1}\int\widehat u` (second declaration, an identity needing no integrability hypothesis); necessity takes $`\widehat u:=\overline{\widehat\psi}F_\eta|\zeta|^{-m}`, integrable by admissibility, and realizes it as the Fourier data of the bounded continuous function $`u=(2\pi)^{-1}\mathcal F^{-1}\widehat u`. The polynomial $`Q` is invisible by `l1_lizorkin_quotient_invariance`. Where the equation is a pointwise identity — a Schwartz solution $`u`, in spectral or in the article's physical form — the third and fourth declarations state it directly. *Deviations.* The article writes the equation pointwise for $`u\in\mathcal O_M`, with $`\Lambda^m` read as the Fourier multiplier $`|\zeta|^m`; that is the only available reading, since for a slowly increasing $`u` the pointwise principal value generally diverges and, when it converges, only agrees modulo polynomials. The formalized statement therefore imposes the equation on Fourier data, weakens $`u\in\mathcal O_M` to "$`u` carries the Fourier data $`\widehat u`", and drops the continuity hypothesis on $`\widehat\eta` near the origin. The manuscript's theorem itself needs no correction.
:::

:::corollary "l1_construction_admissible" (lean := "LeanRidgelet.l1_isAdmissiblePair_lambdaOperatorPow, LeanRidgelet.l1_construction_of_admissible_pairs, LeanRidgelet.angularFourier1D_iteratedDeriv") (uses := "l1_admissibility, l1_lambda_multiplier")
*Construction of admissible pairs (`cor:const.ap`), sharpened to a criterion.* For a Schwartz $`\varphi`, the pair $`(\Lambda^m\varphi,\eta)` is admissible **if and only if** $`\overline{\widehat\varphi}F_\eta` is integrable away from the origin with nonzero integral (first declaration): the factor $`|\zeta|^m` of $`\widehat{\Lambda^m\varphi}` cancels the factor $`|\zeta|^{-m}` of the admissibility density exactly, which is the whole mechanism of the construction. The article's statement — $`\psi=\Lambda^m\psi_0^{(k)}` is admissible with $`\eta` when $`\int\zeta^k\overline{\widehat{\psi_0}}F_\eta\ne0` — is the case $`\varphi=\psi_0^{(k)}` (second declaration), through the iterated angular derivative rule $`\widehat{\varphi^{(k)}}=(i\zeta)^k\widehat\varphi` (third). The structure theorem is not used. Integrability of the constructed ridgelet function is not a hypothesis: `l1_lambda_multiplier` supplies it for every $`m\ge1`. *Deviations.* For odd $`m` the constructed $`\psi` leaves the Schwartz class, which is why admissibility only requires integrability of $`\psi`. The article's continuity hypothesis on $`\zeta^k\widehat\eta` near the origin is dropped, the explicit integrability of the admissibility density replacing it.
:::

:::theorem "l1_reconstruction" (lean := "LeanRidgelet.l1_reconstruction_formula") (uses := "l1_admissibility, l1_ridgelet_transforms, l1_truncation_limit, l1_pairing_extension")
*Reconstruction formula (`thm:formula`).* For an admissible pair whose activation has polynomial growth of degree $`k`, a ridgelet function with finite $`k`-th moment and $`k` vanishing moments, and $`f\in L^1` with finite $`k`-th moment and $`\widehat f\in L^1`,
$$`\mathscr R^\dagger_\eta\mathscr R_\psi f=K_{\psi,\eta}\,f`
in the truncation limit, at almost every point and at every continuity point of $`f`. *Deviation (author decision 2026-07-22).* The article states the theorem for $`(\psi,\eta)\in\mathcal S(\mathbb R)\times\mathcal S_0'(\mathbb R)` with a distributional pairing. At function level the growth/moment matching is necessary for absolute convergence — for growth degree $`k\ge1` there are $`f\in L^1` with $`\widehat f\in L^1` whose reconstruction integrand is not Bochner integrable — and the vanishing moments (the article's own remark after `thm:eq.ac`) hide the polynomial part of $`\eta`. All three added hypotheses are vacuous in the deferred distributional pass.
:::

:::theorem "l1_reconstruction_radon" (lean := "LeanRidgelet.l1_reconstruction_formula_radon, LeanRidgelet.l1_radon_filtered_backprojection") (uses := "l1_reconstruction, l1_radon_backprojection, l1_lambda_multiplier, mathlib_polar_coordinates, mathlib_radon_schwartz_section")
*Reconstruction via the Radon transform (`thm:formula.radon`).* Under the backprojection admissibility `eq:radon.ac` in spectral form — $`\overline{\widehat\psi(\zeta)}F_\eta(\zeta)=|\zeta|^m\widehat u(\zeta)` on $`\zeta\ne0` with $`\widehat u\in L^1` — the truncated ridgelet reconstruction of a Schwartz function converges at every point to $`2(2\pi)^{m-1}f(x)`, the value of the filtered backprojection $`\mathscr R^\dagger\Lambda^{m-1}\mathscr Rf` (second declaration, Radon's classical inversion formula, proved). *Deviations.* The filter is the standard $`\Lambda^{m-1}` (see `l1_radon_backprojection`), and the normalization of `eq:radon.ac` is $`\int\widehat u=2`, not the article's $`\int\widehat u=-1`: the truncation limit is $`(2\pi)^{m-1}\int\widehat u\cdot f(x)`, and the article's own approximate-identity kernel $`k(z)=\mathscr Hu(z)/z` has $`\int k=\int\widehat u/2`, so both routes force $`\int\widehat u=2`. At function level the radon route also needs vanishing moments of $`\psi`, for the same Lizorkin-quotient reason as `thm:formula`. The fractional Laplacian identity `cor:radon.d` is deferred.
:::

:::corollary "l1_fractional_laplacian_intertwining" (uses := "l1_reconstruction_radon, l1_lizorkin_spaces")
*Intertwining with the fractional Laplacian (`cor:radon.d`, deferred).* The article's Corollary 5.8 reads
$$`\mathscr R^\dagger_\eta\mathscr R_\psi=\mathscr R^*\Lambda^{m-1}\mathscr R=(-\Delta)^{(m-1)/2}\mathscr R^*\mathscr R=\mathscr R^*\mathscr R(-\Delta)^{(m-1)/2}.`
The first equality is the content of `l1_reconstruction_radon`; the remaining two identify the filtered backprojection with a fractional power of the Laplacian on $`\mathbb R^m` and require the fractional Laplacian as an operator on tempered distributions, which is part of the deferred distributional pass.
:::

*Section 5.3--5.4: extension to $`L^2`*

:::theorem "l1_parseval_plancherel" (lean := "LeanRidgelet.l1_plancherel_identity, LeanRidgelet.l1_parseval_relation") (uses := "l1_admissibility, l1_fourier_expression, l1_plancherel_lintegral, mathlib_fourier_plancherel, abstract_reconstruction, relu_operator_theory")
*Parseval and Plancherel (`thm:parseval`).* For a self-admissible $`\psi` with $`K_{\psi,\psi}=1` and $`f\in L^1\cap L^2(\mathbb R^m)`, $`\|\mathscr R_\psi f\|_2=\|f\|_2`; for normalized self-admissible $`\psi`, $`\eta` with cross normalization $`K_{\psi,\eta}=1`, $`\langle\mathscr R_\psi f,\mathscr R_\eta g\rangle=\langle f,g\rangle`. Both are proved by a direct Fourier computation that does not pass through the reconstruction formula. *Standing hypotheses.* Both members are integrable (through self-admissibility), continuous and bounded, so at function level the `L²` layer speaks about a pair of *ridgelet functions*, not about an unbounded activation: the ReLU, the truncated powers, the unit step, the sigmoid and Dirac's $`\delta` all fall outside it. The article has no such restriction because it pairs in $`\mathcal S\times\mathcal S_0'`. The restriction is an artefact of the function-level Euclidean formulation, not a gap in the project: since a tempered distribution lies in a weighted Sobolev space, an unbounded activation enters the companion L2 theory through its coordinate in $`\mathcal A_{s,t}` — the ReLU as `LeanRidgelet.reluActivation` for $`t>3/2` — where the corresponding statements are *proved*, and in the sharper form of an exact operator identity rather than a truncation limit: `abstract_reconstruction` gives $`SS^*=c_LI` and $`\|S^*f\|^2=c_L\|f\|^2`, and `relu_operator_theory` the reconstruction. Connecting the two formulations is plan item M7 (R4). Universality with an unbounded activation is in any case reached here through the $`L^1` route (`l1_relu_universality`). *Deviation.* The article asserts the relation for $`(\psi,\eta)\in\mathcal S\times\mathcal S_0'`, "immediate by duality"; at function level the parameter-space pairing must converge absolutely, which requires both transforms in $`L^2(\mathbb Y^{m+1})`, so self-admissibility of both members with the diagonal normalizations $`K_{\psi,\psi}=K_{\eta,\eta}=1` is taken as a hypothesis.
:::

:::theorem "l1_L2_extension" (lean := "LeanRidgelet.l1_ridgeletTransform_L2_extension") (uses := "l1_parseval_plancherel, l1_plancherel_lintegral, mathlib_lp_integrable_dense")
*Bounded extension to `L²` (`thm:L2`).* For a self-admissible $`\psi` with $`K_{\psi,\psi}=1`, the ridgelet transform on $`L^1\cap L^2(\mathbb R^m)` admits a unique bounded extension to $`L^2(\mathbb R^m)`, and the extension is an isometry into $`L^2(\mathbb Y^{m+1})`.
:::

:::theorem "l1_reconstruction_L2" (lean := "LeanRidgelet.l1_reconstruction_formula_L2") (uses := "l1_L2_extension, l1_parseval_plancherel, l1_dual_operator, l1_l2_duality_steps")
*Reconstruction in `L²` (`thm:formula.L2`).* For normalized self-admissible $`\psi`, $`\eta` with cross normalization $`K_{\psi,\eta}=1` and $`f\in L^1\cap L^2(\mathbb R^m)`, the truncated reconstruction converges to $`f` in $`L^2(\mathbb R^m)` — the compatibility statement between the L1 and L2 reconstructions on $`L^1\cap L^2`. The general $`f\in L^2` case follows from `thm:L2`. *Standing hypotheses.* As in `l1_parseval_plancherel`, on which this rests, both $`\psi` and $`\eta` are integrable, continuous and bounded, so this Euclidean form of the `L²` reconstruction does not cover the unbounded activations of Section 6; those are covered by the L2 theory in weighted Sobolev coordinates (see `l1_parseval_plancherel`). *Deviation (author decision 2026-07-25).* The article assumes admissible decomposability and then opens its proof with "assume without loss of generality that $`(\psi,\psi)` and $`(\eta,\eta)` are self-admissible"; that reduction needs the equivalence-invariance of the composite $`\mathscr R^\dagger_\eta\mathscr R_\psi`, a distributional statement absent from the function-level development, so self-admissibility of both members is a hypothesis, exactly as in the amended Parseval relation the proof rests on.
:::

*Section 6: unbounded activation functions*

:::proposition "l1_truncated_power_fourier" (lean := "LeanRidgelet.l1_truncatedPower_hasFourierAwayFromOrigin") (uses := "l1_standard_activations, l1_fourier_away_from_origin, l1_gelfand_shilov_pairing")
*Truncated powers as Lizorkin distributions.* By the Gel'fand--Shilov formula $`\widehat{z_+^k}=k!/(i\zeta)^{k+1}+\pi i^k\delta^{(k)}`, the truncated power $`z_+^k` has Fourier data $`k!/(i\zeta)^{k+1}` away from the origin.
:::

:::proposition "l1_truncated_power_admissible" (lean := "LeanRidgelet.l1_truncatedPower_admissible_exists, LeanRidgelet.bumpRidgelet, LeanRidgelet.isAdmissiblePair_bumpRidgelet, LeanRidgelet.integral_pow_mul_bumpRidgelet, LeanRidgelet.bumpRidgeletSchwartz_mem_lizorkinSpace, LeanRidgelet.l1_truncatedPower_isAdmissiblePair_of_window, LeanRidgelet.angularFourier1D_gaussianWindow, LeanRidgelet.l1_truncatedPower_admissible") (uses := "l1_truncated_power_fourier, l1_construction_admissible, l1_bump_ridgelet_construction, mathlib_lizorkin_space, mathlib_gaussian_schwartz")
*Admissibility of truncated powers (Section 6.2).* For every dimension $`m` and degree $`k` there is an integrable ridgelet function, with weighted integrability and vanishing moments of every order, admissible against $`z_+^k` (first declaration). The article's construction is available for an arbitrary Schwartz window (sixth declaration): $`(\Lambda^mw^{(\ell+k+1)},z_+^k)` is admissible as soon as $`\int\zeta^\ell\overline{\widehat w(\zeta)}\,d\zeta\ne0`, because the factor $`|\zeta|^m` cancels the $`|\zeta|^{-m}` of the admissibility density and the factor $`(i\zeta)^{\ell+k+1}` cancels the pole $`k!/(i\zeta)^{k+1}` down to $`\zeta^\ell`. The article's own Gaussian witness $`\psi=\Lambda^mG^{(\ell+k+1)}` is the last declaration: its angular Fourier transform is $`\widehat G(\zeta)=\sqrt{2\pi}e^{-\zeta^2/2}>0` (Mathlib's Gaussian Fourier transform at $`b=1/2`, no frequency rescaling being needed in the article convention), so $`\int\zeta^\ell\overline{\widehat G}` is a positive integral exactly for even $`\ell`, and the integrability of the filtered function comes from `mathlib_hilbert_symbol` through `l1_lambda_multiplier`. The Gaussian is realized as a Schwartz function in `mathlib_gaussian_schwartz`. *Deviation.* The witness used for the universality corollary is not the article's but an *explicit* one: the inverse Fourier transform of a smooth bump supported in $`(5\pi/2,7\pi/2)`. Because its spectrum is compactly supported *away from the origin*, the admissibility integrand is a nonzero constant times a nonnegative continuous compactly supported density on the positive half-line, so integrability and $`K\ne0` come together, and all moments vanish — the witness is a Lizorkin test function. The Dirac-delta and sigmoid examples of Section 6 are deferred with the distributional pass.
:::

:::theorem "l1_relu_universality" (lean := "LeanRidgelet.l1_relu_network_universal_approximation") (uses := "l1_truncated_power_admissible, l1_reconstruction")
*Universal approximation with ReLU networks.* For every $`f\in L^1(\mathbb R^m)` with a finite first moment and $`\widehat f\in L^1(\mathbb R^m)` there are an integrable ridgelet function $`\psi` and a nonzero constant $`K` such that the continuous ReLU network with coefficient $`\mathscr R_\psi f` reconstructs $`Kf` in the truncation limit, almost everywhere. *Deviation.* The first-moment hypothesis is inherited from the amended reconstruction formula with the ReLU growth degree $`k=1`; it is vacuous in the deferred distributional pass.
:::

:::proposition "l1_activation_classes" (uses := "l1_fourier_away_from_origin, l1_standard_activations, l1_admissibility, mathlib_polynomial_growth")
*The activation zoo of Section 6 (partly deferred).* Section 6.1 classifies candidate activations: Proposition 6.1 (a locally integrable $`\eta` with $`|\eta|\lesssim(1+|z|)^k` is a tempered distribution) is available as the growth predicate of the upstream chapter combined with local integrability, and is what `l1_fourier_away_from_origin` assumes; Proposition 6.2 (the $`\mathcal O_M` criterion) corresponds to Mathlib's `Function.HasTemperateGrowth`. The class memberships themselves — Example 6.4 ($`\sigma,\sigma^{(-1)},\tanh\in\mathcal O_M`, $`\sigma^{(k)}\in\mathcal S`), Example 6.5 (the RBF and its derivatives are Schwartz) and Example 6.6 ($`\delta^{(k)}\in\mathcal S'`) — are not formalized. Of the admissibility examples of Section 6.2, only Example 6.7 is (`l1_truncated_power_admissible`), and only in the direction "$`\ell` even $`\Rightarrow` admissible": the article's converse $`K_{\psi,\eta}=0` for odd $`\ell`, and with it Table 5, is unformalized. Example 6.8 ($`\delta^{(k)}` with $`\Lambda^mG`) needs the distributional pass. Examples 6.9 ($`G^{(k)}`) and the $`k\ge1` half of 6.10 ($`\sigma^{(k)}`) are *function-level* statements blocked only by the article's witness $`\Lambda^mG`, i.e. by the same missing $`L^1` decay of the Hilbert transform that keeps `LeanRidgelet.l1_truncatedPower_admissible` unproved; the $`\sigma` and $`\sigma^{(-1)}` rows of 6.10 are slowly increasing rather than integrable and need the distributional pass as well.
:::
