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

#doc (Manual) "L1 theory: ridgelet transforms with unbounded activations" =>
%%%
file := "overview-l1"
%%%

This chapter maps the L1 theory of Sonoda--Murata, *Neural network with unbounded activation
functions is universal approximator* (arXiv:1505.03654v2), onto the declarations in
`LeanRidgelet.OverviewL1`. It corresponds to plan milestone M7. The chapter follows the
publication order of the article: the weak ridgelet transform with respect to distributions, the
admissibility condition, the reconstruction formulas, the $`L^2` extension, and the universality
of neural networks with unbounded activation functions such as the ReLU.

The present pass is stated at function level. The parameter space is realized in Euclidean
coordinates $`(\boldsymbol{a},b)\in\mathbb R^m\times\mathbb R`; the polar coordinates
$`(\boldsymbol{u},\alpha,\beta)` of the article enter through the Radon transform. The
distributional Fourier transform of an activation $`\eta` is carried by a function
$`F_\eta` that represents $`\widehat\eta` away from the origin, so that point masses at the
origin — the polynomial part of $`\eta`, i.e. the kernel of the Lizorkin quotient
$`\mathcal S'(\mathbb R)/\mathcal P\cong\mathcal S_0'(\mathbb R)` — are invisible. The Lizorkin
spaces as types, the distribution classes on the half-space, the remaining rows of the balancing
theorem, Dirac-delta activations, the sigmoid examples, and the fractional Laplacian identity
are deferred nodes without Lean links. The linked declarations state the intended function-level
API while proofs are developed in parallel; this chapter therefore distinguishes formalized
statements from deferred mathematical scope without reporting proof-completion status.

*Coordinates, transforms, and admissibility*

:::definition "l1_parameter_space" (lean := "LeanRidgelet.RidgeletParameterSpace, LeanRidgelet.ridgeletParameterMeasure, LeanRidgelet.paperFourier1D")
*Parameter space and reference measure.* The parameter space $`\mathbb Y^{m+1}=\mathbb R^m\times\mathbb R` carries the measure $`\|\boldsymbol{a}\|^{-2}\,d\boldsymbol{a}\,db`, the Euclidean expression of the article's fixed measure $`\alpha^{-m}\,d\alpha\,d\beta\,d\boldsymbol{u}`. The one-dimensional article Fourier convention $`\widehat\psi(\zeta)=\int\psi(z)e^{-iz\zeta}\,dz` is the `V = ℝ` case of the shared convention module.
:::

:::definition "l1_ridgelet_transforms" (lean := "LeanRidgelet.euclideanRidgeletTransform, LeanRidgelet.euclideanDualRidgeletTransform, LeanRidgelet.truncatedDualRidgeletTransform, LeanRidgelet.ridgeletTruncationFilter") (uses := "l1_parameter_space")
*Ridgelet and dual ridgelet transforms.* With homogeneity index $`s` (the article fixes $`s=1` from Section 4 on),
$$`\mathscr R_\psi f(\boldsymbol{a},b)=\int f(\boldsymbol{x})\overline{\psi(\boldsymbol{a}\cdot\boldsymbol{x}-b)}\,\|\boldsymbol{a}\|^s\,d\boldsymbol{x},\qquad \mathscr R^\dagger_\eta T(\boldsymbol{x})=\int T(\boldsymbol{a},b)\,\eta(\boldsymbol{a}\cdot\boldsymbol{x}-b)\,\|\boldsymbol{a}\|^{-s}\,d\boldsymbol{a}\,db.`
The truncated dual transform integrates over the annulus $`\varepsilon\le\|\boldsymbol{a}\|\le\delta`, and the reconstruction limit is taken along the product filter $`\varepsilon\to0^+`, $`\delta\to\infty`.
:::

:::definition "l1_radon_backprojection" (lean := "LeanRidgelet.radonTransform, LeanRidgelet.dualRadonTransform, LeanRidgelet.pvHilbertTransform, LeanRidgelet.backprojectionFilter, LeanRidgelet.reflectedConjConvolution")
*Radon transform and backprojection filter.* The Radon transform integrates over hyperplanes, $`\mathscr Rf(\boldsymbol{u},p)=\int_{(\mathbb R\boldsymbol{u})^\perp}f(p\boldsymbol{u}+\boldsymbol{y})\,d\boldsymbol{y}`, and the dual Radon transform integrates over the unit sphere with the Haar-induced surface measure. The backprojection filter $`\Lambda^m` is $`\partial_p^m` for even $`m` and $`\mathscr H\partial_p^m` for odd $`m`. Lean defines the principal-value transform through the filter limit of truncated integrals; convergence is supplied by the hypotheses of the results that use it. The intended Fourier multiplier is $`i^m|\omega|^m`.
:::

:::definition "l1_weak_ridgelet" (lean := "LeanRidgelet.weakRidgeletTransform") (uses := "l1_radon_backprojection")
*Weak ridgelet transform.* For a locally integrable ridgelet function,
$$`\mathscr R_\psi f(\boldsymbol{u},\alpha,\beta)=\int_{\mathbb R}\mathscr Rf(\boldsymbol{u},\alpha z+\beta)\,\overline{\psi(z)}\,dz.`
The article's Definition 4.1 reads the integral as the action of a distribution $`\psi\in\mathcal S'(\mathbb R)`; that reading is deferred with the distributional pass.
:::

:::definition "l1_fourier_away_from_origin" (lean := "LeanRidgelet.PolynomiallyBounded, LeanRidgelet.HasFourierAwayFromOrigin") (uses := "l1_parameter_space")
*Fourier data away from the origin.* A locally integrable, polynomially bounded activation $`\eta` has Fourier data $`F_\eta` away from the origin when $`\int F_\eta\varphi=\int\eta\widehat\varphi` for every Schwartz $`\varphi` supported away from $`0`. This realizes the Lizorkin quotient $`\mathcal S'(\mathbb R)/\mathcal P\cong\mathcal S_0'(\mathbb R)` at function level.
:::

:::definition "l1_admissibility" (lean := "LeanRidgelet.admissibilityConstant, LeanRidgelet.IsAdmissiblePair, LeanRidgelet.IsSelfAdmissible, LeanRidgelet.IsEquivalentPair, LeanRidgelet.IsAdmissiblyDecomposable") (uses := "l1_fourier_away_from_origin")
*Admissibility.* The pair $`(\psi,\eta)` with Fourier data $`F_\eta` is admissible when $`\psi` is integrable, the integrand of
$$`K_{\psi,\eta}=(2\pi)^{m-1}\int_{\mathbb R\setminus\{0\}}\frac{\overline{\widehat\psi(\zeta)}\,F_\eta(\zeta)}{|\zeta|^m}\,d\zeta`
is integrable on $`\mathbb R\setminus\{0\}`, and $`K_{\psi,\eta}\ne0`. Self-admissible, equivalent, and admissibly decomposable pairs are defined as in Section 5.3 of the article, with equivalence expressed on the Fourier side.
:::

:::definition "l1_standard_activations" (lean := "LeanRidgelet.truncatedPower, LeanRidgelet.truncatedPowerFourier, LeanRidgelet.gaussianWindow")
*Standard unbounded activations.* The truncated powers $`z_+^k` contain the step function ($`k=0`) and the ReLU ($`k=1`); their distributional Fourier transforms away from the origin are $`k!/(i\zeta)^{k+1}`. The Gaussian window generates the admissible ridgelet functions of Section 6.2.
:::

:::definition "l1_lizorkin_spaces"
*Lizorkin spaces (deferred).* The Lizorkin test space $`\mathcal S_0(\mathbb R)` of Schwartz functions with all moments vanishing and its dual $`\mathcal S_0'(\mathbb R)\cong\mathcal S'(\mathbb R)/\mathcal P`, together with the classes $`\mathcal S(\mathbb H)`, $`\mathcal S'(\mathbb H)`, $`\mathcal D'(\mathbb Y^{m+1})` on the open half-space, remain to be formalized as types for the distributional pass.
:::

*Well-definedness and duality*

:::theorem "l1_balancing_theorem" (lean := "LeanRidgelet.l1_ridgelet_pointwise_convergent_L1_bounded, LeanRidgelet.l1_weakRidgeletTransform_eq_euclidean, LeanRidgelet.l1_balancing_weakRidgeletTransform_memLp") (uses := "l1_weak_ridgelet, l1_ridgelet_transforms")
*Balancing theorem (`thm:existence`), formalized rows.* For $`f\in L^1(\mathbb R^m)` and a bounded continuous $`\psi`, the ridgelet integral converges absolutely at every parameter with $`\|\mathscr R_\psi f(\boldsymbol{a},b)\|\le\|f\|_1\|\psi\|_\infty\|\boldsymbol{a}\|^s`, and the weak (Radon) definition agrees with the strong Euclidean one at $`s=1`. For continuous $`\psi\in L^p(\mathbb R)`, the weak transform lies in $`L^p` in the shift $`\beta` for every direction and scale.
:::

:::theorem "l1_balancing_distributional_rows" (uses := "l1_lizorkin_spaces, l1_balancing_theorem")
*Balancing theorem, remaining rows (deferred).* The rows $`\mathcal D\times\mathcal D'`, $`\mathcal E'\times\mathcal D'`, $`\mathcal S\times\mathcal S'`, $`\mathcal O_C'\times\mathcal S'`, and $`\mathcal D_{L^1}'\times\mathcal D_{L^p}'` of the article's Table 3 require the distribution classes on $`\mathbb Y^{m+1}` and are part of the distributional pass.
:::

:::proposition "l1_continuity_L1_Linfty" (lean := "LeanRidgelet.l1_ridgeletTransform_bounded_L1_Linfty") (uses := "l1_balancing_theorem")
*Continuity `prop:conti.L1`.* For a Schwartz ridgelet function with vanishing moments, the ridgelet transform is bounded from $`L^1(\mathbb R^m)` to $`L^\infty(\mathbb Y^{m+1})`. The article's operator-norm constant $`\sup_{r,\beta}|r\psi(r\beta)|` diverges, so the Lean statement carries vanishing-moment hypotheses; a paper gap memo in the docstring records the remaining concern about integrable power singularities and candidate repairs.
:::

:::theorem "l1_dual_operator" (lean := "LeanRidgelet.l1_dualRidgeletTransform_pairing") (uses := "l1_ridgelet_transforms")
*Dual operator (`thm:dual`).* Under absolute integrability, the dual ridgelet transform is the dual of the ridgelet transform with respect to the pairing of $`L^2(\mathbb Y^{m+1},\|\boldsymbol{a}\|^{-2}d\boldsymbol{a}\,db)` and $`L^2(\mathbb R^m)`.
:::

*Admissible pairs*

:::proposition "l1_lizorkin_quotient_invariance" (lean := "LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial") (uses := "l1_fourier_away_from_origin")
*Polynomial invisibility.* Adding a polynomial to the activation does not change its Fourier data away from the origin, hence neither the admissibility constant: admissibility is a property of the Lizorkin class of $`\eta`.
:::

:::theorem "l1_structure_theorem" (lean := "LeanRidgelet.l1_structure_theorem_admissible_pairs") (uses := "l1_admissibility, l1_radon_backprojection")
*Structure theorem for admissible pairs (`thm:eq.ac`).* With $`\widehat\eta` continuous near the origin apart from a point mass corresponding to a polynomial $`Q`, the pair $`(\psi,\eta)` is admissible iff the backprojection equation
$$`\Lambda^m u=\overline{\widetilde\psi}*(\eta-Q)`
has a slowly increasing solution $`u` whose Fourier data away from the origin is integrable with nonzero integral.
:::

:::corollary "l1_construction_admissible" (lean := "LeanRidgelet.l1_construction_of_admissible_pairs") (uses := "l1_structure_theorem")
*Construction of admissible pairs (`cor:const.ap`).* If $`\zeta^k\widehat\eta(\zeta)` extends continuously through the origin and $`\psi_0\in\mathcal S(\mathbb R)` satisfies $`\int\zeta^k\overline{\widehat{\psi_0}}F_\eta\ne0`, then $`\psi=\Lambda^m\psi_0^{(k)}` is admissible with $`\eta`. For odd $`m` the constructed $`\psi` leaves the Schwartz class (paper gap memo), which is why admissibility only requires integrability of $`\psi`.
:::

*Reconstruction formulas*

:::theorem "l1_reconstruction" (lean := "LeanRidgelet.l1_reconstruction_formula") (uses := "l1_admissibility, l1_ridgelet_transforms")
*Reconstruction formula (`thm:formula`).* For $`f\in L^1` with $`\widehat f\in L^1` and an admissible pair,
$$`\mathscr R^\dagger_\eta\mathscr R_\psi f=K_{\psi,\eta}\,f`
in the truncation limit, at almost every point and at every continuity point of $`f`.
:::

:::theorem "l1_reconstruction_radon" (lean := "LeanRidgelet.l1_reconstruction_formula_radon") (uses := "l1_reconstruction, l1_radon_backprojection")
*Reconstruction via the Radon transform (`thm:formula.radon`).* Under the normalized real-domain admissibility condition $`\Lambda^m u=\overline{\widetilde\psi}*\eta`, $`\int\widehat u=-1`, the reconstruction operator is the filtered backprojection: $`\mathscr R^\dagger_\eta\mathscr R_\psi f=\mathscr R^\dagger\Lambda^{m-1}\mathscr Rf=2(2\pi)^{m-1}f`. The fractional Laplacian identity `cor:radon.d` is deferred.
:::

*Extension to $`L^2` and compatibility*

:::theorem "l1_parseval_plancherel" (lean := "LeanRidgelet.l1_parseval_relation, LeanRidgelet.l1_plancherel_identity") (uses := "l1_reconstruction")
*Parseval and Plancherel (`thm:parseval`).* For an admissible pair normalized by $`K_{\psi,\eta}=1` and $`f,g\in L^1\cap L^2(\mathbb R^m)`, $`\langle\mathscr R_\psi f,\mathscr R_\eta g\rangle=\langle f,g\rangle`; for a self-admissible $`\psi`, $`\|\mathscr R_\psi f\|_2=\|f\|_2`.
:::

:::theorem "l1_L2_extension" (lean := "LeanRidgelet.l1_ridgeletTransform_L2_extension") (uses := "l1_parseval_plancherel")
*Bounded extension to `L²` (`thm:L2`).* For a self-admissible $`\psi` with $`K_{\psi,\psi}=1`, the ridgelet transform on $`L^1\cap L^2(\mathbb R^m)` admits a unique bounded extension to $`L^2(\mathbb R^m)`, and the extension is an isometry into $`L^2(\mathbb Y^{m+1})`.
:::

:::theorem "l1_reconstruction_L2" (lean := "LeanRidgelet.l1_reconstruction_formula_L2") (uses := "l1_L2_extension, l1_parseval_plancherel")
*Reconstruction in `L²` (`thm:formula.L2`).* For an admissibly decomposable pair with $`K_{\psi,\eta}=1` and $`f\in L^1\cap L^2(\mathbb R^m)`, the truncated reconstruction converges to $`f` in $`L^2`. This is the compatibility statement between the L1 and L2 reconstructions on $`L^1\cap L^2`.
:::

*Unbounded activation functions*

:::proposition "l1_truncated_power_fourier" (lean := "LeanRidgelet.l1_truncatedPower_hasFourierAwayFromOrigin") (uses := "l1_standard_activations, l1_fourier_away_from_origin")
*Truncated powers as Lizorkin distributions.* By the Gel'fand--Shilov formula $`\widehat{z_+^k}=k!/(i\zeta)^{k+1}+\pi i^k\delta^{(k)}`, the truncated power $`z_+^k` has Fourier data $`k!/(i\zeta)^{k+1}` away from the origin.
:::

:::proposition "l1_truncated_power_admissible" (lean := "LeanRidgelet.l1_truncatedPower_admissible") (uses := "l1_truncated_power_fourier, l1_construction_admissible")
*Admissibility of truncated powers.* The truncated power $`z_+^k` is admissible with the Gaussian-derivative ridgelet function $`\psi=\Lambda^mG^{(\ell+k+1)}` for every even $`\ell`. The Dirac-delta and sigmoid examples of Section 6 are deferred with the distributional pass.
:::

:::theorem "l1_relu_universality" (lean := "LeanRidgelet.l1_relu_network_universal_approximation") (uses := "l1_truncated_power_admissible, l1_reconstruction")
*Universal approximation with ReLU networks.* For every $`f\in L^1(\mathbb R^m)` with $`\widehat f\in L^1(\mathbb R^m)` there are an integrable ridgelet function $`\psi` and a nonzero constant $`K` such that the continuous ReLU network with coefficient $`\mathscr R_\psi f` reconstructs $`Kf` in the truncation limit.
:::
