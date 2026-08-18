/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Balancing
public import LeanRidgelet.L1.BumpRidgelet
public import LeanRidgelet.L1.Defs
public import LeanRidgelet.L1.FourierData
public import LeanRidgelet.L1.FourierExpression
public import LeanRidgelet.L1.LambdaOperator
public import LeanRidgelet.L1.Lizorkin
public import LeanRidgelet.L1.PairingExtension
public import LeanRidgelet.L1.Plancherel
public import LeanRidgelet.L1.Radon
public import LeanRidgelet.L1.Reconstruction
public import LeanRidgelet.L1.ReconstructionL2
public import LeanRidgelet.L1.ReconstructionSection
public import LeanRidgelet.L1.StructureTheorem
public import LeanRidgelet.L1.TruncatedLimit
public import LeanRidgelet.L1.TruncatedPower

/-!
# L1 theory overview: main results of `1505.03654v2`

Roadmap of the formalization of

> S. Sonoda and N. Murata, *Neural network with unbounded activation functions is universal
> approximator* (arXiv:1505.03654v2),

developed in `LeanRidgelet/L1/`. This module only re-exports those files; it is the entry point
that names the article's results and points at the declaration proving each. This is plan
milestone M7.

## The article's results and where they live

* `L1.Defs` — the coordinates, transforms, Lambda operator and admissibility of Sections 2--5.
* `L1.Lizorkin` — the Lizorkin quotient: `l1_hasFourierAwayFromOrigin_add_polynomial`.
* `L1.TruncatedPower` — Gel'fand--Shilov for `z₊^k`:
  `l1_truncatedPower_hasFourierAwayFromOrigin`.
* `L1.Balancing` — `thm:existence` (formalized rows)
  `l1_ridgelet_pointwise_convergent_L1_bounded`, `l1_weakRidgeletTransform_eq_euclidean`,
  `l1_balancing_weakRidgeletTransform_memLp`; `prop:conti.L1`
  `l1_ridgeletTransform_bounded_L1_Linfty`; `thm:dual` `l1_dualRidgeletTransform_pairing`.
* `L1.FourierExpression` — `eq:fstridge`: `angularFourier1D_euclideanRidgeletTransform`.
* `L1.PairingExtension`, `L1.ReconstructionSection`, `L1.Reconstruction` — steps T1--T6 and
  `thm:formula`: `l1_reconstruction_formula`.
* `L1.LambdaOperator` — the multiplier property `lambdaOperatorPow_eq_fourier_multiplier`.
* `L1.FourierData` — uniqueness of Fourier data away from the origin
  `hasFourierAwayFromOrigin_ae_eq` and the convolution theorem there
  `hasFourierAwayFromOrigin_reflectedConjConvolution`.
* `L1.StructureTheorem` — `thm:eq.ac` `l1_structure_theorem_admissible_pairs`,
  `l1_structure_theorem_sufficiency`, `l1_structure_theorem_sufficiency_physical`;
  `cor:const.ap` `l1_isAdmissiblePair_lambdaOperatorPow`,
  `l1_construction_of_admissible_pairs`; Examples 5.2 and 5.3
  `l1_polynomial_not_isAdmissiblePair`, `l1_step_not_isAdmissiblePair_lambdaOperatorPow`.
* `L1.Radon` — `thm:formula.radon` `l1_reconstruction_formula_radon` and Radon's inversion
  formula `l1_radon_filtered_backprojection`.
* `L1.Plancherel` — `thm:parseval` `l1_plancherel_identity`, `l1_parseval_relation`; `thm:L2`
  `l1_ridgeletTransform_L2_extension`.
* `L1.ReconstructionL2` — `thm:formula.L2`: `l1_reconstruction_formula_L2`.
* `L1.BumpRidgelet` — the Section 6.2 construction in general form
  `l1_truncatedPower_isAdmissiblePair_of_window`, the manuscript's Gaussian instance
  `l1_truncatedPower_admissible`, `l1_truncatedPower_admissible_exists` and ReLU universality
  `l1_relu_network_universal_approximation`.

**Every result of the article listed above is proved: the L1 development contains no `sorry`.**
The assumption audit (`audit/Assumptions.lean`) checks this mechanically.

## Coordinates and conventions

Euclidean parameter coordinates `(a, b)`, the weighted measure `‖a‖⁻² da db`, the homogeneity
index `s`, and the angular Fourier convention are fixed in `LeanRidgelet.L1.Defs`; see its
module docstring. Manuscript notation for the transforms is available through
`open scoped LeanRidgelet.Notation`.

## Distributional boundary of this first pass

The article develops the ridgelet transform for Lizorkin distributions `𝒮'(ℝ)/𝒫`. This pass
states the results at function level: the ridgelet function `ψ` is integrable rather than
Schwartz, and the activation `η` is locally integrable and polynomially bounded, with its
distributional Fourier transform carried by a function `Fη` representing `η̂` away from the
origin (`HasFourierAwayFromOrigin`). Deferred to a later distributional pass: the distribution
classes `𝒮'(ℍ)`, `𝒟'(𝕐^{m+1})` on the half-space, the remaining rows of the balancing theorem
`thm:existence`, the dual transform with genuine distribution action, Dirac-delta activations
`δ^{(k)}`, the sigmoid examples `eg:sig`/`eg:adm.sig`, and the fractional Laplacian identity
`cor:radon.d`. The test-function side of the quotient is already available as a type:
`LizorkinSpace` and `LizorkinDistribution` in `LeanRidgelet.ToMathlib.Lizorkin`.

## Analytic infrastructure

General-purpose material developed for this theory lives in `LeanRidgelet/ToMathlib/` with
Mathlib-only imports: the Radon transform and the Fourier slice theorem (`RadonTransform`),
Young's convolution inequality (`YoungConvolution`), the principal-value Hilbert transform, its
symbol and its `L¹` bound for integrands of vanishing integral (`HilbertTransform`) over the
Dirichlet integral (`DirichletIntegral`), the Gaussian as a Schwartz function
(`GaussianSchwartz`), the general
polar-coordinate formula (`PolarCoordinates`), almost-everywhere Fourier inversion
(`FourierInversion`), the `L¹ ∩ L²` Plancherel theorem (`FourierPlancherel`), the `L²` duality
criterion (`L2Duality`), density of the integrable classes in `L^p` (`LpIntegrableDense`),
product shears (`ProdShear`), polynomially weighted `L¹` smoothing (`WeightedL1Smoothing`),
polynomial growth (`PolynomialGrowth`), Schwartz auxiliaries (`SchwartzAux`) and the Lizorkin
space (`Lizorkin`).

## Deviations from the article

Every deviation is recorded in the docstring of the affected declaration and summarized in the
module docstring of the file holding it. In outline: the backprojection filter is the standard
Lambda operator `Λ^m` rather than the article's `eq:bp` (`LeanRidgelet.L1.Defs`), the
normalization of `eq:radon.ac` is `∫ û = 2` (`LeanRidgelet.L1.Radon`), `prop:conti.L1` is read
in the `s = 0` normalization (`LeanRidgelet.L1.Balancing`), the reconstruction formulas carry
matched growth and moment hypotheses (`LeanRidgelet.L1.Reconstruction`), Parseval's relation
and the `L²` reconstruction assume self-admissibility of both members
(`LeanRidgelet.L1.Plancherel`, `LeanRidgelet.L1.ReconstructionL2`), and the admissible ridgelet
function for the truncated powers is constructed explicitly rather than as `Λ^m G^{(ℓ+k+1)}`
(`LeanRidgelet.L1.BumpRidgelet`), and the backprojection equation of `thm:eq.ac` is imposed on
the Fourier data of both sides rather than pointwise, since the pointwise principal value
defining `Λ^m` on a slowly increasing function need not converge
(`LeanRidgelet.L1.StructureTheorem`).
-/
