/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Basic
public import LeanRidgelet.Fourier.AngularDistribution
public import LeanRidgelet.Fourier.Convention
public import LeanRidgelet.ToMathlib.HilbertTransform
public import LeanRidgelet.ToMathlib.Lizorkin
public import LeanRidgelet.ToMathlib.PolynomialGrowth
public import LeanRidgelet.ToMathlib.RadonTransform
public import LeanRidgelet.ToMathlib.SchwartzAux

/-!
# L1 theory: coordinates, transforms and admissibility

Definitions of the L1 ridgelet theory of

> S. Sonoda and N. Murata, *Neural network with unbounded activation functions is universal
> approximator* (arXiv:1505.03654v2),

formalized at function level. See `LeanRidgelet.OverviewL1` for the roadmap of the whole
development and for the list of main results.

## Coordinates and conventions

* The parameter space `𝕐^{m+1} = ℝ^m × ℝ` is realized in Euclidean coordinates `(a, b)` as
  `RidgeletParameterSpace m`. The polar coordinates `(u, α, β) ∈ 𝕊^{m-1} × ℝ₊ × ℝ` of the
  article correspond to `a = u / α`, `b = β / α`; the fixed measure `α^{-m} dα dβ du` of
  Section 5.3 becomes the weighted measure `‖a‖⁻² da db` (`ridgeletParameterMeasure`).
* The homogeneity index `s` of `eq:eucrid` is an explicit argument of the Euclidean transforms.
  The article fixes `s = 1` from Section 4 on; `prop:conti.L1` is stated at `s = 0` (Murata's
  Euclidean normalization, the remark after `eq:eucrid`), and wherever boundedness of the
  transform matters the theory may be read at `s = 0` throughout, with `da db` replacing
  `‖a‖⁻² da db`.
* The one-dimensional Fourier transform is the article convention
  `ψ̂(ζ) = ∫ z, exp (-i z ζ) ψ z`, the `V = ℝ` case of
  `LeanRidgelet.Fourier.angularFourierIntegralInner`, abbreviated `angularFourier1D`.

## Deviations from the article

* **Ridgelet functions are merely integrable, not Schwartz.** For odd `m` the constructed
  ridgelet `ψ = Λ^m ψ₀` involves the Hilbert transform and decays only algebraically.
* **Activations carry Fourier data away from the origin.** Instead of a Lizorkin distribution
  `η ∈ 𝒮₀'(ℝ)` the development uses `HasFourierAwayFromOrigin η Fη`: a locally integrable,
  polynomially bounded `η` together with a function `Fη` representing `η̂` against Schwartz
  test functions supported away from `0`. Point masses at the origin — the polynomial part of
  `η`, i.e. the kernel of the Lizorkin quotient `𝒮'(ℝ)/𝒫 ≅ 𝒮₀'(ℝ)` — are invisible to `Fη`;
  the quotient relation itself is `LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial`.
  The Lizorkin space as a type is `LizorkinSpace` in
  `LeanRidgelet.ToMathlib.Lizorkin`.
* **The backprojection filter is the standard Lambda operator.** See the docstring of
  `lambdaOperatorPow` for the correction to the article's `eq:bp`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Parameter space, reference measures and the Fourier convention -/

/-- The parameter space `𝕐^{m+1} = ℝ^m × ℝ` of hidden parameters `(a, b)` in Euclidean
coordinates. -/
abbrev RidgeletParameterSpace (m : ℕ) := InputSpace m × ℝ

/-- The measure `‖a‖⁻² da db` on `𝕐^{m+1}`, the Euclidean-coordinate expression of the fixed
measure `α^{-m} dα dβ du` used for `L²(𝕐^{m+1})` in Section 5.3 of the manuscript. -/
def ridgeletParameterMeasure (m : ℕ) : Measure (RidgeletParameterSpace m) :=
  volume.withDensity fun p => ENNReal.ofReal ((‖p.1‖ ^ 2)⁻¹)

/-- The one-dimensional manuscript Fourier integral `ψ̂(ζ) = ∫ z, exp (-i z ζ) ψ z`, the
`V = ℝ` case of `LeanRidgelet.Fourier.angularFourierIntegralInner`. -/
def angularFourier1D (g : ℝ → ℂ) : ℝ → ℂ :=
  Fourier.angularFourierIntegralInner g

/-- The defining integral of `angularFourier1D` with the real inner product expanded. -/
theorem angularFourier1D_apply (g : ℝ → ℂ) (ζ : ℝ) :
    angularFourier1D g ζ = ∫ z : ℝ, Complex.exp (-Complex.I * ((z * ζ : ℝ) : ℂ)) * g z := by
  rw [angularFourier1D, Fourier.angularFourierIntegralInner]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [MeasureTheory.inner_real_eq_mul]

/-- The article convention in terms of Mathlib's `𝓕`: rescaling the frequency by `(2π)⁻¹`
turns `ĝ(ζ) = ∫ g(z) e^{-i z ζ} dz` into `𝓕 g`. This is the bridge used whenever a Mathlib
Fourier theorem has to be transported to the angular convention. -/
theorem angularFourier1D_eq_mathlib (g : ℝ → ℂ) (ζ : ℝ) :
    angularFourier1D g ζ = 𝓕 g ((2 * Real.pi)⁻¹ • ζ) := by
  unfold angularFourier1D
  rw [Fourier.angularFourierIntegralInner_eq_mathlib]
  rfl

/-! ## Ridgelet, dual ridgelet and truncated dual transforms -/

/-- The classical ridgelet transform in Euclidean coordinates with homogeneity index `s`
(`eq:eucrid`): `R_ψ f (a, b) = ∫ x, f x * conj (ψ (⟪a, x⟫ - b)) * ‖a‖^s`. The manuscript fixes
`s = 1` from Section 4 on. -/
def euclideanRidgeletTransform (m : ℕ) (s : ℝ) (ψ : ℝ → ℂ) (f : InputSpace m → ℂ) :
    RidgeletParameterSpace m → ℂ :=
  fun p => ∫ x, f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)

/-- The classical dual ridgelet transform in Euclidean coordinates with homogeneity index `s`
(`eq:drid`): `R†_η T (x) = ∫ (a, b), T (a, b) * η (⟪a, x⟫ - b) * ‖a‖^{-s}`, as an absolutely
convergent integral. -/
def euclideanDualRidgeletTransform (m : ℕ) (s : ℝ) (η : ℝ → ℂ)
    (T : RidgeletParameterSpace m → ℂ) (x : InputSpace m) : ℂ :=
  ∫ p : RidgeletParameterSpace m, T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ s : ℝ) : ℂ)⁻¹

/-- The dual ridgelet transform truncated to the annulus `ε ≤ ‖a‖ ≤ δ`. In the polar
coordinates of the manuscript's definition the truncation reads `1/δ ≤ α ≤ 1/ε`, so the limit
`ε → 0⁺`, `δ → ∞` below is the manuscript's limit `ε → 0⁺`, `δ → ∞` after the substitution
`(ε, δ) ← (1/δ, 1/ε)`. -/
def truncatedDualRidgeletTransform (m : ℕ) (s : ℝ) (η : ℝ → ℂ)
    (T : RidgeletParameterSpace m → ℂ) (ε δ : ℝ) (x : InputSpace m) : ℂ :=
  ∫ p in {p : RidgeletParameterSpace m | ε ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ δ},
    T p * η (inner ℝ p.1 x - p.2) * ((‖p.1‖ ^ s : ℝ) : ℂ)⁻¹

/-- The filter governing the truncation limit `ε → 0⁺`, `δ → ∞` of the dual ridgelet
transform. -/
def ridgeletTruncationFilter : Filter (ℝ × ℝ) :=
  (𝓝[>] (0 : ℝ)) ×ˢ Filter.atTop

/-! ## The Radon route: Fourier slice theorem and the weak transform -/

/-- **Fourier slice theorem** (Section 2.4 of the manuscript) in the angular Fourier
convention: the `m`-dimensional angular Fourier transform of `f ∈ L¹(ℝ^m)`, restricted to the
ray through a unit vector `u`, is the one-dimensional angular Fourier transform of the Radon
transform: `f̂(ω • u) = (R[f](u, ·))^(ω)`. The Mathlib-convention version for a general
finite-dimensional inner product space is `MeasureTheory.fourier_slice_radonTransform`. -/
theorem angularFourier_slice_radonTransform {m : ℕ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (u : InputSpace m) (hu : ‖u‖ = 1) (ω : ℝ) :
    Fourier.angularFourierIntegralInner f (ω • u) =
      angularFourier1D (radonTransform f u) ω := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  have hint : Integrable
      (fun py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ (InputSpace m)) =>
        Complex.exp (-Complex.I * ((py.1 * ω : ℝ) : ℂ)) *
          f (py.1 • u + (py.2 : InputSpace m))) volume := by
    refine Integrable.bdd_mul (c := 1) h ?_ (Filter.Eventually.of_forall fun py => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · rw [Complex.norm_exp]
      simp [Complex.mul_re]
  calc Fourier.angularFourierIntegralInner f (ω • u)
      = ∫ py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ (InputSpace m)),
          Complex.exp (-Complex.I * ((py.1 * ω : ℝ) : ℂ)) *
            f (py.1 • u + (py.2 : InputSpace m)) := by
        rw [Fourier.angularFourierIntegralInner,
          ← (measurePreserving_lineOrthogonalSplit u hu).integral_comp
            (lineOrthogonalSplit u hu).measurableEmbedding
            fun x => Complex.exp (-Complex.I * (inner ℝ x (ω • u) : ℂ)) * f x]
        refine integral_congr_ae (Filter.Eventually.of_forall fun py => ?_)
        simp only [lineOrthogonalSplit_apply, inner_lineOrthogonalSplit_smul hu]
    _ = ∫ p : ℝ, ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ (InputSpace m)),
          Complex.exp (-Complex.I * ((p * ω : ℝ) : ℂ)) *
            f (p • u + (y : InputSpace m)) := by
        rw [Measure.volume_eq_prod] at hint ⊢
        exact MeasureTheory.integral_prod _ hint
    _ = ∫ p : ℝ, Complex.exp (-Complex.I * ((p * ω : ℝ) : ℂ)) * radonTransform f u p := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        exact integral_const_mul _ _
    _ = angularFourier1D (radonTransform f u) ω := by
        rw [angularFourier1D, Fourier.angularFourierIntegralInner]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        have hinner : inner ℝ p ω = p * ω := by
          rw [RCLike.inner_apply, conj_trivial]
          ring
        simp only [hinner]

/-- The weak ridgelet transform with respect to a locally integrable ridgelet function
(Definition 4.1 in polar coordinates):
`R_ψ f (u, α, β) = ∫ z, Radon f (u, α z + β) * conj (ψ z)`. The genuinely distributional
version, where `∫ · conj (ψ z) dz` is the action of `ψ ∈ 𝒮'(ℝ)` on a Schwartz function of `z`,
is deferred to the distributional pass. -/
def weakRidgeletTransform (m : ℕ) (ψ : ℝ → ℂ) (f : InputSpace m → ℂ)
    (u : InputSpace m) (α β : ℝ) : ℂ :=
  ∫ z, radonTransform f u (α * z + β) * conj (ψ z)

/-! ## The filter of filtered backprojection -/

/-- The `m`-th power `Λ^m` of the **Lambda operator** `Λ = √(-d²/dz²)` (also known in
tomography as the fractional Laplacian or the Calderón operator), the filter of filtered
backprojection: `(-1)^{⌊m/2⌋} ∂^m` for even `m` and `(-1)^{⌊m/2⌋} 𝓗 ∂^m` for odd `m`, with
one-dimensional Fourier multiplier `|ω|^m`, so that Radon's inversion formula
`R† Λ^{m-1} R = 2 (2π)^{m-1}` holds with a positive constant. In the tomography literature
`Λ^m` is Natterer's Riesz potential `I^{-m}`, and for `m = 1` on the plane the multiplier
`|ω|` is the ramp filter.

**Correction to the article.** The article's backprojection filter (`eq:bp`) is `∂^m` for
even `m` and `H ∂^m` for odd `m` with `H = i 𝓗`, which equals `i^m Λ^m`: its multiplier
`i^m |ω|^m` carries the spurious phase `i^m` (equal to `-1` for `m ≡ 2 (mod 4)` and `±i` for
odd `m`), so with `eq:bp` the inversion formula `R† Λ^{m-1} R = 2 (2π)^{m-1}` would acquire
the factor `i^{m-1}`. This formalization uses the standard `Λ^m` throughout; the other
affected statements (`thm:eq.ac`, `cor:const.ap`, Section 6.2) are equivalent up to a nonzero
scalar rescaling of the solution or of the constructed ridgelet function. -/
def lambdaOperatorPow (m : ℕ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun z => (-1 : ℂ) ^ (m / 2) *
    (if Even m then iteratedDeriv m g z else pvHilbertTransform (iteratedDeriv m g) z)

/-- The convolution `conj (ψ~) ⋆ η` with the reflection `ψ~(z) = ψ (-z)`, appearing in the
structure theorem for admissible pairs (`thm:eq.ac`). -/
def reflectedConjConvolution (ψ η : ℝ → ℂ) : ℝ → ℂ :=
  (fun z => conj (ψ (-z))) ⋆[ContinuousLinearMap.mul ℂ ℂ] η

/-! ## Fourier data away from the origin and admissibility -/

/-- The one-dimensional angular Fourier integral of a Schwartz function is the angular-frequency
Schwartz Fourier transform of `LeanRidgelet.Fourier.AngularDistribution`. -/
theorem angularFourier1D_coe_schwartz (φ : SchwartzMap ℝ ℂ) :
    angularFourier1D (⇑φ) = ⇑(Fourier.angularFourierSchwartz φ) := by
  funext ζ
  exact (Fourier.angularFourierSchwartz_eq_angularFourierIntegralInner φ ζ).symm

/-- `Fη` represents the distributional Fourier transform of `η` away from the origin: for every
Schwartz test function `φ` whose support avoids `0`, the pairing `⟨η̂, φ⟩ = ⟨η, φ̂⟩` is computed
by integrating `Fη` against `φ`. Point masses `δ^{(j)}` at the origin — equivalently, polynomial
components of `η` — are invisible to `Fη`, which realizes the Lizorkin quotient
`𝒮₀'(ℝ) ≅ 𝒮'(ℝ)/polynomials` at function level. -/
def HasFourierAwayFromOrigin (η Fη : ℝ → ℂ) : Prop :=
  MeasureTheory.LocallyIntegrable η volume ∧ PolynomiallyBounded η ∧
  MeasureTheory.LocallyIntegrableOn Fη {(0 : ℝ)}ᶜ volume ∧
  ∀ φ : SchwartzMap ℝ ℂ, tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ →
    ∫ ζ, Fη ζ * φ ζ = ∫ z, η z * angularFourier1D (⇑φ) z

/-- The admissibility constant `K_{ψ,η} = (2π)^{m-1} ∫_{ℝ \ {0}} conj (ψ̂ ζ) * Fη ζ / |ζ|^m dζ`
(`eq:defK`), with the Fourier transform of `η` away from the origin given by `Fη`. -/
def admissibilityConstant (m : ℕ) (ψ Fη : ℝ → ℂ) : ℂ :=
  (2 * Real.pi) ^ (m - 1) *
    ∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ)

/-- The admissibility condition for a pair `(ψ, η)` whose Fourier transform away from the origin
is `Fη`: the ridgelet function is integrable (so `ψ̂` is an honest integral), the defining
integrand of `K_{ψ,η}` is integrable on `ℝ \ {0}`, and `K_{ψ,η} ≠ 0`. -/
def IsAdmissiblePair (m : ℕ) (ψ η Fη : ℝ → ℂ) : Prop :=
  Integrable ψ volume ∧ HasFourierAwayFromOrigin η Fη ∧
  IntegrableOn (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
    {(0 : ℝ)}ᶜ volume ∧
  admissibilityConstant m ψ Fη ≠ 0

/-- `ψ` is self-admissible when the pair `(ψ, ψ)` is admissible (Section 5.3). -/
def IsSelfAdmissible (m : ℕ) (ψ : ℝ → ℂ) : Prop :=
  IsAdmissiblePair m ψ ψ (angularFourier1D ψ)

/-- Two pairs are equivalent when they define the same convolution `conj (ψ~) ⋆ η`
(Section 5.3), expressed here on the Fourier side: the products `conj (ψ̂) * Fη` agree away from
the origin. -/
def IsEquivalentPair (ψ Fη ψ' Fη' : ℝ → ℂ) : Prop :=
  ∀ ζ : ℝ, ζ ≠ 0 → conj (angularFourier1D ψ ζ) * Fη ζ = conj (angularFourier1D ψ' ζ) * Fη' ζ

/-- An admissible pair `(ψ, η)` is admissibly decomposable when it is equivalent to a cross pair
`(ψ⋆, η⋆)` of two self-admissible functions (Section 5.3). -/
def IsAdmissiblyDecomposable (m : ℕ) (ψ η Fη : ℝ → ℂ) : Prop :=
  IsAdmissiblePair m ψ η Fη ∧
  ∃ ψs ηs : ℝ → ℂ, IsSelfAdmissible m ψs ∧ IsSelfAdmissible m ηs ∧
    IsEquivalentPair ψ Fη ψs (angularFourier1D ηs)

/-! ## Pairs solving the backprojection equation in spectral form

The structure theorem `thm:eq.ac` and the Radon reconstruction `thm:formula.radon` both start
from the backprojection equation in its spectral form `conj (ψ̂) Fη = |ζ|^m û` away from the
origin. These lemmas evaluate the admissibility data of such a pair once and for all. Since
`Fη` is only determined up to a null set of `ℝ \ {0}` (see
`LeanRidgelet.hasFourierAwayFromOrigin_ae_eq`), each of them is stated for the almost
everywhere form of the equation, with the pointwise form as a wrapper.
-/

variable {m : ℕ} {ψ Fη Fu : ℝ → ℂ}

/-- Under the spectral backprojection equation the admissibility density is `û` away from the
origin. -/
theorem admissibilityDensity_eq_of_backprojection {ζ : ℝ} (hζ : ζ ≠ 0)
    (hbp : conj (angularFourier1D ψ ζ) * Fη ζ = ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ) :
    conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) = Fu ζ := by
  have habs : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (abs_ne_zero.mpr hζ))
  rw [hbp, mul_comm, mul_div_assoc, div_self habs, mul_one]

/-- The spectral backprojection equation, holding pointwise away from the origin, holds almost
everywhere on `ℝ \ {0}`. -/
theorem backprojection_ae_of_forall
    (hbp : ∀ ζ : ℝ, ζ ≠ 0 →
      conj (angularFourier1D ψ ζ) * Fη ζ = ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ) :
    (fun ζ : ℝ => conj (angularFourier1D ψ ζ) * Fη ζ)
      =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ :=
  (ae_restrict_iff' (measurableSet_singleton (0 : ℝ)).compl).2
    (Filter.Eventually.of_forall fun ζ hζ => hbp ζ (by simpa using hζ))

/-- The integrability half of admissibility for a pair solving the backprojection equation in
spectral form almost everywhere: it is inherited from the integrability of `û`. -/
theorem integrableOn_admissibilityIntegrand_of_backprojection_ae
    (hbp : (fun ζ : ℝ => conj (angularFourier1D ψ ζ) * Fη ζ)
      =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ)
    (huint : IntegrableOn Fu {(0 : ℝ)}ᶜ volume) :
    IntegrableOn (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      {(0 : ℝ)}ᶜ volume := by
  refine huint.congr ?_
  filter_upwards [hbp, ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ hζ0
  exact (admissibilityDensity_eq_of_backprojection (by simpa using hζ0) hζ).symm

/-- **The admissibility constant of a pair solving the backprojection equation in spectral form
almost everywhere**: `K_{ψ,η} = (2π)^{m-1} ∫ û`. -/
theorem admissibilityConstant_of_backprojection_ae
    (hbp : (fun ζ : ℝ => conj (angularFourier1D ψ ζ) * Fη ζ)
      =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ) :
    admissibilityConstant m ψ Fη
      = ((2 * Real.pi) ^ (m - 1) : ℂ) * ∫ ζ in {(0 : ℝ)}ᶜ, Fu ζ := by
  rw [admissibilityConstant]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hbp, ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ hζ0
  exact admissibilityDensity_eq_of_backprojection (by simpa using hζ0) hζ

/-- The integrability half of admissibility for a pair solving the backprojection equation in
spectral form: it is inherited from the integrability of `û`. -/
theorem integrableOn_admissibilityIntegrand_of_backprojection
    (hbp : ∀ ζ : ℝ, ζ ≠ 0 →
      conj (angularFourier1D ψ ζ) * Fη ζ = ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ)
    (huint : IntegrableOn Fu {(0 : ℝ)}ᶜ volume) :
    IntegrableOn (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      {(0 : ℝ)}ᶜ volume :=
  integrableOn_admissibilityIntegrand_of_backprojection_ae
    (backprojection_ae_of_forall hbp) huint

/-- **The admissibility constant of a pair solving the backprojection equation in spectral
form**: `K_{ψ,η} = (2π)^{m-1} ∫ û`. This is the identity that fixes the normalization of
`eq:radon.ac`; see `LeanRidgelet.l1_reconstruction_formula_radon`. -/
theorem admissibilityConstant_of_backprojection
    (hbp : ∀ ζ : ℝ, ζ ≠ 0 →
      conj (angularFourier1D ψ ζ) * Fη ζ = ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ) :
    admissibilityConstant m ψ Fη
      = ((2 * Real.pi) ^ (m - 1) : ℂ) * ∫ ζ in {(0 : ℝ)}ᶜ, Fu ζ :=
  admissibilityConstant_of_backprojection_ae (backprojection_ae_of_forall hbp)

/-! ## Standard unbounded activation functions -/

/-- The truncated power function `z₊^k`, containing the step function (`k = 0`) and the ReLU
(`k = 1`). The if-then-else form (rather than `(max z 0) ^ k`) is deliberate: with natural
powers `(max z 0) ^ 0 = 1` everywhere, which would be the constant function rather than the
unit step. -/
def truncatedPower (k : ℕ) (z : ℝ) : ℂ :=
  if 0 < z then ((z ^ k : ℝ) : ℂ) else 0

/-- The function part `k! / (i ζ)^{k+1}` of the distributional Fourier transform
`(z₊^k)^ = k!/(iζ)^{k+1} + π i^k δ^{(k)}` of the truncated power (Gel'fand--Shilov). -/
def truncatedPowerFourier (k : ℕ) (ζ : ℝ) : ℂ :=
  (k.factorial : ℂ) / (Complex.I * (ζ : ℂ)) ^ (k + 1)

/-- The Gaussian window `G(z) = exp (-z²/2)` used to construct admissible ridgelet functions in
Section 6.2. -/
def gaussianWindow (z : ℝ) : ℂ :=
  (Real.exp (-z ^ 2 / 2) : ℂ)

end LeanRidgelet
