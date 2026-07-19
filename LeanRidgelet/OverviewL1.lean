/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Basic
public import LeanRidgelet.Fourier.Convention
public import LeanRidgelet.Fourier.PaperDistribution
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# L1 theory overview: main results of `1505.03654v2`

This file lists, as Lean statements, the main results of the L1 ridgelet theory

> S. Sonoda and N. Murata, *Neural network with unbounded activation functions is universal
> approximator* (arXiv:1505.03654v2, `00data/1505.03654v2.pdf`),

together with the definitions needed to state them. Every unfinished result is a named theorem
with a `sorry` proof, registered in `audit/Assumptions.lean`, so the assumption audit tracks the
exact formalization boundary. This is plan milestone M7.

## Coordinates and conventions

* The parameter space `𝕐^{m+1} = ℝ^m × ℝ` is realized in Euclidean coordinates `(a, b)` as
  `RidgeletParameterSpace m := InputSpace m × ℝ`. The polar coordinates
  `(u, α, β) ∈ 𝕊^{m-1} × ℝ₊ × ℝ` of the manuscript correspond to
  `a = u / α`, `b = β / α`; the fixed measure `α^{-m} dα dβ du` of Section 5.3 becomes the
  weighted measure `‖a‖⁻² da db`, provided here as `ridgeletParameterMeasure`.
* The manuscript's homogeneity index `s` from `eq:eucrid` is kept as an explicit argument of the
  Euclidean transforms; all main theorems fix `s = 1` following Section 4.
* The one-dimensional Fourier transform is the manuscript convention
  `ψ̂(ζ) = ∫ z, exp (-i z ζ) ψ z`, reused from `LeanRidgelet.Fourier.paperFourierIntegralInner`
  through the alias `paperFourier1D`.

## Distributional boundary of this first pass

The manuscript develops the ridgelet transform for Lizorkin distributions
`𝒮'(ℝ)/polynomials`. This overview states the results at function level:

* The ridgelet function `ψ` is a plain function with an `Integrable` hypothesis, so that its
  Fourier transform is an honest integral. This is deliberately wider than the manuscript's
  `𝒮(ℝ)`: for odd `m` the constructed ridgelet `ψ = Λ^m ψ₀` (`backprojectionFilter`) involves
  the Hilbert transform and leaves the Schwartz class, decaying only algebraically.
* The activation `η` is a locally integrable, polynomially bounded function, and its
  distributional Fourier transform is carried by a function `Fη` that represents `η̂` away from
  the origin (`HasFourierAwayFromOrigin`). Point masses at the origin — the polynomial part of
  `η`, i.e. the kernel of the Lizorkin quotient — are invisible to `Fη`; the quotient relation
  itself is the named result `l1_hasFourierAwayFromOrigin_add_polynomial`.
* Deferred to a later distributional pass: the Lizorkin spaces `𝒮₀(ℝ)`/`𝒮₀'(ℝ)` as types, the
  distribution classes `𝒮'(ℍ)`, `𝒟'(𝕐^{m+1})` on the half-space, the remaining rows of the
  balancing theorem `thm:existence` (`𝒟 × 𝒟'`, `ℰ' × 𝒟'`, `𝒮 × 𝒮'`, `𝒪_C' × 𝒮'`,
  `𝒟_{L¹}' × 𝒟_{L^p}'`), the dual transform with genuine distribution action, Dirac-delta
  activations `δ^{(k)}`, the sigmoid examples `eg:sig`/`eg:adm.sig`, and the fractional
  Laplacian identity `cor:radon.d`.

Analytic definitions introduced here (`radonTransform`, `pvHilbertTransform`,
`backprojectionFilter`, admissibility) are expected to move into dedicated files under
`LeanRidgelet/Transform/` as their basic API is developed.

Gaps in the manuscript discovered during formalization are recorded as **paper gap memo**
paragraphs in the docstrings of `l1_ridgeletTransform_bounded_L1_Linfty` (the `L¹ → L^∞`
operator-norm constant and the vanishing-moment hypotheses) and
`l1_construction_of_admissible_pairs` (the constructed ridgelet leaves the Schwartz class for
odd `m`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Parameter space and reference measures -/

/-- The parameter space `𝕐^{m+1} = ℝ^m × ℝ` of hidden parameters `(a, b)` in Euclidean
coordinates. -/
abbrev RidgeletParameterSpace (m : ℕ) := InputSpace m × ℝ

/-- The measure `‖a‖⁻² da db` on `𝕐^{m+1}`, the Euclidean-coordinate expression of the fixed
measure `α^{-m} dα dβ du` used for `L²(𝕐^{m+1})` in Section 5.3 of the manuscript. -/
def ridgeletParameterMeasure (m : ℕ) : Measure (RidgeletParameterSpace m) :=
  volume.withDensity fun p => ENNReal.ofReal ((‖p.1‖ ^ 2)⁻¹)

/-- The one-dimensional manuscript Fourier integral `ψ̂(ζ) = ∫ z, exp (-i z ζ) ψ z`, the
`V = ℝ` case of `LeanRidgelet.Fourier.paperFourierIntegralInner`. -/
def paperFourier1D (g : ℝ → ℂ) : ℝ → ℂ :=
  Fourier.paperFourierIntegralInner g

/-! ## Ridgelet transform and dual ridgelet transform -/

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

/-! ## Radon transform and backprojection filter -/

/-- The Radon transform `R f (u, p) = ∫_{(ℝu)^⊥} f (p u + y) dy` (`eq:radon`), integrating over
the orthogonal complement of the line `ℝu` with its canonical Lebesgue measure. The manuscript
uses it for `‖u‖ = 1`. -/
def radonTransform (m : ℕ) (f : InputSpace m → ℂ) (u : InputSpace m) (p : ℝ) : ℂ :=
  ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ (InputSpace m)), f (p • u + ↑y)

/-- The dual Radon transform `R† Φ (x) = ∫_{𝕊^{m-1}} Φ (u, ⟪u, x⟫) du` (`eq:dradon`), with the
surface measure `volume.toSphere` on the unit sphere. -/
def dualRadonTransform (m : ℕ) (Φ : InputSpace m → ℝ → ℂ) (x : InputSpace m) : ℂ :=
  ∫ u : Metric.sphere (0 : InputSpace m) 1,
    Φ u (inner ℝ (u : InputSpace m) x) ∂(volume : Measure (InputSpace m)).toSphere

/-- The weak ridgelet transform with respect to a locally integrable ridgelet function
(Definition 4.1 in polar coordinates):
`R_ψ f (u, α, β) = ∫ z, Radon f (u, α z + β) * conj (ψ z)`. The genuinely distributional
version, where `∫ · conj (ψ z) dz` is the action of `ψ ∈ 𝒮'(ℝ)` on a Schwartz function of `z`,
is deferred to the distributional pass. -/
def weakRidgeletTransform (m : ℕ) (ψ : ℝ → ℂ) (f : InputSpace m → ℂ)
    (u : InputSpace m) (α β : ℝ) : ℂ :=
  ∫ z, radonTransform m f u (α * z + β) * conj (ψ z)

/-- The principal-value Hilbert transform in the manuscript normalization
`H g (x) = (i/π) p.v. ∫ g t / (x - t) dt`, so that `(H g)^ (ω) = sign ω * ĝ ω` and
`H (H g) = g`. Realized as a junk-valued limit of truncated integrals. -/
def pvHilbertTransform (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    (Complex.I / (Real.pi : ℂ)) * ∫ t in {t : ℝ | ε < |x - t|}, g t / ((x : ℂ) - (t : ℂ))

/-- The backprojection filter `Λ^m` (`eq:bp`): `∂^m` for even `m` and `H ∂^m` for odd `m`,
designed as the one-dimensional Fourier multiplier `i^m |ω|^m`. -/
def backprojectionFilter (m : ℕ) (g : ℝ → ℂ) : ℝ → ℂ :=
  if Even m then iteratedDeriv m g else pvHilbertTransform (iteratedDeriv m g)

/-- The convolution `conj (ψ~) ⋆ η` with the reflection `ψ~(z) = ψ (-z)`, appearing in the
structure theorem for admissible pairs (`thm:eq.ac`). -/
def reflectedConjConvolution (ψ η : ℝ → ℂ) : ℝ → ℂ :=
  (fun z => conj (ψ (-z))) ⋆[ContinuousLinearMap.mul ℂ ℂ] η

/-! ## Fourier data away from the origin and admissibility -/

/-- Polynomial growth bound, the criterion for a locally integrable function to define a
tempered distribution (Proposition 6.1 of the manuscript). -/
def PolynomiallyBounded (η : ℝ → ℂ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ z : ℝ, ‖η z‖ ≤ C * (1 + |z|) ^ k

theorem polynomiallyBounded_nonneg_const {η : ℝ → ℂ} {C : ℝ} {k : ℕ}
    (h : ∀ z : ℝ, ‖η z‖ ≤ C * (1 + |z|) ^ k) : 0 ≤ C := by
  have h0 := h 0
  simpa using (norm_nonneg (η 0)).trans h0

/-- Polynomial growth bounds are stable under addition. -/
theorem PolynomiallyBounded.add {η₁ η₂ : ℝ → ℂ}
    (h₁ : PolynomiallyBounded η₁) (h₂ : PolynomiallyBounded η₂) :
    PolynomiallyBounded fun z => η₁ z + η₂ z := by
  obtain ⟨C₁, k₁, hb₁⟩ := h₁
  obtain ⟨C₂, k₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, max k₁ k₂, fun z => ?_⟩
  have hz : (1 : ℝ) ≤ 1 + |z| := le_add_of_nonneg_right (abs_nonneg z)
  calc ‖η₁ z + η₂ z‖ ≤ ‖η₁ z‖ + ‖η₂ z‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + |z|) ^ k₁ + C₂ * (1 + |z|) ^ k₂ := add_le_add (hb₁ z) (hb₂ z)
    _ ≤ C₁ * (1 + |z|) ^ max k₁ k₂ + C₂ * (1 + |z|) ^ max k₁ k₂ := by
        gcongr <;>
          first
            | exact polynomiallyBounded_nonneg_const hb₁
            | exact polynomiallyBounded_nonneg_const hb₂
            | exact hz
            | exact le_max_left _ _
            | exact le_max_right _ _
    _ = (C₁ + C₂) * (1 + |z|) ^ max k₁ k₂ := by ring

/-- Every polynomial, evaluated along the real line, has polynomial growth. -/
theorem polynomiallyBounded_polynomial_eval (Q : Polynomial ℂ) :
    PolynomiallyBounded fun z : ℝ => Q.eval (z : ℂ) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    refine ⟨‖a‖, n, fun z => ?_⟩
    simp only [Polynomial.eval_monomial, norm_mul, norm_pow]
    have hz : ‖(z : ℂ)‖ ≤ 1 + |z| := by
      simp only [Complex.norm_real]
      exact le_add_of_nonneg_left zero_le_one
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hz n) (norm_nonneg a)

/-- The one-dimensional paper Fourier integral of a Schwartz function is the paper-normalized
Schwartz Fourier transform of `LeanRidgelet.Fourier.PaperDistribution`. -/
theorem paperFourier1D_coe_schwartz (φ : SchwartzMap ℝ ℂ) :
    paperFourier1D (⇑φ) = ⇑(Fourier.paperFourierSchwartz φ) := by
  funext ζ
  exact (Fourier.paperFourierSchwartz_eq_paperFourierIntegralInner φ ζ).symm

/-- A polynomially bounded measurable function is integrable against any Schwartz function. -/
theorem PolynomiallyBounded.integrable_mul_schwartz {η : ℝ → ℂ}
    (hb : PolynomiallyBounded η) (hm : AEStronglyMeasurable η volume)
    (φ : SchwartzMap ℝ ℂ) : Integrable (fun z => η z * φ z) volume := by
  obtain ⟨C, k, hbd⟩ := hb
  have hC : 0 ≤ C := polynomiallyBounded_nonneg_const hbd
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z : ℝ, (1 + ‖z‖) ^ (k + 2) * ‖φ z‖ ≤ M := by
    refine ⟨2 ^ (k + 2) *
      (Finset.Iic (k + 2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ, fun z => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, 0))
      le_rfl le_rfl φ z
    simpa [norm_iteratedFDeriv_zero] using h
  have hpt : ∀ z : ℝ, ‖η z * φ z‖ ≤ C * M * (1 + z ^ 2)⁻¹ := by
    intro z
    have hsq : (0 : ℝ) < 1 + z ^ 2 := by positivity
    have hcmp : ((1 + ‖z‖) ^ k * ‖φ z‖) * (1 + z ^ 2) ≤ M := by
      have hz2 : 1 + z ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
        have hza : ‖z‖ = |z| := Real.norm_eq_abs z
        nlinarith [abs_nonneg z, sq_abs z]
      calc ((1 + ‖z‖) ^ k * ‖φ z‖) * (1 + z ^ 2)
          ≤ ((1 + ‖z‖) ^ k * ‖φ z‖) * (1 + ‖z‖) ^ 2 := by
            have hnn : (0 : ℝ) ≤ (1 + ‖z‖) ^ k * ‖φ z‖ := by positivity
            exact mul_le_mul_of_nonneg_left hz2 hnn
        _ = (1 + ‖z‖) ^ (k + 2) * ‖φ z‖ := by ring
        _ ≤ M := hM z
    have hbz : ‖η z * φ z‖ ≤ C * ((1 + ‖z‖) ^ k * ‖φ z‖) := by
      rw [norm_mul]
      have h1 : ‖η z‖ ≤ C * (1 + ‖z‖) ^ k := by
        simpa [Real.norm_eq_abs] using hbd z
      calc ‖η z‖ * ‖φ z‖ ≤ C * (1 + ‖z‖) ^ k * ‖φ z‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = C * ((1 + ‖z‖) ^ k * ‖φ z‖) := by ring
    have hdiv : (1 + ‖z‖) ^ k * ‖φ z‖ ≤ M * (1 + z ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hsq).mpr hcmp
    calc ‖η z * φ z‖ ≤ C * ((1 + ‖z‖) ^ k * ‖φ z‖) := hbz
      _ ≤ C * (M * (1 + z ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hdiv hC
      _ = C * M * (1 + z ^ 2)⁻¹ := by ring
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (C * M))
    (hm.mul φ.continuous.aestronglyMeasurable) (Filter.Eventually.of_forall hpt)

/-- The coercion of an iterated Schwartz derivative is the iterated derivative. -/
theorem coe_iterate_schwartz_derivCLM (n : ℕ) (φ : SchwartzMap ℝ ℂ) :
    ⇑((⇑(SchwartzMap.derivCLM ℂ ℂ))^[n] φ) = iteratedDeriv n (⇑φ) := by
  induction n generalizing φ with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, iteratedDeriv_succ', ih (SchwartzMap.derivCLM ℂ ℂ φ)]
    congr 1

/-- A Schwartz function supported away from the origin has all iterated derivatives vanishing
at the origin. -/
theorem iteratedDeriv_eq_zero_of_tsupport_subset_compl (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) (n : ℕ) : iteratedDeriv n (⇑φ) 0 = 0 := by
  have hmem : (0 : ℝ) ∈ (tsupport ⇑φ)ᶜ := fun h => hφ h rfl
  have h0 : ⇑φ =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [(isClosed_tsupport ⇑φ).isOpen_compl.mem_nhds hmem] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [Filter.EventuallyEq.iteratedDeriv_eq n h0]
  simp

/-- Moments of the paper Fourier transform of a Schwartz function supported away from the
origin all vanish: `∫ ζ^n φ̂(ζ) dζ = 0`. This is the analytic heart of the invisibility of
polynomials in the Lizorkin quotient. -/
theorem integral_pow_mul_paperFourier1D_eq_zero (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) (n : ℕ) :
    ∫ ζ : ℝ, (ζ : ℂ) ^ n * paperFourier1D (⇑φ) ζ = 0 := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπℂ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hπ)
  -- The Schwartz function realizing `iteratedDeriv n φ`.
  set Φ : SchwartzMap ℝ ℂ := (⇑(SchwartzMap.derivCLM ℂ ℂ))^[n] φ with hΦ_def
  have hΦ : ⇑Φ = iteratedDeriv n (⇑φ) := coe_iterate_schwartz_derivCLM n φ
  -- Fourier transform of the iterated derivative.
  have hderiv : 𝓕 (iteratedDeriv n (⇑φ)) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • 𝓕 (⇑φ) x := by
    refine Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤) (fun k _ => ?_) le_top
    rw [← coe_iterate_schwartz_derivCLM k φ]
    exact SchwartzMap.integrable _
  -- The Fourier transform of `Φ` is integrable.
  have hFΦ : Integrable (𝓕 ⇑Φ) volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  -- Fourier inversion evaluates the total integral of `𝓕 Φ` at the origin.
  have hinv : (∫ w : ℝ, 𝓕 (⇑Φ) w) = Φ 0 := by
    have h1 : 𝓕⁻ (𝓕 ⇑Φ) = ⇑Φ :=
      Φ.continuous.fourierInv_fourier_eq (SchwartzMap.integrable _) hFΦ
    have h2 : 𝓕⁻ (𝓕 ⇑Φ) 0 = ∫ w : ℝ, 𝓕 (⇑Φ) w := by
      rw [Real.fourierInv_eq]
      simp
    rw [← h2, h1]
  have hΦ0 : Φ 0 = 0 := by
    have := iteratedDeriv_eq_zero_of_tsupport_subset_compl φ hφ n
    rw [← hΦ] at this
    exact this
  -- The centered moment of the Mathlib Fourier transform vanishes.
  have hJ : (∫ w : ℝ, (w : ℂ) ^ n * 𝓕 (⇑φ) w) = 0 := by
    have hIℂ : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 := by
      apply pow_ne_zero
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hsum : (∫ w : ℝ, 𝓕 (⇑Φ) w) =
        (2 * (Real.pi : ℂ) * Complex.I) ^ n * ∫ w : ℝ, (w : ℂ) ^ n * 𝓕 (⇑φ) w := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [hΦ, hderiv]
      simp only [smul_eq_mul]
      ring
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) ^ n *
        (∫ w : ℝ, (w : ℂ) ^ n * 𝓕 (⇑φ) w) = 0 := by
      rw [← hsum, hinv, hΦ0]
    exact (mul_eq_zero.mp h0).resolve_left hIℂ
  -- Rescale the paper transform to the Mathlib transform.
  have hbridge : ∀ ζ : ℝ, paperFourier1D (⇑φ) ζ = 𝓕 (⇑φ) ((2 * Real.pi)⁻¹ • ζ) := by
    intro ζ
    unfold paperFourier1D
    rw [Fourier.paperFourierIntegralInner_eq_mathlib]
    rfl
  have hζ : ∀ ζ : ℝ, (ζ : ℂ) ^ n * paperFourier1D (⇑φ) ζ =
      ((2 * Real.pi : ℝ) : ℂ) ^ n *
        ((fun w : ℝ => (w : ℂ) ^ n * 𝓕 (⇑φ) w) ((2 * Real.pi)⁻¹ • ζ)) := by
    intro ζ
    rw [hbridge ζ]
    simp only [smul_eq_mul]
    have hcast : (((2 * Real.pi)⁻¹ * ζ : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (ζ : ℂ) := by
      push_cast
      ring
    rw [hcast, mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπℂ]
    simp
  calc ∫ ζ : ℝ, (ζ : ℂ) ^ n * paperFourier1D (⇑φ) ζ
      = ∫ ζ : ℝ, ((2 * Real.pi : ℝ) : ℂ) ^ n *
          ((fun w : ℝ => (w : ℂ) ^ n * 𝓕 (⇑φ) w) ((2 * Real.pi)⁻¹ • ζ)) :=
        integral_congr_ae (Filter.Eventually.of_forall hζ)
    _ = ((2 * Real.pi : ℝ) : ℂ) ^ n *
          ∫ ζ : ℝ, (fun w : ℝ => (w : ℂ) ^ n * 𝓕 (⇑φ) w) ((2 * Real.pi)⁻¹ • ζ) :=
        integral_const_mul _ _
    _ = 0 := by
        rw [Measure.integral_comp_inv_smul volume
          (fun w : ℝ => (w : ℂ) ^ n * 𝓕 (⇑φ) w) (2 * Real.pi), hJ]
        simp

/-- Integrating a polynomial against the paper Fourier transform of a Schwartz function
supported away from the origin gives zero. -/
theorem integral_polynomial_mul_paperFourier1D_eq_zero (Q : Polynomial ℂ)
    (φ : SchwartzMap ℝ ℂ) (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ z : ℝ, Q.eval (z : ℂ) * paperFourier1D (⇑φ) z = 0 := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    have hip : Integrable (fun z : ℝ => p.eval (z : ℂ) * paperFourier1D (⇑φ) z) volume := by
      rw [paperFourier1D_coe_schwartz]
      exact (polynomiallyBounded_polynomial_eval p).integrable_mul_schwartz
        (((Polynomial.continuous p).comp Complex.continuous_ofReal).aestronglyMeasurable)
        (Fourier.paperFourierSchwartz φ)
    have hiq : Integrable (fun z : ℝ => q.eval (z : ℂ) * paperFourier1D (⇑φ) z) volume := by
      rw [paperFourier1D_coe_schwartz]
      exact (polynomiallyBounded_polynomial_eval q).integrable_mul_schwartz
        (((Polynomial.continuous q).comp Complex.continuous_ofReal).aestronglyMeasurable)
        (Fourier.paperFourierSchwartz φ)
    have hsplit : ∫ z : ℝ, (p + q).eval (z : ℂ) * paperFourier1D (⇑φ) z =
        (∫ z : ℝ, p.eval (z : ℂ) * paperFourier1D (⇑φ) z) +
          ∫ z : ℝ, q.eval (z : ℂ) * paperFourier1D (⇑φ) z := by
      rw [← integral_add hip hiq]
      apply integral_congr_ae
      filter_upwards with z
      simp [Polynomial.eval_add, add_mul]
    rw [hsplit, hp, hq, add_zero]
  | monomial n a =>
    have hmono : ∀ z : ℝ, (Polynomial.monomial n a).eval (z : ℂ) * paperFourier1D (⇑φ) z =
        a * ((z : ℂ) ^ n * paperFourier1D (⇑φ) z) := by
      intro z
      rw [Polynomial.eval_monomial]
      ring
    calc ∫ z : ℝ, (Polynomial.monomial n a).eval (z : ℂ) * paperFourier1D (⇑φ) z
        = ∫ z : ℝ, a * ((z : ℂ) ^ n * paperFourier1D (⇑φ) z) :=
          integral_congr_ae (Filter.Eventually.of_forall hmono)
      _ = a * ∫ z : ℝ, (z : ℂ) ^ n * paperFourier1D (⇑φ) z := integral_const_mul _ _
      _ = 0 := by rw [integral_pow_mul_paperFourier1D_eq_zero φ hφ n, mul_zero]

/-- `Fη` represents the distributional Fourier transform of `η` away from the origin: for every
Schwartz test function `φ` whose support avoids `0`, the pairing `⟨η̂, φ⟩ = ⟨η, φ̂⟩` is computed
by integrating `Fη` against `φ`. Point masses `δ^{(j)}` at the origin — equivalently, polynomial
components of `η` — are invisible to `Fη`, which realizes the Lizorkin quotient
`𝒮₀'(ℝ) ≅ 𝒮'(ℝ)/polynomials` at function level. -/
def HasFourierAwayFromOrigin (η Fη : ℝ → ℂ) : Prop :=
  MeasureTheory.LocallyIntegrable η volume ∧ PolynomiallyBounded η ∧
  MeasureTheory.LocallyIntegrableOn Fη {(0 : ℝ)}ᶜ volume ∧
  ∀ φ : SchwartzMap ℝ ℂ, tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ →
    ∫ ζ, Fη ζ * φ ζ = ∫ z, η z * paperFourier1D (⇑φ) z

/-- The admissibility constant `K_{ψ,η} = (2π)^{m-1} ∫_{ℝ \ {0}} conj (ψ̂ ζ) * Fη ζ / |ζ|^m dζ`
(`eq:defK`), with the Fourier transform of `η` away from the origin given by `Fη`. -/
def admissibilityConstant (m : ℕ) (ψ Fη : ℝ → ℂ) : ℂ :=
  (2 * Real.pi) ^ (m - 1) *
    ∫ ζ in {(0 : ℝ)}ᶜ, conj (paperFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ)

/-- The admissibility condition for a pair `(ψ, η)` whose Fourier transform away from the origin
is `Fη`: the ridgelet function is integrable (so `ψ̂` is an honest integral), the defining
integrand of `K_{ψ,η}` is integrable on `ℝ \ {0}`, and `K_{ψ,η} ≠ 0`. -/
def IsAdmissiblePair (m : ℕ) (ψ η Fη : ℝ → ℂ) : Prop :=
  Integrable ψ volume ∧ HasFourierAwayFromOrigin η Fη ∧
  IntegrableOn (fun ζ => conj (paperFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
    {(0 : ℝ)}ᶜ volume ∧
  admissibilityConstant m ψ Fη ≠ 0

/-- `ψ` is self-admissible when the pair `(ψ, ψ)` is admissible (Section 5.3). -/
def IsSelfAdmissible (m : ℕ) (ψ : ℝ → ℂ) : Prop :=
  IsAdmissiblePair m ψ ψ (paperFourier1D ψ)

/-- Two pairs are equivalent when they define the same convolution `conj (ψ~) ⋆ η`
(Section 5.3), expressed here on the Fourier side: the products `conj (ψ̂) * Fη` agree away from
the origin. -/
def IsEquivalentPair (ψ Fη ψ' Fη' : ℝ → ℂ) : Prop :=
  ∀ ζ : ℝ, ζ ≠ 0 → conj (paperFourier1D ψ ζ) * Fη ζ = conj (paperFourier1D ψ' ζ) * Fη' ζ

/-- An admissible pair `(ψ, η)` is admissibly decomposable when it is equivalent to a cross pair
`(ψ⋆, η⋆)` of two self-admissible functions (Section 5.3). -/
def IsAdmissiblyDecomposable (m : ℕ) (ψ η Fη : ℝ → ℂ) : Prop :=
  IsAdmissiblePair m ψ η Fη ∧
  ∃ ψs ηs : ℝ → ℂ, IsSelfAdmissible m ψs ∧ IsSelfAdmissible m ηs ∧
    IsEquivalentPair ψ Fη ψs (paperFourier1D ηs)

/-! ## Standard unbounded activation functions -/

/-- The truncated power function `z₊^k`, containing the step function (`k = 0`) and the ReLU
(`k = 1`). -/
def truncatedPower (k : ℕ) (z : ℝ) : ℂ :=
  ((max z 0) ^ k : ℝ)

/-- The function part `k! / (i ζ)^{k+1}` of the distributional Fourier transform
`(z₊^k)^ = k!/(iζ)^{k+1} + π i^k δ^{(k)}` of the truncated power (Gel'fand--Shilov). -/
def truncatedPowerFourier (k : ℕ) (ζ : ℝ) : ℂ :=
  (k.factorial : ℂ) / (Complex.I * (ζ : ℂ)) ^ (k + 1)

/-- The Gaussian window `G(z) = exp (-z²/2)` used to construct admissible ridgelet functions in
Section 6.2. -/
def gaussianWindow (z : ℝ) : ℂ :=
  (Real.exp (-z ^ 2 / 2) : ℂ)

/-! ## Main results

Each statement records the corresponding theorem-like environment of `1505.03654v2`.
-/

/-- Section 3.1 and the `L¹ × (L^p ∩ C⁰)` row of the balancing theorem `thm:existence`, strong
form: for `f ∈ L¹(ℝ^m)` and a bounded continuous `ψ`, the Euclidean ridgelet integral converges
absolutely at every parameter and satisfies `‖R_ψ f (a, b)‖ ≤ ‖f‖₁ ‖ψ‖_∞ ‖a‖^s`. -/
theorem l1_ridgelet_pointwise_convergent_L1_bounded (m : ℕ) [NeZero m] (s : ℝ)
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ} {C : ℝ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∀ z, ‖ψ z‖ ≤ C)
    (p : RidgeletParameterSpace m) :
    Integrable (fun x => f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ))
      volume ∧
    ‖euclideanRidgeletTransform m s ψ f p‖ ≤ (∫ x, ‖f x‖) * C * ‖p.1‖ ^ s := by
  have hr : (0 : ℝ) ≤ ‖p.1‖ ^ s := Real.rpow_nonneg (norm_nonneg _) s
  have hgc : Continuous fun x : InputSpace m =>
      conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ) :=
    ((RCLike.continuous_conj.comp
      (hψc.comp ((continuous_const.inner continuous_id).sub continuous_const))).mul
      continuous_const)
  have hgb : ∀ x : InputSpace m,
      ‖conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖ ≤ C * ‖p.1‖ ^ s := by
    intro x
    have hnr : ‖((‖p.1‖ ^ s : ℝ) : ℂ)‖ = ‖p.1‖ ^ s := by
      simp [abs_of_nonneg hr]
    rw [norm_mul, RCLike.norm_conj, hnr]
    exact mul_le_mul_of_nonneg_right (hψb _) hr
  have hint : Integrable (fun x => f x *
      (conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ))) volume :=
    hf.mul_bdd hgc.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  refine ⟨by simpa [mul_assoc] using hint, ?_⟩
  have hle : ‖euclideanRidgeletTransform m s ψ f p‖ ≤
      ∫ x, ‖f x‖ * (C * ‖p.1‖ ^ s) := by
    simp only [euclideanRidgeletTransform]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (hf.norm.mul_const _) (Filter.Eventually.of_forall fun x => ?_)
    calc ‖f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖
        = ‖f x‖ * ‖conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖ := by
          rw [mul_assoc, norm_mul]
      _ ≤ ‖f x‖ * (C * ‖p.1‖ ^ s) := mul_le_mul_of_nonneg_left (hgb x) (norm_nonneg _)
  refine hle.trans_eq ?_
  rw [integral_mul_const, mul_assoc]

/-- Remark after Definition 4.1: for a locally integrable ridgelet function the weak (Radon)
definition of the ridgelet transform coincides with the strong Euclidean one at `s = 1`, via
`a = u / α`, `b = β / α`. -/
theorem l1_weakRidgeletTransform_eq_euclidean (m : ℕ) [NeZero m]
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    {u : InputSpace m} (hu : ‖u‖ = 1) {α β : ℝ} (hα : 0 < α) :
    weakRidgeletTransform m ψ f u α β =
      euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) := by
  sorry

/-- Balancing theorem `thm:existence`, `L¹ × (L^p ∩ C⁰)` row, range statement: for `f ∈ L¹(ℝ^m)`
and a continuous `ψ ∈ L^p(ℝ)`, the weak ridgelet transform belongs to `L^p` in the shift `β`,
uniformly in the direction `u` and the scale `α`. The remaining rows of `tab:weakridge` require
the distribution classes on `𝕐^{m+1}` and are deferred. -/
theorem l1_balancing_weakRidgeletTransform_memLp (m : ℕ) [NeZero m] (p : ℝ≥0∞)
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψp : MemLp ψ p volume)
    {u : InputSpace m} (hu : ‖u‖ = 1) {α : ℝ} (hα : 0 < α) :
    MemLp (fun β => weakRidgeletTransform m ψ f u α β) p volume := by
  sorry

/-- Proposition 4.2 (`prop:conti.L1`): for a Schwartz ridgelet function with vanishing moments,
the ridgelet transform is bounded from `L¹(ℝ^m)` to `L^∞(𝕐^{m+1})`.

**Paper gap memo (2026-07-19).** The manuscript proof bounds the operator norm by
`sup_{r,β} |r ψ(r β)|`, which is infinite for every `ψ ≠ 0`: fix `z = r β` with `ψ z ≠ 0` and
let `r → ∞`. Following the author's guidance that ridgelet functions customarily carry vanishing
moment conditions, this statement adds the hypotheses `ψ 0 = 0` and the vanishing of all integer
moments `∫ z^k ψ z dz = 0`. A concern that remains to be settled during the proof: for `f` with
an integrable power singularity, e.g. `f (x) = |x|^{-1/2} 𝟙_{|x| ≤ 1}` in `m = 1`, the weak form
gives `R_ψ f (u, α, 0) ≈ α^{-1/2} ∫ |z|^{-1/2} conj (ψ z) dz`, and this fractional moment is not
controlled by the integer vanishing moments, so the essential supremum may still diverge as
`α → 0` (`‖a‖ → ∞`). If so, candidate repairs are: restricting to bounded weights `‖a‖ ≤ r₀`
(scales `α ≥ 1/r₀`), inserting the weight `min 1 ‖a‖⁻¹` into the conclusion, or reading the
statement in the `s = 0` normalization of Section 3, where it holds with constant `‖ψ‖_∞` and
no moment condition. -/
theorem l1_ridgeletTransform_bounded_L1_Linfty (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ)
    (hψ0 : ψ 0 = 0) (hmom : ∀ k : ℕ, ∫ z : ℝ, (z : ℂ) ^ k * ψ z = 0) :
    ∃ C : ℝ, ∀ f : InputSpace m → ℂ, Integrable f volume →
      ∀ᵐ q ∂ridgeletParameterMeasure m,
        ‖euclideanRidgeletTransform m 1 (⇑ψ) f q‖ ≤ C * ∫ x, ‖f x‖ := by
  sorry

/-- Theorem 4.3 (`thm:dual`) at function level: the dual ridgelet transform is the dual operator
of the ridgelet transform with respect to the pairing of `L²(𝕐^{m+1}, ‖a‖⁻² da db)` and
`L²(ℝ^m)`. -/
theorem l1_dualRidgeletTransform_pairing (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ} {T : RidgeletParameterSpace m → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hT : Integrable
      (fun q : RidgeletParameterSpace m => T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume) :
    ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m =
      ∫ x, f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) := by
  sorry

/-- Section 5.1: the Fourier data away from the origin, hence the admissibility constant
`K_{ψ,η}`, is invariant under adding a polynomial to the activation. This is the function-level
form of working in the Lizorkin quotient `𝒮'(ℝ)/polynomials ≅ 𝒮₀'(ℝ)`. -/
theorem l1_hasFourierAwayFromOrigin_add_polynomial
    {η Fη : ℝ → ℂ} (h : HasFourierAwayFromOrigin η Fη) (Q : Polynomial ℂ) :
    HasFourierAwayFromOrigin (fun z => η z + Q.eval (z : ℂ)) Fη := by
  obtain ⟨hloc, hpoly, hFloc, hpair⟩ := h
  have hQc : Continuous fun z : ℝ => Q.eval (z : ℂ) :=
    (Polynomial.continuous Q).comp Complex.continuous_ofReal
  refine ⟨hloc.add hQc.locallyIntegrable,
    hpoly.add (polynomiallyBounded_polynomial_eval Q), hFloc, ?_⟩
  intro φ hφ
  have hηint : Integrable (fun z : ℝ => η z * paperFourier1D (⇑φ) z) volume := by
    rw [paperFourier1D_coe_schwartz]
    exact hpoly.integrable_mul_schwartz hloc.aestronglyMeasurable
      (Fourier.paperFourierSchwartz φ)
  have hQint : Integrable (fun z : ℝ => Q.eval (z : ℂ) * paperFourier1D (⇑φ) z) volume := by
    rw [paperFourier1D_coe_schwartz]
    exact (polynomiallyBounded_polynomial_eval Q).integrable_mul_schwartz
      hQc.aestronglyMeasurable (Fourier.paperFourierSchwartz φ)
  have hsplit : ∫ z : ℝ, (η z + Q.eval (z : ℂ)) * paperFourier1D (⇑φ) z =
      (∫ z : ℝ, η z * paperFourier1D (⇑φ) z) +
        ∫ z : ℝ, Q.eval (z : ℂ) * paperFourier1D (⇑φ) z := by
    rw [← integral_add hηint hQint]
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [hsplit, integral_polynomial_mul_paperFourier1D_eq_zero Q φ hφ, add_zero]
  exact hpair φ hφ

/-- Theorem 5.5 (`thm:eq.ac`), structure theorem for admissible pairs, at function level: given
the Fourier data of `η` away from the origin, with `η̂` continuous near the origin (away from a
possible point mass at `0` corresponding to the polynomial `Q`), the pair `(ψ, η)` is admissible
if and only if the backprojection equation `Λ^m u = conj (ψ~) ⋆ (η - Q)` has a slowly increasing
solution `u` whose Fourier transform away from the origin is integrable with a nonzero
integral. -/
theorem l1_structure_theorem_admissible_pairs (m : ℕ) [NeZero m]
    (ψ : SchwartzMap ℝ ℂ) {η Fη : ℝ → ℂ}
    (hη : HasFourierAwayFromOrigin η Fη)
    (hcont : ∃ ε > 0, ContinuousOn Fη (Set.Ioo (-ε) ε \ {0})) :
    IsAdmissiblePair m (⇑ψ) η Fη ↔
      ∃ (u Fu : ℝ → ℂ) (Q : Polynomial ℂ),
        Function.HasTemperateGrowth u ∧
        HasFourierAwayFromOrigin u Fu ∧
        (∀ z, backprojectionFilter m u z =
          reflectedConjConvolution (⇑ψ) (fun t => η t - Q.eval (t : ℂ)) z) ∧
        IntegrableOn Fu {(0 : ℝ)}ᶜ volume ∧
        (∫ ζ in {(0 : ℝ)}ᶜ, Fu ζ) ≠ 0 := by
  sorry

/-- Corollary 5.6 (`cor:const.ap`), construction of admissible pairs: if `ζ^k η̂ (ζ)` extends
continuously through the origin and `ψ₀` is a Schwartz function with
`∫ ζ^k conj (ψ̂₀ ζ) Fη ζ dζ ≠ 0`, then `ψ = Λ^m ψ₀^{(k)}` is admissible with `η`.

**Paper gap memo (2026-07-19).** The manuscript takes admissible pairs in
`𝒮(ℝ) × 𝒮'(ℝ)`, but for odd `m` the constructed ridgelet `ψ = Λ^m ψ₀^{(k)}` is not Schwartz:
its Fourier transform `i^m |ζ|^m (iζ)^k ψ̂₀ ζ` is continuous and rapidly decreasing yet not
smooth at the origin, so `ψ` itself only decays algebraically (for the Gaussian window the
Hilbert transform produces Dawson-type `O(1/z)` tails, integrable after one derivative). This is
why `IsAdmissiblePair` asks only `Integrable ψ` here; the conclusion below is meaningful and the
manuscript's constructions are covered. -/
theorem l1_construction_of_admissible_pairs (m : ℕ) [NeZero m]
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) (k : ℕ)
    (hcont : ∃ ε > 0, ∃ g : ℝ → ℂ, ContinuousOn g (Set.Ioo (-ε) ε) ∧
      ∀ ζ ∈ Set.Ioo (-ε) ε, ζ ≠ 0 → g ζ = (ζ : ℂ) ^ k * Fη ζ)
    (ψ₀ : SchwartzMap ℝ ℂ)
    (hint : IntegrableOn
      (fun ζ : ℝ => (ζ : ℂ) ^ k * conj (paperFourier1D (⇑ψ₀) ζ) * Fη ζ) {(0 : ℝ)}ᶜ volume)
    (hne : (∫ ζ in {(0 : ℝ)}ᶜ,
      (fun ζ : ℝ => (ζ : ℂ) ^ k * conj (paperFourier1D (⇑ψ₀) ζ) * Fη ζ) ζ) ≠ 0) :
    IsAdmissiblePair m (backprojectionFilter m (iteratedDeriv k (⇑ψ₀))) η Fη := by
  sorry

/-- Theorem 5.7 (`thm:formula`), the reconstruction formula: for `f ∈ L¹(ℝ^m)` with
`f̂ ∈ L¹(ℝ^m)` and an admissible pair `(ψ, η)`, the truncated dual ridgelet transform of
`R_ψ f` converges to `K_{ψ,η} f (x)` at almost every `x` and at every continuity point of
`f`. -/
theorem l1_reconstruction_formula (m : ℕ) [NeZero m]
    {ψ η Fη : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hadm : IsAdmissiblePair m ψ η Fη)
    (hf : Integrable f volume)
    (hfhat : Integrable (Fourier.paperFourierIntegralInner f) volume) :
    (∀ᵐ x ∂(volume : Measure (InputSpace m)),
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          truncatedDualRidgeletTransform m 1 η
            (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
        ridgeletTruncationFilter (𝓝 (admissibilityConstant m ψ Fη * f x))) ∧
    ∀ x, ContinuousAt f x →
      Filter.Tendsto
        (fun q : ℝ × ℝ =>
          truncatedDualRidgeletTransform m 1 η
            (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
        ridgeletTruncationFilter (𝓝 (admissibilityConstant m ψ Fη * f x)) := by
  sorry

/-- Theorem 5.8 (`thm:formula.radon`), the reconstruction formula via the Radon transform,
stated for Schwartz functions: if a real-valued smooth integrable `u` satisfies the
backprojection equation `Λ^m u = conj (ψ~) ⋆ η` with the normalization `∫ û = -1`
(`eq:radon.ac`), then the reconstruction operator acts as the filtered backprojection
`R† Λ^{m-1} R = 2 (2π)^{m-1} Id`. The first conjunct is Radon's inversion formula, which the
manuscript uses as a known result. -/
theorem l1_reconstruction_formula_radon (m : ℕ) [NeZero m]
    {ψ η u : ℝ → ℂ} (f : SchwartzMap (InputSpace m) ℂ)
    (hψ : Integrable ψ volume) (hη : PolynomiallyBounded η)
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u) (hu_real : ∀ z, (u z).im = 0)
    (hu_int : Integrable u volume)
    (hbp : ∀ z, backprojectionFilter m u z = reflectedConjConvolution ψ η z)
    (hnorm : (∫ ζ, paperFourier1D u ζ) = -1) :
    (∀ x, dualRadonTransform m
        (fun v => backprojectionFilter (m - 1) (radonTransform m (⇑f) v)) x =
      ((2 * (2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x) ∧
    ∀ x, Filter.Tendsto
      (fun q : ℝ × ℝ =>
        truncatedDualRidgeletTransform m 1 η
          (euclideanRidgeletTransform m 1 ψ (⇑f)) q.1 q.2 x)
      ridgeletTruncationFilter
      (𝓝 (((2 * (2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x)) := by
  sorry

/-- Theorem 5.9 (`thm:parseval`), Parseval's relation: for an admissible pair normalized by
`K_{ψ,η} = 1` with a bounded continuous activation, and `f, g ∈ L¹ ∩ L²(ℝ^m)`,
`⟨R_ψ f, R_η g⟩_{L²(𝕐^{m+1})} = ⟨f, g⟩_{L²(ℝ^m)}`. -/
theorem l1_parseval_relation (m : ℕ) [NeZero m]
    {ψ η Fη : ℝ → ℂ} {f g : InputSpace m → ℂ}
    (hadm : IsAdmissiblePair m ψ η Fη)
    (hK : admissibilityConstant m ψ Fη = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    ∫ q, euclideanRidgeletTransform m 1 ψ f q *
        conj (euclideanRidgeletTransform m 1 η g q) ∂ridgeletParameterMeasure m =
      ∫ x, f x * conj (g x) := by
  sorry

/-- Theorem 5.9 (`thm:parseval`), Plancherel's identity: for a self-admissible `ψ` normalized by
`K_{ψ,ψ} = 1` and `f ∈ L¹ ∩ L²(ℝ^m)`, the ridgelet transform is an `L²`-isometry:
`‖R_ψ f‖_{L²(𝕐^{m+1})} = ‖f‖₂`. -/
theorem l1_plancherel_identity (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (paperFourier1D ψ) = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    ∫ q, ‖euclideanRidgeletTransform m 1 ψ f q‖ ^ 2 ∂ridgeletParameterMeasure m =
      ∫ x, ‖f x‖ ^ 2 := by
  sorry

/-- Theorem 5.10 (`thm:L2`), bounded extension of the ridgelet transform to `L²(ℝ^m)`: for a
self-admissible `ψ` with `K_{ψ,ψ} = 1`, there is a unique bounded operator
`L²(ℝ^m) → L²(𝕐^{m+1})` that agrees with the integral transform on `L¹ ∩ L²(ℝ^m)`, and it is an
isometry. -/
theorem l1_ridgeletTransform_L2_extension (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hself : IsSelfAdmissible m ψ)
    (hK : admissibilityConstant m ψ (paperFourier1D ψ) = 1) :
    ∃! R : TargetSpace m →L[ℂ] Lp ℂ 2 (ridgeletParameterMeasure m),
      (∀ f : TargetSpace m, Integrable (⇑f) volume →
        (⇑(R f) : RidgeletParameterSpace m → ℂ) =ᵐ[ridgeletParameterMeasure m]
          euclideanRidgeletTransform m 1 ψ (⇑f)) ∧
      ∀ f : TargetSpace m, ‖R f‖ = ‖f‖ := by
  sorry

/-- Theorem 5.11 (`thm:formula.L2`), the reconstruction formula in `L²`: for an admissibly
decomposable pair with `K_{ψ,η} = 1` and `f ∈ L¹ ∩ L²(ℝ^m)`, the truncated reconstruction
converges to `f` in `L²(ℝ^m)`. Together with `l1_ridgeletTransform_L2_extension` this expresses
the compatibility of the L1 and L2 reconstructions on `L¹ ∩ L²`; the version for general
`f ∈ L²(ℝ^m)` follows by the bounded extension and is part of the same milestone. -/
theorem l1_reconstruction_formula_L2 (m : ℕ) [NeZero m]
    {ψ η Fη : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hdec : IsAdmissiblyDecomposable m ψ η Fη)
    (hK : admissibilityConstant m ψ Fη = 1)
    (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hηc : Continuous η) (hηb : ∃ C, ∀ z, ‖η z‖ ≤ C)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Filter.Tendsto
      (fun q : ℝ × ℝ =>
        eLpNorm
          (fun x =>
            truncatedDualRidgeletTransform m 1 η
              (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x - f x) 2 volume)
      ridgeletTruncationFilter (𝓝 0) := by
  sorry

/-- Section 6.1 with Gel'fand--Shilov: the truncated power `z₊^k` (step function, ReLU, ...) is
a Lizorkin distribution whose Fourier transform away from the origin is the function
`k! / (iζ)^{k+1}`; the point mass `π i^k δ^{(k)}` at the origin is invisible away from `0`. -/
theorem l1_truncatedPower_hasFourierAwayFromOrigin (k : ℕ) :
    HasFourierAwayFromOrigin (truncatedPower k) (truncatedPowerFourier k) := by
  sorry

/-- Section 6.2: the truncated power `z₊^k` is admissible with the Gaussian-derivative ridgelet
function `ψ = Λ^m G^{(ℓ+k+1)}` for every even `ℓ`. -/
theorem l1_truncatedPower_admissible (m : ℕ) [NeZero m] (k ℓ : ℕ) (hℓ : Even ℓ) :
    IsAdmissiblePair m
      (backprojectionFilter m (iteratedDeriv (ℓ + k + 1) gaussianWindow))
      (truncatedPower k) (truncatedPowerFourier k) := by
  sorry

/-- Headline corollary of the L1 theory: neural networks with the unbounded ReLU activation are
universal approximators. For every `f ∈ L¹(ℝ^m)` with `f̂ ∈ L¹(ℝ^m)` there exist an integrable
ridgelet function `ψ` and a nonzero constant `K` such that the network
`x ↦ ∫ R_ψ f (a, b) relu (⟪a, x⟫ - b) ‖a‖⁻¹ da db` reconstructs `K f`. -/
theorem l1_relu_network_universal_approximation (m : ℕ) [NeZero m]
    {f : InputSpace m → ℂ} (hf : Integrable f volume)
    (hfhat : Integrable (Fourier.paperFourierIntegralInner f) volume) :
    ∃ (ψ : ℝ → ℂ) (K : ℂ), Integrable ψ volume ∧ K ≠ 0 ∧
      ∀ᵐ x ∂(volume : Measure (InputSpace m)),
        Filter.Tendsto
          (fun q : ℝ × ℝ =>
            truncatedDualRidgeletTransform m 1 (truncatedPower 1)
              (euclideanRidgeletTransform m 1 ψ f) q.1 q.2 x)
          ridgeletTruncationFilter (𝓝 (K * f x)) := by
  sorry

end LeanRidgelet
