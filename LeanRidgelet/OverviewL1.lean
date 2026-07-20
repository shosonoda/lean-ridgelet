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
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.MeasureTheory.Group.Integral
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

/-! ## Fourier data of the truncated powers

The pairing identity of `l1_truncatedPower_hasFourierAwayFromOrigin` is proved by induction on
the power. The base case computes the half-line integral of a paper Fourier transform through
finite truncations, Fubini's theorem, and the Riemann--Lebesgue lemma; the inductive step
trades one power of `z` for one derivative of the test function and integrates by parts on the
real line.
-/

/-- A test function supported away from the origin is uniformly separated from it. -/
theorem exists_pos_le_abs_of_tsupport_subset {g : ℝ → ℂ}
    (hg : tsupport g ⊆ {(0 : ℝ)}ᶜ) :
    ∃ δ > (0 : ℝ), ∀ ζ ∈ tsupport g, δ ≤ |ζ| := by
  have hmem : (0 : ℝ) ∈ (tsupport g)ᶜ := fun h => hg h rfl
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_tsupport g).isOpen_compl 0 hmem
  refine ⟨δ, hδ, fun ζ hζ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hball (by simpa [Real.dist_eq] using hlt) hζ

/-- Multiplying an integrable function by a factor bounded on its support preserves
integrability. -/
theorem integrable_mul_of_bound_on_tsupport {c g : ℝ → ℂ} {C : ℝ}
    (hc : AEStronglyMeasurable c volume) (hg : Integrable g volume)
    (hbound : ∀ ζ ∈ tsupport g, ‖c ζ‖ ≤ C) :
    Integrable (fun ζ => c ζ * g ζ) volume := by
  refine Integrable.mono' (hg.norm.const_mul C)
    (hc.mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun ζ => ?_)
  by_cases hζ : ζ ∈ tsupport g
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound ζ hζ) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hζ]
    simp

/-- The paper-convention derivative rule for Schwartz functions: `(φ')^ (ζ) = i ζ φ̂ (ζ)`. -/
theorem paperFourier1D_deriv (φ : SchwartzMap ℝ ℂ) :
    paperFourier1D (deriv (⇑φ)) =
      fun ζ : ℝ => Complex.I * (ζ : ℂ) * paperFourier1D (⇑φ) ζ := by
  have hbridge : ∀ (g : ℝ → ℂ) (ζ : ℝ),
      paperFourier1D g ζ = 𝓕 g ((2 * Real.pi)⁻¹ • ζ) := by
    intro g ζ
    unfold paperFourier1D
    rw [Fourier.paperFourierIntegralInner_eq_mathlib]
    rfl
  have hd : Integrable (deriv (⇑φ)) volume :=
    SchwartzMap.integrable (SchwartzMap.derivCLM ℂ ℂ φ)
  have hder := Real.fourier_deriv (SchwartzMap.integrable φ) φ.differentiable hd
  funext ζ
  rw [hbridge (deriv (⇑φ)) ζ, hder, hbridge (⇑φ) ζ]
  simp only [smul_eq_mul]
  have hsc : (2 * (Real.pi : ℂ) * Complex.I * (((2 * Real.pi)⁻¹ * ζ : ℝ) : ℂ)) =
      Complex.I * (ζ : ℂ) := by
    push_cast
    field_simp
  rw [← hsc]

/-- Half-line integral of the paper Fourier transform of a Schwartz function supported away
from the origin: `∫_{0}^{∞} φ̂(z) dz = ∫ (iζ)⁻¹ φ(ζ) dζ`. This is the step-function
(`k = 0`) case of the Gel'fand--Shilov pairing. -/
theorem setIntegral_Ioi_paperFourier1D (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ z in Set.Ioi (0 : ℝ), paperFourier1D (⇑φ) z =
      ∫ ζ : ℝ, (Complex.I * (ζ : ℂ))⁻¹ * φ ζ := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_abs_of_tsupport_subset hφ
  set h : ℝ → ℂ := fun ζ => (Complex.I * (ζ : ℂ))⁻¹ * φ ζ with hh_def
  have hkermeas : AEStronglyMeasurable (fun ζ : ℝ => (Complex.I * (ζ : ℂ))⁻¹) volume :=
    ((Complex.measurable_ofReal.const_mul Complex.I).inv).aestronglyMeasurable
  have hkerbound : ∀ ζ ∈ tsupport ⇑φ, ‖(Complex.I * (ζ : ℂ))⁻¹‖ ≤ δ⁻¹ := by
    intro ζ hζ
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact inv_anti₀ hδ (hsep ζ hζ)
  have hint : Integrable h volume :=
    integrable_mul_of_bound_on_tsupport hkermeas (SchwartzMap.integrable φ) hkerbound
  have hexpnorm : ∀ w : ℂ, w.re = 0 → ‖Complex.exp w‖ = 1 := by
    intro w hw
    rw [Complex.norm_exp, hw, Real.exp_zero]
  have hint2 : ∀ R : ℝ,
      Integrable (fun ζ : ℝ => Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ) volume := by
    intro R
    refine hint.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · refine le_of_eq (hexpnorm _ ?_)
      simp [Complex.mul_re]
  -- the truncated identity
  have happly : ∀ z : ℝ, paperFourier1D (⇑φ) z =
      ∫ ζ : ℝ, Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ := by
    intro z
    rw [paperFourier1D_coe_schwartz]
    exact Fourier.paperFourierSchwartz_apply φ z
  have htrunc : ∀ R : ℝ, 0 ≤ R →
      ∫ z in (0 : ℝ)..R, paperFourier1D (⇑φ) z =
        (∫ ζ : ℝ, h ζ) -
          ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
    intro R hR
    have hF : Integrable
        (Function.uncurry fun (z ζ : ℝ) => Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ)
        ((volume.restrict (Set.Ioc 0 R)).prod volume) := by
      have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) R) volume :=
        integrableOn_const (by simp)
      have hdom : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖φ p.2‖)
          ((volume.restrict (Set.Ioc 0 R)).prod volume) :=
        Integrable.mul_prod hone (SchwartzMap.integrable φ).norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · rw [Function.uncurry_apply_pair, norm_mul, hexpnorm _ (by simp [Complex.mul_re]),
          one_mul]
    calc ∫ z in (0 : ℝ)..R, paperFourier1D (⇑φ) z
        = ∫ z in Set.Ioc (0 : ℝ) R,
            ∫ ζ : ℝ, Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ := by
          rw [intervalIntegral.integral_of_le hR]
          exact integral_congr_ae (Filter.Eventually.of_forall fun z => happly z)
      _ = ∫ ζ : ℝ, ∫ z in Set.Ioc (0 : ℝ) R,
            Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ :=
          integral_integral_swap hF
      _ = ∫ ζ : ℝ, (∫ z in Set.Ioc (0 : ℝ) R,
            Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ)))) * φ ζ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
          simp only [integral_mul_const]
      _ = (∫ ζ : ℝ, h ζ) -
            ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
          rw [← integral_sub hint (hint2 R)]
          refine integral_congr_ae ?_
          have h0 : ∀ᵐ ζ : ℝ ∂volume, ζ ≠ 0 := by
            refine ae_iff.mpr ?_
            simp
          filter_upwards [h0] with ζ hζ0
          have hc : (-Complex.I * (ζ : ℂ)) ≠ 0 := by
            simp [Complex.ext_iff, hζ0]
          have hker : (∫ z in Set.Ioc (0 : ℝ) R,
              Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ)))) =
              (Complex.exp (-Complex.I * (ζ : ℂ) * (R : ℂ)) - 1) / (-Complex.I * (ζ : ℂ)) := by
            rw [← intervalIntegral.integral_of_le hR]
            have hcongr : ∀ z ∈ Set.uIcc (0 : ℝ) R,
                Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) =
                  Complex.exp ((-Complex.I * (ζ : ℂ)) * (z : ℂ)) := by
              intro z _
              ring_nf
            rw [intervalIntegral.integral_congr hcongr, integral_exp_mul_complex hc]
            simp [mul_comm]
          rw [hker, hh_def]
          have hIζ : (Complex.I * (ζ : ℂ)) ≠ 0 := by
            simp [Complex.ext_iff, hζ0]
          field_simp
          ring_nf
  -- limits as `R → ∞`
  have hlhs : Filter.Tendsto (fun R : ℝ => ∫ z in (0 : ℝ)..R, paperFourier1D (⇑φ) z)
      Filter.atTop (𝓝 (∫ z in Set.Ioi (0 : ℝ), paperFourier1D (⇑φ) z)) := by
    refine intervalIntegral_tendsto_integral_Ioi 0 ?_ Filter.tendsto_id
    rw [paperFourier1D_coe_schwartz]
    exact (SchwartzMap.integrable _).integrableOn
  have hbridge : ∀ (g : ℝ → ℂ) (ζ : ℝ),
      paperFourier1D g ζ = 𝓕 g ((2 * Real.pi)⁻¹ • ζ) := by
    intro g ζ
    unfold paperFourier1D
    rw [Fourier.paperFourierIntegralInner_eq_mathlib]
    rfl
  have hrl : Filter.Tendsto
      (fun R : ℝ => ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ)
      Filter.atTop (𝓝 0) := by
    have hid : ∀ R : ℝ,
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ = paperFourier1D h R := by
      intro R
      unfold paperFourier1D Fourier.paperFourierIntegralInner
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    have hcomp : Filter.Tendsto (fun R : ℝ => (2 * Real.pi)⁻¹ • R)
        Filter.atTop (Filter.cocompact ℝ) := by
      have h1 : Filter.Tendsto (fun R : ℝ => (2 * Real.pi)⁻¹ • R)
          Filter.atTop Filter.atTop := by
        simpa [smul_eq_mul] using
          (Filter.tendsto_id (α := ℝ)).const_mul_atTop
            (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)
      refine h1.mono_right ?_
      rw [cocompact_eq_atBot_atTop]
      exact le_sup_right
    have := (Real.zero_at_infty_fourier h).comp hcomp
    refine this.congr fun R => ?_
    rw [Function.comp_apply, ← hbridge h R, hid R]
  have hrhs : Filter.Tendsto
      (fun R : ℝ => (∫ ζ : ℝ, h ζ) -
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ)
      Filter.atTop (𝓝 ((∫ ζ : ℝ, h ζ) - 0)) :=
    tendsto_const_nhds.sub hrl
  have heq : (fun R : ℝ => ∫ z in (0 : ℝ)..R, paperFourier1D (⇑φ) z) =ᶠ[Filter.atTop]
      fun R : ℝ => (∫ ζ : ℝ, h ζ) -
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    exact htrunc R hR
  have hfinal := tendsto_nhds_unique (hlhs.congr' heq) hrhs
  simpa [hh_def] using hfinal

/-- The Gel'fand--Shilov pairing for truncated powers: for a Schwartz test function supported
away from the origin, `∫ k!/(iζ)^{k+1} φ(ζ) dζ = ∫_{0}^{∞} z^k φ̂(z) dz`. -/
theorem truncatedPowerFourier_pairing (k : ℕ) (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ ζ =
      ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * paperFourier1D (⇑φ) z := by
  induction k generalizing φ with
  | zero =>
    have h0 := setIntegral_Ioi_paperFourier1D φ hφ
    simp only [truncatedPowerFourier, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
      pow_zero, one_mul, one_div]
    exact h0.symm
  | succ k ih =>
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_abs_of_tsupport_subset hφ
    set φ' : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ with hφ'_def
    have hcoe : ⇑φ' = deriv (⇑φ) := rfl
    have hφ'supp : tsupport ⇑φ' ⊆ {(0 : ℝ)}ᶜ := by
      rw [hcoe]
      exact tsupport_deriv_subset.trans hφ
    have hmeasT : ∀ n : ℕ, AEStronglyMeasurable (truncatedPowerFourier n) volume := by
      intro n
      refine Measurable.aestronglyMeasurable ?_
      unfold truncatedPowerFourier
      exact measurable_const.div ((Complex.measurable_ofReal.const_mul Complex.I).pow_const _)
    have hbound : ∀ n : ℕ, ∀ ζ ∈ tsupport ⇑φ,
        ‖truncatedPowerFourier n ζ‖ ≤ (n.factorial : ℝ) / δ ^ (n + 1) := by
      intro n ζ hζ
      have hδζ : δ ≤ |ζ| := hsep ζ hζ
      simp only [truncatedPowerFourier]
      rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_natCast]
      have h1 : (0 : ℝ) < δ ^ (n + 1) := pow_pos hδ _
      have h2 : δ ^ (n + 1) ≤ |ζ| ^ (n + 1) := pow_le_pow_left₀ hδ.le hδζ _
      gcongr
      exact hδζ
    -- integration by parts: `∫ T_{k+1} φ = -i ∫ T_k φ'`
    have hu : ∀ ζ ∈ tsupport ⇑φ,
        HasDerivAt (truncatedPowerFourier k)
          ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ) ζ := by
      intro ζ hζ
      have hζ0 : ζ ≠ 0 := by simpa using hφ hζ
      have hIζ : Complex.I * Complex.ofRealCLM ζ ≠ 0 := by
        simp [Complex.ext_iff, hζ0]
      have h4 := ((((Complex.ofRealCLM.hasDerivAt (x := ζ)).const_mul Complex.I).pow
        (k + 1)).inv (pow_ne_zero _ hIζ)).const_mul ((k.factorial : ℕ) : ℂ)
      have hF : truncatedPowerFourier k =ᶠ[𝓝 ζ] fun y : ℝ =>
          ((k.factorial : ℕ) : ℂ) * ((fun t : ℝ =>
            (Complex.I * Complex.ofRealCLM t) ^ (k + 1)) y)⁻¹ := by
        filter_upwards with t
        simp [truncatedPowerFourier, div_eq_mul_inv]
      have h5 := h4.congr_of_eventuallyEq hF
      have hIζ' : (Complex.I * (ζ : ℂ)) ≠ 0 := by
        simp [Complex.ext_iff, hζ0]
      have hval : ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ) =
          ((k.factorial : ℕ) : ℂ) *
            (-(((k + 1 : ℕ) : ℂ) * (Complex.I * Complex.ofRealCLM ζ) ^ (k + 1 - 1) *
              (Complex.I * Complex.ofRealCLM 1)) /
              ((fun y : ℝ => Complex.I * Complex.ofRealCLM y) ^ (k + 1)) ζ ^ 2) := by
        simp only [truncatedPowerFourier, Complex.ofRealCLM_apply, Pi.pow_apply,
          Nat.add_sub_cancel, Complex.ofReal_one, mul_one]
        push_cast [Nat.factorial_succ]
        field_simp
        ring
      rw [hval]
      exact h5
    have hv : ∀ ζ ∈ tsupport (truncatedPowerFourier k),
        HasDerivAt (⇑φ) (deriv (⇑φ) ζ) ζ :=
      fun ζ _ => (φ.differentiable ζ).hasDerivAt
    have hint1 : Integrable (truncatedPowerFourier k * deriv (⇑φ)) volume := by
      have := integrable_mul_of_bound_on_tsupport (hmeasT k)
        (hcoe ▸ SchwartzMap.integrable φ' : Integrable (deriv (⇑φ)) volume)
        (fun ζ hζ => hbound k ζ (tsupport_deriv_subset hζ))
      exact this
    have hint2 : Integrable
        ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) * ⇑φ) volume := by
      have := integrable_mul_of_bound_on_tsupport
        (((hmeasT (k + 1)).const_mul (-Complex.I)))
        (SchwartzMap.integrable φ)
        (fun ζ hζ => by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
          exact hbound (k + 1) ζ hζ)
      exact this
    have hint3 : Integrable (truncatedPowerFourier k * ⇑φ) volume := by
      have := integrable_mul_of_bound_on_tsupport (hmeasT k)
        (SchwartzMap.integrable φ) (hbound k)
      exact this
    have hibp0 := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv hint1 hint2 hint3
    have hpull : ∫ ζ : ℝ, (fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      ring
    have hibp : ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ' ζ := by
      have h5 : ∫ ζ : ℝ, truncatedPowerFourier k ζ * deriv (⇑φ) ζ
          = Complex.I * ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ := by
        rw [hibp0, hpull]
        ring
      rw [← hcoe] at h5
      rw [h5, ← mul_assoc]
      simp [Complex.I_mul_I]
    -- the derivative shift on the Fourier side
    have hstep : -Complex.I * ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * paperFourier1D (⇑φ') z
        = ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ (k + 1) * paperFourier1D (⇑φ) z := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      have hd : paperFourier1D (⇑φ') z = Complex.I * (z : ℂ) * paperFourier1D (⇑φ) z := by
        rw [hcoe, paperFourier1D_deriv φ]
      simp only [hd]
      have hII : -Complex.I * Complex.I = 1 := by simp [Complex.I_mul_I]
      calc -Complex.I * ((z : ℂ) ^ k * (Complex.I * (z : ℂ) * paperFourier1D (⇑φ) z))
          = (-Complex.I * Complex.I) * ((z : ℂ) ^ (k + 1) * paperFourier1D (⇑φ) z) := by
            ring
        _ = (z : ℂ) ^ (k + 1) * paperFourier1D (⇑φ) z := by rw [hII, one_mul]
    calc ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ' ζ := hibp
      _ = -Complex.I * ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * paperFourier1D (⇑φ') z := by
          rw [ih φ' hφ'supp]
      _ = ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ (k + 1) * paperFourier1D (⇑φ) z := hstep

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
  obtain ⟨C, hψC⟩ := hψb
  have hα' : α ≠ 0 := ne_of_gt hα
  -- the Euclidean integrand with the constants factored out
  set g : InputSpace m → ℂ := fun x =>
    f x * conj (ψ ((inner ℝ u x - β) / α)) with hg_def
  set F : ℝ → ℂ := fun p =>
    radonTransform m f u p * conj (ψ ((p - β) / α)) with hF_def
  have hgint : Integrable g volume := by
    refine hf.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (RCLike.continuous_conj.comp
        (hψc.comp (by fun_prop))).aestronglyMeasurable
    · rw [RCLike.norm_conj]
      exact hψC _
  -- the measure-preserving orthogonal splitting `(p, y) ↦ p • u + y`
  let j : ℝ ≃ₗᵢ[ℝ] ↥(ℝ ∙ u) := LinearIsometryEquiv.toSpanUnitSingleton u hu
  let Ψ : WithLp 2 (ℝ × ↥((ℝ ∙ u)ᗮ)) ≃ₗᵢ[ℝ] InputSpace m :=
    (LinearIsometryEquiv.withLpProdCongr 2 j
      (LinearIsometryEquiv.refl ℝ ↥((ℝ ∙ u)ᗮ))).trans
      (ℝ ∙ u).orthogonalDecomposition.symm
  let M : (ℝ × ↥((ℝ ∙ u)ᗮ)) ≃ᵐ InputSpace m :=
    (MeasurableEquiv.toLp 2 (ℝ × ↥((ℝ ∙ u)ᗮ))).trans Ψ.toMeasurableEquiv
  have hM : ∀ py : ℝ × ↥((ℝ ∙ u)ᗮ), M py = py.1 • u + (py.2 : InputSpace m) := by
    intro py
    change Ψ (WithLp.toLp 2 py) = _
    simp [Ψ, j, LinearIsometryEquiv.withLpProdCongr]
  have hmp : MeasurePreserving (⇑M)
      (volume : Measure (ℝ × ↥((ℝ ∙ u)ᗮ))) (volume : Measure (InputSpace m)) :=
    (Ψ.measurePreserving).comp (WithLp.volume_preserving_toLp ℝ ↥((ℝ ∙ u)ᗮ))
  -- the inner integral over the orthogonal complement
  have hip : ∀ (p : ℝ) (y : ↥((ℝ ∙ u)ᗮ)),
      inner ℝ u ((p • u + (y : InputSpace m)) : InputSpace m) = p := by
    intro p y
    have hy : inner ℝ u (y : InputSpace m) = 0 :=
      ((Submodule.mem_orthogonal (ℝ ∙ u) (y : InputSpace m)).mp y.2) u
        (Submodule.mem_span_singleton_self u)
    rw [inner_add_right, real_inner_smul_right, hy, real_inner_self_eq_norm_sq, hu]
    simp
  have hinner : ∀ p : ℝ, (∫ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m))) = F p := by
    intro p
    have hcongr : ∀ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m)) =
          f (p • u + (y : InputSpace m)) * conj (ψ ((p - β) / α)) := by
      intro y
      simp only [hg_def, hip p y]
    calc (∫ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m)))
        = ∫ y : ↥((ℝ ∙ u)ᗮ),
            f (p • u + (y : InputSpace m)) * conj (ψ ((p - β) / α)) :=
          integral_congr_ae (Filter.Eventually.of_forall hcongr)
      _ = (∫ y : ↥((ℝ ∙ u)ᗮ), f (p • u + (y : InputSpace m))) * conj (ψ ((p - β) / α)) :=
          integral_mul_const _ _
      _ = F p := rfl
  -- Fubini through the splitting
  have hFg : ∫ p : ℝ, F p = ∫ x, g x := by
    have hcomp : ∫ x, g x = ∫ py : ℝ × ↥((ℝ ∙ u)ᗮ), g (M py) :=
      (hmp.integral_comp M.measurableEmbedding g).symm
    have hint : Integrable (fun py : ℝ × ↥((ℝ ∙ u)ᗮ) => g (M py)) volume := by
      have := (hmp.integrable_comp_emb M.measurableEmbedding (g := g)).mpr hgint
      exact this
    rw [hcomp]
    rw [Measure.volume_eq_prod] at hint ⊢
    rw [MeasureTheory.integral_prod _ hint]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)).symm
    rw [← hinner p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change g (M (p, y)) = g (p • u + (y : InputSpace m))
    rw [hM (p, y)]
  -- affine change of variables in the radial variable
  have hsub : ∫ z : ℝ, F (α * z + β) = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := by
    calc ∫ z : ℝ, F (α * z + β)
        = ∫ z : ℝ, (fun w : ℝ => F (w + β)) (α • z) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp [smul_eq_mul]
      _ = |(α ^ Module.finrank ℝ ℝ)⁻¹| • ∫ w : ℝ, F (w + β) :=
          Measure.integral_comp_smul volume (fun w : ℝ => F (w + β)) α
      _ = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := by
          rw [integral_add_right_eq_self (μ := volume) F β]
          congr 1
          rw [Module.finrank_self, pow_one, abs_inv, abs_of_pos hα]
  -- the Euclidean side with the constants factored out
  have hrhs : euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) =
      (α⁻¹ : ℝ) • ∫ x, g x := by
    have hna : (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) = ((α⁻¹ : ℝ) : ℂ) := by
      rw [Real.rpow_one, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hα)]
    have hpt : ∀ x : InputSpace m,
        f x * conj (ψ (inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α)) *
            (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) = ((α⁻¹ : ℝ) : ℂ) * g x := by
      intro x
      have harg : inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α =
          (inner ℝ u x - β) / α := by
        rw [real_inner_smul_left]
        field_simp
      rw [hna, hg_def, harg]
      ring
    calc euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α)
        = ∫ x, f x * conj (ψ (inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α)) *
            (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) := rfl
      _ = ∫ x, ((α⁻¹ : ℝ) : ℂ) * g x :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ((α⁻¹ : ℝ) : ℂ) * ∫ x, g x := integral_const_mul _ _
      _ = (α⁻¹ : ℝ) • ∫ x, g x := by rw [Complex.real_smul]
  -- assemble
  have hweak : ∀ z : ℝ,
      radonTransform m f u (α * z + β) * conj (ψ z) = F (α * z + β) := by
    intro z
    have hz : (α * z + β - β) / α = z := by field_simp; ring
    rw [hF_def]
    simp only [hz]
  calc weakRidgeletTransform m ψ f u α β
      = ∫ z : ℝ, F (α * z + β) := by
        unfold weakRidgeletTransform
        exact integral_congr_ae (Filter.Eventually.of_forall hweak)
    _ = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := hsub
    _ = (α⁻¹ : ℝ) • ∫ x, g x := by rw [hFg]
    _ = euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) := hrhs.symm

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
  obtain ⟨C, hψC⟩ := hψb
  set g : RidgeletParameterSpace m → ℂ := fun q => T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹ with hg_def
  set K : RidgeletParameterSpace m → InputSpace m → ℂ := fun q x =>
    f x * conj (ψ (inner ℝ q.1 x - q.2)) * conj (g q) with hK_def
  -- almost every parameter has a nonzero weight component
  have hae : ∀ᵐ q : RidgeletParameterSpace m ∂volume, q.1 ≠ 0 := by
    rw [ae_iff]
    have hset : {q : RidgeletParameterSpace m | ¬ q.1 ≠ 0} =
        ({0} : Set (InputSpace m)) ×ˢ (Set.univ : Set ℝ) := by
      ext q
      simp [Set.mem_prod]
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  -- unfold the weighted parameter measure
  have hwmeas : Measurable fun q : RidgeletParameterSpace m =>
      ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.norm.pow_const 2).inv)
  have hstep1 :
      ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m =
        ∫ q : RidgeletParameterSpace m,
          ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) := by
    unfold ridgeletParameterMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hwmeas
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (by positivity)]
  -- pointwise identity in the parameter variable
  have hq : ∀ᵐ q : RidgeletParameterSpace m ∂volume,
      ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) =
        ∫ x, K q x := by
    filter_upwards [hae] with q hq1
    have hna : (‖q.1‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hq1
    simp only [euclideanRidgeletTransform, Real.rpow_one, hK_def]
    rw [Complex.real_smul, mul_comm ((((‖q.1‖ ^ 2)⁻¹ : ℝ) : ℂ))
      ((∫ x, f x * conj (ψ (inner ℝ q.1 x - q.2)) * ((‖q.1‖ : ℝ) : ℂ)) * conj (T q)),
      mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg_def, map_mul, map_inv₀, Complex.conj_ofReal]
    have hcne : ((‖q.1‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hna
    push_cast
    field_simp
  -- integrability of the kernel on the product space
  have hKint : Integrable (Function.uncurry K)
      ((volume : Measure (RidgeletParameterSpace m)).prod
        (volume : Measure (InputSpace m))) := by
    have hdom : Integrable (fun p : RidgeletParameterSpace m × InputSpace m =>
        ‖g p.1‖ * (C * ‖f p.2‖))
        ((volume : Measure (RidgeletParameterSpace m)).prod
          (volume : Measure (InputSpace m))) :=
      Integrable.mul_prod hT.norm (hf.norm.const_mul C)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable
          (fun p : RidgeletParameterSpace m × InputSpace m => f p.2)
          ((volume : Measure (RidgeletParameterSpace m)).prod
            (volume : Measure (InputSpace m))) :=
        hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      have h2 : AEStronglyMeasurable
          (fun p : RidgeletParameterSpace m × InputSpace m => conj (g p.1))
          ((volume : Measure (RidgeletParameterSpace m)).prod
            (volume : Measure (InputSpace m))) :=
        (RCLike.continuous_conj.comp_aestronglyMeasurable
          (hT.aestronglyMeasurable.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_fst))
      have h3 : Continuous
          (fun p : RidgeletParameterSpace m × InputSpace m =>
            conj (ψ (inner ℝ p.1.1 p.2 - p.1.2))) := by
        refine RCLike.continuous_conj.comp (hψc.comp ?_)
        exact (Continuous.inner (continuous_fst.fst) continuous_snd).sub
          (continuous_fst.snd)
      exact (h1.mul h3.aestronglyMeasurable).mul h2
    · rw [Function.uncurry_apply_pair, hK_def]
      simp only [norm_mul, RCLike.norm_conj]
      calc ‖f p.2‖ * ‖ψ (inner ℝ p.1.1 p.2 - p.1.2)‖ * ‖g p.1‖
          ≤ ‖f p.2‖ * C * ‖g p.1‖ := by
            have h0 : (0 : ℝ) ≤ ‖g p.1‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hψC _) (norm_nonneg _)) h0
        _ = ‖g p.1‖ * (C * ‖f p.2‖) := by ring
  -- pointwise identity in the input variable
  have hx : ∀ x : InputSpace m,
      ∫ q : RidgeletParameterSpace m, K q x =
        f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) := by
    intro x
    simp only [euclideanDualRidgeletTransform, Real.rpow_one, hK_def]
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hg_def, map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  calc ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m
      = ∫ q : RidgeletParameterSpace m,
          ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) := hstep1
    _ = ∫ q : RidgeletParameterSpace m, ∫ x, K q x := integral_congr_ae hq
    _ = ∫ x, ∫ q : RidgeletParameterSpace m, K q x := integral_integral_swap hKint
    _ = ∫ x, f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) :=
        integral_congr_ae (Filter.Eventually.of_forall hx)

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
  have habs : ∀ z : ℝ, ‖truncatedPower k z‖ ≤ (1 + |z|) ^ k := by
    intro z
    by_cases hz : 0 < z
    · simp only [truncatedPower, if_pos hz, Complex.norm_real, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg z) (le_add_of_nonneg_left zero_le_one) k
    · simp only [truncatedPower, if_neg hz, norm_zero]
      positivity
  have hmeas : Measurable (truncatedPower k) := by
    unfold truncatedPower
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (Complex.measurable_ofReal.comp (measurable_id.pow_const k)) measurable_const
  refine ⟨?_, ⟨1, k, fun z => by simpa using habs z⟩, ?_, ?_⟩
  · -- local integrability of the truncated power
    have hg : MeasureTheory.LocallyIntegrable (fun z : ℝ => ((1 + |z|) ^ k : ℝ)) volume :=
      Continuous.locallyIntegrable (by fun_prop)
    refine hg.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have h1 : (0 : ℝ) ≤ 1 + |z| := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg h1] using habs z
  · -- local integrability of the Fourier data away from the origin
    refine ContinuousOn.locallyIntegrableOn ?_ (measurableSet_singleton (0 : ℝ)).compl
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact Continuous.continuousOn (by fun_prop)
    · intro ζ hζ
      have hζ0 : ζ ≠ 0 := hζ
      exact pow_ne_zero _ (by simp [Complex.ext_iff, hζ0])
  · -- the pairing identity
    intro φ hφ
    rw [truncatedPowerFourier_pairing k φ hφ]
    have h1 : ∫ z : ℝ, truncatedPower k z * paperFourier1D (⇑φ) z =
        ∫ z in Set.Ioi (0 : ℝ), truncatedPower k z * paperFourier1D (⇑φ) z := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      have hz' : ¬ 0 < z := by simpa [Set.mem_Ioi] using hz
      simp [truncatedPower, if_neg hz']
    rw [h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    have hz0 : 0 < z := hz
    simp [truncatedPower, if_pos hz0]

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
