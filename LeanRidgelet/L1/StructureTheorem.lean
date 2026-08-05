/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.FourierData
public import LeanRidgelet.L1.Lizorkin
public import LeanRidgelet.L1.TruncatedPower
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# L1 theory: the structure theorem for admissible pairs (`thm:eq.ac`)

The article characterizes admissibility of `(ψ, η)` by the solvability of the backprojection
equation `Λ^m u = conj (ψ~) ⋆ (η - Q)` with `∫ û ≠ 0`.

## Main results

* `LeanRidgelet.l1_structure_theorem_admissible_pairs`: **`thm:eq.ac`**, the structure theorem
  for admissible pairs, with the backprojection equation read through Fourier data.
* `LeanRidgelet.l1_structure_theorem_sufficiency`,
  `LeanRidgelet.l1_structure_theorem_sufficiency_physical`: the sufficiency half in spectral and
  in physical form, for a Schwartz solution `u`, where the equation is a pointwise identity.
* `LeanRidgelet.l1_isAdmissiblePair_lambdaOperatorPow`: **`cor:const.ap` in sharpened form** —
  a filtered ridgelet function `Λ^m φ` is admissible with `η` *if and only if* `conj (φ̂) Fη` is
  integrable away from the origin with nonzero integral;
  `LeanRidgelet.l1_construction_of_admissible_pairs` is the manuscript's statement
  `ψ = Λ^m ψ₀^{(k)}`.
* `LeanRidgelet.l1_polynomial_not_isAdmissiblePair` and
  `LeanRidgelet.l1_step_not_isAdmissiblePair_lambdaOperatorPow`: Examples 5.2 and 5.3.

## Deviations from the article

* **The backprojection equation is read through Fourier data.** The article writes
  `Λ^m u = conj (ψ~) ⋆ (η - Q)` as a pointwise identity for `u ∈ 𝒪_M`, with `Λ^m` understood as
  the Fourier multiplier `|ζ|^m` — the only reading available there, since the pointwise
  principal value defining `Λ^m` on a slowly increasing function generally diverges (for
  `u(z) = e^{iaz}` already the truncated integral fails to converge absolutely), and converges
  only modulo polynomials when it does. The statement below therefore imposes the equation on
  the Fourier data of both sides, which is well posed at function level and carries the same
  content: the *existence of `u` as a genuine function* with Fourier data `Fu`. The pointwise
  form is kept as `l1_structure_theorem_sufficiency_physical`, where `u` is Schwartz and the
  principal value converges. The manuscript's theorem itself needs no correction: its `Λ^m` is
  the multiplier, and the pointwise formula of `eq:bp` is the representative valid on Schwartz
  functions.
* **`u ∈ 𝒪_M` is weakened to "`u` carries the Fourier data `Fu`".** The witness produced by the
  proof is bounded and continuous (`hasFourierAwayFromOrigin_angularFourierInv`) rather than
  smooth and slowly increasing; smoothness is what the manuscript's duality `𝒪_M ≅ 𝒪'_C`
  supplies and is not needed for any downstream statement.
* **The continuity hypothesis on `Fη` near the origin is dropped.** The manuscript assumes
  `η̂ ∈ C⁰(N \ {0})` in order to produce a bounded `û` near the origin; the function-level
  construction below needs only the integrability already contained in admissibility.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The structure theorem -/

/-- **Theorem 5.4 (`thm:eq.ac`), the structure theorem for admissible pairs**, at function
level: the pair `(ψ, η)` is admissible if and only if the backprojection equation
`Λ^m u = conj (ψ~) ⋆ (η - Q)` is solvable by a function `u` carrying Fourier data `Fu` that is
integrable away from the origin with nonzero integral.

The equation appears in the form "the Fourier data of `conj (ψ~) ⋆ (η - Q)` is `|ζ|^m Fu`",
which is the multiplier reading of `Λ^m u = conj (ψ~) ⋆ (η - Q)`; see the *Deviations* section
of this module. The content of the right-hand side is the existence of `u` **as a function**:
by `hasFourierAwayFromOrigin_reflectedConjConvolution` and `hasFourierAwayFromOrigin_ae_eq` the
second conjunct alone is equivalent to the spectral equation `conj (ψ̂) Fη = |ζ|^m Fu`, which
merely renames the admissibility density, whereas the first conjunct is the function-level
substitute for the manuscript's Fourier duality `𝒪_M ≅ 𝒪'_C`.

Here `Λ^m` is the standard Lambda-operator power (`lambdaOperatorPow`); relative to the
article's filter `eq:bp` this rescales the solution `u` by `i^{-m}`, which affects none of the
stated conditions. -/
theorem l1_structure_theorem_admissible_pairs (m : ℕ) [NeZero m]
    (ψ : SchwartzMap ℝ ℂ) {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) :
    IsAdmissiblePair m (⇑ψ) η Fη ↔
      ∃ (u Fu : ℝ → ℂ) (Q : Polynomial ℂ),
        HasFourierAwayFromOrigin u Fu ∧
        HasFourierAwayFromOrigin
          (reflectedConjConvolution (⇑ψ) (fun t => η t - Q.eval (t : ℂ)))
          (fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * Fu ζ) ∧
        IntegrableOn Fu {(0 : ℝ)}ᶜ volume ∧
        (∫ ζ in {(0 : ℝ)}ᶜ, Fu ζ) ≠ 0 := by
  have hπ : ((2 * Real.pi) ^ (m - 1) : ℂ) ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rintro ⟨hψint, -, hint, hK⟩
    -- the admissibility density is the Fourier data of an honest bounded continuous function
    set Fu : ℝ → ℂ :=
      fun ζ => conj (angularFourier1D (⇑ψ) ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ) with hFu_def
    have hFuint : Integrable Fu volume := by
      rwa [← restrict_compl_singleton (μ := (volume : Measure ℝ)) (a := (0 : ℝ)),
        ← IntegrableOn]
    refine ⟨_, Fu, 0, hasFourierAwayFromOrigin_angularFourierInv hFuint, ?_, hint, ?_⟩
    · have hηQ : HasFourierAwayFromOrigin (fun t : ℝ => η t - (0 : Polynomial ℂ).eval (t : ℂ))
          Fη := by simpa using hη
      refine (hasFourierAwayFromOrigin_reflectedConjConvolution ψ hηQ).congr_data ?_
      intro ζ hζ
      have hζ' : ζ ≠ 0 := by simpa using hζ
      have habs : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (abs_ne_zero.mpr hζ'))
      simp only [hFu_def]
      field_simp
    · intro hzero
      refine hK ?_
      rw [admissibilityConstant, ← hFu_def, hzero, mul_zero]
  · rintro ⟨u, Fu, Q, -, hdata, hint, hne⟩
    have hηQ : HasFourierAwayFromOrigin (fun t : ℝ => η t - Q.eval (t : ℂ)) Fη := by
      have h := l1_hasFourierAwayFromOrigin_add_polynomial hη (-Q)
      simpa [sub_eq_add_neg] using h
    have hbp := hasFourierAwayFromOrigin_ae_eq
      (hasFourierAwayFromOrigin_reflectedConjConvolution ψ hηQ) hdata
    refine ⟨SchwartzMap.integrable _, hη,
      integrableOn_admissibilityIntegrand_of_backprojection_ae hbp hint, ?_⟩
    rw [admissibilityConstant_of_backprojection_ae hbp]
    exact mul_ne_zero hπ hne

/-- **Sufficiency half of the structure theorem `thm:eq.ac`, spectral form up to a null set.**
The common core of the two pointwise sufficiency statements below: `Fη` is determined only up to
a null set of `ℝ \ {0}` (`hasFourierAwayFromOrigin_ae_eq`), so the backprojection equation is
imposed almost everywhere there. -/
theorem isAdmissiblePair_of_backprojection_ae (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ)
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) (u : SchwartzMap ℝ ℂ)
    (hbp : (fun ζ : ℝ => conj (angularFourier1D (⇑ψ) ζ) * Fη ζ)
      =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑u) ζ)
    (hK : (∫ ζ : ℝ, angularFourier1D (⇑u) ζ) ≠ 0) :
    IsAdmissiblePair m (⇑ψ) η Fη := by
  have huint : Integrable (angularFourier1D (⇑u)) volume := by
    rw [← coe_angularSchwartz]
    exact SchwartzMap.integrable _
  refine ⟨SchwartzMap.integrable _, hη,
    integrableOn_admissibilityIntegrand_of_backprojection_ae hbp huint.integrableOn, ?_⟩
  rw [admissibilityConstant_of_backprojection_ae hbp, restrict_compl_singleton]
  refine mul_ne_zero ?_ hK
  refine pow_ne_zero _ ?_
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- **Sufficiency half of the structure theorem `thm:eq.ac`, spectral form.** If the
backprojection equation holds in the Fourier data sense — `conj (ψ̂) Fη = |ζ|^m û` away from the
origin — with a Schwartz solution `u` whose transform has a nonzero total integral, then the pair
`(ψ, η)` is admissible, with `K_{ψ,η} = (2π)^{m-1} ∫ û`. -/
theorem l1_structure_theorem_sufficiency (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ)
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) (u : SchwartzMap ℝ ℂ)
    (hbp : ∀ ζ : ℝ, ζ ≠ 0 →
      conj (angularFourier1D (⇑ψ) ζ) * Fη ζ = ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑u) ζ)
    (hK : (∫ ζ : ℝ, angularFourier1D (⇑u) ζ) ≠ 0) :
    IsAdmissiblePair m (⇑ψ) η Fη :=
  isAdmissiblePair_of_backprojection_ae m ψ hη u (backprojection_ae_of_forall hbp) hK

/-- **Sufficiency half of the structure theorem `thm:eq.ac`, physical form.** If the
manuscript's backprojection equation `Λ^m u = conj (ψ~) ⋆ (η - Q)` holds pointwise for a
Schwartz solution `u` with `∫ û ≠ 0`, then the pair `(ψ, η)` is admissible, with
`K_{ψ,η} = (2π)^{m-1} ∫ û`.

For a Schwartz `u` the pointwise principal value defining `Λ^m u` converges, so the physical
form is available; the translation to the spectral form is the convolution theorem away from
the origin (`hasFourierAwayFromOrigin_reflectedConjConvolution`) together with the multiplier
property (`hasFourierAwayFromOrigin_lambdaOperatorPow`) and the uniqueness of Fourier data
(`hasFourierAwayFromOrigin_ae_eq`). The polynomial `Q` is invisible throughout
(`l1_hasFourierAwayFromOrigin_add_polynomial`), as it must be in the Lizorkin quotient. -/
theorem l1_structure_theorem_sufficiency_physical (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ)
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) (u : SchwartzMap ℝ ℂ)
    (Q : Polynomial ℂ)
    (hbp : ∀ z : ℝ, lambdaOperatorPow m (⇑u) z =
      reflectedConjConvolution (⇑ψ) (fun t => η t - Q.eval (t : ℂ)) z)
    (hK : (∫ ζ : ℝ, angularFourier1D (⇑u) ζ) ≠ 0) :
    IsAdmissiblePair m (⇑ψ) η Fη := by
  have hηQ : HasFourierAwayFromOrigin (fun t => η t - Q.eval (t : ℂ)) Fη := by
    have h := l1_hasFourierAwayFromOrigin_add_polynomial hη (-Q)
    simpa [sub_eq_add_neg] using h
  have hR := hasFourierAwayFromOrigin_reflectedConjConvolution ψ hηQ
  have hL := hasFourierAwayFromOrigin_lambdaOperatorPow m u
  rw [funext hbp] at hL
  exact isAdmissiblePair_of_backprojection_ae m ψ hη u
    (hasFourierAwayFromOrigin_ae_eq hR hL) hK

/-! ## Construction of admissible pairs (`cor:const.ap`) -/

/-- The angular derivative rule iterated: `(φ^{(k)})^(ζ) = (i ζ)^k φ̂(ζ)`. -/
theorem angularFourier1D_iteratedDeriv (k : ℕ) (φ : SchwartzMap ℝ ℂ) (ζ : ℝ) :
    angularFourier1D (iteratedDeriv k (⇑φ)) ζ
      = (Complex.I * (ζ : ℂ)) ^ k * angularFourier1D (⇑φ) ζ := by
  induction k generalizing φ with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    have hcoe : ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv (⇑φ) := rfl
    have h1 : iteratedDeriv (n + 1) (⇑φ) = iteratedDeriv n (⇑(SchwartzMap.derivCLM ℂ ℂ φ)) := by
      rw [hcoe, iteratedDeriv_succ']
    rw [h1, ih (SchwartzMap.derivCLM ℂ ℂ φ), hcoe,
      congrFun (angularFourier1D_deriv φ) ζ, pow_succ]
    ring

/-- **`cor:const.ap` in sharpened form: exact criterion for a filtered ridgelet function.**
For a Schwartz `φ` whose filtered version `Λ^m φ` is integrable, the pair `(Λ^m φ, η)` is
admissible *if and only if* `conj (φ̂) Fη` is integrable away from the origin with nonzero
integral. The factor `|ζ|^m` of `(Λ^m φ)^` cancels the factor `|ζ|^{-m}` of the admissibility
density exactly, which is the whole mechanism of the manuscript's construction.

Integrability of `Λ^m φ` is automatic (`integrable_lambdaOperatorPow`): for even `m` the
filtered function is Schwartz, and for odd `m` it is the Hilbert transform of a derivative,
whose integral vanishes. -/
theorem l1_isAdmissiblePair_lambdaOperatorPow (m : ℕ) [NeZero m] (φ : SchwartzMap ℝ ℂ)
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) :
    IsAdmissiblePair m (lambdaOperatorPow m (⇑φ)) η Fη ↔
      IntegrableOn (fun ζ => conj (angularFourier1D (⇑φ) ζ) * Fη ζ) {(0 : ℝ)}ᶜ volume ∧
        (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D (⇑φ) ζ) * Fη ζ) ≠ 0 := by
  have hψ : Integrable (lambdaOperatorPow m (⇑φ)) volume := integrable_lambdaOperatorPow m φ
  have hπ : ((2 * Real.pi) ^ (m - 1) : ℂ) ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcongr :
      (fun ζ : ℝ => conj (angularFourier1D (lambdaOperatorPow m (⇑φ)) ζ) * Fη ζ /
          ((|ζ| ^ m : ℝ) : ℂ))
        =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] fun ζ => conj (angularFourier1D (⇑φ) ζ) * Fη ζ := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with ζ hζ
    have hζ' : ζ ≠ 0 := by simpa using hζ
    have habs : ((|ζ| ^ m : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (abs_ne_zero.mpr hζ'))
    rw [angularFourier1D_lambdaOperatorPow m φ hψ ζ, map_mul, Complex.conj_ofReal]
    field_simp
  have hKeq : admissibilityConstant m (lambdaOperatorPow m (⇑φ)) Fη
      = ((2 * Real.pi) ^ (m - 1) : ℂ) *
        ∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D (⇑φ) ζ) * Fη ζ := by
    rw [admissibilityConstant]
    congr 1
    exact integral_congr_ae hcongr
  constructor
  · rintro ⟨-, -, hint, hK⟩
    refine ⟨hint.congr hcongr, fun hzero => hK ?_⟩
    rw [hKeq, hzero, mul_zero]
  · rintro ⟨hint, hne⟩
    exact ⟨hψ, hη, hint.congr hcongr.symm, by rw [hKeq]; exact mul_ne_zero hπ hne⟩

/-- **Corollary 5.5 (`cor:const.ap`), construction of admissible pairs**: if `ψ₀` is a Schwartz
function with `∫ ζ^k conj (ψ̂₀ ζ) Fη ζ dζ` absolutely convergent and nonzero, then
`ψ = Λ^m ψ₀^{(k)}` is admissible with `η`.

**Deviations from the article (2026-08-05).**
* The integrability of the constructed ridgelet function is a hypothesis. It is automatic for
  even `m` (`Λ^m ψ₀^{(k)} = ± ψ₀^{(m+k)}` is Schwartz) and, for odd `m`, is the `L¹` decay
  estimate for the Hilbert transform of a Schwartz function still missing from the development;
  it also holds whenever `ψ̂₀` vanishes near the origin, since then `Λ^m ψ₀^{(k)}` is Schwartz.
  The manuscript takes admissible pairs in `𝒮(ℝ) × 𝒮'(ℝ)`, but for odd `m` the constructed
  `ψ` is *not* Schwartz: its Fourier transform `|ζ|^m (iζ)^k ψ̂₀ ζ` is continuous and rapidly
  decreasing yet not smooth at the origin, so `ψ` only decays algebraically. This is why
  `IsAdmissiblePair` asks for `Integrable ψ` (paper gap memo, 2026-07-19).
* The manuscript's continuity hypothesis on `ζ^k η̂ (ζ)` near the origin is dropped: it serves
  to make the admissibility integral converge near the origin, which the explicit integrability
  hypothesis already provides. -/
theorem l1_construction_of_admissible_pairs (m : ℕ) [NeZero m]
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη) (k : ℕ) (ψ₀ : SchwartzMap ℝ ℂ)
    (hint : IntegrableOn
      (fun ζ : ℝ => (ζ : ℂ) ^ k * conj (angularFourier1D (⇑ψ₀) ζ) * Fη ζ) {(0 : ℝ)}ᶜ volume)
    (hne : (∫ ζ in {(0 : ℝ)}ᶜ,
      (ζ : ℂ) ^ k * conj (angularFourier1D (⇑ψ₀) ζ) * Fη ζ) ≠ 0) :
    IsAdmissiblePair m (lambdaOperatorPow m (iteratedDeriv k (⇑ψ₀))) η Fη := by
  set φ : SchwartzMap ℝ ℂ := (⇑(SchwartzMap.derivCLM ℂ ℂ))^[k] ψ₀ with hφ_def
  have hφ : ⇑φ = iteratedDeriv k (⇑ψ₀) := coe_iterate_schwartz_derivCLM k ψ₀
  have hI : ((-Complex.I) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  have hval : ∀ ζ : ℝ, conj (angularFourier1D (⇑φ) ζ) * Fη ζ
      = (-Complex.I) ^ k * ((ζ : ℂ) ^ k * conj (angularFourier1D (⇑ψ₀) ζ) * Fη ζ) := by
    intro ζ
    rw [hφ, angularFourier1D_iteratedDeriv k ψ₀ ζ, map_mul, map_pow, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [← hφ]
  refine (l1_isAdmissiblePair_lambdaOperatorPow m φ hη).2 ⟨?_, ?_⟩
  · refine (hint.const_mul ((-Complex.I) ^ k)).congr ?_
    filter_upwards with ζ
    exact (hval ζ).symm
  · rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const_mul]
    exact mul_ne_zero hI hne

/-! ## Examples 5.2 and 5.3: where admissibility fails

The manuscript's two examples show that the naive product `conj (ψ̂) η̂ |ζ|^{-m}` of tempered
distributions is not associative, the two groupings differing by a term supported at the
origin. At function level that ambiguity cannot arise: `Fη` is a function on `ℝ \ {0}` and the
admissibility density is a pointwise product of complex numbers. What survives of the two
examples is the verdict, and it agrees with the manuscript's.
-/

/-- The zero function carries the zero Fourier data. -/
theorem hasFourierAwayFromOrigin_zero : HasFourierAwayFromOrigin 0 0 :=
  ⟨locallyIntegrable_zero, ⟨0, 0, by simp⟩, locallyIntegrable_zero.locallyIntegrableOn _,
    by intro φ _; simp⟩

/-- A polynomial has vanishing Fourier data away from the origin: its distributional Fourier
transform is a combination of derivatives of `δ`, all supported at the origin. -/
theorem l1_hasFourierAwayFromOrigin_polynomial (Q : Polynomial ℂ) :
    HasFourierAwayFromOrigin (fun z : ℝ => Q.eval (z : ℂ)) 0 := by
  simpa using l1_hasFourierAwayFromOrigin_add_polynomial hasFourierAwayFromOrigin_zero Q

/-- **Example 5.2**: a polynomial activation is never admissible, `K_{ψ,η} = 0` for every `ψ`.

The manuscript exhibits `η(z) = z`, `ψ = Λ G` with `G` the Gaussian, for which the two
groupings of `pv (1/|ζ|) × |ζ| G(ζ) × δ(ζ)` give `0` and `G(0) ≠ 0`; the admissibility integral
`eq:defK`, which removes the origin, gives `0`. In the Lizorkin quotient the reason is
structural and needs no computation: the Fourier data of a polynomial away from the origin
vanishes, so the admissibility density does too. This is why the article takes activations in
`𝒮'(ℝ)/𝒫 ≅ 𝒮₀'(ℝ)`. -/
theorem l1_polynomial_not_isAdmissiblePair (m : ℕ) (ψ : ℝ → ℂ) (Q : Polynomial ℂ) :
    ¬ IsAdmissiblePair m ψ (fun z : ℝ => Q.eval (z : ℂ)) 0 := by
  rintro ⟨-, -, -, hK⟩
  refine hK ?_
  rw [admissibilityConstant]
  simp

/-- **Example 5.3**: the unit step `z₊^0` is not admissible with a filtered ridgelet function
`Λ^m φ` whose window has `φ̂ (0) ≠ 0`; the admissibility integral diverges at the origin.

The manuscript's instance is `m = 1`, `φ = G` the Gaussian and
`η(z) = z₊^0 + (2π)^{-1} e^{iz}`, where `K_{ψ,η} = ∞ + G(1)`. The second summand of `η` has a
point mass of `η̂` away from the origin and is outside the function-level framework, but it is
not the source of the divergence: by `l1_isAdmissiblePair_lambdaOperatorPow` the admissibility
density of `(Λ^m φ, z₊^0)` is `conj (φ̂ ζ) / (i ζ)`, which is not absolutely integrable at the
origin as soon as `φ̂ (0) ≠ 0`. Removing the origin from the integral, as `eq:defK` does, is
therefore not enough to make every pair admissible — the manuscript's point. -/
theorem l1_step_not_isAdmissiblePair_lambdaOperatorPow (m : ℕ) [NeZero m] (φ : SchwartzMap ℝ ℂ)
    (hφ : angularFourier1D (⇑φ) 0 ≠ 0) :
    ¬ IsAdmissiblePair m (lambdaOperatorPow m (⇑φ)) (truncatedPower 0)
        (truncatedPowerFourier 0) := by
  intro hadm
  have hint := ((l1_isAdmissiblePair_lambdaOperatorPow m φ
    (l1_truncatedPower_hasFourierAwayFromOrigin 0)).1 hadm).1
  -- the density is bounded below by `(c/2) |ζ|^{-1}` near the origin
  have hcont : Continuous (angularFourier1D (⇑φ)) := by
    rw [angularFourier1D_coe_schwartz]
    exact (Fourier.angularFourierSchwartz φ).continuous
  set c : ℝ := ‖angularFourier1D (⇑φ) 0‖ with hc_def
  have hc : 0 < c := norm_pos_iff.2 hφ
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ ζ : ℝ, |ζ| < δ → c / 2 ≤ ‖angularFourier1D (⇑φ) ζ‖ := by
    have h := hcont.norm.tendsto 0
    have hmem : Set.Ioi (c / 2) ∈ 𝓝 (‖angularFourier1D (⇑φ) 0‖) :=
      Ioi_mem_nhds (by rw [← hc_def]; linarith)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (h hmem)
    exact ⟨δ, hδ, fun ζ hζ => le_of_lt (hsub (by simpa [Real.dist_eq] using hζ))⟩
  have hsub : Set.Ioo (0 : ℝ) δ ⊆ {(0 : ℝ)}ᶜ := fun ζ hζ => ne_of_gt hζ.1
  have hIoo : IntegrableOn
      (fun ζ => conj (angularFourier1D (⇑φ) ζ) * truncatedPowerFourier 0 ζ)
      (Set.Ioo (0 : ℝ) δ) volume := hint.mono hsub le_rfl
  have hlb : ∀ ζ ∈ Set.Ioo (0 : ℝ) δ,
      ‖(c / 2) * ζ ^ (-1 : ℝ)‖
        ≤ ‖conj (angularFourier1D (⇑φ) ζ) * truncatedPowerFourier 0 ζ‖ := by
    intro ζ hζ
    have hζ0 : (0 : ℝ) < ζ := hζ.1
    have habs : |ζ| < δ := by rw [abs_of_pos hζ0]; exact hζ.2
    have hnorm : ‖truncatedPowerFourier 0 ζ‖ = ζ⁻¹ := by
      simp [truncatedPowerFourier, abs_of_pos hζ0]
    have hR : ‖conj (angularFourier1D (⇑φ) ζ) * truncatedPowerFourier 0 ζ‖
        = ‖angularFourier1D (⇑φ) ζ‖ * ζ⁻¹ := by
      rw [norm_mul, RCLike.norm_conj, hnorm]
    have hL : ‖(c / 2) * ζ ^ (-1 : ℝ)‖ = (c / 2) * ζ⁻¹ := by
      rw [Real.rpow_neg_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c / 2) * ζ⁻¹)]
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right (hball ζ habs) (by positivity)
  have hmeas : AEStronglyMeasurable (fun ζ : ℝ => (c / 2) * ζ ^ (-1 : ℝ))
      (volume.restrict (Set.Ioo (0 : ℝ) δ)) := by
    fun_prop
  have hbig : IntegrableOn (fun ζ : ℝ => (c / 2) * ζ ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) δ) volume := by
    refine Integrable.mono' hIoo.norm hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ζ hζ
    exact hlb ζ hζ
  have hfin : IntegrableOn (fun ζ : ℝ => ζ ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) δ) volume := by
    refine (hbig.const_mul (c / 2)⁻¹).congr ?_
    filter_upwards with ζ
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (c / 2) ≠ 0), one_mul]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).1 hfin
  linarith

end LeanRidgelet
