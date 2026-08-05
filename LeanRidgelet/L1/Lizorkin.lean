/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs

/-!
# L1 theory: the Lizorkin quotient at function level

Adding a polynomial to an activation changes neither its Fourier data away from the origin nor
its admissibility constant: admissibility is a property of the Lizorkin class of `η`. This is
the function-level form of the quotient `𝒮'(ℝ)/𝒫 ≅ 𝒮₀'(ℝ)` in which the article takes its
activations (Section 2.3).

## Main results

* `LeanRidgelet.integral_pow_mul_angularFourier1D_eq_zero`: all moments of the Fourier
  transform of a Schwartz function supported away from the origin vanish.
* `LeanRidgelet.integral_polynomial_mul_angularFourier1D_eq_zero`: the polynomial form.
* `LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial`: **polynomial invisibility**.

The test-function side of the same duality, `𝒮₀(ℝ)` and `𝒮₀'(ℝ)` as types, is
`LizorkinSpace` and `LizorkinDistribution` in `LeanRidgelet.ToMathlib.Lizorkin`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-- Moments of the angular Fourier transform of a Schwartz function supported away from the
origin all vanish: `∫ ζ^n φ̂(ζ) dζ = 0`. This is the analytic heart of the invisibility of
polynomials in the Lizorkin quotient. -/
theorem integral_pow_mul_angularFourier1D_eq_zero (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) (n : ℕ) :
    ∫ ζ : ℝ, (ζ : ℂ) ^ n * angularFourier1D (⇑φ) ζ = 0 := by
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
  -- Rescale the angular transform to the Mathlib transform.
  have hζ : ∀ ζ : ℝ, (ζ : ℂ) ^ n * angularFourier1D (⇑φ) ζ =
      ((2 * Real.pi : ℝ) : ℂ) ^ n *
        ((fun w : ℝ => (w : ℂ) ^ n * 𝓕 (⇑φ) w) ((2 * Real.pi)⁻¹ • ζ)) := by
    intro ζ
    rw [angularFourier1D_eq_mathlib (⇑φ) ζ]
    simp only [smul_eq_mul]
    have hcast : (((2 * Real.pi)⁻¹ * ζ : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (ζ : ℂ) := by
      push_cast
      ring
    rw [hcast, mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπℂ]
    simp
  calc ∫ ζ : ℝ, (ζ : ℂ) ^ n * angularFourier1D (⇑φ) ζ
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

/-- Integrating a polynomial against the angular Fourier transform of a Schwartz function
supported away from the origin gives zero. -/
theorem integral_polynomial_mul_angularFourier1D_eq_zero (Q : Polynomial ℂ)
    (φ : SchwartzMap ℝ ℂ) (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ z : ℝ, Q.eval (z : ℂ) * angularFourier1D (⇑φ) z = 0 := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    have hip : Integrable (fun z : ℝ => p.eval (z : ℂ) * angularFourier1D (⇑φ) z) volume := by
      rw [angularFourier1D_coe_schwartz]
      exact (polynomiallyBounded_polynomial_eval p).integrable_mul_schwartz
        (((Polynomial.continuous p).comp Complex.continuous_ofReal).aestronglyMeasurable)
        (Fourier.angularFourierSchwartz φ)
    have hiq : Integrable (fun z : ℝ => q.eval (z : ℂ) * angularFourier1D (⇑φ) z) volume := by
      rw [angularFourier1D_coe_schwartz]
      exact (polynomiallyBounded_polynomial_eval q).integrable_mul_schwartz
        (((Polynomial.continuous q).comp Complex.continuous_ofReal).aestronglyMeasurable)
        (Fourier.angularFourierSchwartz φ)
    have hsplit : ∫ z : ℝ, (p + q).eval (z : ℂ) * angularFourier1D (⇑φ) z =
        (∫ z : ℝ, p.eval (z : ℂ) * angularFourier1D (⇑φ) z) +
          ∫ z : ℝ, q.eval (z : ℂ) * angularFourier1D (⇑φ) z := by
      rw [← integral_add hip hiq]
      apply integral_congr_ae
      filter_upwards with z
      simp [Polynomial.eval_add, add_mul]
    rw [hsplit, hp, hq, add_zero]
  | monomial n a =>
    have hmono : ∀ z : ℝ, (Polynomial.monomial n a).eval (z : ℂ) * angularFourier1D (⇑φ) z =
        a * ((z : ℂ) ^ n * angularFourier1D (⇑φ) z) := by
      intro z
      rw [Polynomial.eval_monomial]
      ring
    calc ∫ z : ℝ, (Polynomial.monomial n a).eval (z : ℂ) * angularFourier1D (⇑φ) z
        = ∫ z : ℝ, a * ((z : ℂ) ^ n * angularFourier1D (⇑φ) z) :=
          integral_congr_ae (Filter.Eventually.of_forall hmono)
      _ = a * ∫ z : ℝ, (z : ℂ) ^ n * angularFourier1D (⇑φ) z := integral_const_mul _ _
      _ = 0 := by rw [integral_pow_mul_angularFourier1D_eq_zero φ hφ n, mul_zero]

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
  have hηint : Integrable (fun z : ℝ => η z * angularFourier1D (⇑φ) z) volume := by
    rw [angularFourier1D_coe_schwartz]
    exact hpoly.integrable_mul_schwartz hloc.aestronglyMeasurable
      (Fourier.angularFourierSchwartz φ)
  have hQint : Integrable (fun z : ℝ => Q.eval (z : ℂ) * angularFourier1D (⇑φ) z) volume := by
    rw [angularFourier1D_coe_schwartz]
    exact (polynomiallyBounded_polynomial_eval Q).integrable_mul_schwartz
      hQc.aestronglyMeasurable (Fourier.angularFourierSchwartz φ)
  have hsplit : ∫ z : ℝ, (η z + Q.eval (z : ℂ)) * angularFourier1D (⇑φ) z =
      (∫ z : ℝ, η z * angularFourier1D (⇑φ) z) +
        ∫ z : ℝ, Q.eval (z : ℂ) * angularFourier1D (⇑φ) z := by
    rw [← integral_add hηint hQint]
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [hsplit, integral_polynomial_mul_angularFourier1D_eq_zero Q φ hφ, add_zero]
  exact hpair φ hφ

end LeanRidgelet
