/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import LeanRidgelet.ToMathlib.WeightedL1Smoothing

/-!
# Polynomially bounded functions on the real line

A locally integrable function of polynomial growth defines a tempered distribution. This file
introduces the growth predicate itself, together with the polynomially weighted `L¹` estimates
that accompany it: submultiplicativity of the weight `1 + |z|`, weighted integrability of
Schwartz functions, and the invariance of vanishing moments under shifts and conjugation.

## Main definitions and results

* `MeasureTheory.PolynomiallyBounded`: `‖f z‖ ≤ C (1 + |z|)^k` for some `C` and `k`.
* `MeasureTheory.PolynomiallyBounded.add`, `MeasureTheory.polynomiallyBounded_polynomial_eval`:
  the predicate is additive and holds for every polynomial.
* `MeasureTheory.PolynomiallyBounded.integrable_mul_schwartz`: a measurable function of
  polynomial growth is integrable against every Schwartz function, i.e. defines a tempered
  distribution.
* `MeasureTheory.integrable_one_add_abs_pow_mul_schwartz`: `(1 + |s|)^k ‖φ s‖` is integrable
  for a Schwartz function `φ`.
* `MeasureTheory.integral_pow_mul_conj_comp_sub_eq_zero`: vanishing moments up to order `k` are
  inherited by every shifted conjugate section `r ↦ conj (ψ (r - c))`.

Mathlib has `Function.HasTemperateGrowth`, which additionally demands smoothness with
polynomially bounded derivatives of every order, but no bare polynomial growth predicate for
merely measurable functions. These statements are upstream candidates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

/-- Submultiplicativity of the polynomial weight: `1 + |z + t| ≤ (1 + |z|) (1 + |t|)`. -/
theorem one_add_abs_add_le_mul (z t : ℝ) : 1 + |z + t| ≤ (1 + |z|) * (1 + |t|) := by
  have h1 : |z + t| ≤ |z| + |t| := abs_add_le z t
  nlinarith [abs_nonneg z, abs_nonneg t]

namespace MeasureTheory

/-- Polynomial growth bound: `‖η z‖ ≤ C (1 + |z|)^k`.  Together with local integrability this
is the classical criterion for a function to define a tempered distribution. -/
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

/-- Vanishing moments are inherited by shifted conjugate sections: if `ψ` has finite `k`-th
moment and vanishing moments up to `k`, then `∫ r^j conj (ψ (r - c)) dr = 0` for every
`j ≤ k` and every shift `c`. This is the mechanism by which the polynomial part of the
function — the kernel of the Lizorkin quotient — becomes invisible to a pairing against a
function with vanishing moments. -/
theorem integral_pow_mul_conj_comp_sub_eq_zero {ψ : ℝ → ℂ} {k : ℕ}
    (hψm : AEStronglyMeasurable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    {j : ℕ} (hj : j ≤ k) (c : ℝ) :
    ∫ r : ℝ, (r : ℂ) ^ j * conj (ψ (r - c)) = 0 := by
  -- integrability of each monomial section
  have hmono : ∀ i : ℕ, i ≤ k → Integrable (fun s : ℝ => (s : ℂ) ^ i * ψ s) volume := by
    intro i hi
    have hmeas : AEStronglyMeasurable (fun s : ℝ => (s : ℂ) ^ i * ψ s) volume :=
      ((Complex.continuous_ofReal.pow i).aestronglyMeasurable).mul hψm
    refine hψk.mono' hmeas (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |s| ^ i ≤ (1 + |s|) ^ k := by
      calc |s| ^ i ≤ (1 + |s|) ^ i :=
            pow_le_pow_left₀ (abs_nonneg s) (le_add_of_nonneg_left zero_le_one) i
        _ ≤ (1 + |s|) ^ k :=
            pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg s)) hi
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  -- translate the section back to the origin
  have htrans : (∫ r : ℝ, (r : ℂ) ^ j * conj (ψ (r - c)))
      = ∫ s : ℝ, ((s + c : ℝ) : ℂ) ^ j * conj (ψ s) := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun r : ℝ => (r : ℂ) ^ j * conj (ψ (r - c))) c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [add_sub_cancel_right]
  rw [htrans]
  -- expand the binomial and use the vanishing moments of `ψ`
  have hexp : ∀ s : ℝ, ((s + c : ℝ) : ℂ) ^ j * conj (ψ s)
      = ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * (c : ℂ) ^ (j - i) * conj ((s : ℂ) ^ i * ψ s) := by
    intro s
    have hadd : ((s + c : ℝ) : ℂ) = (s : ℂ) + (c : ℂ) := by push_cast; ring
    rw [hadd, add_pow]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hconjpow : conj ((s : ℂ) ^ i) = (s : ℂ) ^ i := by
      rw [map_pow, Complex.conj_ofReal]
    rw [hconjpow]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have hconjint : ∀ i : ℕ, i ≤ k →
      Integrable (fun s : ℝ => conj ((s : ℂ) ^ i * ψ s)) volume := fun i hik =>
    (hmono i hik).norm.mono'
      (RCLike.continuous_conj.comp_aestronglyMeasurable (hmono i hik).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s => by simp)
  have hterm : ∀ i ∈ Finset.range (j + 1),
      Integrable (fun s : ℝ =>
        (j.choose i : ℂ) * (c : ℂ) ^ (j - i) * conj ((s : ℂ) ^ i * ψ s)) volume := by
    intro i hi
    have hik : i ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hj
    exact (hconjint i hik).const_mul _
  rw [integral_finsetSum _ hterm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hik : i ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hj
  rw [integral_const_mul, integral_conj, hψvm i hik, map_zero, mul_zero]

/-- Weighted integrability of a one-dimensional Schwartz function. -/
theorem integrable_one_add_abs_pow_mul_schwartz (φ : SchwartzMap ℝ ℂ) (k : ℕ) :
    Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖φ s‖) volume := by
  have h1 := φ.integrable_pow_mul volume k
  have h2 : Integrable (fun s : ℝ => (2 : ℝ) ^ k * (‖φ s‖ + ‖s‖ ^ k * ‖φ s‖)) volume :=
    ((φ.integrable.norm).add h1).const_mul _
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · exact ((by fun_prop : Continuous fun s : ℝ =>
      (1 + |s|) ^ k)).aestronglyMeasurable.mul φ.continuous.norm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 := add_pow_le_two_pow_mul k (a := (1 : ℝ)) (b := |s|) one_pos.le (abs_nonneg s)
    calc (1 + |s|) ^ k * ‖φ s‖ ≤ 2 ^ k * (1 ^ k + |s| ^ k) * ‖φ s‖ := by gcongr
      _ = 2 ^ k * (‖φ s‖ + ‖s‖ ^ k * ‖φ s‖) := by
          rw [Real.norm_eq_abs]
          ring

end MeasureTheory
