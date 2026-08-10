/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.Matrix.Mul

/-!
# The discrete Fourier transform on a product of cyclic groups

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`Mathlib.Analysis.Fourier.ZMod` gives the discrete Fourier transform `ZMod.dft` on a single cyclic
group `ZMod N`, together with the inversion formula. Nothing there covers `ι → ZMod N` with the
dot-product pairing, which is the transform used whenever `(ZMod N)^m` plays the role of a
discretized Euclidean space. This file supplies it.

Everything rests on one identity, orthogonality of characters on a product,
$$`\sum_{\xi}\mathrm e\!\left(\xi\cdot t\right)=\begin{cases}N^{|\iota|}&t=0\\0&t\neq0,\end{cases}`
proved by factoring the character of a dot product into a product of characters over the
coordinates and reducing to the one-dimensional statement.

## Main definitions and results

* `AddChar.map_finsetSum`: an additive character carries a finite sum to a finite product.
* `ZMod.sum_stdAddChar_mul`: orthogonality on `ZMod N`, the public form of a computation that
  `Mathlib.Analysis.Fourier.ZMod` currently performs inline inside a private proof.
* `ZMod.piDFT`: the Fourier transform on `ι → ZMod N`, `f̂(ξ) = ∑ₓ e(-ξ·x) f(x)`.
* `ZMod.sum_stdAddChar_dotProduct`: orthogonality of characters on `ι → ZMod N`.
* `ZMod.sum_stdAddChar_smul_piDFT`: the inversion formula, in the form
  `∑_ξ e(ξ·x) f̂(ξ) = N^{|ι|} • f(x)` that avoids dividing.
* `ZMod.piDFT_apply_zero`: the value at the zero frequency is the total sum.

The conventions are those of `ZMod.dft`: the character is `ZMod.stdAddChar`, which sends `j` to
`exp (2πij/N)`, the forward transform carries the minus sign, and the counting measure is
unnormalized, so inversion produces the factor `N^{|ι|}`.
-/

@[expose] public section

open Finset

namespace AddChar

/-- An additive character carries a finite sum to a finite product. The two-term case is
`AddChar.map_add_eq_mul`. -/
theorem map_finsetSum {ι A M : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, ψ.map_add_eq_mul, ih]

end AddChar

namespace ZMod

variable {N : ℕ} [NeZero N] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Orthogonality of the standard additive character on `ZMod N`: summing `e(c t)` over `c`
gives `N` at `t = 0` and cancels otherwise. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ c : ZMod N, stdAddChar (c * t) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · have hzero := AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
    simp only [AddChar.mulShift_apply] at hzero
    simpa only [mul_comm] using hzero

/-- The standard additive character takes values on the unit circle. -/
theorem norm_stdAddChar (z : ZMod N) : ‖stdAddChar z‖ = 1 := by
  rw [stdAddChar_apply]
  exact Circle.norm_coe _

/-- Conjugating the standard additive character negates its argument. -/
theorem conj_stdAddChar (z : ZMod N) :
    (starRingEnd ℂ) (stdAddChar z) = stdAddChar (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar z)]

/-- **Convolution theorem on `ZMod N`**, in the inverted form that avoids dividing: the inverse
transform of the product `û v̂` is `N` times the cyclic convolution of `u` and `v`. Mathlib has
`ZMod.dft` and its inversion formula but no convolution theorem for it. -/
theorem sum_dft_mul_dft_mul_stdAddChar (u v : ZMod N → ℂ) (t : ZMod N) :
    ∑ ω : ZMod N, dft u ω * dft v ω * stdAddChar (ω * t)
      = (N : ℂ) * ∑ b : ZMod N, u b * v (t - b) := by
  have hchar : ∀ ω j k : ZMod N,
      stdAddChar (-(j * ω)) * stdAddChar (-(k * ω)) * stdAddChar (ω * t)
        = stdAddChar (ω * (t - j - k)) := by
    intro ω j k
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have expand : ∀ ω : ZMod N, dft u ω * dft v ω * stdAddChar (ω * t)
      = ∑ j : ZMod N, ∑ k : ZMod N, u j * v k * stdAddChar (ω * (t - j - k)) := by
    intro ω
    simp only [dft_apply, smul_eq_mul]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hchar ω j k]
    ring
  calc ∑ ω : ZMod N, dft u ω * dft v ω * stdAddChar (ω * t)
      = ∑ j : ZMod N, ∑ k : ZMod N, u j * v k * ∑ ω : ZMod N, stdAddChar (ω * (t - j - k)) := by
        rw [Finset.sum_congr rfl fun ω _ => expand ω, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ j : ZMod N, u j * v (t - j) * (N : ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [sum_stdAddChar_mul]
        calc ∑ k : ZMod N, u j * v k * (if t - j - k = 0 then (N : ℂ) else 0)
            = ∑ k : ZMod N, (if k = t - j then u j * v k * (N : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              by_cases hk : k = t - j
              · simp [hk]
              · have hne : t - j - k ≠ 0 := by
                  simpa [sub_eq_zero, eq_comm] using hk
                simp [hne, hk]
          _ = u j * v (t - j) * (N : ℂ) := by simp
    _ = (N : ℂ) * ∑ b : ZMod N, u b * v (t - b) := by
        rw [← Finset.sum_mul, mul_comm]

/-- The discrete Fourier transform on `ι → ZMod N` with the dot-product pairing:
`f̂(ξ) = ∑ₓ e(-ξ·x) f(x)`, the `|ι|`-dimensional counterpart of `ZMod.dft`. -/
noncomputable def piDFT (f : (ι → ZMod N) → E) (ξ : ι → ZMod N) : E :=
  ∑ x : ι → ZMod N, stdAddChar (-(ξ ⬝ᵥ x)) • f x

theorem piDFT_apply (f : (ι → ZMod N) → E) (ξ : ι → ZMod N) :
    piDFT f ξ = ∑ x : ι → ZMod N, stdAddChar (-(ξ ⬝ᵥ x)) • f x := rfl

/-- The zero frequency of the transform is the total sum. -/
theorem piDFT_apply_zero (f : (ι → ZMod N) → E) : piDFT f 0 = ∑ x : ι → ZMod N, f x := by
  simp [piDFT_apply]

/-- Orthogonality of characters on `ι → ZMod N`. Factoring `e(ξ·t)` over the coordinates turns
the sum into a product of one-dimensional sums, each given by `ZMod.sum_stdAddChar_mul`. -/
theorem sum_stdAddChar_dotProduct (t : ι → ZMod N) :
    ∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ t)
      = if t = 0 then (N : ℂ) ^ Fintype.card ι else 0 := by
  have hprod : ∏ i : ι, ∑ c : ZMod N, stdAddChar (c * t i)
      = ∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ t) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun ξ _ => (AddChar.map_finsetSum stdAddChar univ _).symm
  have hite : ∏ i : ι, ∑ c : ZMod N, stdAddChar (c * t i)
      = ∏ i : ι, if t i = 0 then (N : ℂ) else 0 :=
    Finset.prod_congr rfl fun i _ => sum_stdAddChar_mul (t i)
  rw [← hprod, hite]
  split_ifs with h
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    rw [Pi.zero_apply] at hi
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

/-- Fourier inversion on `ι → ZMod N`, in the form that avoids dividing:
`∑_ξ e(ξ·x) f̂(ξ) = N^{|ι|} • f(x)`. -/
theorem sum_stdAddChar_smul_piDFT (f : (ι → ZMod N) → E) (x : ι → ZMod N) :
    ∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ x) • piDFT f ξ
      = ((N : ℂ) ^ Fintype.card ι) • f x := by
  calc ∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ x) • piDFT f ξ
      = ∑ y : ι → ZMod N, (∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ (x - y))) • f y := by
        simp only [piDFT_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ξ _ => ?_
        rw [← AddChar.map_add_eq_mul, dotProduct_sub, sub_eq_add_neg]
    _ = ((N : ℂ) ^ Fintype.card ι) • f x := by
        simp only [sum_stdAddChar_dotProduct, sub_eq_zero, ite_smul, zero_smul]
        simp

/-- Fourier inversion in the form solved for `f`. -/
theorem piDFT_inversion (f : (ι → ZMod N) → E) (x : ι → ZMod N) :
    f x = (((N : ℂ) ^ Fintype.card ι)⁻¹) • ∑ ξ : ι → ZMod N, stdAddChar (ξ ⬝ᵥ x) • piDFT f ξ := by
  rw [sum_stdAddChar_smul_piDFT, smul_smul, inv_mul_cancel₀, one_smul]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne N))

end ZMod
