/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of a temperate function bounded away from zero

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib has `Function.hasTemperateGrowth_one_add_norm_sq_rpow`: the Bessel potential multiplier
`x ↦ (1 + ‖x‖²)^a` has temperate growth. The proof composes `u ↦ u^a`, which is temperate on any set
bounded away from the origin, with the inner function `1 + ‖x‖²`, whose *range* is bounded away from
the origin. Its own comment observes that the argument works for any such set.

That generalization is what this file supplies:

> if `q` has temperate growth and `q ≥ c` for some `c > 0`, then so does `q ^ a`, for every real
> `a`.

The Mathlib lemma is the case `q = 1 + ‖·‖²`, `c = 1`. What the generalization buys is the freedom
to *choose* the inner function, which is what one needs for a multiplier that is not itself
temperate:
`‖x‖^a` is not, having a singularity at the origin for `a` non-even, but it agrees outside a ball
with `q ^ (a/2)` for a `q` that is a bump-corrected `‖x‖²`, and that is temperate by the lemma here.

## Main results

* `Function.HasTemperateGrowth.rpow_of_le`: the statement above.
-/

@[expose] public section

noncomputable section

open Set

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivatives of `u ↦ u^a` are bounded by a polynomial on any ray `(b, ∞)` with `b > 0`. This
is the estimate behind `Function.HasTemperateGrowth.rpow_of_le`, and the only analytic content of
it: the `n`-th derivative is a constant times `u^{a-n}`, which on `u > b` is bounded by a fixed
power of `1 + u` when `a - n ≥ 0` and by a constant when `a - n < 0`. -/
theorem norm_iteratedFDerivWithin_rpow_le {b : ℝ} (hb : 0 < b) (a : ℝ) (N : ℕ) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ u ∈ Ioi b,
      ‖iteratedFDerivWithin ℝ n (fun u : ℝ => u ^ a) (Ioi b) u‖ ≤ C * (1 + ‖u‖) ^ k := by
  have hunique : UniqueDiffOn ℝ (Ioi b) := (isOpen_Ioi).uniqueDiffOn
  set K : ℝ := |a| + N with hK
  have hK0 : 0 ≤ K := by positivity
  set k : ℕ := ⌈K⌉₊ with hk
  have hKk : K ≤ (k : ℝ) := Nat.le_ceil K
  set P : ℝ := ∑ n ∈ Finset.range (N + 1), ‖(descPochhammer ℝ n).eval a‖ with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨k, P * max 1 (b ^ (-K)), by positivity, fun n hn u hu => ?_⟩
  have hu0 : 0 < u := hb.trans hu
  have hdiff : ContDiffAt ℝ n (fun u : ℝ => u ^ a) u :=
    Real.contDiffAt_rpow_const (Or.inl hu0.ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique hdiff hu, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  -- the Pochhammer factor is at most `P`
  have hpoch : ‖(descPochhammer ℝ n).eval a‖ ≤ P := by
    refine Finset.single_le_sum (f := fun n => ‖(descPochhammer ℝ n).eval a‖)
      (fun _ _ => norm_nonneg _) ?_
    simpa using Nat.lt_succ_of_le hn
  -- and the power factor is at most `max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k`
  have hnorm : ‖u‖ = u := Real.norm_of_nonneg hu0.le
  have h1u : (1 : ℝ) ≤ 1 + ‖u‖ := by rw [hnorm]; linarith
  have hone : (1 : ℝ) ≤ (1 + ‖u‖) ^ k := one_le_pow₀ h1u
  have hule : u ≤ 1 + ‖u‖ := by rw [hnorm]; linarith
  have habs : ‖u ^ (a - n)‖ = u ^ (a - n) := by
    rw [Real.norm_rpow_of_nonneg hu0.le, Real.norm_of_nonneg hu0.le]
  have hpow : ‖u ^ (a - n)‖ ≤ max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k := by
    rw [habs]
    by_cases hcase : 1 ≤ u
    · -- large `u`: the exponent is at most `K ≤ k`
      have hle : a - n ≤ (k : ℝ) := by
        have h1 : a ≤ |a| := le_abs_self a
        have h2 : a - n ≤ K := by
          rw [hK]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        linarith [hKk]
      calc u ^ (a - n) ≤ u ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hcase hle
        _ ≤ (1 + ‖u‖) ^ (k : ℝ) := Real.rpow_le_rpow hu0.le hule (by positivity)
        _ = (1 + ‖u‖) ^ k := Real.rpow_natCast _ k
        _ ≤ max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    · -- small `u`: the exponent is at least `-K`, so the power is at most `b ^ (-K)`
      have hcase' : u < 1 := not_le.mp hcase
      have hge : -K ≤ a - n := by
        rw [hK]
        have h1 : -|a| ≤ a := neg_abs_le a
        have h2 : (n : ℝ) ≤ N := Nat.cast_le.mpr hn
        linarith
      calc u ^ (a - n) ≤ u ^ (-K) := Real.rpow_le_rpow_of_exponent_ge hu0 hcase'.le hge
        _ ≤ b ^ (-K) := Real.rpow_le_rpow_of_nonpos hb hu.le (by linarith)
        _ ≤ max 1 (b ^ (-K)) := le_max_right _ _
        _ ≤ max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k := le_mul_of_one_le_right (by positivity) hone
  calc ‖(descPochhammer ℝ n).eval a‖ * ‖u ^ (a - n)‖
      ≤ P * (max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k) := by
        refine mul_le_mul hpoch hpow (norm_nonneg _) hP0
    _ = P * max 1 (b ^ (-K)) * (1 + ‖u‖) ^ k := by ring

/-- **A real power of a temperate function bounded away from zero has temperate growth.** This
generalizes `Function.hasTemperateGrowth_one_add_norm_sq_rpow`, which is the case `q = 1 + ‖·‖²` and
`c = 1`, to an arbitrary inner function; the point of the generalization is that one may then
*choose* the inner function, which is what a multiplier with a singularity at the origin needs. -/
theorem HasTemperateGrowth.rpow_of_le {q : E → ℝ} (hq : q.HasTemperateGrowth) {c : ℝ} (hc : 0 < c)
    (hqc : ∀ x, c ≤ q x) (a : ℝ) : (fun x => q x ^ a).HasTemperateGrowth := by
  set t : Set ℝ := Ioi (c / 2) with ht
  have hc2 : 0 < c / 2 := by positivity
  have hrange : Set.range q ⊆ t := by
    rintro - ⟨x, rfl⟩
    exact lt_of_lt_of_le (by linarith) (hqc x)
  have hunique : UniqueDiffOn ℝ t := (isOpen_Ioi).uniqueDiffOn
  have hdiff : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u ^ a) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun u hu => (lt_trans hc2 hu).ne'
  exact HasTemperateGrowth.comp' hrange hunique hdiff
    (fun N => by
      obtain ⟨k, C, hC, hbound⟩ := norm_iteratedFDerivWithin_rpow_le hc2 a N
      exact ⟨k, C, hC, hbound⟩) hq

end Function
