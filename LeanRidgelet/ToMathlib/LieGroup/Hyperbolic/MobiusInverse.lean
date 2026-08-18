/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.Mobius

/-!
# The Möbius transformation of the ball is a bijection

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.Mobius` shows that `φ_a` maps the unit ball into itself.
This file shows it maps the ball *onto* itself, injectively — which is what a change of variables
along `φ_a` needs, the invariant measure of `ℍ^m` being a measure on the ball.

Both come from the same source, the *involution*

`σ_a(x) := -φ_a(x) = (‖x-a‖² a - (1-‖a‖²)(x-a))/[x,a]²`,

which swaps `0` and `a` and satisfies `σ_a ∘ σ_a = id`. The composition is a rational map of `x`, so
proving `σ_a(σ_a x) = x` by brute force would mean normalizing a large rational expression; instead
it factors through three identities that are each one `ring` after the inner products are expanded:

`σ_a(x) - a = -\frac{1-‖a‖²}{[x,a]²}(x - ‖x‖² a)`,
`‖σ_a(x) - a‖² = \frac{(1-‖a‖²)²‖x‖²}{[x,a]²}`,
`[σ_a(x),a]² = \frac{(1-‖a‖²)²}{[x,a]²}`.

Substituting the three into the definition of `σ_a` makes every bracket cancel and leaves `x`. The
second follows from the first by taking norms, and the third from the second together with the
general identity `[y,a]² = ‖y-a‖² + (1-‖y‖²)(1-‖a‖²)`, which is the one place the interplay between
the bracket and the Poisson kernel is used.

## Main definitions

* `HyperbolicSpace.mobiusInvol`: the involution `σ_a = -φ_a` of the ball swapping `0` and `a`.

## Main results

* `HyperbolicSpace.mobiusInvol_mobiusInvol`: `σ_a ∘ σ_a = id` on the closed ball.
* `HyperbolicSpace.injOn_mobius`: `φ_a` is injective on the ball.
* `HyperbolicSpace.image_mobius`: `φ_a` maps the ball onto the ball.
-/

@[expose] public section

noncomputable section

open Metric Set

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The bracket against the Poisson kernel -/

/-- The bracket differs from the squared Euclidean distance by the product of the two "defects"
from the boundary: `[y,a]² = ‖y-a‖² + (1-‖y‖²)(1-‖a‖²)`.

This is the only relation between the bracket and the Poisson kernel that is needed, and it is what
makes the bracket of an image point computable from the image's norm. -/
theorem mobiusBracketSq_eq_add (y a : E) :
    mobiusBracketSq y a = ‖y - a‖ ^ 2 + (1 - ‖y‖ ^ 2) * (1 - ‖a‖ ^ 2) := by
  rw [mobiusBracketSq, norm_sub_sq_real]
  ring

/-! ## The involution -/

/-- The involution of the unit ball swapping the origin and `a`,
`σ_a(x) = (‖x-a‖² a - (1-‖a‖²)(x-a))/[x,a]²`. It is the negative of `HyperbolicSpace.mobius`. -/
def mobiusInvol (a x : E) : E := -mobius a x

@[simp] theorem neg_mobiusInvol (a x : E) : -mobiusInvol a x = mobius a x := neg_neg _

theorem mobiusInvol_eq (a y : E) :
    mobiusInvol a y
      = (mobiusBracketSq y a)⁻¹ • (‖y - a‖ ^ 2 • a - (1 - ‖a‖ ^ 2) • (y - a)) := by
  rw [mobiusInvol, mobius, mobiusNum, ← smul_neg, neg_sub]

@[simp] theorem mobiusInvol_self (a : E) : mobiusInvol a a = 0 := by
  simp [mobiusInvol]

@[simp] theorem mobiusInvol_zero_right (a : E) : mobiusInvol a (0 : E) = a := by
  simp [mobiusInvol]

@[simp] theorem norm_mobiusInvol (a x : E) : ‖mobiusInvol a x‖ = ‖mobius a x‖ := by
  rw [mobiusInvol, norm_neg]

theorem norm_mobiusInvol_lt_one {x a : E} (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    ‖mobiusInvol a x‖ < 1 := by
  rw [norm_mobiusInvol]
  exact norm_mobius_lt_one hx ha

/-! ## The three identities -/

/-- `σ_a(x) - a = -\frac{1-‖a‖²}{[x,a]²}(x - ‖x‖² a)`. Both sides are linear combinations of `x`
and `a`, so after the squared norms are expanded this is a scalar computation on each
coefficient. -/
theorem mobiusInvol_sub_self {x a : E} (hB : mobiusBracketSq x a ≠ 0) :
    mobiusInvol a x - a
      = (-((1 - ‖a‖ ^ 2) / mobiusBracketSq x a)) • (x - ‖x‖ ^ 2 • a) := by
  have hD : ‖x - a‖ ^ 2 = mobiusBracketSq x a - (1 - ‖x‖ ^ 2) * (1 - ‖a‖ ^ 2) := by
    rw [mobiusBracketSq_eq_add]; ring
  rw [mobiusInvol_eq, hD]
  match_scalars
  · field_simp
    ring
  · field_simp

/-- `‖σ_a(x) - a‖² = (1-‖a‖²)²‖x‖²/[x,a]²`, by taking norms in the previous identity and using
`‖x - ‖x‖² a‖² = ‖x‖² [x,a]²`. -/
theorem norm_sq_mobiusInvol_sub_self {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    ‖mobiusInvol a x - a‖ ^ 2 = (1 - ‖a‖ ^ 2) ^ 2 * ‖x‖ ^ 2 / mobiusBracketSq x a := by
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hB' : mobiusBracketSq x a ≠ 0 := ne_of_gt hB
  have haux : ‖x - ‖x‖ ^ 2 • a‖ ^ 2 = ‖x‖ ^ 2 * mobiusBracketSq x a := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, mobiusBracketSq]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [mobiusInvol_sub_self hB', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, haux]
  field_simp

/-- `[σ_a(x),a]² = (1-‖a‖²)²/[x,a]²`. The two contributions to
`mobiusBracketSq_eq_add` at the image point are `(1-‖a‖²)²‖x‖²/[x,a]²` and
`(1-‖a‖²)²(1-‖x‖²)/[x,a]²`, and they add up with `‖x‖²` cancelling. -/
theorem mobiusBracketSq_mobiusInvol {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    mobiusBracketSq (mobiusInvol a x) a = (1 - ‖a‖ ^ 2) ^ 2 / mobiusBracketSq x a := by
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hB' : mobiusBracketSq x a ≠ 0 := ne_of_gt hB
  have hnorm : 1 - ‖mobiusInvol a x‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) / mobiusBracketSq x a := by
    rw [norm_mobiusInvol]
    exact one_sub_norm_sq_mobius hx ha
  rw [mobiusBracketSq_eq_add, norm_sq_mobiusInvol_sub_self hx ha, hnorm]
  field_simp
  ring

/-- **The involution property**, `σ_a(σ_a x) = x`. Substituting the three identities into the
definition of `σ_a` makes every bracket cancel. -/
theorem mobiusInvol_mobiusInvol {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    mobiusInvol a (mobiusInvol a x) = x := by
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hB' : mobiusBracketSq x a ≠ 0 := ne_of_gt hB
  have hA : (0 : ℝ) < 1 - ‖a‖ ^ 2 := one_sub_norm_sq_pos ha
  have hA' : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := ne_of_gt hA
  rw [mobiusInvol_eq a (mobiusInvol a x), norm_sq_mobiusInvol_sub_self hx ha,
    mobiusBracketSq_mobiusInvol hx ha, mobiusInvol_sub_self hB']
  match_scalars
  · field_simp
    ring
  · field_simp

/-! ## Bijectivity on the ball -/

/-- `φ_a` is injective on the ball: it is the negative of an involution. -/
theorem injOn_mobius {a : E} (ha : ‖a‖ < 1) : InjOn (mobius a) (ball (0 : E) 1) := by
  intro x hx y hy hxy
  have hx' : ‖x‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.1 hx)
  have hy' : ‖y‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.1 hy)
  have hinvol : mobiusInvol a x = mobiusInvol a y := by rw [mobiusInvol, mobiusInvol, hxy]
  calc x = mobiusInvol a (mobiusInvol a x) := (mobiusInvol_mobiusInvol hx' ha).symm
    _ = mobiusInvol a (mobiusInvol a y) := by rw [hinvol]
    _ = y := mobiusInvol_mobiusInvol hy' ha

/-- **`φ_a` maps the ball onto the ball.** Given `y` in the ball, `σ_a(-y)` is a preimage, because
`σ_a` is an involution of the ball and `φ_a = -σ_a`. -/
theorem image_mobius {a : E} (ha : ‖a‖ < 1) :
    mobius a '' ball (0 : E) 1 = ball (0 : E) 1 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact mem_ball_zero_iff.2 (norm_mobius_lt_one (mem_ball_zero_iff.1 hx) ha)
  · intro y hy
    have hy' : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
    have hny : ‖(-y : E)‖ < 1 := by rwa [norm_neg]
    refine ⟨mobiusInvol a (-y), mem_ball_zero_iff.2 (norm_mobiusInvol_lt_one hny ha), ?_⟩
    have h := mobiusInvol_mobiusInvol (x := (-y : E)) (a := a) (le_of_lt hny) ha
    rw [← neg_mobiusInvol, h, neg_neg]

end HyperbolicSpace

end

end
