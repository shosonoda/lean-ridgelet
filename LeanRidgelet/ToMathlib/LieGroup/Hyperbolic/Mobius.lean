/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.BallModel

/-!
# Möbius transformations of the unit ball and the cocycle of the composite distance

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

The isometries of `ℍ^m` that move the origin are the Möbius transformations of the ball. Following
L. Ahlfors, for `a` in the open unit ball put

`[x,a]² := 1 - 2⟪x,a⟫ + ‖x‖²‖a‖²`,   `φ_a(x) := ((1-‖a‖²)(x-a) - ‖x-a‖² a) / [x,a]²`.

The whole file rests on one algebraic identity, and it is worth stating separately because it is
smaller than the classical formulation suggests. Writing `N_x` for the numerator of `φ_a(x)`,

`⟪N_x, N_y⟫` and `[x,a]²[y,a]²` are related by
`[y,a]²‖x-a‖² + [x,a]²‖y-a‖² - 2⟪N_x,N_y⟫ = (1-‖a‖²)²‖x-y‖²`,

a polynomial identity in the six scalars `⟪x,y⟫`, `⟪x,a⟫`, `⟪y,a⟫`, `‖x‖²`, `‖y‖²`, `‖a‖²` — so
`ring` proves it once the inner products are expanded, with no geometry involved. Everything else
is division:

* at `y = x` it gives `‖φ_a(x)‖² = ‖x-a‖²/[x,a]²`, hence
  `1 - ‖φ_a(x)‖² = (1-‖a‖²)(1-‖x‖²)/[x,a]²`, hence that `φ_a` maps the ball to the ball and the
  boundary sphere to itself;
* in general it gives the *conformal distortion*
  `‖φ_a(x) - φ_a(y)‖² = (1-‖a‖²)²‖x-y‖²/([x,a]²[y,a]²)`;
* dividing the two gives the transformation law of the Poisson kernel,
  `P(φ_a x, φ_a u) = P(x,u)/P(a,u)`, that is **the cocycle of the composite distance**
  `⟨φ_a x, φ_a u⟩ = ⟨x,u⟩ - ⟨a,u⟩`.

The cocycle is the hypothesis the abstract Helgason--Fourier layer asks of a model, so proving it
here is what shows that layer is not vacuous. Positivity of `[x,a]²` is not a computation either:
Cauchy--Schwarz gives `(1 - ‖x‖‖a‖)² ≤ [x,a]²`, which is positive as soon as `‖x‖ ≤ 1` and
`‖a‖ < 1` — so the boundary is covered along with the interior.

What is *not* here is the invariance of the volume measure. That needs the Jacobian, hence the
derivative of `φ_a`; the conformal distortion identity below is the statement it will be read off
from, since a map whose difference quotients are a scalar multiple of an isometry has derivative a
scalar multiple of an isometry, and such a derivative has determinant of modulus `λ^m` — exactly the
factor the density `(2/(1-‖x‖²))^m` needs.

## Main definitions

* `HyperbolicSpace.mobiusBracketSq`: Ahlfors' `[x,a]²`.
* `HyperbolicSpace.mobius`: the Möbius transformation `φ_a` of the ball, carrying `a` to the origin.

## Main results

* `HyperbolicSpace.mobiusBracketSq_pos`: `[x,a]² > 0` on the closed ball, by Cauchy--Schwarz.
* `HyperbolicSpace.norm_sq_mobius`: `‖φ_a(x)‖² = ‖x-a‖²/[x,a]²`.
* `HyperbolicSpace.one_sub_norm_sq_mobius`: `1 - ‖φ_a(x)‖² = (1-‖a‖²)(1-‖x‖²)/[x,a]²`.
* `HyperbolicSpace.norm_mobius_lt_one`, `HyperbolicSpace.norm_mobius_eq_one`: the ball and the
  boundary are preserved.
* `HyperbolicSpace.norm_sq_mobius_sub`: the conformal distortion identity.
* `HyperbolicSpace.poissonKernel_mobius` and
  `HyperbolicSpace.compositeDistance_mobius`: **the cocycle**.
-/

@[expose] public section

noncomputable section

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Ahlfors' bracket -/

/-- Ahlfors' bracket, `[x,a]² = 1 - 2⟪x,a⟫ + ‖x‖²‖a‖²`, the denominator of the Möbius
transformation of the unit ball.

For a boundary point it is the squared Euclidean distance to `a`
(`mobiusBracketSq_of_norm_eq_one`), which is why the transformation law of the Poisson kernel comes
out as cleanly as it does. -/
def mobiusBracketSq (x a : E) : ℝ := 1 - 2 * (inner ℝ x a : ℝ) + ‖x‖ ^ 2 * ‖a‖ ^ 2

@[simp] theorem mobiusBracketSq_zero_right (x : E) : mobiusBracketSq x (0 : E) = 1 := by
  simp [mobiusBracketSq]

@[simp] theorem mobiusBracketSq_zero_left (a : E) : mobiusBracketSq (0 : E) a = 1 := by
  simp [mobiusBracketSq]

/-- On the boundary the bracket is the squared Euclidean distance. -/
theorem mobiusBracketSq_of_norm_eq_one {u : E} (hu : ‖u‖ = 1) (a : E) :
    mobiusBracketSq u a = ‖u - a‖ ^ 2 := by
  rw [mobiusBracketSq, norm_sub_sq_real, hu]
  ring

/-- Cauchy--Schwarz bounds the bracket below by `(1 - ‖x‖‖a‖)²`. This is the only inequality in the
file, and it is what makes the bracket positive on the *closed* ball. -/
theorem one_sub_mul_sq_le_mobiusBracketSq (x a : E) :
    (1 - ‖x‖ * ‖a‖) ^ 2 ≤ mobiusBracketSq x a := by
  have h := real_inner_le_norm x a
  rw [mobiusBracketSq]
  nlinarith [h]

theorem mobiusBracketSq_pos {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    0 < mobiusBracketSq x a := by
  have hle : ‖x‖ * ‖a‖ < 1 := by
    calc ‖x‖ * ‖a‖ ≤ 1 * ‖a‖ := by
          exact mul_le_mul_of_nonneg_right hx (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < 1 := ha
  have hpos : 0 < (1 - ‖x‖ * ‖a‖) ^ 2 := by positivity
  exact lt_of_lt_of_le hpos (one_sub_mul_sq_le_mobiusBracketSq x a)

theorem mobiusBracketSq_ne_zero {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    mobiusBracketSq x a ≠ 0 :=
  ne_of_gt (mobiusBracketSq_pos hx ha)

/-! ## The transformation -/

/-- The numerator of the Möbius transformation, `N_x = (1-‖a‖²)(x-a) - ‖x-a‖² a`. -/
def mobiusNum (a x : E) : E := (1 - ‖a‖ ^ 2) • (x - a) - ‖x - a‖ ^ 2 • a

/-- **The Möbius transformation of the unit ball** carrying `a` to the origin,
`φ_a(x) = ((1-‖a‖²)(x-a) - ‖x-a‖² a)/[x,a]²`.

In one dimension this is `x ↦ (x-a)/(1-ax)`. It sends `a` to `0` and `0` to `-a`; the involution
that swaps them is its negative. -/
def mobius (a x : E) : E := (mobiusBracketSq x a)⁻¹ • mobiusNum a x

@[simp] theorem mobius_self (a : E) : mobius a a = 0 := by
  simp [mobius, mobiusNum]

@[simp] theorem mobius_zero_left (x : E) : mobius (0 : E) x = x := by
  simp [mobius, mobiusNum]

@[simp] theorem mobius_zero_right (a : E) : mobius a (0 : E) = -a := by
  have h : mobiusNum a (0 : E) = -a := by
    rw [mobiusNum]
    rw [zero_sub, norm_neg, smul_neg, sub_eq_add_neg, ← neg_add]
    rw [← add_smul]
    have : (1 : ℝ) - ‖a‖ ^ 2 + ‖a‖ ^ 2 = 1 := by ring
    rw [this, one_smul]
  rw [mobius, mobiusBracketSq_zero_left, h, inv_one, one_smul]

/-! ## The algebraic identity -/

/-- The inner product of two numerators, expanded into the six scalars
`⟪x,y⟫`, `⟪x,a⟫`, `⟪y,a⟫`, `‖x‖²`, `‖y‖²`, `‖a‖²`. Stated with free coefficients because it is used
both on the diagonal and off it. -/
private theorem inner_smul_sub_smul (c d c' d' : ℝ) (x y a : E) :
    (inner ℝ (c • (x - a) - d • a) (c' • (y - a) - d' • a) : ℝ)
      = c * c' * ((inner ℝ x y : ℝ) - (inner ℝ x a : ℝ) - (inner ℝ y a : ℝ) + ‖a‖ ^ 2)
        - c * d' * ((inner ℝ x a : ℝ) - ‖a‖ ^ 2)
        - d * c' * ((inner ℝ y a : ℝ) - ‖a‖ ^ 2)
        + d * d' * ‖a‖ ^ 2 := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm a x, real_inner_comm a y]
  ring

/-- **The identity the file rests on.** In terms of the numerators `N_x`, `N_y` and the brackets,

`[y,a]²‖x-a‖² + [x,a]²‖y-a‖² - 2⟪N_x,N_y⟫ = (1-‖a‖²)²‖x-y‖²`.

It is a polynomial identity in the six scalars, so `ring` proves it; no geometry enters. -/
theorem mobiusNum_key (a x y : E) :
    mobiusBracketSq y a * ‖x - a‖ ^ 2 + mobiusBracketSq x a * ‖y - a‖ ^ 2
        - 2 * (inner ℝ (mobiusNum a x) (mobiusNum a y) : ℝ)
      = (1 - ‖a‖ ^ 2) ^ 2 * ‖x - y‖ ^ 2 := by
  have hx : ‖x - a‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℝ x a : ℝ) + ‖a‖ ^ 2 := norm_sub_sq_real x a
  have hy : ‖y - a‖ ^ 2 = ‖y‖ ^ 2 - 2 * (inner ℝ y a : ℝ) + ‖a‖ ^ 2 := norm_sub_sq_real y a
  have hxy : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℝ x y : ℝ) + ‖y‖ ^ 2 := norm_sub_sq_real x y
  rw [mobiusNum, mobiusNum, inner_smul_sub_smul, mobiusBracketSq, mobiusBracketSq, hx, hy, hxy]
  ring

/-- The diagonal case: `‖N_x‖² = ‖x-a‖² [x,a]²`. -/
theorem norm_sq_mobiusNum (a x : E) :
    ‖mobiusNum a x‖ ^ 2 = ‖x - a‖ ^ 2 * mobiusBracketSq x a := by
  have h := mobiusNum_key a x x
  rw [sub_self, norm_zero] at h
  rw [← real_inner_self_eq_norm_sq]
  linarith [h]

/-! ## The ball and the boundary are preserved -/

theorem norm_sq_mobius {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    ‖mobius a x‖ ^ 2 = ‖x - a‖ ^ 2 / mobiusBracketSq x a := by
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hB' : mobiusBracketSq x a ≠ 0 := ne_of_gt hB
  rw [mobius, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sq_mobiusNum]
  field_simp

/-- `1 - ‖φ_a(x)‖² = (1-‖a‖²)(1-‖x‖²)/[x,a]²`: the identity from which both the preservation of the
ball and the transformation law of the Poisson kernel follow. -/
theorem one_sub_norm_sq_mobius {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    1 - ‖mobius a x‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) / mobiusBracketSq x a := by
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hxa : ‖x - a‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℝ x a : ℝ) + ‖a‖ ^ 2 := norm_sub_sq_real x a
  rw [norm_sq_mobius hx ha]
  rw [eq_div_iff (ne_of_gt hB), sub_mul, div_mul_cancel₀ _ (ne_of_gt hB), mobiusBracketSq, hxa]
  ring

/-- The Möbius transformation maps the open ball into itself. -/
theorem norm_mobius_lt_one {x a : E} (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) : ‖mobius a x‖ < 1 := by
  have hx' : ‖x‖ ≤ 1 := le_of_lt hx
  have hB : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx' ha
  have hnum : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) :=
    mul_pos (one_sub_norm_sq_pos ha) (one_sub_norm_sq_pos hx)
  have h : 0 < 1 - ‖mobius a x‖ ^ 2 := by
    rw [one_sub_norm_sq_mobius hx' ha]
    exact div_pos hnum hB
  nlinarith [norm_nonneg (mobius a x)]

/-- The Möbius transformation maps the boundary sphere into itself. -/
theorem norm_mobius_eq_one {u a : E} (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) : ‖mobius a u‖ = 1 := by
  have hu' : ‖u‖ ≤ 1 := le_of_eq hu
  have h : 1 - ‖mobius a u‖ ^ 2 = 0 := by
    rw [one_sub_norm_sq_mobius hu' ha, hu]
    simp
  have hfac : (‖mobius a u‖ - 1) * (‖mobius a u‖ + 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.1 hfac with hz | hz
  · linarith
  · nlinarith [norm_nonneg (mobius a u)]

/-! ## The conformal distortion -/

/-- **The conformal distortion identity**,
`‖φ_a(x) - φ_a(y)‖² = (1-‖a‖²)²‖x-y‖²/([x,a]²[y,a]²)`.

The distortion depends on the two points only through the two brackets, which is conformality: in
the limit `y → x` it says the derivative of `φ_a` at `x` is `(1-‖a‖²)/[x,a]²` times a linear
isometry. That is what a later file will read the Jacobian of the invariant measure off. -/
theorem norm_sq_mobius_sub {x y a : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (ha : ‖a‖ < 1) :
    ‖mobius a x - mobius a y‖ ^ 2
      = (1 - ‖a‖ ^ 2) ^ 2 * ‖x - y‖ ^ 2 / (mobiusBracketSq x a * mobiusBracketSq y a) := by
  have hBx : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx ha
  have hBy : (0 : ℝ) < mobiusBracketSq y a := mobiusBracketSq_pos hy ha
  have hBx' : mobiusBracketSq x a ≠ 0 := ne_of_gt hBx
  have hBy' : mobiusBracketSq y a ≠ 0 := ne_of_gt hBy
  -- the two numerators, put over the common denominator `[x,a]²[y,a]²`
  have hcomb : ‖mobiusBracketSq y a • mobiusNum a x - mobiusBracketSq x a • mobiusNum a y‖ ^ 2
      = mobiusBracketSq x a * mobiusBracketSq y a * ((1 - ‖a‖ ^ 2) ^ 2 * ‖x - y‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    rw [norm_sq_mobiusNum, norm_sq_mobiusNum]
    linear_combination (mobiusBracketSq x a * mobiusBracketSq y a) * mobiusNum_key a x y
  have hx1 : mobius a x = (mobiusBracketSq x a * mobiusBracketSq y a)⁻¹ •
      (mobiusBracketSq y a • mobiusNum a x) := by
    rw [mobius, smul_smul]
    congr 1
    field_simp
  have hy1 : mobius a y = (mobiusBracketSq x a * mobiusBracketSq y a)⁻¹ •
      (mobiusBracketSq x a • mobiusNum a y) := by
    rw [mobius, smul_smul]
    congr 1
    field_simp
  rw [hx1, hy1, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hcomb]
  field_simp

/-! ## The cocycle -/

/-- **The transformation law of the Poisson kernel**, `P(φ_a x, φ_a u) = P(x,u)/P(a,u)`.

Dividing the two preceding identities cancels the brackets at `x` completely and leaves the bracket
at the boundary point, which is `‖u-a‖²` there — that is `P(a,u)^{-1}` up to `1-‖a‖²`. -/
theorem poissonKernel_mobius {x u a : E} (hx : ‖x‖ < 1) (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    poissonKernel (mobius a x) (mobius a u) = poissonKernel x u / poissonKernel a u := by
  have hx' : ‖x‖ ≤ 1 := le_of_lt hx
  have hu' : ‖u‖ ≤ 1 := le_of_eq hu
  have hBx : (0 : ℝ) < mobiusBracketSq x a := mobiusBracketSq_pos hx' ha
  have hBu : (0 : ℝ) < mobiusBracketSq u a := mobiusBracketSq_pos hu' ha
  have hua : (0 : ℝ) < ‖u - a‖ ^ 2 := by
    rw [← mobiusBracketSq_of_norm_eq_one hu a]; exact hBu
  have hAa : (0 : ℝ) < 1 - ‖a‖ ^ 2 := one_sub_norm_sq_pos ha
  have hxu : (0 : ℝ) < ‖x - u‖ ^ 2 := by
    have : x - u ≠ 0 := sub_ne_zero_of_ne (ne_of_mem_ball_of_mem_sphere hx hu)
    positivity
  have hBx' : mobiusBracketSq x a ≠ 0 := ne_of_gt hBx
  have hua' : ‖u - a‖ ^ 2 ≠ 0 := ne_of_gt hua
  have hAa' : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := ne_of_gt hAa
  have hxu' : ‖x - u‖ ^ 2 ≠ 0 := ne_of_gt hxu
  rw [poissonKernel, poissonKernel, poissonKernel, one_sub_norm_sq_mobius hx' ha,
    norm_sq_mobius_sub hx' hu' ha, mobiusBracketSq_of_norm_eq_one hu a, norm_sub_rev a u]
  field_simp

/-- **The cocycle of the composite distance**, `⟨φ_a x, φ_a u⟩ = ⟨x,u⟩ - ⟨a,u⟩`.

This is the identity the abstract Helgason--Fourier layer asks of a model: it is what turns the
action of the isometry group on `ℍ^m` into a multiplier on the Helgason--Fourier kernel, since the
kernel is the exponential of a linear functional of the composite distance and so is multiplicative
in it. -/
theorem compositeDistance_mobius {x u a : E} (hx : ‖x‖ < 1) (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    compositeDistance (mobius a x) (mobius a u)
      = compositeDistance x u - compositeDistance a u := by
  have hPx : 0 < poissonKernel x u := poissonKernel_pos hx hu
  have hPa : 0 < poissonKernel a u := poissonKernel_pos ha hu
  rw [compositeDistance, compositeDistance, compositeDistance, poissonKernel_mobius hx hu ha,
    Real.log_div (ne_of_gt hPx) (ne_of_gt hPa)]

end HyperbolicSpace

end

end
