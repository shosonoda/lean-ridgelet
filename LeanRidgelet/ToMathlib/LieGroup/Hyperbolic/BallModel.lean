/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Poincaré ball model of real hyperbolic space

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib has the upper half plane with its hyperbolic metric, but only in dimension two
(`Mathlib.Analysis.Complex.UpperHalfPlane`), and no hyperbolic space of general dimension. This
file starts the Poincaré ball model of `ℍ^m = SO⁺(1,m)/O(m)`, the rank-one noncompact symmetric
space, in the form the Helgason--Fourier theory needs.

Nothing here uses Riemannian geometry. Mathlib's `Geometry.Manifold.Riemannian` has neither a
volume measure nor a Laplace--Beltrami operator, so the invariant measure is *defined* as the
weighted Lebesgue measure `(2/(1-‖x‖²))^m dx` on the open unit ball, and the identification with
the Riemannian volume of the metric `4(1-‖x‖²)^{-2}∑ dx_i ⊗ dx_i` is a remark, not a dependency.

The two objects the theory is built from are the Poisson kernel `P(x,u) = (1-‖x‖²)/‖x-u‖²` and its
logarithm, the composite distance `⟨x,u⟩`. In the ball model the origin is at distance zero from
every horosphere through it, so `⟨0,u⟩ = 0` for every boundary point — that is the normalization
which makes `e^{(-iλ+ϱ)⟨x,u⟩}` the analogue of the plane wave `e^{-i⟪λ,x⟫}` based at the origin.

## Main definitions

* `HyperbolicSpace.poissonKernel`: `P(x,u) = (1 - ‖x‖²)/‖x - u‖²`.
* `HyperbolicSpace.compositeDistance`: `⟨x,u⟩ = log P(x,u)`, the rank-one composite distance.
* `HyperbolicSpace.rho`: the half-sum of the positive restricted roots, `ϱ = (m-1)/2`.
* `HyperbolicSpace.invariantMeasure`: the `G`-invariant measure `(2/(1-‖x‖²))^m dx` on the ball.

## Main results

* `HyperbolicSpace.compositeDistance_origin`: `⟨0,u⟩ = 0` on the boundary.
* `HyperbolicSpace.exp_compositeDistance`: `e^{⟨x,u⟩} = P(x,u)` inside the ball, the positivity of
  the Poisson kernel being what makes the logarithm faithful.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The ball, its boundary, and the Poisson kernel -/

/-- The Poincaré ball model of real hyperbolic space: the open unit ball of a Euclidean space.
The dimension of the space is the dimension of `ℍ^m`. -/
def poincareBall (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Set E :=
  ball (0 : E) 1

/-- The ideal boundary `∂ℍ^m = 𝕊^{m-1}`, the unit sphere. -/
def idealBoundary (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Set E :=
  sphere (0 : E) 1

theorem mem_poincareBall_iff {x : E} : x ∈ poincareBall E ↔ ‖x‖ < 1 := by
  simp [poincareBall]

theorem mem_idealBoundary_iff {u : E} : u ∈ idealBoundary E ↔ ‖u‖ = 1 := by
  simp [idealBoundary]

/-- The Poisson kernel of the ball, `P(x,u) = (1 - ‖x‖²)/‖x - u‖²`.

Its logarithm is the composite distance and its `ϱ`-th power is the weight `e^{ϱ⟨x,u⟩}` that a
layer of a network on `ℍ^m` carries. For `m = 2` it is the classical Poisson kernel of the disk;
for `m > 2` the classical Euclidean one is `(1-‖x‖²)/‖x-u‖^m`, and the two differ because the
hyperbolic and the Euclidean Laplacians only share their harmonic functions in dimension two. -/
def poissonKernel (x u : E) : ℝ := (1 - ‖x‖ ^ 2) / ‖x - u‖ ^ 2

/-- The rank-one vector-valued composite distance `⟨x,u⟩ = log((1 - ‖x‖²)/‖x - u‖²)`, the signed
distance from the origin to the horosphere through `x` with normal `u`.

The rank of `ℍ^m` is one, so `𝔞 ≅ ℝ` and the "vector-valued" distance is a scalar. -/
def compositeDistance (x u : E) : ℝ := Real.log (poissonKernel x u)

/-- The half-sum of the positive restricted roots of `ℍ^m`, `ϱ = (m-1)/2`, as an element of
`𝔞* ≅ ℝ`. -/
def rho (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : ℝ :=
  ((Module.finrank ℝ E : ℝ) - 1) / 2

/-! ## Positivity and the normalization at the origin -/

omit [InnerProductSpace ℝ E] in
theorem ne_of_mem_ball_of_mem_sphere {x u : E} (hx : ‖x‖ < 1) (hu : ‖u‖ = 1) : x ≠ u := by
  rintro rfl
  exact absurd hu (ne_of_lt hx)

omit [InnerProductSpace ℝ E] in
theorem one_sub_norm_sq_pos {x : E} (hx : ‖x‖ < 1) : 0 < 1 - ‖x‖ ^ 2 := by
  nlinarith [norm_nonneg x]

omit [InnerProductSpace ℝ E] in
theorem poissonKernel_pos {x u : E} (hx : ‖x‖ < 1) (hu : ‖u‖ = 1) : 0 < poissonKernel x u := by
  have hnum : 0 < 1 - ‖x‖ ^ 2 := one_sub_norm_sq_pos hx
  have hden : 0 < ‖x - u‖ ^ 2 := by
    have : x - u ≠ 0 := sub_ne_zero_of_ne (ne_of_mem_ball_of_mem_sphere hx hu)
    positivity
  exact div_pos hnum hden

omit [InnerProductSpace ℝ E] in
@[simp] theorem poissonKernel_origin {u : E} (hu : ‖u‖ = 1) : poissonKernel (0 : E) u = 1 := by
  simp [poissonKernel, hu]

omit [InnerProductSpace ℝ E] in
/-- The origin of the ball lies on every horosphere through it: the composite distance from the
origin to a boundary point vanishes. This is the normalization that makes `e^{(-iλ+ϱ)⟨x,u⟩}` the
analogue of a plane wave based at the origin. -/
@[simp] theorem compositeDistance_origin {u : E} (hu : ‖u‖ = 1) :
    compositeDistance (0 : E) u = 0 := by
  simp [compositeDistance, hu]

omit [InnerProductSpace ℝ E] in
/-- Inside the ball the Poisson kernel is positive, so it is recovered from the composite
distance. -/
theorem exp_compositeDistance {x u : E} (hx : ‖x‖ < 1) (hu : ‖u‖ = 1) :
    Real.exp (compositeDistance x u) = poissonKernel x u :=
  Real.exp_log (poissonKernel_pos hx hu)

/-! ## The invariant measure -/

/-- The density of the `G`-invariant measure of `ℍ^m` against Lebesgue measure in the Poincaré ball
model, `(2/(1 - ‖x‖²))^m`. It is the Riemannian volume density of the metric
`4(1 - ‖x‖²)^{-2}∑ dx_i ⊗ dx_i`, but is taken here as a definition so that no manifold theory is
needed. -/
def volumeDensity (x : E) : ℝ := (2 / (1 - ‖x‖ ^ 2)) ^ (Module.finrank ℝ E)

theorem volumeDensity_pos [FiniteDimensional ℝ E] {x : E} (hx : ‖x‖ < 1) : 0 < volumeDensity x := by
  have := one_sub_norm_sq_pos hx
  unfold volumeDensity
  positivity

/-- The `G`-invariant measure of `ℍ^m` in the Poincaré ball model. Its invariance under the Möbius
transformations of the ball is the content of a later file; here it is only defined.

It is a measure on the whole space rather than on the ball as a subtype, concentrated on the ball
by the restriction. That keeps `ℍ^m` a plain Euclidean space for every downstream construction and
avoids carrying a subtype through the Helgason--Fourier theory; nothing outside the ball is ever
seen, since the density is integrated against the restricted measure. -/
def invariantMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (volume.restrict (poincareBall E)).withDensity fun x => ENNReal.ofReal (volumeDensity x)

end HyperbolicSpace

end

end
