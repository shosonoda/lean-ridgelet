/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.HelgasonFourier
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusMeasure

/-!
# The Möbius transformation on the ideal boundary

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`φ_a` preserves the unit sphere, so it restricts to a self-map `∂φ_a` of the ideal boundary
`∂ℍ^m = 𝕊^{m-1}`. This file identifies that restriction: it is a conformal bijection of the sphere
whose multiplier is the Poisson kernel. Everything is algebra, with one appeal to differentiability
for continuity; no measure theory and no differential geometry enter.

One rewriting is the whole content. On the boundary Ahlfors' bracket is the squared Euclidean
distance, `[u,a]² = ‖u-a‖²`, so the conformal factor `λ_a(x) = (1-‖a‖²)/[x,a]²` of
`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusMeasure` restricted to the boundary *is* the
Poisson kernel,

`λ_a(u) = (1-‖a‖²)/‖u-a‖² = (1-‖a‖²)/‖a-u‖² = P(a,u)`.

Substituting that into the conformal distortion identity `‖φ_a x - φ_a y‖² = λ_a(x)λ_a(y)‖x-y‖²`
gives the multiplier form on the boundary,

`‖∂φ_a(u) - ∂φ_a(v)‖² = P(a,u) P(a,v) ‖u-v‖²`,

so `∂φ_a` multiplies the chordal distance of the sphere by the geometric mean of the Poisson kernel
at the two endpoints. That is conformality of the boundary map in metric form, with multiplier
`P(a,·)`; no derivative along the sphere is taken, and the statement needs none.

The map is bijective, with inverse `u ↦ σ_a(-u)` for the involution `σ_a = -φ_a` of
`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusInverse`. The negation there is not decoration:
`φ_a` is not an involution, only `σ_a` is. Continuity in both directions comes from the
differentiability of `φ_a` on the closed ball, so `∂φ_a` is a homeomorphism of `𝕊^{m-1}`.

## Main definitions

* `HyperbolicSpace.boundaryMobius`: `∂φ_a`, the restriction of `φ_a` to the ideal boundary, as a
  self-map of `Metric.sphere (0 : E) 1`.
* `HyperbolicSpace.boundaryMobiusSymm`: its inverse, the restriction of `u ↦ σ_a(-u)`.
* `HyperbolicSpace.boundaryMobiusEquiv`, `HyperbolicSpace.boundaryMobiusHomeomorph`: the bundled
  forms.

## Main results

* `HyperbolicSpace.mobiusFactor_eq_poissonKernel`: on the boundary the conformal factor is the
  Poisson kernel.
* `HyperbolicSpace.norm_sq_mobius_sub_of_mem_sphere` and `HyperbolicSpace.dist_boundaryMobius`:
  **conformality with multiplier `P(a,·)`**, squared and as an identity between distances.
* `HyperbolicSpace.bijective_boundaryMobius`, `HyperbolicSpace.continuous_boundaryMobius`.
* `HyperbolicSpace.boundaryDistance_mobius`: the transformation law of the composite distance read
  on the boundary sphere, `⟨φ_a x, ∂φ_a u⟩ = ⟨x,u⟩ - ⟨a,u⟩`.

## The abstract cocycle predicate does not apply as stated

`SymmetricSpace.IsCompositeCocycle T S A shift` asks for `A (T x) (S b) = A x b + shift b` at
*every* `x` of one type `X`. With `X = E`, `A = HyperbolicSpace.boundaryDistance`, `T = φ_a` and
`S = ∂φ_a` that statement is false for `a ≠ 0`, not merely unproved: the composite distance of the
ball model is defined on all of `E` and carries a junk value outside the ball, and at `x = u` — a
boundary point equal to the normal — both sides of its defining quotient vanish, so
`⟨u,u⟩ = Real.log 0 = 0` and likewise `⟨φ_a u, ∂φ_a u⟩ = 0`
(`HyperbolicSpace.boundaryDistance_coe_self`). The identity would then force `⟨a,u⟩ = 0`, that is
`P(a,u) = 1`, for every boundary point, which already fails at `u = a/‖a‖`, where
`P(a,u) = (1+‖a‖)/(1-‖a‖)`. The honest domain is the ball, so an instance would need `X` to be the
subtype `poincareBall E` and `A` to be the restriction of `boundaryDistance` rather than the
function `HyperbolicSpace.HasInversion` is stated with. The law is therefore recorded as the plain
lemma `HyperbolicSpace.boundaryDistance_mobius`, carrying the hypothesis `‖x‖ < 1` that makes it
true, and no instance of the predicate is produced.

## What is proved, and what is still missing

Proved: `∂φ_a` is a homeomorphism of `𝕊^{m-1}`, and it multiplies the chordal distance by
`√(P(a,u)P(a,v))`, so its multiplier is the Poisson kernel `P(a,·)`.

Not proved, and what the quasi-invariance of `HyperbolicSpace.boundaryMeasure` needs on top of the
above: the measure-theoretic step `d(∂φ_a u) = P(a,u)^{m-1} du`, that a conformal self-map of the
sphere scales the surface measure by the `(m-1)`-st power of its multiplier. The gap is in Mathlib,
not in the identities here: there is no change-of-variables formula for a Hausdorff measure on a
submanifold. `MeasureTheory.Measure.toSphere`, which defines the boundary measure, is built from the
polar decomposition of Lebesgue measure and comes with no transformation law under a map of the
sphere, and `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` is a statement about the
ambient measure, for which the sphere is null. Supplying that theory is the remaining step.
-/

@[expose] public section

noncomputable section

open Metric

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The multiplier on the boundary is the Poisson kernel -/

/-- On the ideal boundary the conformal factor of the Möbius transformation is the Poisson kernel,
`λ_a(u) = P(a,u)`. Ahlfors' bracket `[u,a]²` is the squared Euclidean distance `‖u-a‖²` there, and
that is the denominator of `P(a,u)`. The hypothesis `‖a‖ < 1` is not needed: both sides are
quotients, and no positivity is used. -/
theorem mobiusFactor_eq_poissonKernel {u a : E} (hu : ‖u‖ = 1) :
    mobiusFactor a u = poissonKernel a u := by
  rw [mobiusFactor, poissonKernel, mobiusBracketSq_of_norm_eq_one hu a, norm_sub_rev a u]

/-- **The Möbius transformation is conformal on the ideal boundary with multiplier the Poisson
kernel**: `‖φ_a u - φ_a v‖² = P(a,u) P(a,v) ‖u-v‖²` for boundary points `u`, `v`.

The squared chordal distance is multiplied by the product of the multipliers at the two endpoints,
which is conformality with multiplier `P(a,·)`: it is the conformal distortion identity of
`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusMeasure` with both factors read on the boundary
by `HyperbolicSpace.mobiusFactor_eq_poissonKernel`. -/
theorem norm_sq_mobius_sub_of_mem_sphere {u v a : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : ‖a‖ < 1) :
    ‖mobius a u - mobius a v‖ ^ 2 = poissonKernel a u * poissonKernel a v * ‖u - v‖ ^ 2 := by
  rw [norm_sq_mobius_sub_eq_mul (le_of_eq hu) (le_of_eq hv) ha, mobiusFactor_eq_poissonKernel hu,
    mobiusFactor_eq_poissonKernel hv]

/-! ## The boundary map and its inverse -/

/-- **The Möbius transformation on the ideal boundary**, `∂φ_a`: the restriction of `φ_a` to
`∂ℍ^m = 𝕊^{m-1}`, a self-map of the sphere by `HyperbolicSpace.norm_mobius_eq_one`.

The hypothesis `‖a‖ < 1` is an explicit argument rather than an instance or a bundled point of the
ball: it is exactly what the codomain claim needs, it is the form every lemma of this family takes
it in, and proof irrelevance makes the map independent of which proof is supplied. -/
def boundaryMobius (a : E) (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨mobius a (u : E),
    mem_sphere_zero_iff_norm.2 (norm_mobius_eq_one (mem_sphere_zero_iff_norm.1 u.2) ha)⟩

@[simp] theorem coe_boundaryMobius {a : E} (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) :
    (boundaryMobius a ha u : E) = mobius a (u : E) := rfl

/-- The inverse of `∂φ_a` on the ideal boundary, the restriction of `u ↦ σ_a(-u)`.

The negation is essential rather than cosmetic: `φ_a` is not an involution, its negative `σ_a` is
(`HyperbolicSpace.mobiusInvol_mobiusInvol`), so the inverse of `φ_a` is `y ↦ σ_a(-y)` — in one
dimension `y ↦ (y+a)/(1+ay)` against `φ_a(x) = (x-a)/(1-ax)`. -/
def boundaryMobiusSymm (a : E) (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨mobiusInvol a (-(u : E)), mem_sphere_zero_iff_norm.2 (by
    rw [norm_mobiusInvol]
    exact norm_mobius_eq_one (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.1 u.2) ha)⟩

@[simp] theorem coe_boundaryMobiusSymm {a : E} (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) :
    (boundaryMobiusSymm a ha u : E) = mobiusInvol a (-(u : E)) := rfl

theorem boundaryMobiusSymm_boundaryMobius {a : E} (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) :
    boundaryMobiusSymm a ha (boundaryMobius a ha u) = u := by
  have hu : ‖(u : E)‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.1 u.2)
  have hneg : -mobius a (u : E) = mobiusInvol a (u : E) := rfl
  refine Subtype.ext ?_
  rw [coe_boundaryMobiusSymm, coe_boundaryMobius, hneg, mobiusInvol_mobiusInvol hu ha]

theorem boundaryMobius_boundaryMobiusSymm {a : E} (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) :
    boundaryMobius a ha (boundaryMobiusSymm a ha u) = u := by
  have hu : ‖(-(u : E))‖ ≤ 1 := by
    rw [norm_neg]
    exact le_of_eq (mem_sphere_zero_iff_norm.1 u.2)
  refine Subtype.ext ?_
  rw [coe_boundaryMobius, coe_boundaryMobiusSymm, ← neg_mobiusInvol a (mobiusInvol a (-(u : E))),
    mobiusInvol_mobiusInvol hu ha, neg_neg]

/-- **The boundary map is a bijection of the sphere**, the inverse being the boundary restriction of
`u ↦ σ_a(-u)`. -/
def boundaryMobiusEquiv (a : E) (ha : ‖a‖ < 1) : sphere (0 : E) 1 ≃ sphere (0 : E) 1 where
  toFun := boundaryMobius a ha
  invFun := boundaryMobiusSymm a ha
  left_inv := boundaryMobiusSymm_boundaryMobius ha
  right_inv := boundaryMobius_boundaryMobiusSymm ha

@[simp] theorem coe_boundaryMobiusEquiv (a : E) (ha : ‖a‖ < 1) :
    (boundaryMobiusEquiv a ha : sphere (0 : E) 1 → sphere (0 : E) 1) = boundaryMobius a ha := rfl

theorem injective_boundaryMobius {a : E} (ha : ‖a‖ < 1) :
    Function.Injective (boundaryMobius a ha) := (boundaryMobiusEquiv a ha).injective

theorem surjective_boundaryMobius {a : E} (ha : ‖a‖ < 1) :
    Function.Surjective (boundaryMobius a ha) := (boundaryMobiusEquiv a ha).surjective

theorem bijective_boundaryMobius {a : E} (ha : ‖a‖ < 1) :
    Function.Bijective (boundaryMobius a ha) := (boundaryMobiusEquiv a ha).bijective

/-! ## Conformality as an identity between distances -/

/-- **Conformality of the boundary map in metric form**: `∂φ_a` multiplies the chordal distance of
the sphere by the geometric mean of the Poisson kernel at the two endpoints,

`dist (∂φ_a u) (∂φ_a v) = √(P(a,u) P(a,v)) · dist u v`.

This is the square root of `HyperbolicSpace.norm_sq_mobius_sub_of_mem_sphere`, the Poisson kernel
being positive at boundary points. -/
theorem dist_boundaryMobius {a : E} (ha : ‖a‖ < 1) (u v : sphere (0 : E) 1) :
    dist (boundaryMobius a ha u) (boundaryMobius a ha v)
      = Real.sqrt (poissonKernel a (u : E) * poissonKernel a (v : E)) * dist u v := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  have hv : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
  have hP : (0 : ℝ) ≤ poissonKernel a (u : E) * poissonKernel a (v : E) :=
    le_of_lt (mul_pos (poissonKernel_pos ha hu) (poissonKernel_pos ha hv))
  rw [Subtype.dist_eq, Subtype.dist_eq, coe_boundaryMobius, coe_boundaryMobius, dist_eq_norm,
    dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (mobius a (u : E) - mobius a (v : E))),
    norm_sq_mobius_sub_of_mem_sphere hu hv ha, Real.sqrt_mul hP,
    Real.sqrt_sq (norm_nonneg ((u : E) - (v : E)))]

/-! ## Continuity -/

/-- The boundary map is continuous: `φ_a` is differentiable at every point of the closed ball, in
particular at every point of the sphere, and the sphere carries the subspace topology. -/
theorem continuous_boundaryMobius {a : E} (ha : ‖a‖ < 1) : Continuous (boundaryMobius a ha) := by
  have h : Continuous fun u : sphere (0 : E) 1 => mobius a (u : E) := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    have hu : ‖(u : E)‖ ≤ 1 := le_of_eq (mem_sphere_zero_iff_norm.1 u.2)
    exact ((differentiableAt_mobius hu ha).continuousAt).comp continuous_subtype_val.continuousAt
  exact h.subtype_mk _

theorem continuous_boundaryMobiusSymm {a : E} (ha : ‖a‖ < 1) :
    Continuous (boundaryMobiusSymm a ha) := by
  have h : Continuous fun u : sphere (0 : E) 1 => mobiusInvol a (-(u : E)) := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    have hu : ‖(-(u : E))‖ ≤ 1 := by
      rw [norm_neg]
      exact le_of_eq (mem_sphere_zero_iff_norm.1 u.2)
    refine ContinuousAt.comp (g := mobiusInvol a)
      (f := fun v : sphere (0 : E) 1 => -(v : E)) (x := u) ?_ ?_
    · exact ((differentiableAt_mobius hu ha).continuousAt).neg
    · exact (continuous_subtype_val.neg).continuousAt
  exact h.subtype_mk _

/-- **The boundary map is a homeomorphism of the sphere.** Bijectivity is the involution `σ_a`,
continuity in both directions the differentiability of `φ_a` on the closed ball. -/
def boundaryMobiusHomeomorph (a : E) (ha : ‖a‖ < 1) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 where
  toEquiv := boundaryMobiusEquiv a ha
  continuous_toFun := continuous_boundaryMobius ha
  continuous_invFun := continuous_boundaryMobiusSymm ha

/-! ## The transformation law of the composite distance on the boundary -/

omit [InnerProductSpace ℝ E] in
/-- The composite distance of the ball model takes the junk value `0` at a boundary point read
against itself, because `P(u,u) = 0/0 = 0` and `Real.log 0 = 0`.

This is what obstructs an instance of `SymmetricSpace.IsCompositeCocycle` for the Möbius action on
all of `E`, as the module docstring explains: the predicate quantifies over every point of the
ambient space, and there the transformation law would read `0 = 0 - ⟨a,u⟩`. -/
@[simp] theorem boundaryDistance_coe_self (u : sphere (0 : E) 1) :
    boundaryDistance (u : E) u = 0 := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  simp [boundaryDistance, compositeDistance, poissonKernel, hu]

/-- **The transformation law of the composite distance on the boundary sphere**,
`⟨φ_a x, ∂φ_a u⟩ = ⟨x,u⟩ - ⟨a,u⟩`: moving the point of the ball and the boundary normal by the same
Möbius transformation translates `boundaryDistance` by a quantity depending on the normal alone.

This is `HyperbolicSpace.compositeDistance_mobius` transported to the sphere-indexed form the
abstract Helgason--Fourier layer consumes. It is a lemma rather than an instance of
`SymmetricSpace.IsCompositeCocycle`: that predicate asks for the identity at every point of the
ambient space, where it is false, and the hypothesis `‖x‖ < 1` here is what makes it true. See the
module docstring. -/
theorem boundaryDistance_mobius {x a : E} (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) (u : sphere (0 : E) 1) :
    boundaryDistance (mobius a x) (boundaryMobius a ha u)
      = boundaryDistance x u - boundaryDistance a u := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  simp only [boundaryDistance, coe_boundaryMobius]
  exact compositeDistance_mobius hx hu ha

end HyperbolicSpace

end

end
