/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.BallModel
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.Mobius
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Inversion
public import LeanRidgelet.ToMathlib.LieGroup.SphereInvariantMeasure

/-!
# The Helgason--Fourier transform on real hyperbolic space

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`LeanRidgelet.ToMathlib.LieGroup.Symmetric` develops the Helgason--Fourier theory with the geometry
of `X = G/K` as data. This file supplies that data for `ℍ^m` in the Poincaré ball model and, in
doing so, turns the inversion formula from a schema into a *proposition*: `HasInversion` below is a
definite claim about a definite space, which is what was missing before any model existed.

The four pieces of data are all in place.

* The space is the ambient Euclidean space carrying `HyperbolicSpace.invariantMeasure`, which is
  concentrated on the ball. Using the whole space rather than the ball as a subtype costs nothing
  and keeps every construction on a plain Euclidean space.
* The rank is one, so `𝔞 ≅ ℝ` and the composite distance is the scalar
  `HyperbolicSpace.compositeDistance`, with `ϱ = (m-1)/2`.
* The boundary is the unit sphere with its uniform probability measure. Mathlib's
  `Measure.toSphere` is not normalized, so the measure used here is the normalized one; that it is
  the *rotation-invariant* probability measure is `boundaryMeasure_eq_sphereOrbitMeasure`, by the
  uniqueness theorem of `LeanRidgelet.ToMathlib.LieGroup.SphereInvariantMeasure`.
* The Plancherel density is `(|W| ‖c(λ)‖²)^{-1}`, with `|W|` and `c` left as arguments. For `ℍ^m`
  the Weyl group has order two and `c` is an explicit ratio of Gamma functions, but pinning that
  down is a normalization question that a later file has to settle by proof rather than by
  quotation.

## Main definitions

* `HyperbolicSpace.boundaryMeasure`: the uniform probability measure on `∂ℍ^m = 𝕊^{m-1}`.
* `HyperbolicSpace.helgasonFourier`: `f̂(λ,u) = ∫ f(x) P(x,u)^{ϱ - iλ} dμ(x)`.
* `HyperbolicSpace.HasInversion`: **the Helgason--Fourier inversion formula on `ℍ^m`**, as a
  proposition.

## Main results

* `HyperbolicSpace.boundaryMeasure_eq_sphereOrbitMeasure`: the boundary measure is the
  rotation-invariant probability measure on the sphere.
* `HyperbolicSpace.norm_horosphericalCharacter_compositeDistance`: the modulus of the
  Helgason--Fourier kernel is a real power of the Poisson kernel — in particular the weight the
  layer of a network on `ℍ^m` carries is `P(x,u)^ϱ`, independently of the frequency.
* `HyperbolicSpace.horosphericalCharacter_compositeDistance_mobius`: **the kernel is a cocycle for
  the Möbius action** — moving the point and the boundary normal together multiplies the kernel by a
  factor depending on the boundary normal alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The boundary measure -/

/-- The uniform probability measure on the ideal boundary `∂ℍ^m = 𝕊^{m-1}`: Mathlib's surface
measure divided by its total mass.

Normalizing here rather than carrying the total mass through the theory is what makes the boundary
integral of the inversion formula an average, which is the form the Helgason--Fourier theory uses
(`∫ db = 1`). -/
def boundaryMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

instance instIsProbabilityMeasureBoundaryMeasure [Nontrivial E] :
    IsProbabilityMeasure (boundaryMeasure E) := by
  have hne : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have htop : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  constructor
  rw [boundaryMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne htop]

/-- The boundary measure is the rotation-invariant probability measure on the sphere: it is the
orbit measure of any unit vector under the orthogonal group. So the normalization chosen above is
not a choice at all — it is the only rotation-invariant one. -/
theorem boundaryMeasure_eq_sphereOrbitMeasure [Nontrivial E] (v : sphere (0 : E) 1) :
    boundaryMeasure E = sphereOrbitMeasure v :=
  (sphereOrbitMeasure_eq_smul_toSphere v).symm

/-! ## The transform -/

/-- The composite distance read as a function of a point of the boundary sphere, which is the form
the Helgason--Fourier theory consumes. -/
def boundaryDistance (x : E) (u : sphere (0 : E) 1) : ℝ := compositeDistance x (u : E)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem boundaryDistance_origin (u : sphere (0 : E) 1) : boundaryDistance (0 : E) u = 0 :=
  compositeDistance_origin (mem_sphere_zero_iff_norm.1 u.2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The modulus of the Helgason--Fourier kernel on `ℍ^m` is a real power of the Poisson kernel:
`|e^{(iλ+t)⟨x,u⟩}| = P(x,u)^t`, with no dependence on the frequency `λ`.

At `t = ϱ` this is the weight the layer of a network on `ℍ^m` carries, so the weight is
`P(x,u)^{(m-1)/2}` — the square root of the Euclidean Poisson kernel when `m = 2`, and in general
the half-density that makes the Helgason--Fourier transform an isometry. -/
theorem norm_horosphericalCharacter_compositeDistance (t lam : ℝ) {x u : E} (hx : ‖x‖ < 1)
    (hu : ‖u‖ = 1) :
    ‖SymmetricSpace.horosphericalCharacter t lam (compositeDistance x u)‖
      = poissonKernel x u ^ t := by
  have hP : 0 < poissonKernel x u := poissonKernel_pos hx hu
  rw [SymmetricSpace.norm_horosphericalCharacter, Real.rpow_def_of_pos hP]
  simp [RCLike.inner_apply, compositeDistance]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The Helgason--Fourier kernel is a cocycle for the Möbius action.** Moving the point and the
boundary normal together by the same Möbius transformation multiplies the kernel by a factor that
depends on the boundary normal alone:

`e^{(iλ+t)⟨φ_a x, φ_a u⟩} = e^{(iλ+t)⟨x,u⟩} · e^{-(iλ+t)⟨a,u⟩}`.

Two facts meet here and nothing else: the composite distance is a cocycle
(`compositeDistance_mobius`, an algebraic identity about the ball) and the kernel is the exponential
of a linear functional of it, hence multiplicative (`horosphericalCharacter_add`). This is the
mechanism by which the isometry group of `ℍ^m` acts on the Helgason--Fourier transform, and it is
what the abstract layer abstracts. -/
theorem horosphericalCharacter_compositeDistance_mobius (t lam : ℝ) {x u a : E} (hx : ‖x‖ < 1)
    (hu : ‖u‖ = 1) (ha : ‖a‖ < 1) :
    SymmetricSpace.horosphericalCharacter t lam (compositeDistance (mobius a x) (mobius a u))
      = SymmetricSpace.horosphericalCharacter t lam (compositeDistance x u)
        * SymmetricSpace.horosphericalCharacter t lam (-compositeDistance a u) := by
  rw [compositeDistance_mobius hx hu ha, sub_eq_add_neg,
    SymmetricSpace.horosphericalCharacter_add]

/-- **The Helgason--Fourier transform on `ℍ^m`**,
`f̂(λ,u) = ∫ f(x) e^{(-iλ+ϱ)⟨x,u⟩} dμ(x) = ∫ f(x) P(x,u)^{ϱ-iλ} dμ(x)`,
with `μ` the invariant measure of the ball and `ϱ = (m-1)/2`. -/
def helgasonFourier (f : E → ℂ) (lam : ℝ) (u : sphere (0 : E) 1) : ℂ :=
  SymmetricSpace.helgasonFourier (invariantMeasure E) boundaryDistance (rho E) f lam u

theorem helgasonFourier_eq (f : E → ℂ) (lam : ℝ) (u : sphere (0 : E) 1) :
    helgasonFourier f lam u
      = ∫ x : E, f x *
          SymmetricSpace.horosphericalCharacter (rho E) (-lam) (boundaryDistance x u)
        ∂(invariantMeasure E) := rfl

/-! ## The inversion formula -/

/-- **The Helgason--Fourier inversion formula on real hyperbolic space**, as a proposition:

`f(x) = |W|^{-1} ∫_ℝ ∫_{𝕊^{m-1}} f̂(λ,u) e^{(iλ+ϱ)⟨x,u⟩} |c(λ)|^{-2} du dλ`.

Rank one, so the frequency variable is a real number and `dλ` is Lebesgue measure on `ℝ`. Fixing
`dλ` to be Lebesgue is deliberate: Helgason's inversion formula is written against a normalization
of `dλ` that is not Lebesgue measure, and the difference is exactly where the powers of `π` in the
constant live, so the constant has to be produced by a proof rather than quoted.

This is a statement, not a theorem. Proving it is the next stage; the route is through the Möbius
action of the ball, the Abel transform, and Harish-Chandra's inversion of the spherical transform,
and `SymmetricSpace.hasHelgasonInversion_of_spherical` is where those inputs meet. -/
def HasInversion (W : ℝ) (c : ℝ → ℂ) (f : E → ℂ) : Prop :=
  SymmetricSpace.HasHelgasonInversion (invariantMeasure E) (volume : Measure ℝ)
    (boundaryMeasure E) boundaryDistance (rho E) W c f

theorem hasInversion_iff (W : ℝ) (c : ℝ → ℂ) (f : E → ℂ) :
    HasInversion W c f
      ↔ ∀ x : E, (∫ lam : ℝ, (∫ u : sphere (0 : E) 1, helgasonFourier f lam u *
          ((SymmetricSpace.plancherelDensity W c lam : ℝ) : ℂ) *
          SymmetricSpace.horosphericalCharacter (rho E) lam (boundaryDistance x u)
        ∂(boundaryMeasure E)) ∂(volume : Measure ℝ)) = f x :=
  Iff.rfl

end HyperbolicSpace

end

end
