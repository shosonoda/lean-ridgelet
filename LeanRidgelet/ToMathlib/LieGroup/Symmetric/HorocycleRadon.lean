/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Defs

/-!
# The horocycle Radon transform and the Fourier slice theorem on a symmetric space

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

On `ℝ^m` the Fourier transform is the one-dimensional Fourier transform of the Radon transform:
integrating over the hyperplanes normal to a direction and then transforming in the offset gives
the Fourier transform along that direction. S. Helgason opens Ch. III of *Geometric Analysis on
Symmetric Spaces* by observing that the Helgason--Fourier transform of `X = G/K` satisfies the
same relation with *horospheres* in place of hyperplanes (see also §5 No. 3 there), and this file
proves it.

The horospheres with a fixed normal `b ∈ B` are the level sets of `x ↦ A(x,b)`, so "integrate over
a horosphere" means "integrate over a fibre of the composite distance". Mathlib has no Riemannian
measure to build those fibre integrals from, and on a general `X` there is no reason for one to
exist, so the family of fibre measures is *data*: a kernel `κ b t` concentrated on the horosphere
at distance `t` with normal `b`, together with the hypothesis that integrating against `μ` is
integrating against `κ b t` and then over `t`. In a concrete model that hypothesis is the
horospherical change of variables, and it is where the normalization of `dt` on `𝔞` is fixed —
which is exactly where the constant of the inversion formula comes from, so it is worth having in
the open rather than buried in a definition.

Once the kernel is given, the theorem is Fubini and one rewriting: on the horosphere at distance
`t` the kernel `e^{(-iλ+ϱ)(A(x,b))}` is the *constant* `e^{(-iλ+ϱ)(t)}`, so it comes out of the
fibre integral, and what is left is the Euclidean Fourier transform in `t` of the weighted Radon
transform `e^{ϱ(t)} Rf(t,b)`.

## Main definitions

* `SymmetricSpace.horocycleRadon`: `Rf(b,t) = ∫ f dκ(b,t)`, the integral of `f` over the horosphere
  at composite distance `t` with normal `b`.
* `SymmetricSpace.dualHorocycle`: the dual transform `φ^∨(x) = ∫_B φ(A(x,b), b) db`, averaging a
  function of horospheres over the horospheres through a point.

## Main results

* `SymmetricSpace.helgasonFourier_eq_integral_horocycleRadon`: **the Fourier slice theorem** — the
  Helgason--Fourier transform is the `𝔞`-integral of the horocycle Radon transform against the
  character.
* `SymmetricSpace.helgasonFourier_eq_fourier_weightedHorocycleRadon`: the same statement with the
  character split, so that the right-hand side is visibly a Euclidean Fourier transform of
  `t ↦ e^{ϱ(t)} Rf(b,t)`.
* `SymmetricSpace.sphericalFunction_eq_dualHorocycle`: the spherical function is the dual
  transform of the character.
* `SymmetricSpace.helgasonInversionIntegral_eq_integral_dualHorocycle`: the inversion integral is
  the `𝔞`-integral of dual transforms, which is the shape of Helgason's inversion of the Radon
  transform, `f = w^{-1}(\Lambda\Lambda f^\wedge)^\vee`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SymmetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]

/-! ## The transform and its dual -/

/-- The horocycle Radon transform `Rf(b,t) = ∫_{ξ(t,b)} f`, the integral of `f` over the horosphere
at composite distance `t` from the origin with normal `b`.

The horosphere is presented by a measure `κ b t` concentrated on it. Mathlib has no Riemannian
measure, so this family is data; the hypotheses that tie it to the composite distance and to the
invariant measure appear in the theorems below. -/
def horocycleRadon (kap : B → E → Measure X) (f : X → ℂ) (b : B) (t : E) : ℂ :=
  ∫ x : X, f x ∂(kap b t)

/-- The dual horocycle transform `φ^∨(x) = ∫_B φ(A(x,b), b) db`: the average of a function on the
space of horospheres over the horospheres passing through `x`. Together with `horocycleRadon` it is
the dual pair `(X, Ξ) = (G/K, G/MN)` of Helgason's duality. -/
def dualHorocycle (nu : Measure B) (A : X → B → E) (phi : E → B → ℂ) (x : X) : ℂ :=
  ∫ b : B, phi (A x b) b ∂nu

omit [MeasurableSpace E] [MeasurableSpace X] in
/-- The spherical function is the dual transform of the character: `φ_λ = (e^{(iλ+ϱ)})^∨`. Since
the character depends only on the `𝔞`-variable, the spherical function is the dual transform of a
function that is constant along the boundary. -/
theorem sphericalFunction_eq_dualHorocycle (nu : Measure B) (A : X → B → E) (rho lam : E) :
    sphericalFunction nu A rho lam
      = dualHorocycle nu A (fun t _ => horosphericalCharacter rho lam t) :=
  rfl

/-! ## The Fourier slice theorem -/

omit [MeasurableSpace B] in
/-- **The Fourier slice theorem on a noncompact symmetric space.** The Helgason--Fourier transform
at a boundary normal `b` is the integral over `𝔞` of the horocycle Radon transform against the
character:
`f̂(λ,b) = ∫_𝔞 e^{(-iλ+ϱ)(t)} Rf(b,t) dt`.

This is the symmetric-space form of "the Fourier transform is the one-dimensional Fourier transform
of the Radon transform" (Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. III, opening
remark (ii) and §5 No. 3).

The two hypotheses are exactly the two things a concrete model has to supply. `hsupp` says the
kernel really is carried by the horosphere — on the fibre the composite distance is the constant
`t` — and `hdis` is the horospherical change of variables for the integrand at hand, which is
where the normalization of `dt` on `𝔞` is fixed. Given them the proof is one rewriting: a constant
comes out of the fibre integral. -/
theorem helgasonFourier_eq_integral_horocycleRadon (μ : Measure X) (mua : Measure E)
    (A : X → B → E) (rho : E) (f : X → ℂ) (lam : E) (b : B) (kap : B → E → Measure X)
    (hsupp : ∀ t : E, ∀ᵐ x ∂(kap b t), A x b = t)
    (hdis : (∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂μ)
      = ∫ t : E, (∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂(kap b t)) ∂mua) :
    helgasonFourier μ A rho f lam b
      = ∫ t : E, horosphericalCharacter rho (-lam) t * horocycleRadon kap f b t ∂mua := by
  rw [helgasonFourier, hdis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [horocycleRadon]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hsupp t] with x hx
  rw [hx]
  ring

omit [MeasurableSpace B] in
/-- The Fourier slice theorem with the character split into its phase and its weight, so that the
right-hand side is visibly the Euclidean Fourier transform on `𝔞` of the *weighted* horocycle Radon
transform `t ↦ e^{ϱ(t)} Rf(b,t)`.

Read this way, the Helgason--Fourier transform of `X` is nothing but the Fourier transform of
`\mathbb R^r`, applied to a function on `𝔞` obtained from `f` by integrating over horospheres. It
is why the inversion formula on `X` reduces to a Euclidean Fourier inversion together with an
inversion of the Radon transform, and why the density `|c(λ)|^{-2}` appears as a Fourier multiplier
rather than as a geometric factor. -/
theorem helgasonFourier_eq_fourier_weightedHorocycleRadon (μ : Measure X) (mua : Measure E)
    (A : X → B → E) (rho : E) (f : X → ℂ) (lam : E) (b : B) (kap : B → E → Measure X)
    (hsupp : ∀ t : E, ∀ᵐ x ∂(kap b t), A x b = t)
    (hdis : (∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂μ)
      = ∫ t : E, (∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂(kap b t)) ∂mua) :
    helgasonFourier μ A rho f lam b
      = ∫ t : E, Complex.exp (-(Complex.I * ((inner ℝ lam t : ℝ) : ℂ))) *
          (((Real.exp (inner ℝ rho t) : ℝ) : ℂ) * horocycleRadon kap f b t) ∂mua := by
  rw [helgasonFourier_eq_integral_horocycleRadon μ mua A rho f lam b kap hsupp hdis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [horosphericalCharacter_neg]
  ring

/-! ## The inversion integral as a dual transform -/

omit [MeasurableSpace X] in
/-- The inversion integral is the `𝔞`-integral of dual horocycle transforms. Helgason's inversion
of the Radon transform has the shape `f = w^{-1}(\Lambda\Lambda f^\wedge)^\vee` (*Geometric
Analysis on Symmetric Spaces*, Ch. II, Thm 3.13), a Fourier multiplier applied to the Radon
transform and then averaged back by the dual transform; this records that the right-hand side of
the Helgason--Fourier inversion formula has that shape, the multiplier being the Plancherel density
`κ` together with the character. -/
theorem helgasonInversionIntegral_eq_integral_dualHorocycle (mua : Measure E) (nu : Measure B)
    (A : X → B → E) (rho : E) (F : E → B → ℂ) (kappa : E → ℝ) (x : X) :
    helgasonInversionIntegral mua nu A rho F kappa x
      = ∫ lam : E, dualHorocycle nu A
          (fun t b => F lam b * ((kappa lam : ℝ) : ℂ) * horosphericalCharacter rho lam t) x
        ∂mua :=
  rfl

end SymmetricSpace

end

end
