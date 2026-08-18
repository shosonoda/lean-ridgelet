/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Helgason--Fourier transform, as data

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

On a noncompact symmetric space `X = G/K` the Fourier transform of S. Helgason replaces the
plane wave `e^{-i⟪λ,x⟫}` of `ℝ^m` by `e^{(-iλ+ϱ)(A(x,b))}`, where

* `𝔞 ≅ ℝ^r` is the Lie algebra of the split torus, `r` the rank of `X`;
* `B = K/M` is the boundary of `X`;
* `A(x,b) ∈ 𝔞` is the *composite distance* from the origin to the horosphere through `x` with
  normal `b`, that is `A(gK, kM) = -H(g^{-1}k)` for the Iwasawa decomposition `g ∈ K e^{H(g)} N`;
* `ϱ ∈ 𝔞*` is the half-sum of the positive restricted roots.

See S. Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. II §3 No. 4 and Ch. III §1 for the
composite distance and definition (4) of Ch. III §1 for the transform.

Mathlib has none of the group theory: no Iwasawa decomposition, no spherical functions, no
Harish-Chandra `c`-function. This file therefore takes `A` and `ϱ` as **data** and defines the
transform, the spherical function and the inversion integral in terms of them. Nothing here asserts
anything about a group; the identities that the geometry does satisfy — the cocycle relation for
`A` and the quasi-invariance of the boundary measure — are hypotheses of the theorems that need
them, never fields of a structure. Concrete models supply the data and discharge those hypotheses.

The design mirrors the one already used for the abstract Fourier slice scheme: keeping the geometry
in explicit arguments is what lets a conditional theorem be stated before any of the underlying Lie
theory exists.

## Main definitions

* `SymmetricSpace.horosphericalCharacter`: the character `v ↦ e^{(iλ+ϱ)(v)}` on `𝔞`, from which
  everything else is built. It is the exponential of a linear functional, so it is multiplicative
  in `v` — that single fact is what makes the cocycle relation for `A` turn into a product formula
  for the kernels.
* `SymmetricSpace.helgasonFourier`: `f̂(λ,b) = ∫_X f(x) e^{(-iλ+ϱ)(A(x,b))} dμ(x)`.
* `SymmetricSpace.sphericalFunction`: `φ_λ(x) = ∫_B e^{(iλ+ϱ)(A(x,b))} db`.
* `SymmetricSpace.helgasonInversionIntegral`: the right-hand side of the inversion formula,
  `∫_{𝔞*×B} F(λ,b) κ(λ) e^{(iλ+ϱ)(A(x,b))} db dλ`, with the Plancherel density `κ` as data.

## Main results

* `SymmetricSpace.integral_helgasonFourier_eq`: averaging the Helgason--Fourier transform over the
  boundary pairs the function against the spherical function. This is the measure-theoretic core of
  "on `K`-invariant functions the Helgason--Fourier transform is the spherical transform"
  (Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. III §1).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SymmetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X B : Type*}

/-! ## The horospherical character -/

/-- The character `v ↦ e^{(iλ+ϱ)(v)}` of `𝔞`, with the functional written through the inner
product: `ϱ` and `λ` are vectors of `E ≅ 𝔞* ≅ 𝔞`.

Taking `ϱ = 0` gives the plane wave `e^{i⟪λ,v⟫}` of Euclidean Fourier analysis, and taking `λ = 0`
gives the weight `e^{ϱ(v)}` that the layer of a network on `G/K` carries. -/
def horosphericalCharacter (rho lam v : E) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ lam v : ℝ) : ℂ) + ((inner ℝ rho v : ℝ) : ℂ))

@[simp] theorem horosphericalCharacter_zero_right (rho lam : E) :
    horosphericalCharacter rho lam (0 : E) = 1 := by
  simp [horosphericalCharacter]

@[simp] theorem horosphericalCharacter_zero_rho (lam v : E) :
    horosphericalCharacter (0 : E) lam v = Complex.exp (Complex.I * ((inner ℝ lam v : ℝ) : ℂ)) := by
  simp [horosphericalCharacter]

/-- The modulus of the character is the weight `e^{ϱ(v)}`: the frequency contributes nothing.
This is why the growth of `e^{(-iλ+ϱ)(A(x,b))}` is governed by `ϱ` alone, uniformly in `λ`. -/
theorem norm_horosphericalCharacter (rho lam v : E) :
    ‖horosphericalCharacter rho lam v‖ = Real.exp (inner ℝ rho v) := by
  rw [horosphericalCharacter, Complex.norm_exp]
  simp

theorem horosphericalCharacter_ne_zero (rho lam v : E) :
    horosphericalCharacter rho lam v ≠ 0 :=
  Complex.exp_ne_zero _

/-- The character splits into a unimodular phase and a real weight,
`e^{(iλ+ϱ)(v)} = e^{iλ(v)} \cdot e^{ϱ(v)}`. This is the form in which the Helgason--Fourier
transform is read as a Euclidean Fourier transform of a weighted transform: the phase is the plane
wave and the weight belongs to the function being transformed. -/
theorem horosphericalCharacter_eq (rho lam v : E) :
    horosphericalCharacter rho lam v
      = Complex.exp (Complex.I * ((inner ℝ lam v : ℝ) : ℂ)) *
        ((Real.exp (inner ℝ rho v) : ℝ) : ℂ) := by
  rw [horosphericalCharacter, Complex.exp_add, Complex.ofReal_exp]

/-- Reflecting the frequency conjugates the phase and leaves the weight alone. -/
theorem horosphericalCharacter_neg (rho lam v : E) :
    horosphericalCharacter rho (-lam) v
      = Complex.exp (-(Complex.I * ((inner ℝ lam v : ℝ) : ℂ))) *
        ((Real.exp (inner ℝ rho v) : ℝ) : ℂ) := by
  rw [horosphericalCharacter_eq]
  congr 2
  rw [inner_neg_left]
  push_cast
  ring

/-- The character is multiplicative in the `𝔞`-variable. Together with the cocycle relation
`A(g·x, g·b) = A(x,b) + A(g·o, g·b)` this is what turns the `G`-action on `X` into a multiplier on
the Helgason--Fourier kernel. -/
theorem horosphericalCharacter_add (rho lam v w : E) :
    horosphericalCharacter rho lam (v + w)
      = horosphericalCharacter rho lam v * horosphericalCharacter rho lam w := by
  rw [horosphericalCharacter, horosphericalCharacter, horosphericalCharacter, ← Complex.exp_add]
  congr 1
  simp only [inner_add_right, Complex.ofReal_add]
  ring

/-! ## The transform, the spherical function, and the inversion integral -/

/-- **The Helgason--Fourier transform** `f̂(λ,b) = ∫_X f(x) e^{(-iλ+ϱ)(A(x,b))} dμ(x)`
(Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. III §1, definition (4)).

The composite distance `A`, the constant `ϱ` and the invariant measure `μ` are data. -/
def helgasonFourier [MeasurableSpace X] (μ : Measure X) (A : X → B → E) (rho : E) (f : X → ℂ)
    (lam : E) (b : B) : ℂ :=
  ∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂μ

/-- **The spherical function** `φ_λ(x) = ∫_B e^{(iλ+ϱ)(A(x,b))} db`, the average of the
Helgason--Fourier kernel over the boundary. -/
def sphericalFunction [MeasurableSpace B] (nu : Measure B) (A : X → B → E) (rho lam : E)
    (x : X) : ℂ :=
  ∫ b : B, horosphericalCharacter rho lam (A x b) ∂nu

/-- The integral that the inversion formula asserts to be `f(x)`:
`∫_{𝔞*} ∫_B F(λ,b) κ(λ) e^{(iλ+ϱ)(A(x,b))} db dλ`.

The Plancherel density `κ` is data; on a symmetric space it is `|W|^{-1}|c(λ)|^{-2}`, built from
the order of the Weyl group and the Harish-Chandra `c`-function. -/
def helgasonInversionIntegral [MeasurableSpace E] [MeasurableSpace B] (mua : Measure E)
    (nu : Measure B) (A : X → B → E) (rho : E) (F : E → B → ℂ) (kappa : E → ℝ) (x : X) : ℂ :=
  ∫ lam : E, (∫ b : B, F lam b * ((kappa lam : ℝ) : ℂ) *
    horosphericalCharacter rho lam (A x b) ∂nu) ∂mua

/-! ## Elementary properties -/

@[simp] theorem helgasonFourier_zero [MeasurableSpace X] (μ : Measure X) (A : X → B → E)
    (rho : E) (lam : E) (b : B) :
    helgasonFourier μ A rho (fun _ => (0 : ℂ)) lam b = 0 := by
  simp [helgasonFourier]

theorem helgasonFourier_const_mul [MeasurableSpace X] (μ : Measure X) (A : X → B → E) (rho : E)
    (c : ℂ) (f : X → ℂ) (lam : E) (b : B) :
    helgasonFourier μ A rho (fun x => c * f x) lam b
      = c * helgasonFourier μ A rho f lam b := by
  simp only [helgasonFourier, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- At a point whose composite distance to every boundary normal vanishes — the origin of the
symmetric space — the spherical function is `1`, the boundary measure being a probability
measure. -/
theorem sphericalFunction_eq_one [MeasurableSpace B] (nu : Measure B) [IsProbabilityMeasure nu]
    (A : X → B → E) (rho lam : E) {x : X} (hx : ∀ b : B, A x b = 0) :
    sphericalFunction nu A rho lam x = 1 := by
  simp [sphericalFunction, hx]

/-- Averaging the Helgason--Fourier transform over the boundary pairs the function against the
spherical function at the reflected frequency:
`∫_B f̂(λ,b) db = ∫_X f(x) φ_{-λ}(x) dμ(x)`.

This is the measure-theoretic content of Helgason's remark that the Helgason--Fourier transform
extends the spherical transform: when `f` is `K`-invariant its transform does not depend on `b`, so
the left-hand side is `f̂(λ,b)` itself and the right-hand side is the spherical transform of `f`
(*Geometric Analysis on Symmetric Spaces*, Ch. III §1). The proof is Fubini, so the joint
integrability hypothesis is the whole of it. -/
theorem integral_helgasonFourier_eq [MeasurableSpace X] [MeasurableSpace B] (μ : Measure X)
    (nu : Measure B) [SFinite μ] [SFinite nu] (A : X → B → E) (rho : E) (f : X → ℂ) (lam : E)
    (hint : Integrable
      (fun p : X × B => f p.1 * horosphericalCharacter rho (-lam) (A p.1 p.2)) (μ.prod nu)) :
    (∫ b : B, helgasonFourier μ A rho f lam b ∂nu)
      = ∫ x : X, f x * sphericalFunction nu A rho (-lam) x ∂μ := by
  have hswap := integral_integral_swap (μ := μ) (ν := nu)
    (f := fun (x : X) (b : B) => f x * horosphericalCharacter rho (-lam) (A x b)) hint
  calc (∫ b : B, helgasonFourier μ A rho f lam b ∂nu)
      = ∫ b : B, (∫ x : X, f x * horosphericalCharacter rho (-lam) (A x b) ∂μ) ∂nu := rfl
    _ = ∫ x : X, (∫ b : B, f x * horosphericalCharacter rho (-lam) (A x b) ∂nu) ∂μ := hswap.symm
    _ = ∫ x : X, f x * sphericalFunction nu A rho (-lam) x ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [sphericalFunction]
        rw [integral_const_mul]

end SymmetricSpace

end

end
