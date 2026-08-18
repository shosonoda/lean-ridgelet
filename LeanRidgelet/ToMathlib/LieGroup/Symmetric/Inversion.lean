/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.CFunction

/-!
# The Helgason--Fourier inversion formula: statement and reduction

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

The inversion formula on a noncompact symmetric space is

`f(x) = |W|^{-1} ∫_{𝔞* × B} f̂(λ,b) e^{(iλ+ϱ)(A(x,b))} |c(λ)|^{-2} dλ db`

(Helgason, *Geometric Analysis on Symmetric Spaces*, Ch. III, Thm 1.3). This file states it — as a
predicate on the data, never as an axiom, a structure field or a `sorry` — and records the shape of
Helgason's proof of it.

That proof has exactly two inputs, and the value of writing it out is that it says which one is
deep. The first is Lemma 1.2 of the same section: the inner integral over the boundary is the
convolution `f × φ_λ` of `f` with the spherical function. It rests on the symmetry of the spherical
function (Thm 1.1), which is a cocycle computation with the Iwasawa decomposition and the
quasi-invariance of the boundary measure — nontrivial, but formal. The second is Harish-Chandra's
inversion formula for the *spherical* transform (*Groups and Geometric Analysis*, Ch. IV, Thm 7.5),
which is the genuinely deep analytic input, resting on the asymptotics of the spherical function
and hence on the `c`-function.

`hasHelgasonInversion_of_spherical` below is that reduction. It takes the two inputs as hypotheses
and concludes the inversion formula, so the remaining work in any concrete model is precisely to
discharge them. Neither hypothesis mentions a group, which is why the reduction can be stated
before any of the Lie theory exists.

## Main definitions

* `SymmetricSpace.HasHelgasonInversion`: the inversion formula for a given function, as a
  proposition about the data.

## Main results

* `SymmetricSpace.hasHelgasonInversion_of_spherical`: the inversion formula follows from
  (i) the identification of the boundary integral with the convolution against the spherical
  function and (ii) the inversion formula for the spherical transform.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SymmetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]

/-- **The Helgason--Fourier inversion formula** for `f`, as a proposition about the geometry:
the inversion integral of the Helgason--Fourier transform of `f`, against the density
`(|W| ‖c(λ)‖²)^{-1}`, returns `f`.

This is a `Prop` on data rather than an assumption object: a concrete model instantiates the data
and then has a definite statement to prove. With the geometry left free it is not even a
well-posed claim, which is why the constructions of a model have to come first. -/
def HasHelgasonInversion (μ : Measure X) (mua : Measure E) (nu : Measure B) (A : X → B → E)
    (rho : E) (W : ℝ) (c : E → ℂ) (f : X → ℂ) : Prop :=
  ∀ x : X, helgasonInversionIntegral mua nu A rho (helgasonFourier μ A rho f)
    (plancherelDensity W c) x = f x

theorem hasHelgasonInversion_iff (μ : Measure X) (mua : Measure E) (nu : Measure B)
    (A : X → B → E) (rho : E) (W : ℝ) (c : E → ℂ) (f : X → ℂ) :
    HasHelgasonInversion μ mua nu A rho W c f
      ↔ ∀ x : X, (∫ lam : E, (∫ b : B, helgasonFourier μ A rho f lam b *
          ((plancherelDensity W c lam : ℝ) : ℂ) *
          horosphericalCharacter rho lam (A x b) ∂nu) ∂mua) = f x :=
  Iff.rfl

/-- **The reduction of Helgason's proof.** The inversion formula holds as soon as

* `hconv`: the boundary integral `∫_B f̂(λ,b) e^{(iλ+ϱ)(A(x,b))} db` equals a function `conv λ x`
  — in the group setting the convolution `(f × φ_λ)(x)`, by Lemma 1.2 of
  *Geometric Analysis on Symmetric Spaces*, Ch. III §1, which is where the symmetry of the
  spherical function is used; and
* `hsph`: that function is inverted by the Plancherel density, `∫_{𝔞*} κ(λ) conv λ x dλ = f(x)`
  — Harish-Chandra's inversion formula for the spherical transform.

The proof is then only bookkeeping: the density does not depend on `b`, so it comes out of the
boundary integral. What the statement buys is the separation of the two inputs, and in particular
the isolation of the one deep analytic fact. -/
theorem hasHelgasonInversion_of_spherical (μ : Measure X) (mua : Measure E) (nu : Measure B)
    (A : X → B → E) (rho : E) (W : ℝ) (c : E → ℂ) (f : X → ℂ) (conv : E → X → ℂ)
    (hconv : ∀ (lam : E) (x : X),
      (∫ b : B, helgasonFourier μ A rho f lam b * horosphericalCharacter rho lam (A x b) ∂nu)
        = conv lam x)
    (hsph : ∀ x : X,
      (∫ lam : E, ((plancherelDensity W c lam : ℝ) : ℂ) * conv lam x ∂mua) = f x) :
    HasHelgasonInversion μ mua nu A rho W c f := by
  intro x
  rw [← hsph x]
  simp only [helgasonInversionIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  change (∫ b : B, helgasonFourier μ A rho f lam b * ((plancherelDensity W c lam : ℝ) : ℂ) *
      horosphericalCharacter rho lam (A x b) ∂nu)
    = ((plancherelDensity W c lam : ℝ) : ℂ) * conv lam x
  rw [← hconv lam x, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  ring

end SymmetricSpace

end

end
