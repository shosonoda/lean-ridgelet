/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Symmetric
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic

/-!
# Fourier slice method, Case III on real hyperbolic space

Section 5 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984)

instantiates the network on a noncompact symmetric space at two spaces. This file does the first of
them, the *continuous horospherical hyperbolic network* on the Poincaré ball, using the model built
in `LeanRidgelet.ToMathlib.LieGroup.Hyperbolic`.

`FS.Symmetric` states the reconstruction formula with the geometry as free data, so its hypothesis
is not a proposition one can be asked to prove. Here the data is fixed: the invariant measure of the
ball, the uniform probability measure on the boundary sphere, the composite distance
`⟨x,u⟩ = log((1-‖x‖²)/‖x-u‖²)`, and `ϱ = (m-1)/2`. What is left over is exactly the
Helgason--Fourier inversion formula for `ℍ^m` — `HyperbolicSpace.HasInversion`, a definite claim
about a definite space — and `FS.Targets` declares it as the one outstanding target.

The rank is one, so the scale variable is a real number: this is the `r = 1` shape that
`fs_inversionIntegral_polar` showed the Euclidean polar instance also has. That is why the Jacobian
exponent here is `1` rather than the dimension `m` of the space, and it is the structural point of
Case III.

## Main definitions

* `LeanRidgelet.hyperbolicWeight`: the weight `e^{ϱ⟨x,u⟩}` the layer carries, which
  `fs_hyperbolicWeight_eq_poissonKernel_rpow` identifies with `P(x,u)^ϱ`.
* `LeanRidgelet.hyperbolicSynthesis`: the network
  `S[γ](x) = ∫ γ(a,u,b) σ(a⟨x,u⟩ - b) e^{ϱ⟨x,u⟩} da du db`.
* `LeanRidgelet.hyperbolicRidgelet`: the ridgelet transform `R[f;ρ](a,u,b)`.

## Main results

* `fs_hyperbolic_reconstruction_of_inversion`: **the reconstruction formula on `ℍ^m`**, conditional
  on the Helgason--Fourier inversion formula for `ℍ^m` and on nothing else.
* `fs_hyperbolicWeight_eq_poissonKernel_rpow`: the layer's weight is the `ϱ`-th power of the
  Poisson kernel — a half-density, not an input-dependent coefficient.

## Deviations from the article

None in the statement. The scalar is `fourierSlicePairing 1`, the rank-one case of the pairing; see
the module docstring of `FS.Symmetric` for the bookkeeping of `|W|` between the scalar and the
density.

The article's appendix gives the Poincaré disk the triple `|W| = 1`,
`|c(λ)|^{-2} = (π/2)λ tanh(πλ/2)` and an unspecified `dλ`. Here `dλ` is Lebesgue measure and `|W|`
and `c` are arguments, because those three data are only meaningful together: S. Helgason normalizes
`c` by `c(-iϱ) = 1` in *Groups and Geometric Analysis* but writes the inversion formula of
*Geometric Analysis on Symmetric Spaces* against a different `dλ`, and read with Lebesgue `dλ` the
two differ by a power of `π`. Fixing the constant is part of proving the target, not of stating it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The network on the Poincaré ball -/

/-- The weight `e^{ϱ⟨x,u⟩}` that a layer of the continuous horospherical hyperbolic network
carries: the horospherical character of `ℍ^m` at zero frequency. -/
def hyperbolicWeight (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (u : sphere (0 : E) 1) : ℂ :=
  SymmetricSpace.horosphericalCharacter (HyperbolicSpace.rho E) 0
    (HyperbolicSpace.boundaryDistance x u)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The weight is a power of the Poisson kernel**, `e^{ϱ⟨x,u⟩} = P(x,u)^ϱ` with
`ϱ = (m-1)/2`.

So the layer does not carry an input-dependent coefficient but the half-density that makes the
Helgason--Fourier transform an isometry; for `m = 2` it is the square root of the Euclidean Poisson
kernel. This settles in the affirmative the reading of the weight raised as an open design question
in the development plan. -/
theorem fs_hyperbolicWeight_eq_poissonKernel_rpow {x : E} {u : sphere (0 : E) 1} (hx : ‖x‖ < 1) :
    hyperbolicWeight E x u
      = ((HyperbolicSpace.poissonKernel x (u : E) ^ HyperbolicSpace.rho E : ℝ) : ℂ) := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  have hP : 0 < HyperbolicSpace.poissonKernel x (u : E) := HyperbolicSpace.poissonKernel_pos hx hu
  rw [hyperbolicWeight, SymmetricSpace.horosphericalCharacter, Real.rpow_def_of_pos hP,
    HyperbolicSpace.boundaryDistance, HyperbolicSpace.compositeDistance, Complex.ofReal_exp]
  simp [RCLike.inner_apply]

/-- **The continuous horospherical hyperbolic network** (Section 5),
`S[γ](x) = ∫_{ℝ × ∂𝔹^m × ℝ} γ(a,u,b) σ(a⟨x,u⟩ - b) e^{ϱ⟨x,u⟩} da du db`.

The scale variable is a real number because `ℍ^m` has rank one, whatever its dimension. -/
def hyperbolicSynthesis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (σ : ℝ → ℂ)
    (γ : ℝ → sphere (0 : E) 1 → ℝ → ℂ) (x : E) : ℂ :=
  sliceSynthesis (volume : Measure ℝ) (HyperbolicSpace.boundaryMeasure E) σ γ
    HyperbolicSpace.boundaryDistance (hyperbolicWeight E) x

/-- The ridgelet transform on the Poincaré ball,
`R[f;ρ](a,u,b) = ∫ c[f](x) conj (ρ(a⟨x,u⟩ - b)) e^{ϱ⟨x,u⟩} dμ(x)`,
against the multiplier `c[f]` the article inserts to cancel one power of the Harish-Chandra
density. -/
def hyperbolicRidgelet (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (ρ : ℝ → ℂ) (cf : E → ℂ)
    (a : ℝ) (u : sphere (0 : E) 1) (b : ℝ) : ℂ :=
  ∫ x : E, cf x * conj (ρ (inner ℝ a (HyperbolicSpace.boundaryDistance x u) - b)) *
    hyperbolicWeight E x u ∂(HyperbolicSpace.invariantMeasure E)

/-- The network in Fourier expression form on the Poincaré ball. -/
def hyperbolicFourierExpression (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (Fσ : ℝ → ℂ)
    (Γ : ℝ → sphere (0 : E) 1 → ℝ → ℂ) (x : E) : ℂ :=
  fourierExpressionSynthesis (volume : Measure ℝ) (HyperbolicSpace.boundaryMeasure E) Fσ Γ
    HyperbolicSpace.boundaryDistance (hyperbolicWeight E) x

/-! ## Reconstruction -/

/-- **The reconstruction formula on real hyperbolic space** (Theorem 5.2 at `X = ℍ^m`), conditional
on the Helgason--Fourier inversion formula for `ℍ^m` and on nothing else.

Every piece of geometry is now fixed — the invariant measure of the ball, the uniform measure on the
boundary sphere, the composite distance and `ϱ` — so the hypothesis `HyperbolicSpace.HasInversion`
is a definite claim about a definite space rather than a schema. That is the difference from
`fs_symmetric_reconstruction_of_inversion`, whose hypothesis mentions free data.

The scalar is `fourierSlicePairing 1`: rank one, so the Jacobian exponent is `1` and not the
dimension `m`. -/
theorem fs_hyperbolic_reconstruction_of_inversion (Fσ Fρ : ℝ → ℂ) (W : ℝ) (c : ℝ → ℂ) (f : E → ℂ)
    (hinv : HyperbolicSpace.HasInversion W c f) (x : E) :
    hyperbolicFourierExpression E Fσ
        (separationOfVariables (HyperbolicSpace.helgasonFourier f)
          (SymmetricSpace.plancherelDensity W c) Fρ) x
      = fourierSlicePairing 1 Fσ Fρ * f x := by
  have hstep : ∀ y : E, inversionIntegral (volume : Measure ℝ)
      (HyperbolicSpace.boundaryMeasure E) (HyperbolicSpace.helgasonFourier f)
      (SymmetricSpace.plancherelDensity W c) HyperbolicSpace.boundaryDistance
      (hyperbolicWeight E) y = f y := by
    intro y
    rw [← hinv y]
    simp only [inversionIntegral, SymmetricSpace.helgasonInversionIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hyperbolicWeight, HyperbolicSpace.helgasonFourier, mul_assoc,
      fs_fourierSlicePhase_mul_horosphericalCharacter_zero]
  have h := fs_reconstruction_of_inversion (volume : Measure ℝ)
    (HyperbolicSpace.boundaryMeasure E) Fσ Fρ (HyperbolicSpace.helgasonFourier f)
    (SymmetricSpace.plancherelDensity W c) HyperbolicSpace.boundaryDistance
    (hyperbolicWeight E) f hstep x
  rw [hyperbolicFourierExpression]
  simpa using h

end LeanRidgelet

end

end
