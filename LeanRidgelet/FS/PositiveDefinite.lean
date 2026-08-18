/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Symmetric
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite

/-!
# Fourier slice method, Case III on the manifold of positive definite matrices

Section 5 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984)

instantiates the network on a noncompact symmetric space at two spaces. This file does the second,
the *continuous horospherical SPD network* on `ℙ_m = GL(m,ℝ)/O(m)`, using the model built in
`LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite`.

This is the higher-rank example, and the contrast with `FS.Hyperbolic` is the point of having both.
The rank of `ℙ_m` is `m`, so the scale variable of the network is a *vector* and the Jacobian
exponent of the reconstruction formula is `m`; the rank of `ℍ^m` is one whatever its dimension, so
there the scale variable is a scalar and the exponent is `1`. Both are the same instance of the same
abstract theorem, which is what the Fourier slice method claims: the exponent is the rank, and the
rank is a property of how the weight is parametrized, not of the input domain.

## Main definitions

* `LeanRidgelet.spdWeight`: the weight `e^{ϱ⟨x,u⟩}` the layer carries.
* `LeanRidgelet.spdSynthesis`: the network
  `S[γ](x) = ∫ γ(a,u,b) σ(a · ⟨x,u⟩ - b) e^{ϱ⟨x,u⟩} da du db`.
* `LeanRidgelet.spdRidgelet`: the ridgelet transform `R[f;ρ](a,u,b)`.

## Main results

* `fs_spd_reconstruction_of_inversion`: **the reconstruction formula on `ℙ_m`**, conditional on the
  Helgason--Fourier inversion formula for `ℙ_m` and on nothing else.

## Deviations from the article

The scalar is `fourierSlicePairing m`, the rank of `ℙ_m` being `m`.

`ϱ` is not an argument: it is `SpdSpace.spdRho m = (-½,…,-½,(m-1)/4)`, the article's value, which
the underlying model confirms rather than contradicts. The article writes its composite distance as
`½ log λ` in the Cholesky diagonal but takes its constants from A. Terras, *Harmonic Analysis on
Symmetric Spaces*, Thm 1.3.1(1), whose kernel is the power function `p_s(Y) = ∏_j |Y_j|^{s_j}` in
the leading principal minors. The model here uses Terras' coordinates throughout, so the value
transfers with no substitution to carry.

The order of the Weyl group and the `c`-function are still arguments. Terras gives both explicitly;
what is not yet pinned is her contour measure `ds` on `Re s = -ρ` against Lebesgue `dλ`, which is
the project's convention, and that conversion is a computation rather than a transcription.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LeanRidgelet

variable {m : ℕ}

/-! ## The network on `ℙ_m` -/

/-- The weight `e^{ϱ⟨x,u⟩}` that a layer of the continuous horospherical SPD network carries: the
horospherical character of `ℙ_m` at zero frequency. -/
def spdWeight (c : EuclideanSpace ℝ (SpdSpace.UpperIdx m)) (Q : SpdSpace.Boundary m) : ℂ :=
  SymmetricSpace.horosphericalCharacter (SpdSpace.spdRho m) 0 (SpdSpace.compositeDistance c Q)

/-- **The continuous horospherical SPD network** (Section 5),
`S[γ](x) = ∫_{ℝ^m × ∂ℙ_m × ℝ} γ(a,u,b) σ(a · ⟨x,u⟩ - b) e^{ϱ⟨x,u⟩} da du db`.

The scale variable is a vector of `ℝ^m` because `ℙ_m` has rank `m`. -/
def spdSynthesis (σ : ℝ → ℂ)
    (γ : EuclideanSpace ℝ (Fin m) → SpdSpace.Boundary m → ℝ → ℂ)
    (x : EuclideanSpace ℝ (SpdSpace.UpperIdx m)) : ℂ :=
  sliceSynthesis (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (ContinuousLinearMap.orthogonalHaar (E := EuclideanSpace ℝ (Fin m))) σ γ
    SpdSpace.compositeDistance spdWeight x

/-- The ridgelet transform on `ℙ_m`,
`R[f;ρ](a,u,b) = ∫ c[f](x) conj (ρ(a · ⟨x,u⟩ - b)) e^{ϱ⟨x,u⟩} dμ(x)`,
against the multiplier `c[f]` the article inserts to cancel one power of the Harish-Chandra
density. -/
def spdRidgelet (ρ : ℝ → ℂ)
    (cf : EuclideanSpace ℝ (SpdSpace.UpperIdx m) → ℂ) (a : EuclideanSpace ℝ (Fin m))
    (Q : SpdSpace.Boundary m) (b : ℝ) : ℂ :=
  ∫ x : EuclideanSpace ℝ (SpdSpace.UpperIdx m), cf x *
    conj (ρ (inner ℝ a (SpdSpace.compositeDistance x Q) - b)) * spdWeight x Q
    ∂(SpdSpace.invariantMeasure m)

/-- The network in Fourier expression form on `ℙ_m`. -/
def spdFourierExpression (Fσ : ℝ → ℂ)
    (Γ : EuclideanSpace ℝ (Fin m) → SpdSpace.Boundary m → ℝ → ℂ)
    (x : EuclideanSpace ℝ (SpdSpace.UpperIdx m)) : ℂ :=
  fourierExpressionSynthesis (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (ContinuousLinearMap.orthogonalHaar (E := EuclideanSpace ℝ (Fin m))) Fσ Γ
    SpdSpace.compositeDistance spdWeight x

/-! ## Reconstruction -/

/-- **The reconstruction formula on the manifold of positive definite matrices** (Theorem 5.2 at
`X = ℙ_m`), conditional on the Helgason--Fourier inversion formula for `ℙ_m` and on nothing else.

The geometry is fixed: the invariant measure `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`, the Haar
probability measure of the orthogonal group standing in for the boundary `K/M`, and the composite
distance `⟨x,u⟩_j = log|(u^⊤ x u)_j|` in the leading principal minors, and the shift
`ϱ = (-½,…,-½,(m-1)/4)`. So the hypothesis `SpdSpace.HasInversion` is a definite claim about a
definite space.

The scalar is `fourierSlicePairing m`: rank `m`, so the Jacobian exponent is the rank, which here
coincides with a dimension count only because `ℙ_m` is a maximal-rank space. -/
theorem fs_spd_reconstruction_of_inversion (Fσ Fρ : ℝ → ℂ)
    (W : ℝ) (c : EuclideanSpace ℝ (Fin m) → ℂ)
    (f : EuclideanSpace ℝ (SpdSpace.UpperIdx m) → ℂ)
    (hinv : SpdSpace.HasInversion W c f) (x : EuclideanSpace ℝ (SpdSpace.UpperIdx m)) :
    spdFourierExpression Fσ
        (separationOfVariables (SpdSpace.helgasonFourier (SpdSpace.spdRho m) f)
          (SymmetricSpace.plancherelDensity W c) Fρ) x
      = fourierSlicePairing (m : ℝ) Fσ Fρ * f x := by
  have hstep : ∀ y : EuclideanSpace ℝ (SpdSpace.UpperIdx m),
      inversionIntegral (volume : Measure (EuclideanSpace ℝ (Fin m)))
        (ContinuousLinearMap.orthogonalHaar (E := EuclideanSpace ℝ (Fin m)))
        (SpdSpace.helgasonFourier (SpdSpace.spdRho m) f)
        (SymmetricSpace.plancherelDensity W c)
        SpdSpace.compositeDistance spdWeight y = f y := by
    intro y
    rw [← hinv y]
    simp only [inversionIntegral, SymmetricSpace.helgasonInversionIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun Q => ?_)
    simp only [spdWeight, SpdSpace.helgasonFourier, mul_assoc,
      fs_fourierSlicePhase_mul_horosphericalCharacter_zero]
  have h := fs_reconstruction_of_inversion (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (ContinuousLinearMap.orthogonalHaar (E := EuclideanSpace ℝ (Fin m))) Fσ Fρ
    (SpdSpace.helgasonFourier (SpdSpace.spdRho m) f) (SymmetricSpace.plancherelDensity W c)
    SpdSpace.compositeDistance spdWeight f hstep x
  rw [spdFourierExpression]
  simpa using h

end LeanRidgelet

end

end
