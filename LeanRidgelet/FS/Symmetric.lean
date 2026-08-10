/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Euclidean

/-!
# Fourier slice method, Case III: networks on a noncompact symmetric space

Section 5 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984).

On a noncompact symmetric space `X = G/K` the scalar product `a ⬝ x` of the Euclidean layer is
replaced by `a ⬝ ⟪x,u⟫`, where `⟪x,u⟫ ∈ 𝔞 ≅ ℝ^r` is the vector-valued composite distance from the
origin to the horosphere through `x` with normal `u ∈ ∂X`, and the layer carries the weight
`e^{ϱ⟪x,u⟫}`. The Helgason--Fourier transform replaces the Fourier transform, and the exponent of
the Jacobian is the rank `r` of `X` rather than the dimension.

Mathlib has none of the underlying theory: no Iwasawa decomposition, no spherical functions, no
Harish-Chandra `c`-function, no Helgason--Fourier transform, and so no inversion formula. What
this file shows is that none of it is needed to formalize the *method*. The geometry enters only
through four pieces of data — the composite distance, the constant `ϱ`, the density built from
`|W|` and the `c`-function, and the Helgason--Fourier transform of the target — and the
reconstruction formula is the instance of `fs_reconstruction_of_inversion` obtained by feeding the
Helgason--Fourier inversion formula to it as the hypothesis it already asks for.

So the inversion formula is an explicit hypothesis of a theorem: never an axiom, never a structure
or typeclass field, and never a `sorry`. Proving it, first for the hyperbolic space and the
manifold of positive definite matrices and eventually for a general `G/K`, is the separate
long-term milestone M10 of the development plan.

## Main definitions and results

* `horosphericalWeight`: the weight `e^{ϱ⟪x,u⟫}` the layer carries.
* `symmetricSynthesis`: the network `S[γ](x) = ∫ γ(a,u,b) σ(a ⬝ ⟪x,u⟫ - b) e^{ϱ⟪x,u⟫}`.
* `symmetricRidgelet`: the ridgelet transform `R[f;ρ](a,u,b)`, against the multiplier `c[f]` the
  article inserts to cancel one power of the Harish-Chandra density.
* `harishChandraDensity`: the density `|W|⁻¹|c(λ)|⁻²` of the inversion formula.
* `fs_symmetric_reconstruction_of_inversion`: **the reconstruction formula on `G/K`**
  (Theorem 5.2), conditional on the Helgason--Fourier inversion formula.
* `fs_symmetricFourierExpression_euclidean`: the shape is inhabited — a point boundary and `ϱ = 0`
  return the Euclidean instance of `FS.Euclidean`.

## Deviations from the article

None in the statement. The scalar is `fourierSlicePairing r`, which is the article's
`⦅σ,ρ⦆ = (|W|/2π) ∫ σ♯ conj (ρ♯) |ω|^{-r}` with `|W|` moved from the scalar into the density of
the inversion formula, where it belongs; see the module docstring of `FS.Scheme` for the same
bookkeeping in the Euclidean case.

The article's `c[f]`, defined by `ĉ[f](λ,u) = f̂(λ,u)|c(λ)|^{-2}`, exists here as the composite
`fun λ u => Ff λ u * (‖cfun λ‖ ^ 2)⁻¹` appearing in `symmetricRidgelet`: the ridgelet transform
carries one factor of the density and the inversion formula the other, which is why the article's
inversion integral has `|c(λ)|^{-2}` and its `c[f]` has `|c(λ)|^{-4}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LeanRidgelet

variable {r : ℕ} {X : Type*} {U : Type*} [MeasurableSpace U]

/-! ## The geometry, as data -/

/-- The weight `e^{ϱ⟪x,u⟫}` carried by the layer, where `⟪x,u⟫ ∈ 𝔞 ≅ ℝ^r` is the composite
distance and `ϱ ∈ 𝔞*` the constant vector of the Helgason--Fourier transform. -/
def horosphericalWeight (ϱ : InputSpace r) (cd : X → U → InputSpace r) (x : X) (u : U) : ℂ :=
  Complex.exp ((inner ℝ ϱ (cd x u) : ℝ) : ℂ)

omit [MeasurableSpace U] in
@[simp] theorem horosphericalWeight_zero (cd : X → U → InputSpace r) (x : X) (u : U) :
    horosphericalWeight (0 : InputSpace r) cd x u = 1 := by
  simp [horosphericalWeight]

/-- The density `|W|⁻¹|c(λ)|⁻²` of the Helgason--Fourier inversion formula, built from the order
of the Weyl group and the Harish-Chandra `c`-function. Both enter as data. -/
def harishChandraDensity (W : ℝ) (cfun : InputSpace r → ℂ) (lam : InputSpace r) : ℝ :=
  (W * ‖cfun lam‖ ^ 2)⁻¹

/-! ## The network and the ridgelet transform -/

/-- The network on a noncompact symmetric space,
`S[γ](x) = ∫ γ(a,u,b) σ(a ⬝ ⟪x,u⟫ - b) e^{ϱ⟪x,u⟫} da du db`.

Turning this into its Fourier expression is Step 1 of the method, which is one-dimensional — the
convolution theorem in the bias — and is not part of this file; see the module docstring of
`FS.Scheme`. -/
def symmetricSynthesis (ν : Measure U) (ϱ : InputSpace r) (cd : X → U → InputSpace r)
    (σ : ℝ → ℂ) (γ : InputSpace r → U → ℝ → ℂ) (x : X) : ℂ :=
  ∫ a : InputSpace r, ∫ u : U, ∫ b : ℝ,
    γ a u b * σ (inner ℝ a (cd x u) - b) * horosphericalWeight ϱ cd x u ∂volume ∂ν

/-- The ridgelet transform on a noncompact symmetric space,
`R[f;ρ](a,u,b) = ∫_X c[f](x) conj (ρ (a ⬝ ⟪x,u⟫ - b)) e^{ϱ⟪x,u⟫} dx`,
against the multiplier `c[f]` supplied as data. -/
def symmetricRidgelet [MeasurableSpace X] (μX : Measure X) (ϱ : InputSpace r)
    (cd : X → U → InputSpace r)
    (ρ : ℝ → ℂ) (cf : X → ℂ) (a : InputSpace r) (u : U) (b : ℝ) : ℂ :=
  ∫ x : X, cf x * conj (ρ (inner ℝ a (cd x u) - b)) * horosphericalWeight ϱ cd x u ∂μX

/-- The network in Fourier expression form on a symmetric space: the specialization of
`fourierExpressionSynthesis` to the composite distance and the horospherical weight. -/
def symmetricFourierExpression (ν : Measure U) (ϱ : InputSpace r) (cd : X → U → InputSpace r)
    (Fσ : ℝ → ℂ) (Γ : InputSpace r → U → ℝ → ℂ) (x : X) : ℂ :=
  fourierExpressionSynthesis (volume : Measure (InputSpace r)) ν Fσ Γ cd
    (horosphericalWeight ϱ cd) x

/-! ## Reconstruction -/

/-- **The reconstruction formula on a noncompact symmetric space** (Theorem 5.2), as the instance
of the abstract scheme in which the input domain is `G/K`, the direction space is the boundary
`∂X`, the scale space is `𝔞* ≅ ℝ^r`, the weight is `e^{ϱ⟪x,u⟫}`, the Fourier data is the
Helgason--Fourier transform of the target and the inversion density is `|W|⁻¹|c(λ)|⁻²`.

The Helgason--Fourier inversion formula is the hypothesis. Mathlib carries none of the theory
needed to prove it — no Iwasawa decomposition, no spherical functions, no `c`-function — so it
enters here and only here, as an explicit hypothesis of a theorem. -/
theorem fs_symmetric_reconstruction_of_inversion (ν : Measure U) (ϱ : InputSpace r)
    (cd : X → U → InputSpace r) (Fσ Fρ : ℝ → ℂ) (Ff : InputSpace r → U → ℂ) (W : ℝ)
    (cfun : InputSpace r → ℂ) (f : X → ℂ)
    (hinv : ∀ y : X, (∫ lam : InputSpace r, ∫ u : U,
        Ff lam u * ((harishChandraDensity W cfun lam : ℝ) : ℂ) *
          fourierSlicePhase (inner ℝ lam (cd y u)) * horosphericalWeight ϱ cd y u ∂ν) = f y)
    (x : X) :
    symmetricFourierExpression ν ϱ cd Fσ
        (separationOfVariables Ff (harishChandraDensity W cfun) Fρ) x
      = fourierSlicePairing (r : ℝ) Fσ Fρ * f x := by
  have := fs_reconstruction_of_inversion (volume : Measure (InputSpace r)) ν Fσ Fρ Ff
    (harishChandraDensity W cfun) cd (horosphericalWeight ϱ cd) f hinv x
  rwa [fs_finrank_inputSpace] at this

/-- The shape is inhabited: with a one-point boundary, `ϱ = 0` and the identity as composite
distance, the symmetric-space Fourier expression is the Euclidean one of `FS.Euclidean`, whose
reconstruction formula `fs_reconstruction_euclidean` is the same instance of the same theorem. So
the conditional theorem above is not vacuous in shape — only the Helgason--Fourier inversion
formula itself is out of reach. -/
theorem fs_symmetricFourierExpression_euclidean (Fσ : ℝ → ℂ)
    (Γ : InputSpace r → Unit → ℝ → ℂ) (x : InputSpace r) :
    symmetricFourierExpression (Measure.dirac ()) (0 : InputSpace r)
        (fun (y : InputSpace r) (_ : Unit) => y) Fσ Γ x
      = fourierExpressionSynthesis (volume : Measure (InputSpace r)) (Measure.dirac ()) Fσ Γ
          (fun (y : InputSpace r) (_ : Unit) => y) (fun _ _ => (1 : ℂ)) x := by
  have hw : horosphericalWeight (0 : InputSpace r) (fun (y : InputSpace r) (_ : Unit) => y)
      = fun _ _ => (1 : ℂ) := by
    funext y u
    exact horosphericalWeight_zero _ y u
  rw [symmetricFourierExpression, hw]

end LeanRidgelet
