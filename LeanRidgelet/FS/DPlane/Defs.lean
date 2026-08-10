/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Euclidean
public import LeanRidgelet.ToMathlib.DPlaneTransform
public import LeanRidgelet.ToMathlib.LieGroup.OrthogonalGroup

/-!
# Fourier slice method, Case IV: the `d`-plane layer, definitions

Section 6 of `arXiv:2402.15984`. The pieces every codimension shares: the coordinate vector of the
input against a frame, the layer built from it, the identity that makes the coefficient function a
`d`-plane transform of a fractional derivative, and the codimension-one case of the matrix polar
integration formula, where it degenerates to the two-sided polar formula.

`LeanRidgelet.FS.DPlane` is the guide to the case; it lists the results and the deviations from the
article.

## Main definitions and results

* `dPlaneCoord`: the coordinate vector `Aᵀx` of the input against the frame.
* `stiefelSynthesis`: the `d`-plane layer over the Stiefel manifold,
  `S[γ](x) = ∫ γ(U,b) σ(Uᵀx - b)`.
* `fs_fourier_dPlaneTransform_fractional`: for `g` a fractional derivative of `f` of order `s`, the
  bias spectrum of `P_d[g](U,·)` is `‖ω‖^s` times the Fourier data `𝓕 f (U ω)` of the target. So
  over the Stiefel manifold the coefficient function the method produces is the `d`-plane transform
  of a fractional derivative of the target, which is the article's observation that the ridgelet
  transform degenerates to a Radon transform there.
* `fs_matrixPolarIntegration_codim_one`: the matrix polar integration formula (Lemma C.2) at `k =
  1`, where it *is* the two-sided polar formula and the constant is `c_{m,1} = 2`. This is why
  codimension one needs none of the Stiefel machinery.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinate vector `Aᵀ x` of the input against the frame `A = L`, the argument of the
multivariate activation. -/
def dPlaneCoord (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (x : E) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => ⟪L (EuclideanSpace.single i (1 : ℝ)), x⟫

/-- The `d`-plane layer over the Stiefel manifold, `S[γ](x) = ∫ γ(U,b) σ(Uᵀx - b) dU db`, with the
weight ranging over orthonormal `k`-frames against a measure `ν` on them.

The measure is left as a parameter because the reconstruction formula fixes only the invariant one,
and that one now exists: `ContinuousLinearMap.stiefelMeasure` is the pushforward of the Haar
probability measure of the orthogonal group along its action on a frame. The Borel structure the
integral needs comes from `ContinuousLinearMap.instMeasurableSpaceLinearIsometry`. -/
def stiefelSynthesis (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E))
    (σ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ∫ L, (∫ b : EuclideanSpace ℝ (Fin k), γ L b * σ (dPlaneCoord L x - b)) ∂ν

/-- **The identity behind the Stiefel reconstruction formula.** If `g` is a fractional derivative
of `f` of order `s`, in the sense that its Fourier transform is `‖ξ‖^s` times that of `f`, then the
bias spectrum of the `d`-plane transform of `g` along a frame is `‖ω‖^s` times the Fourier data of
`f` along that frame.

The article's separation-of-variables ansatz over the Stiefel manifold is
`γ♯(U,ω) = f̂(Uω)|Uω|^{d-t}`, which is exactly the right-hand side with `s = d - t`; so the
coefficient function is the `d`-plane transform of a fractional derivative of the target, and over
the Stiefel manifold the ridgelet transform degenerates to a Radon transform. The fractional
Laplacian is not in Mathlib, so its multiplier property is the hypothesis rather than a
definition. -/
theorem fs_fourier_dPlaneTransform_fractional {s : ℝ} {f g : E → ℂ} (hg : Integrable g volume)
    (hmul : ∀ ξ : E, 𝓕 g ξ = ((‖ξ‖ ^ s : ℝ) : ℂ) * 𝓕 f ξ)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (ω : EuclideanSpace ℝ (Fin k)) :
    𝓕 (MeasureTheory.dPlaneTransform g L) ω = ((‖ω‖ ^ s : ℝ) : ℂ) * 𝓕 f (L ω) := by
  rw [← MeasureTheory.fourier_slice_dPlaneTransform hg L ω, hmul (L ω), L.norm_map]

/-! ## The matrix polar integration formula at codimension one -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Metric in
/-- Scaling a unit vector scales the norm: at `k = 1` the article's weight `|U b|^{m-k}` is
`|b|^{m-1}`. -/
theorem norm_smul_coe_sphere (b : ℝ) (u : sphere (0 : E) 1) : ‖b • (u : E)‖ = |b| := by
  rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.1 u.2, mul_one]

open Metric in
/-- **The matrix polar integration formula at codimension one** — the article's Lemma C.2 with
`k = 1`, where the Stiefel manifold `V_{m,1}` is the unit sphere and the constant is
`c_{m,1} = ∫_{𝕊⁰ × V_{m,0}} = 2`.

In this case the formula is the two-sided polar formula of `ToMathlib.PolarCoordinates`: the
article's weight `|U b|^{m-k}` is `‖b u‖^{m-1} = |b|^{m-1}`, and its constant is the factor `2` of
the double cover. So codimension one needs no Stiefel machinery at all, which is why the `k = 1`
reconstruction formulas are the ones within reach.

For general `k` the formula does need an invariant measure on `V_{m,k}`, and Mathlib has none: no
Stiefel manifold, no compactness or Haar measure plumbed for the orthogonal group, and no
invariance of the sphere measure under rotations. The development plan records the route and the
two gaps. -/
theorem fs_matrixPolarIntegration_codim_one (m : ℕ) [Nontrivial (InputSpace m)]
    {F : InputSpace m → ℂ} (hF : Integrable F volume) :
    (2 : ℝ) • ∫ x : InputSpace m, F x
      = ∫ u : sphere (0 : InputSpace m) 1,
          (∫ b : ℝ, ‖b • (u : InputSpace m)‖ ^ (Module.finrank ℝ (InputSpace m) - 1) •
            F (b • (u : InputSpace m)))
          ∂(volume : Measure (InputSpace m)).toSphere := by
  simp only [norm_smul_coe_sphere]
  exact MeasureTheory.integral_eq_integral_toSphere_integral_two_sided _ hF
end LeanRidgelet
