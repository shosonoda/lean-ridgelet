/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.Defs

/-!
# Fourier slice method, Case IV: codimension one

Section 6 of `arXiv:2402.15984` at `k = 1`, where the Stiefel manifold `V_{m,1}` is the unit sphere
`𝕊^{m-1}` and the matrix polar integration formula degenerates to the two-sided polar formula. The
whole case therefore closes with no measure theory on frames, which is why it comes first.

## Main definitions and results

* `sphereSynthesis`, `sphereFourierExpression`, `fs_sphere_fourierExpression_of_bias`: the layer
  over the sphere and Step 1. There is no scale parameter, so no Step 2 and no Fubini exchange: the
  bias frequency may stay inside the direction integral.
* `fs_sphere_reconstruction_of_inversion`: **the master identity.** Its hypothesis is on the
  *product* `γ♯(u,ω) σ♯(ω)`, which is what makes both the article's family and the classical Radon
  formula instances rather than approximate matches.
* `fs_angularFourier_slice_radonTransform`, `fs_angularFourier_radonTransform_fractional`: the
  Fourier slice theorem and the fractional-derivative identity in the angular convention, which is
  what identifies the coefficient function with a Radon transform.
* `fs_stiefel_reconstruction_codim_one`: **the article's Stiefel reconstruction formula at `k =
  1`**, for an activation of spectrum `|ω|^t`, with the constant `c_{m,1}(2π)^{m-1} = 2(2π)^{m-1}`.
* `fs_radon_reconstruction_codim_one`: **the classical Radon formula** of Carroll--Dickinson and
  Ito, as the instance at the actual spectrum `(iω)^{-1}` of the Heaviside step function.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The layer at codimension one

At `k = 1` the Stiefel manifold `V_{m,1}` is the unit sphere, a weight matrix is a unit vector, and
`stiefelSynthesis` is the ordinary ridge network with the scale parameter removed. This is the one
case of Section 6 that needs no measure theory beyond polar coordinates, because there the matrix
polar integration formula is `fs_matrixPolarIntegration_codim_one`.
-/

section CodimOne

open Metric

variable {m : ℕ}

/-- The `d`-plane layer at codimension one, `S[γ](x) = ∫_{𝕊^{m-1}} ∫_ℝ γ(u,b) σ(⟪u,x⟫ - b) db du`:
the weight ranges over `V_{m,1} = 𝕊^{m-1}` against the surface measure and carries no scale
factor. -/
def sphereSynthesis (σ : ℝ → ℂ) (γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ)
    (x : InputSpace m) : ℂ :=
  ∫ u : sphere (0 : InputSpace m) 1,
      (∫ b : ℝ, γ u b * σ (inner ℝ (u : InputSpace m) x - b))
    ∂(volume : Measure (InputSpace m)).toSphere

/-- The Fourier expression of the codimension-one layer, the output of Step 1:
`S[γ](x) = (2π)⁻¹ ∫_{𝕊^{m-1}} ∫_ℝ γ♯(u,ω) σ♯(ω) e^{iω⟪u,x⟫} dω du`. -/
def sphereFourierExpression (Fσ : ℝ → ℂ) (Γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ)
    (x : InputSpace m) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ u : sphere (0 : InputSpace m) 1,
        (∫ ω : ℝ, Γ u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ (u : InputSpace m) x))
      ∂(volume : Measure (InputSpace m)).toSphere

/-- **Step 1 at codimension one**: the layer equals its Fourier expression.

The analytic input is the one-dimensional bias identity at each direction, exactly as in the
abstract scheme, and it enters as the hypothesis `hbias` for the same reason: which form of it is
available depends on the class the activation is taken from, and the activations of the Stiefel
theorem are tempered distributions rather than integrable functions. Unlike in the abstract scheme
no Fubini rearrangement is needed, because with no scale parameter to change variables in the bias
frequency may stay inside the direction integral. -/
theorem fs_sphere_fourierExpression_of_bias (σ Fσ : ℝ → ℂ)
    (γ Γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ) (x : InputSpace m)
    (hbias : ∀ u : sphere (0 : InputSpace m) 1,
      (∫ b : ℝ, γ u b * σ (inner ℝ (u : InputSpace m) x - b))
        = (2 * (Real.pi : ℂ))⁻¹ *
          ∫ ω : ℝ, Γ u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ (u : InputSpace m) x)) :
    sphereSynthesis σ γ x = sphereFourierExpression Fσ Γ x := by
  rw [sphereSynthesis, sphereFourierExpression, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hbias)

/-! ## The reconstruction formula at codimension one -/

/-- **The reconstruction formula of the Fourier slice method at codimension one.** The
separation-of-variables condition of the Stiefel case is that the product of the bias spectrum of
the coefficient function with the activation spectrum be a constant multiple of
`f̂(ω u) |ω|^{m-1}` — the article's `eq:sov.hom`, whose auxiliary factor `φ♯` is required to be
constant. Under it the network reproduces the target up to the constant `c · c_{m,1} (2π)^{m-1}`.

Both integrals of the derivation are absolutely convergent by hypothesis, which is the article's
standing assumption of Section 2. The direction integral is then evaluated by the matrix polar
integration formula `fs_matrixPolarIntegration_codim_one`, whose constant `c_{m,1} = 2` is the
double cover `(ω, u) ↦ ω u` of `ℝ^m ∖ {0}`, and the remaining Euclidean integral by the inversion
formula, which is the hypothesis `hinv`; on a Euclidean input domain that hypothesis is the theorem
`fs_angularFourier_inversion_inner`, and its constant is the `(2π)^m` appearing here.

The hypothesis is on the *product* `γ♯(u,ω) σ♯(ω)`, so the activation spectrum need not be even;
this is what lets the classical Radon formula be an instance. -/
theorem fs_sphere_reconstruction_of_inversion [Nontrivial (InputSpace m)] (c : ℂ)
    (Fσ : ℝ → ℂ) (Γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ) (Ff f : InputSpace m → ℂ)
    (x : InputSpace m)
    (hansatz : ∀ u : sphere (0 : InputSpace m) 1, ∀ᵐ ω : ℝ,
      Γ u ω * Fσ ω
        = c * ((|ω| ^ ((m : ℝ) - 1) : ℝ) : ℂ) * Ff (ω • (u : InputSpace m)))
    (hF : Integrable (fun ξ : InputSpace m => Ff ξ * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hinv : (∫ ξ : InputSpace m, Ff ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x) :
    sphereFourierExpression Fσ Γ x = c * 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by
  have hdim : Module.finrank ℝ (InputSpace m) = m := finrank_euclideanSpace_fin
  have hm : 0 < m := hdim ▸ Module.finrank_pos
  have hweight : ∀ ω : ℝ, (|ω| ^ ((m : ℝ) - 1) : ℝ)
      = |ω| ^ (Module.finrank ℝ (InputSpace m) - 1) := by
    intro ω
    rw [hdim, show ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hm, Nat.cast_one], Real.rpow_natCast]
  set F : InputSpace m → ℂ := fun ξ => Ff ξ * fourierSlicePhase (inner ℝ ξ x) with hFdef
  have hstep : ∀ u : sphere (0 : InputSpace m) 1,
      (∫ ω : ℝ, Γ u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ (u : InputSpace m) x))
        = c * ∫ ω : ℝ,
            ‖ω • (u : InputSpace m)‖ ^ (Module.finrank ℝ (InputSpace m) - 1) •
              F (ω • (u : InputSpace m)) := by
    intro u
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hansatz u] with ω hω
    simp only [hω, hFdef, norm_smul_coe_sphere, hweight, Complex.real_smul,
      real_inner_smul_left]
    ring
  have hpolar := fs_matrixPolarIntegration_codim_one m hF
  have hpow : (((2 * Real.pi) ^ m : ℝ) : ℂ)
      = (2 * (Real.pi : ℂ)) * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) := by
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  calc sphereFourierExpression Fσ Γ x
      = (2 * (Real.pi : ℂ))⁻¹ * (c * ((2 : ℝ) • ∫ ξ : InputSpace m, F ξ)) := by
        rw [sphereFourierExpression, integral_congr_ae (Filter.Eventually.of_forall hstep),
          integral_const_mul, ← hpolar]
    _ = c * 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by
        rw [Complex.real_smul, hinv, hpow]
        field_simp
        push_cast
        ring

/-! ## The coefficient function is a Radon transform -/

/-- **The Fourier slice theorem in the article's angular convention** at codimension one: the bias
spectrum of the Radon transform of `f` along a unit direction is the angular Fourier data of `f` on
the ray through that direction. Rescaling the frequency does not disturb the slice theorem. -/
theorem fs_angularFourier_slice_radonTransform {f : InputSpace m → ℂ} (hf : Integrable f volume)
    {u : InputSpace m} (hu : ‖u‖ = 1) (ω : ℝ) :
    Fourier.angularFourierIntegralInner (MeasureTheory.radonTransform f u) ω
      = Fourier.angularFourierIntegralInner f (ω • u) := by
  rw [Fourier.angularFourierIntegralInner_eq_mathlib,
    Fourier.angularFourierIntegralInner_eq_mathlib, smul_smul]
  exact (MeasureTheory.fourier_slice_radonTransform hf u hu ((2 * Real.pi)⁻¹ • ω)).symm

/-- **The coefficient function is the Radon transform of a fractional derivative.** If `g` is the
fractional derivative of order `s` of `f`, in the sense that its angular Fourier transform is
`‖ξ‖^s` times that of `f`, then the bias spectrum of `P_d[g](u,·)` is `|ω|^s` times the Fourier
data of `f` along `u`.

This is the codimension-one form of `fs_fourier_dPlaneTransform_fractional`, in the convention the
reconstruction formula is stated in — the two conventions do not agree here, since a multiplier
`‖ξ‖^s` becomes `(2π)^s ‖ξ‖^s` under the rescaling of the frequency. The fractional Laplacian is
not in Mathlib, so its multiplier property is the hypothesis rather than a definition. -/
theorem fs_angularFourier_radonTransform_fractional {s : ℝ} {f g : InputSpace m → ℂ}
    (hg : Integrable g volume)
    (hmul : ∀ ξ : InputSpace m, Fourier.angularFourierIntegralInner g ξ
      = ((‖ξ‖ ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner f ξ)
    {u : InputSpace m} (hu : ‖u‖ = 1) (ω : ℝ) :
    Fourier.angularFourierIntegralInner (MeasureTheory.radonTransform g u) ω
      = ((|ω| ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner f (ω • u) := by
  rw [fs_angularFourier_slice_radonTransform hg hu ω, hmul, norm_smul, hu, mul_one,
    Real.norm_eq_abs]

/-! ## The two reconstruction formulas at codimension one -/

/-- Over `ℝ` the singular frequency is negligible, unlike over a finite field where it is an
atom. -/
theorem fs_ae_ne_zero : ∀ᵐ ω : ℝ, ω ≠ 0 := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with ω hω
  simpa using hω

/-- **The reconstruction formula over the Stiefel manifold at codimension one** — the article's
`thm:stiefel` with `k = 1`, where the Stiefel manifold is the unit sphere and `c_{m,1} = 2`.

The activation has spectrum `σ♯(ω) = |ω|^t`, and the coefficient function is the Radon transform of
the fractional derivative `g = △^{(d-t)/2} f` of the target, `d = m - 1`: this is the article's
`R[f](U,b) = P_d[△^{(d-t)/2}f](U,b)`, whose bias spectrum
`fs_angularFourier_radonTransform_fractional` computes. The conclusion is
`S[R[f]](x) = c_{m,1} (2π)^{d} f(x)`.

*The constant is the reciprocal of the article's*; see the *Deviations from the article* section of
this module, and `fs_radon_reconstruction_codim_one` for the independent confirmation. -/
theorem fs_stiefel_reconstruction_codim_one [Nontrivial (InputSpace m)] (t : ℝ) (σ : ℝ → ℂ)
    (f g : InputSpace m → ℂ) (x : InputSpace m)
    (hf : Integrable f volume) (hFf : Integrable (𝓕 f) volume) (hx : ContinuousAt f x)
    (hg : Integrable g volume)
    (hfrac : ∀ ξ : InputSpace m, Fourier.angularFourierIntegralInner g ξ
      = ((‖ξ‖ ^ ((m : ℝ) - 1 - t) : ℝ) : ℂ) * Fourier.angularFourierIntegralInner f ξ)
    (hbias : ∀ u : sphere (0 : InputSpace m) 1,
      (∫ b : ℝ, MeasureTheory.radonTransform g (u : InputSpace m) b *
          σ (inner ℝ (u : InputSpace m) x - b))
        = (2 * (Real.pi : ℂ))⁻¹ *
          ∫ ω : ℝ, Fourier.angularFourierIntegralInner
                (MeasureTheory.radonTransform g (u : InputSpace m)) ω *
              ((|ω| ^ t : ℝ) : ℂ) * fourierSlicePhase (ω * inner ℝ (u : InputSpace m) x)) :
    sphereSynthesis σ (fun u => MeasureTheory.radonTransform g (u : InputSpace m)) x
      = 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by
  have hansatz : ∀ u : sphere (0 : InputSpace m) 1, ∀ᵐ ω : ℝ,
      Fourier.angularFourierIntegralInner
            (MeasureTheory.radonTransform g (u : InputSpace m)) ω * ((|ω| ^ t : ℝ) : ℂ)
        = 1 * ((|ω| ^ ((m : ℝ) - 1) : ℝ) : ℂ) *
          Fourier.angularFourierIntegralInner f (ω • (u : InputSpace m)) := by
    intro u
    have hu : ‖(u : InputSpace m)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
    filter_upwards [fs_ae_ne_zero] with ω hω
    have hexp : (m : ℝ) - 1 - t + t = (m : ℝ) - 1 := by ring
    have hsplit : ((|ω| ^ ((m : ℝ) - 1) : ℝ) : ℂ)
        = ((|ω| ^ ((m : ℝ) - 1 - t) : ℝ) : ℂ) * ((|ω| ^ t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (abs_pos.mpr hω), hexp]
    rw [fs_angularFourier_radonTransform_fractional hg hfrac hu ω, hsplit]
    ring
  calc sphereSynthesis σ (fun u => MeasureTheory.radonTransform g (u : InputSpace m)) x
      = sphereFourierExpression (fun ω => ((|ω| ^ t : ℝ) : ℂ))
          (fun u => Fourier.angularFourierIntegralInner
            (MeasureTheory.radonTransform g (u : InputSpace m))) x :=
        fs_sphere_fourierExpression_of_bias _ _ _ _ x hbias
    _ = 1 * 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x :=
        fs_sphere_reconstruction_of_inversion 1 _ _
          (Fourier.angularFourierIntegralInner f) f x hansatz
          (fs_integrable_angularFourier_mul_phase hFf x)
          (fs_angularFourier_inversion_inputSpace hf hFf hx)
    _ = 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by ring

/-- **The classical Radon formula** of Carroll--Dickinson and Ito — the article's `thm:ito.radon` —
as an instance of the codimension-one reconstruction formula.

The activation is the Heaviside step function, whose spectrum is `πδ(ω) + (iω)^{-1}`; its
homogeneous part `(iω)^{-1}` is the hypothesis `hbias` here. The coefficient function is
`∂_b(-△_b)^{(m-1)/2} P_d[f](u,b)`, whose bias spectrum is `iω|ω|^{m-1}` times that of the Radon
transform — the hypothesis `hγ`. The conclusion `S[γ](x) = 2(2π)^{m-1} f(x)` is the classical
formula solved for `S[γ]`, and its constant is the reciprocal of the `(2(2π)^{m-1})^{-1}` the
article quotes: this is the independent confirmation of the constant of
`fs_stiefel_reconstruction_codim_one`.

This is *not* the `t = -1` instance of that theorem. The step function's spectrum
`(iω)^{-1} = -i sgn(ω)|ω|^{-1}` is not `|ω|^{-1}`, and the odd factor is exactly what turns the
coefficient function `△_b^{m/2} P_d[f]` of `thm:stiefel` at `t = -1` into the classical
`∂_b(-△_b)^{(m-1)/2} P_d[f]`. Both are instances of `fs_sphere_reconstruction_of_inversion`, whose
hypothesis constrains only the product of the two spectra. -/
theorem fs_radon_reconstruction_codim_one [Nontrivial (InputSpace m)] (σ : ℝ → ℂ)
    (f : InputSpace m → ℂ) (γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ) (x : InputSpace m)
    (hf : Integrable f volume) (hFf : Integrable (𝓕 f) volume) (hx : ContinuousAt f x)
    (hγ : ∀ (u : sphere (0 : InputSpace m) 1) (ω : ℝ),
      Fourier.angularFourierIntegralInner (γ u) ω
        = Complex.I * (ω : ℂ) * ((|ω| ^ ((m : ℝ) - 1) : ℝ) : ℂ) *
          Fourier.angularFourierIntegralInner
            (MeasureTheory.radonTransform f (u : InputSpace m)) ω)
    (hbias : ∀ u : sphere (0 : InputSpace m) 1,
      (∫ b : ℝ, γ u b * σ (inner ℝ (u : InputSpace m) x - b))
        = (2 * (Real.pi : ℂ))⁻¹ *
          ∫ ω : ℝ, Fourier.angularFourierIntegralInner (γ u) ω *
              (Complex.I * (ω : ℂ))⁻¹ * fourierSlicePhase (ω * inner ℝ (u : InputSpace m) x)) :
    sphereSynthesis σ γ x = 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by
  have hansatz : ∀ u : sphere (0 : InputSpace m) 1, ∀ᵐ ω : ℝ,
      Fourier.angularFourierIntegralInner (γ u) ω * (Complex.I * (ω : ℂ))⁻¹
        = 1 * ((|ω| ^ ((m : ℝ) - 1) : ℝ) : ℂ) *
          Fourier.angularFourierIntegralInner f (ω • (u : InputSpace m)) := by
    intro u
    have hu : ‖(u : InputSpace m)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
    filter_upwards [fs_ae_ne_zero] with ω hω
    have hω' : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
    have hIω : Complex.I * (ω : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hω'
    rw [hγ u ω, fs_angularFourier_slice_radonTransform hf hu ω]
    field_simp
  calc sphereSynthesis σ γ x
      = sphereFourierExpression (fun ω => (Complex.I * (ω : ℂ))⁻¹)
          (fun u => Fourier.angularFourierIntegralInner (γ u)) x :=
        fs_sphere_fourierExpression_of_bias _ _ _ _ x hbias
    _ = 1 * 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x :=
        fs_sphere_reconstruction_of_inversion 1 _ _
          (Fourier.angularFourierIntegralInner f) f x hansatz
          (fs_integrable_angularFourier_mul_phase hFf x)
          (fs_angularFourier_inversion_inputSpace hf hFf hx)
    _ = 2 * (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by ring

end CodimOne
end LeanRidgelet
