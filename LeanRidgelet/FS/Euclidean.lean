/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Scheme
public import LeanRidgelet.L1.FourierExpression
public import LeanRidgelet.ToMathlib.PolarCoordinates
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier slice method: the Euclidean case, and agreement with the L1 development

The classical case of Section 2 of arXiv:2402.15984 — the depth-2 fully-connected network on a
Euclidean space — as an instance of the abstract scheme, together with the two identities that
check the abstraction against the existing L1 formalization of arXiv:1505.03654v2.

The Euclidean instance takes the direction space to be a point, so that the weight is a plain
vector of `ℝ^m`, the composite distance is the identity, and the weight function is `1`. The scale
space is `ℝ^m` itself, so the exponent of the Jacobian is `r = m`. What remains is the inversion
density `κ = (2π)^{-m}`, the normalization of the Fourier inversion formula on `ℝ^m`.

## Main results

* `fs_inversionIntegral_euclidean`: with a one-point direction space the inversion integral is the
  plain inversion integral `∫ ξ, F(ξ) κ(ξ) e^{i⟪ξ,x⟫} dξ`.
* `fs_reconstruction_euclidean`: the reconstruction formula for the fully-connected network,
  conditional on the Fourier inversion formula on `ℝ^m` in the article's convention.
* `fs_separationOfVariables_euclideanRidgeletTransform`: **the ansatz is the L1 Fourier
  expression.** The bias spectrum of the classical ridgelet transform `eq:fstridge`, already
  proved in `L1.FourierExpression`, is exactly what `separationOfVariables` produces.
* `fs_admissibilityConstant_eq_fourierSlicePairing`: **the two scalars agree.** The L1
  admissibility constant is `(2π)^m` times the Fourier slice pairing of the same two spectra.

The last two are the soundness check on the abstraction: the general scheme, specialized to the
Euclidean setting, reproduces objects that were formalized independently and long before it.

## Deviations from the article

The factor `(2π)^m` relating the two scalars is not a discrepancy. It is where the normalization
of the Fourier inversion formula sits: the article's coefficient function does not carry the
inversion density, so the density's constant part ends up in its `⦅σ,ρ⦆`, whereas here the ansatz
carries `κ` and the scalar is left as `fourierSlicePairing`. Both conventions give the same
network and the same reconstruction; see the module docstring of `FS.Scheme`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform

namespace LeanRidgelet

/-! ## The Euclidean instance -/

/-- With a one-point direction space, the identity as composite distance and unit weight, the
inversion integral of the abstract scheme is the plain inversion integral on `ℝ^m`. -/
theorem fs_inversionIntegral_euclidean (m : ℕ) (Ff : InputSpace m → ℂ) (κ : InputSpace m → ℝ)
    (x : InputSpace m) :
    inversionIntegral (volume : Measure (InputSpace m)) (Measure.dirac ())
        (fun ξ (_ : Unit) => Ff ξ) κ (fun (y : InputSpace m) (_ : Unit) => y)
        (fun _ _ => (1 : ℂ)) x
      = ∫ ξ : InputSpace m, Ff ξ * ((κ ξ : ℝ) : ℂ) * fourierSlicePhase (inner ℝ ξ x) := by
  rw [inversionIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [integral_dirac, mul_one]

/-- The scale space of the Euclidean instance has dimension `m`, so the Jacobian exponent of
Step 2 is `m`. -/
theorem fs_finrank_inputSpace (m : ℕ) : Module.finrank ℝ (InputSpace m) = m :=
  finrank_euclideanSpace_fin

/-- **The reconstruction formula for the fully-connected network on `ℝ^m`**, as the instance of
the abstract scheme with a one-point direction space. The only hypothesis is the Fourier inversion
formula on `ℝ^m` in the article's convention, carried by the inversion density `κ`. -/
theorem fs_reconstruction_euclidean (m : ℕ) (Fσ Fρ : ℝ → ℂ) (Ff : InputSpace m → ℂ)
    (κ : InputSpace m → ℝ) (f : InputSpace m → ℂ)
    (hinv : ∀ x : InputSpace m,
      (∫ ξ : InputSpace m, Ff ξ * ((κ ξ : ℝ) : ℂ) * fourierSlicePhase (inner ℝ ξ x)) = f x)
    (x : InputSpace m) :
    fourierExpressionSynthesis (volume : Measure (InputSpace m)) (Measure.dirac ()) Fσ
        (separationOfVariables (fun ξ (_ : Unit) => Ff ξ) κ Fρ)
        (fun (y : InputSpace m) (_ : Unit) => y) (fun _ _ => (1 : ℂ)) x
      = fourierSlicePairing (m : ℝ) Fσ Fρ * f x := by
  have hinv' : ∀ y : InputSpace m,
      inversionIntegral (volume : Measure (InputSpace m)) (Measure.dirac ())
        (fun ξ (_ : Unit) => Ff ξ) κ (fun (y : InputSpace m) (_ : Unit) => y)
        (fun _ _ => (1 : ℂ)) y = f y := fun y => by
    rw [fs_inversionIntegral_euclidean]; exact hinv y
  have := fs_reconstruction_of_inversion (volume : Measure (InputSpace m)) (Measure.dirac ())
    Fσ Fρ (fun ξ (_ : Unit) => Ff ξ) κ (fun (y : InputSpace m) (_ : Unit) => y)
    (fun _ _ => (1 : ℂ)) f hinv' x
  rwa [fs_finrank_inputSpace] at this

/-! ## The polar instance -/

open Metric in
/-- **The same Euclidean network, parametrized in polar coordinates.** Writing the weight as
`a = λ u` with `u` on the unit sphere turns the instance above, whose scale space is `ℝ^m` and
whose direction space is a point, into one whose scale space is `ℝ` and whose direction space is
the sphere. The inversion integral is the same, so both are instances of the scheme for the same
domain and the same target.

The Jacobian exponent is therefore `m` in one and `1` in the other: **the rank of the scheme is a
property of the parametrization of the weight, not of the input domain.** The `r = 1` shape is the
one the symmetric-space case takes, with the sphere in the role of the boundary `∂X`.

The inversion density carries the factor `2⁻¹` of the two-sided polar formula, which is the double
cover `(λ, u) ↦ λ u` of `ℝ^m ∖ {0}`. Both hypotheses are the absolute convergence the article
assumes in Section 2. -/
theorem fs_inversionIntegral_polar (m : ℕ) [Nontrivial (InputSpace m)] (Ff : InputSpace m → ℂ)
    (kappa : ℝ) (x : InputSpace m)
    (hF : Integrable (fun ξ : InputSpace m =>
      Ff ξ * ((kappa : ℝ) : ℂ) * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hprod : Integrable (fun p : ℝ × sphere (0 : InputSpace m) 1 =>
        (|p.1| ^ (Module.finrank ℝ (InputSpace m) - 1) : ℝ) •
          (Ff (p.1 • (p.2 : InputSpace m)) * ((kappa : ℝ) : ℂ) *
            fourierSlicePhase (inner ℝ (p.1 • (p.2 : InputSpace m)) x)))
      ((volume : Measure ℝ).prod (volume : Measure (InputSpace m)).toSphere)) :
    inversionIntegral (volume : Measure ℝ)
        ((volume : Measure (InputSpace m)).toSphere)
        (fun lam (u : sphere (0 : InputSpace m) 1) => Ff (lam • (u : InputSpace m)))
        (fun lam => 2⁻¹ * kappa * |lam| ^ (Module.finrank ℝ (InputSpace m) - 1))
        (fun (y : InputSpace m) (u : sphere (0 : InputSpace m) 1) => inner ℝ (u : InputSpace m) y)
        (fun _ _ => (1 : ℂ)) x
      = ∫ ξ : InputSpace m, Ff ξ * ((kappa : ℝ) : ℂ) * fourierSlicePhase (inner ℝ ξ x) := by
  set d : ℕ := Module.finrank ℝ (InputSpace m) with hd
  have hphase : ∀ (lam : ℝ) (u : sphere (0 : InputSpace m) 1),
      inner ℝ lam (inner ℝ (u : InputSpace m) x)
        = inner ℝ (lam • (u : InputSpace m)) x := by
    intro lam u
    rw [real_inner_smul_left]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hstep : ∀ lam : ℝ,
      (∫ u : sphere (0 : InputSpace m) 1,
          Ff (lam • (u : InputSpace m)) * ((2⁻¹ * kappa * |lam| ^ (d - 1) : ℝ) : ℂ) *
            fourierSlicePhase (inner ℝ lam (inner ℝ (u : InputSpace m) x)) * 1
          ∂(volume : Measure (InputSpace m)).toSphere)
        = ((2⁻¹ : ℝ) : ℂ) * ∫ u : sphere (0 : InputSpace m) 1,
            (|lam| ^ (d - 1) : ℝ) • (Ff (lam • (u : InputSpace m)) * ((kappa : ℝ) : ℂ) *
              fourierSlicePhase (inner ℝ (lam • (u : InputSpace m)) x))
            ∂(volume : Measure (InputSpace m)).toSphere := by
    intro lam
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hphase lam u, Complex.real_smul]
    push_cast
    ring
  have htwo := integral_eq_integral_toSphere_integral_two_sided
    (volume : Measure (InputSpace m)) hF
  rw [inversionIntegral, integral_congr_ae (Filter.Eventually.of_forall hstep),
    integral_const_mul, integral_integral_swap hprod,
    ← htwo, Complex.real_smul]
  push_cast
  rw [← mul_assoc]
  norm_num

/-! ## Agreement with the L1 development -/

/-- **The ansatz is the L1 Fourier expression.** The bias spectrum of the classical ridgelet
transform at homogeneity index `s = 0`, computed in `L1.FourierExpression` as `eq:fstridge`, is
exactly the separation-of-variables form the abstract scheme prescribes: the Fourier data of the
target evaluated at `ζ a`, against the conjugate ridgelet spectrum.

Nothing about the abstract scheme was used to prove the L1 identity, which predates it; this is
the check that the two agree. -/
theorem fs_separationOfVariables_euclideanRidgeletTransform (m : ℕ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ} (hf : Integrable f volume) (hψ : Integrable ψ volume)
    (a : InputSpace m) (ζ : ℝ) :
    angularFourier1D (fun b => euclideanRidgeletTransform m 0 ψ f (a, b)) ζ
      = separationOfVariables (fun ξ (_ : Unit) => Fourier.angularFourierIntegralInner f ξ)
          (fun _ => 1) (angularFourier1D ψ) a () ζ := by
  rw [angularFourier1D_euclideanRidgeletTransform m 0 hf hψ a ζ]
  simp only [separationOfVariables, Real.rpow_zero]
  push_cast
  ring

/-- **The two scalars agree.** The L1 admissibility constant `K_{ψ,η}` is `(2π)^m` times the
Fourier slice pairing of the activation spectrum against the ridgelet spectrum.

The factor is where the normalization of the Fourier inversion formula sits: the article's
coefficient function does not carry the inversion density `κ = (2π)^{-m}`, so its constant part
ends up in the article's `⦅σ,ρ⦆`, whereas the ansatz of the abstract scheme carries it. The
hypothesis `1 ≤ m` is only needed because `admissibilityConstant` writes the exponent as the
truncated subtraction `m - 1`. -/
theorem fs_admissibilityConstant_eq_fourierSlicePairing (m : ℕ) (hm : 1 ≤ m) (ψ Fη : ℝ → ℂ) :
    admissibilityConstant m ψ Fη
      = (2 * (Real.pi : ℂ)) ^ m * fourierSlicePairing (m : ℝ) Fη (angularFourier1D ψ) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := Fourier.two_mul_pi_complex_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ m = (2 * (Real.pi : ℂ)) ^ (m - 1) * (2 * (Real.pi : ℂ)) := by
    conv_lhs => rw [show m = (m - 1) + 1 from (Nat.succ_pred_eq_of_pos hm).symm]
    rw [pow_succ]
  have hint : (∫ ζ in {(0 : ℝ)}ᶜ, conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      = ∫ ω in {(0 : ℝ)}ᶜ, Fη ω * conj (angularFourier1D ψ ω) /
          ((|ω| ^ (m : ℝ) : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Real.rpow_natCast]
    ring
  rw [admissibilityConstant, fourierSlicePairing, hint, hpow]
  field_simp

/-! ## Fourier inversion in the article's convention

The hypothesis of the abstract reconstruction theorem is an inversion formula on the input domain.
On a Euclidean input domain it is not a hypothesis but a theorem, and this is it: Mathlib's
inversion formula transported to the article's angular convention. The constant `(2π)^r` produced
by the transport is the reciprocal of the inversion density `κ = (2π)^{-r}` that the Euclidean
instance above carries, so the two cancel.
-/

/-- The two conventions have the same integrable Fourier transforms: they differ by the rescaling
`ξ ↦ (2π)⁻¹ ξ`, which preserves integrability. -/
theorem fs_integrable_angularFourier_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : V → ℂ) :
    Integrable (Fourier.angularFourierIntegralInner f) volume ↔ Integrable (𝓕 f) volume := by
  have h : Fourier.angularFourierIntegralInner f
      = fun ξ : V => 𝓕 f ((2 * Real.pi)⁻¹ • ξ) := by
    funext ξ
    rw [Fourier.angularFourierIntegralInner_eq_mathlib]
    rfl
  rw [h]
  exact integrable_comp_smul_iff volume (𝓕 f) (inv_ne_zero Fourier.two_mul_pi_ne_zero)

/-- **Fourier inversion in the article's angular convention** on a finite-dimensional real inner
product space: the inversion integral of the angular Fourier transform returns `(2π)^r` times the
function, `r` the dimension of the space.

This is Mathlib's `MeasureTheory.Integrable.fourierInv_fourier_eq` after the change of variables
`ξ ↦ (2π) ξ` that passes between the two conventions; the constant is the Jacobian `(2π)^r` of that
rescaling. Together with the inversion density `κ = (2π)^{-r}` it discharges the hypothesis of
`LeanRidgelet.fs_reconstruction_euclidean`. -/
theorem fs_angularFourier_inversion_inner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf : Integrable f volume) (hFf : Integrable (𝓕 f) volume) {x : V}
    (hx : ContinuousAt f x) :
    (∫ ξ : V, Fourier.angularFourierIntegralInner f ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ Module.finrank ℝ V : ℝ) : ℂ) * f x := by
  set r : ℕ := Module.finrank ℝ V with hr
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcv := Measure.integral_comp_smul (volume : Measure V)
    (fun η : V => 𝓕 f η * fourierSlicePhase (inner ℝ ((2 * Real.pi) • η) x))
    (2 * Real.pi)⁻¹
  have hlhs : (∫ ξ : V, Fourier.angularFourierIntegralInner f ξ *
        fourierSlicePhase (inner ℝ ξ x))
      = ∫ η : V, 𝓕 f ((2 * Real.pi)⁻¹ • η) *
          fourierSlicePhase (inner ℝ ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • η)) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Fourier.angularFourierIntegralInner_eq_mathlib, smul_smul,
      mul_inv_cancel₀ Fourier.two_mul_pi_ne_zero, one_smul]
    rfl
  have hjac : |(((2 * Real.pi)⁻¹ : ℝ) ^ r)⁻¹| = ((2 * Real.pi) ^ r : ℝ) := by
    rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]
  have hinv : (∫ η : V, 𝓕 f η * fourierSlicePhase (inner ℝ ((2 * Real.pi) • η) x)) = f x := by
    rw [← hf.fourierInv_fourier_eq hFf hx, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [real_inner_smul_left, smul_eq_mul, fourierSlicePhase, mul_comm Complex.I]
    ring
  rw [hlhs, hcv, hjac, hinv, Complex.real_smul]

/-- The inversion integrand is integrable as soon as the Fourier transform is: the plane wave is
unimodular. -/
theorem fs_integrable_angularFourier_mul_phase {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hFf : Integrable (𝓕 f) volume) (x : V) :
    Integrable (fun ξ : V =>
      Fourier.angularFourierIntegralInner f ξ * fourierSlicePhase (inner ℝ ξ x)) volume := by
  have hcont : Continuous (fun ξ : V => fourierSlicePhase (inner ℝ ξ x)) := by
    unfold fourierSlicePhase
    fun_prop
  exact ((fs_integrable_angularFourier_iff f).mpr hFf).mul_unimodular
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by simp)

/-- Fourier inversion in the article's angular convention on `ℝ^m`, with the dimension read off the
index type. -/
theorem fs_angularFourier_inversion_inputSpace {m : ℕ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hFf : Integrable (𝓕 f) volume) {x : InputSpace m}
    (hx : ContinuousAt f x) :
    (∫ ξ : InputSpace m, Fourier.angularFourierIntegralInner f ξ *
        fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x := by
  rw [fs_angularFourier_inversion_inner hf hFf hx, fs_finrank_inputSpace]

/-! ## Step 1 over `ℝ`: the bias identity

The analytic input of `LeanRidgelet.fs_fourierExpression_of_bias` is one-dimensional. Here it is,
for an integrable activation: the bias integral of the network at a fixed weight and direction is
the inverse transform of the product of the two spectra. Everything is the convolution theorem
followed by Fourier inversion, transported from the Mathlib `2π` convention to the article's
angular one, and the factor `(2π)⁻¹` of the Fourier expression is exactly the Jacobian of that
transport.
-/

/-- Fourier inversion in the article's angular convention, almost everywhere. -/
theorem fs_angularFourier_inversion_ae {h : ℝ → ℂ} (hh : Integrable h volume)
    (hFh : Integrable (𝓕 h) volume) :
    ∀ᵐ t : ℝ, h t
      = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ ω : ℝ, angularFourier1D h ω * fourierSlicePhase (ω * t) := by
  filter_upwards [hh.fourierInv_fourier_ae_eq hFh] with t ht
  have hcv : (∫ ω : ℝ, angularFourier1D h ω * fourierSlicePhase (ω * t))
      = (2 * Real.pi) • ∫ ξ : ℝ, 𝓕 h ξ * fourierSlicePhase (2 * Real.pi * ξ * t) := by
    have := Measure.integral_comp_smul (volume : Measure ℝ)
      (fun ξ : ℝ => 𝓕 h ξ * fourierSlicePhase (2 * Real.pi * ξ * t)) (2 * Real.pi)⁻¹
    rw [Module.finrank_self, pow_one] at this
    rw [show (∫ ω : ℝ, angularFourier1D h ω * fourierSlicePhase (ω * t))
        = ∫ ω : ℝ, 𝓕 h ((2 * Real.pi)⁻¹ • ω) *
            fourierSlicePhase (2 * Real.pi * ((2 * Real.pi)⁻¹ • ω) * t) from
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp only [angularFourier1D_eq_mathlib, smul_eq_mul]
        congr 2
        field_simp), this]
    rw [abs_inv, abs_inv, inv_inv, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [← ht, Real.fourierInv_eq, hcv]
  have hpt : ∀ ξ : ℝ, 𝓕 h ξ * fourierSlicePhase (2 * Real.pi * ξ * t)
      = (Real.fourierChar (t * ξ) : ℂ) • 𝓕 h ξ := by
    intro ξ
    rw [smul_eq_mul, Real.fourierChar_apply, fourierSlicePhase, mul_comm]
    congr 2
    push_cast
    ring
  simp only [hpt]
  rw [Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ Fourier.two_mul_pi_complex_ne_zero, one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp [Circle.smul_def, smul_eq_mul, RCLike.inner_apply, conj_trivial]

/-- The convolution theorem in the article's angular convention: rescaling the frequency does not
disturb it. -/
theorem fs_angularFourier1D_convolution {γ σ : ℝ → ℂ} (hγ : Integrable γ volume)
    (hσ : Integrable σ volume) (ζ : ℝ) :
    angularFourier1D (γ ⋆[ContinuousLinearMap.mul ℂ ℂ] σ) ζ
      = angularFourier1D γ ζ * angularFourier1D σ ζ := by
  simp only [angularFourier1D_eq_mathlib]
  exact Real.fourier_mul_convolution_eq hγ hσ _

/-- **Step 1 over `ℝ`, the one-dimensional bias identity.** For an integrable coefficient function
and an integrable activation, the bias integral of the network at a fixed weight and direction is
the inverse transform of the product of the two spectra. This is the hypothesis `hbias` of
`LeanRidgelet.fs_fourierExpression_of_bias`, discharged for integrable activations; the finite
field case discharges the corresponding statement there.

The conclusion holds almost everywhere, which is what Fourier inversion gives without a continuity
hypothesis. The factor `(2π)⁻¹` is the Jacobian of the passage from the Mathlib convention to the
article's angular one. -/
theorem fs_bias_fourierExpression_ae {γ σ : ℝ → ℂ} (hγ : Integrable γ volume)
    (hσ : Integrable σ volume)
    (hprod : Integrable (𝓕 (γ ⋆[ContinuousLinearMap.mul ℂ ℂ] σ)) volume) :
    ∀ᵐ t : ℝ, (∫ b : ℝ, γ b * σ (t - b))
      = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ ω : ℝ, angularFourier1D γ ω * angularFourier1D σ ω * fourierSlicePhase (ω * t) := by
  have hconv : Integrable (γ ⋆[ContinuousLinearMap.mul ℂ ℂ] σ) volume :=
    hγ.integrable_convolution _ hσ
  filter_upwards [fs_angularFourier_inversion_ae hconv hprod] with t ht
  have hval : (γ ⋆[ContinuousLinearMap.mul ℂ ℂ] σ) t = ∫ b : ℝ, γ b * σ (t - b) := by
    rw [convolution]
    simp
  rw [← hval, ht]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
    simp only [fs_angularFourier1D_convolution hγ hσ ω])


/-! ## The Fourier formula of Irie--Funahashi

Section 7 of the article quotes two results that predate the ridgelet transform. The Radon formula
of Carroll--Dickinson and Ito is `fs_radon_reconstruction_codim_one`, an instance of the
codimension-one master identity. The other is the Fourier formula of Irie and Funahashi, which is
this section: it is the Fourier slice method with the bias frequency pinned at `1` rather than
integrated over, so it needs no admissibility condition at all — only that the activation have
nonzero spectrum there.
-/

/-- **The Fourier formula of Irie and Funahashi**, quoted in Section 7 of the article:
`f(x) = ((2π)^m σ♯(1))^{-1} ∫_{ℝ^m×ℝ} f̂(a) σ(a·x - b) e^{ib} da db`.

The statement is the iterated integral, and is multiplied out so that no division appears and no
hypothesis `σ♯(1) ≠ 0` is needed. The only hypothesis is Fourier inversion at the point, the same
one the abstract scheme asks for. There is no Fubini exchange and no absolute-convergence
assumption: at a fixed weight the bias integral is `∫ σ(a·x - b)e^{ib} db = e^{i a·x} σ♯(1)` by the
substitution `b ↦ a·x - b`, which leaves the weight integral to Fourier inversion. Nor is there an
admissibility condition on `σ`, which is the difference from every other reconstruction formula
here: the bias frequency is pinned rather than integrated, so there is no `|ω|^{-m}` to make
integrable. -/
theorem fs_fourierFormula_irieFunahashi (m : ℕ) (σ : ℝ → ℂ) (Ff f : InputSpace m → ℂ)
    (x : InputSpace m)
    (hinv : (∫ a : InputSpace m, Ff a * fourierSlicePhase (inner ℝ a x))
      = (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x) :
    (∫ a : InputSpace m, ∫ b : ℝ,
        Ff a * σ (inner ℝ a x - b) * fourierSlicePhase b)
      = Fourier.angularFourierIntegralInner σ 1 * (((2 * Real.pi) ^ m : ℝ) : ℂ) * f x := by
  have hbias : ∀ a : InputSpace m,
      (∫ b : ℝ, Ff a * σ (inner ℝ a x - b) * fourierSlicePhase b)
        = (Ff a * fourierSlicePhase (inner ℝ a x)) *
            Fourier.angularFourierIntegralInner σ 1 := by
    intro a
    have hsub : (∫ b : ℝ, Ff a * σ (inner ℝ a x - b) * fourierSlicePhase b)
        = ∫ u : ℝ, Ff a * σ u * fourierSlicePhase (inner ℝ a x - u) := by
      simpa using integral_sub_left_eq_self
        (fun u : ℝ => Ff a * σ u * fourierSlicePhase (inner ℝ a x - u))
        (volume : Measure ℝ) (inner ℝ a x)
    rw [hsub, Fourier.angularFourierIntegralInner, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hphase : fourierSlicePhase (inner ℝ a x - u)
        = fourierSlicePhase (inner ℝ a x) * Complex.exp (-Complex.I * (u : ℂ)) := by
      rw [fourierSlicePhase, fourierSlicePhase, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hphase, RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hbias), integral_mul_const, hinv]
  ring

end LeanRidgelet
