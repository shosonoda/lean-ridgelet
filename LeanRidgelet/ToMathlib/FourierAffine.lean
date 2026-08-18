/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.AffineHaar
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier covariance under affine changes of variables

This file proves the finite-dimensional change-of-variables formulas which underlie the
Fourier-side Mackey description of affine quasi-regular representations. The results are
independent of ridgelet transforms and are intended as Mathlib upstream candidates.

For an invertible linear map `L`, pullback by `L⁻¹` transforms as

`𝓕(f ∘ L⁻¹)(ξ) = |det L| 𝓕f(Lᵀξ)`.

Adding a translation contributes the usual character. The last theorem includes the square-root
Jacobian weight appearing in the unitary `L²` action.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform InnerProductSpace NNReal RealInnerProductSpace

namespace MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Bochner integration after pullback by the inverse of an invertible real linear map. The
statement is unconditional: if either side is non-integrable then both Bochner integrals use the
usual zero convention. -/
theorem integral_comp_linearEquiv_symm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : V ≃ₗ[ℝ] V) (f : V → F) :
    ∫ x, f (L.symm x) =
      (‖LinearMap.det (L : V →ₗ[ℝ] V)‖₊ : ℝ) • ∫ x, f x := by
  let e : V ≃ᵐ V := L.symm.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hmap := integral_map_equiv (μ := volume) e f
  change (∫ x, f x ∂Measure.map (L.symm : V →ₗ[ℝ] V) volume) =
    ∫ x, f (L.symm x) at hmap
  rw [← hmap]
  change ∫ x, f x ∂Measure.map (L.symm : V →ₗ[ℝ] V) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.symm.isUnit_det'.ne_zero,
    integral_smul_measure]
  congr 1
  simp [LinearEquiv.det_coe_symm, ENNReal.toReal_ofReal]

/-- Fourier transform of pullback by the inverse of an invertible real linear map. -/
theorem fourier_comp_linearEquiv_symm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (L : V ≃ₗ[ℝ] V) (f : V → F) (xi : V) :
    𝓕 (fun x => f (L.symm x)) xi =
      (‖LinearMap.det (L : V →ₗ[ℝ] V)‖₊ : ℝ) • 𝓕 f (L.adjoint xi) := by
  rw [Real.fourier_eq]
  let h : V → F := fun y => Real.fourierChar (-⟪L y, xi⟫_ℝ) • f y
  have hfun : (fun x => Real.fourierChar (-⟪x, xi⟫_ℝ) • f (L.symm x)) =
      fun x => h (L.symm x) := by
    funext x
    simp only [h, L.apply_symm_apply]
  rw [hfun]
  have hchange := integral_comp_linearEquiv_symm (F := F) L h
  calc
    ∫ x, h (L.symm x) =
        (‖LinearMap.det (L : V →ₗ[ℝ] V)‖₊ : ℝ) • ∫ x, h x := hchange
    _ = (‖LinearMap.det (L : V →ₗ[ℝ] V)‖₊ : ℝ) • 𝓕 f (L.adjoint xi) := by
      congr 1
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with y
      simp only [h]
      rw [show -⟪L y, xi⟫_ℝ = -⟪y, L.adjoint xi⟫_ℝ from
        congrArg Neg.neg (LinearMap.adjoint_inner_right (L : V →ₗ[ℝ] V) y xi).symm]

/-- Fourier transform converts translation of the argument into multiplication by a character. -/
theorem fourier_comp_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : V → F) (b xi : V) :
    𝓕 (fun x => f (x - b)) xi = Real.fourierChar (-⟪b, xi⟫_ℝ) • 𝓕 f xi := by
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V)
      (fun x => f (x - b)) xi =
    Real.fourierChar (-⟪b, xi⟫_ℝ) •
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V) f xi
  have h := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ V) f (-b)
  have hxi := congrFun h xi
  have hfun : (fun x => f (x - b)) = f ∘ fun v => v + (-b) := by
    funext x
    simp only [Function.comp_apply, sub_eq_add_neg]
  rw [hfun]
  simpa only [innerₗ_apply_apply, inner_neg_left] using hxi

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The inverse of an affine equivalence is its inverse linear part applied after subtracting the
translation vector. -/
theorem affineEquiv_symm_apply (g : V ≃ᵃ[ℝ] V) (x : V) :
    g.symm x = g.linear.symm (x - g 0) := by
  apply g.linear.injective
  rw [g.linear.apply_symm_apply]
  apply (eq_sub_iff_add_eq).2
  rw [← show g (g.symm x) = g.linear (g.symm x) + g 0 from
    congrFun g.toAffineMap.decomp (g.symm x)]
  exact g.apply_symm_apply x

/-- Fourier transform of pullback by the inverse of an affine equivalence. -/
theorem fourier_comp_affineEquiv_symm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (g : V ≃ᵃ[ℝ] V) (f : V → F) (xi : V) :
    𝓕 (fun x => f (g.symm x)) xi =
      Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
        ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊ : ℝ) •
          𝓕 f (g.linear.adjoint xi)) := by
  rw [show (fun x => f (g.symm x)) =
      fun x => f (g.linear.symm (x - g 0)) by
    funext x
    rw [affineEquiv_symm_apply]]
  rw [fourier_comp_sub (fun y => f (g.linear.symm y)) (g 0) xi,
    fourier_comp_linearEquiv_symm]

/-- Fourier covariance of the determinant-weighted affine pullback used in the unitary `L²`
representation. The Jacobian factor on the Fourier side is the square root rather than its
inverse. -/
theorem fourier_weighted_comp_affineEquiv_symm (g : V ≃ᵃ[ℝ] V)
    (f : V → ℂ) (xi : V) :
    𝓕 (fun x => ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) •
        f (g.symm x)) xi =
      Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
        ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ) •
          𝓕 f (g.linear.adjoint xi)) := by
  rw [show (fun x => ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) •
      f (g.symm x)) =
      ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) •
        (fun x => f (g.symm x)) by rfl]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V)
      (((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) •
        (fun x => f (g.symm x))) xi = _
  rw [VectorFourier.fourierIntegral_const_smul]
  change ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) •
      𝓕 (fun x => f (g.symm x)) xi = _
  rw [fourier_comp_affineEquiv_symm]
  change ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ)⁻¹) *
      (Real.fourierChar (-⟪g 0, xi⟫_ℝ) *
        ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊ : ℝ) *
          𝓕 f (g.linear.adjoint xi))) =
      Real.fourierChar (-⟪g 0, xi⟫_ℝ) *
        ((‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊.sqrt : ℂ) *
          𝓕 f (g.linear.adjoint xi))
  let a : ℝ≥0 := ‖LinearMap.det (g.linear : V →ₗ[ℝ] V)‖₊
  have ha : a ≠ 0 := by
    simpa only [a, ne_eq, nnnorm_eq_zero] using g.linear.isUnit_det'.ne_zero
  have hasqrt : ((a.sqrt : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero]
    exact ha
  have hsquare : ((a : ℝ) : ℂ) = ((a.sqrt : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast (show a = a.sqrt ^ 2 from a.sq_sqrt.symm)
  change ((a.sqrt : ℂ)⁻¹) * (Real.fourierChar (-⟪g 0, xi⟫_ℝ) *
      ((a : ℝ) * 𝓕 f (g.linear.adjoint xi))) =
    Real.fourierChar (-⟪g 0, xi⟫_ℝ) *
      ((a.sqrt : ℂ) * 𝓕 f (g.linear.adjoint xi))
  rw [hsquare]
  field_simp

end MeasureTheory
