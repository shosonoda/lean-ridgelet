/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Unimodular multiplication on `Lp`

A measurable complex-valued function of norm one acts unitarily on every normed `Lp` space by
pointwise multiplication.  This file bundles that elementary fact as a linear isometric
equivalence.  In particular, it supplies the phase-multiplication part of induced and
Fourier-side group representations without adding a project-specific assumption object.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {p : ℝ≥0∞} {μ : Measure X}

/-- Pointwise multiplication by an a.e. unimodular measurable function preserves `MemLp`. -/
theorem MemLp.unimodular_mul (u : X → ℂ) (hu : AEStronglyMeasurable u μ)
    (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1) (f : Lp ℂ p μ) :
    MemLp (fun x ↦ u x * f x) p μ := by
  have hmeasurable : AEStronglyMeasurable (fun x ↦ u x * f x) μ :=
    hu.mul (Lp.aestronglyMeasurable f)
  apply (Lp.memLp f).congr_norm hmeasurable
  filter_upwards [hunimodular] with x hx
  simp only [norm_mul, hx, one_mul]

/-- Pointwise multiplication by an a.e. unimodular measurable function, as an `Lp` linear
isometry. -/
noncomputable def unimodularMultiplierLinearIsometry (u : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    [Fact (1 ≤ p)] : Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p μ where
  toFun f := (MemLp.unimodular_mul u hu hunimodular f).toLp _
  map_add' f g := by
    let hsum := MemLp.unimodular_mul u hu hunimodular (f + g)
    let hf := MemLp.unimodular_mul u hu hunimodular f
    let hg := MemLp.unimodular_mul u hu hunimodular g
    change hsum.toLp _ = hf.toLp _ + hg.toLp _
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx]
    simpa only [Pi.add_apply] using mul_add (u x) (f x) (g x)
  map_smul' c f := by
    let hcf := MemLp.unimodular_mul u hu hunimodular (c • f)
    let hf := MemLp.unimodular_mul u hu hunimodular f
    change hcf.toLp _ = c • hf.toLp _
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    let hf := MemLp.unimodular_mul u hu hunimodular f
    change ‖hf.toLp _‖ = ‖f‖
    calc
      ‖hf.toLp _‖ = ENNReal.toReal (eLpNorm (fun x ↦ u x * f x) p μ) :=
        Lp.norm_toLp _ hf
      _ = ENNReal.toReal (eLpNorm (fun x ↦ f x) p μ) := by
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_norm_ae
        filter_upwards [hunimodular] with x hx
        simp only [norm_mul, hx, one_mul]
      _ = ‖f‖ := (Lp.norm_def f).symm

/-- The `Lp` isometry given by an a.e. unimodular multiplier has the expected pointwise
representative. -/
theorem unimodularMultiplierLinearIsometry_apply_ae (u : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    [Fact (1 ≤ p)] (f : Lp ℂ p μ) :
    unimodularMultiplierLinearIsometry u hu hunimodular f =ᵐ[μ] fun x ↦ u x * f x :=
  MemLp.coeFn_toLp (MemLp.unimodular_mul u hu hunimodular f)

/-- Pointwise multiplication by an a.e. unimodular measurable function is onto: conjugating the
multiplier gives an explicit preimage. -/
theorem unimodularMultiplierLinearIsometry_surjective (u : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    [Fact (1 ≤ p)] : Function.Surjective
      (unimodularMultiplierLinearIsometry u hu hunimodular : Lp ℂ p μ → Lp ℂ p μ) := by
  have hconj_measurable : AEStronglyMeasurable (fun x ↦ star (u x)) μ :=
    continuous_star.comp_aestronglyMeasurable hu
  have hconj_unimodular : ∀ᵐ x ∂μ, ‖star (u x)‖ = 1 := by
    filter_upwards [hunimodular] with x hx
    simpa only [norm_star] using hx
  intro f
  refine ⟨unimodularMultiplierLinearIsometry (fun x ↦ star (u x)) hconj_measurable
    hconj_unimodular f, ?_⟩
  apply Lp.ext
  have houter := unimodularMultiplierLinearIsometry_apply_ae u hu hunimodular
    (unimodularMultiplierLinearIsometry (fun x ↦ star (u x)) hconj_measurable
      hconj_unimodular f)
  have hinner := unimodularMultiplierLinearIsometry_apply_ae (fun x ↦ star (u x))
    hconj_measurable hconj_unimodular f
  filter_upwards [hunimodular, houter, hinner] with x hx houterx hinnerx
  rw [houterx, hinnerx, ← mul_assoc]
  simp only [Complex.star_def]
  rw [Complex.mul_conj', hx]
  norm_num

/-- Pointwise multiplication by an a.e. unimodular measurable function, as a linear isometric
equivalence of `Lp`. -/
noncomputable def unimodularMultiplierLinearIsometryEquiv (u : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    [Fact (1 ≤ p)] : Lp ℂ p μ ≃ₗᵢ[ℂ] Lp ℂ p μ :=
  LinearIsometryEquiv.ofSurjective (unimodularMultiplierLinearIsometry u hu hunimodular)
    (unimodularMultiplierLinearIsometry_surjective u hu hunimodular)

/-- The bundled unimodular multiplier has the expected pointwise representative. -/
theorem unimodularMultiplierLinearIsometryEquiv_apply_ae (u : X → ℂ)
    (hu : AEStronglyMeasurable u μ) (hunimodular : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    [Fact (1 ≤ p)] (f : Lp ℂ p μ) :
    unimodularMultiplierLinearIsometryEquiv u hu hunimodular f =ᵐ[μ] fun x ↦ u x * f x :=
  unimodularMultiplierLinearIsometry_apply_ae u hu hunimodular f

end MeasureTheory
