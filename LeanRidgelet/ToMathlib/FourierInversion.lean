/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Almost-everywhere Fourier inversion

Mathlib's Fourier inversion theorem (`MeasureTheory.Integrable.fourierInv_fourier_eq`) recovers
an integrable function with integrable Fourier transform at its continuity points. This file
provides the almost-everywhere counterpart with no continuity hypothesis:

* `MeasureTheory.Integrable.fourierInv_fourier_ae_eq`: for `f` integrable with `𝓕 f`
  integrable, `𝓕⁻ (𝓕 f) = f` almost everywhere.

The proof pairs both sides against Schwartz functions — a Fubini swap computes the pairing of
`𝓕⁻ (𝓕 f)` against `φ` as the pairing of `𝓕 f` against `𝓕⁻ φ`, the multiplication formula
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`) moves the transform back to `f`, and
the Schwartz inversion `𝓕 (𝓕⁻ φ) = φ` closes the circle — and concludes with
`MeasureTheory.ae_eq_of_integral_contDiff_smul_eq`. Candidate for upstreaming to Mathlib.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped RealInnerProductSpace SchwartzMap

namespace MeasureTheory

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem innerₗ_flip_eq' : (innerₗ V).flip = innerₗ V := by
  ext x y
  simp only [LinearMap.flip_apply, innerₗ_apply_apply]
  exact real_inner_comm x y

/-- **Almost-everywhere Fourier inversion**: if `f` is integrable and its Fourier transform is
integrable, then `𝓕⁻ (𝓕 f) = f` almost everywhere. -/
theorem Integrable.fourierInv_fourier_ae_eq {f : V → E}
    (hf : Integrable f volume) (h'f : Integrable (𝓕 f) volume) :
    𝓕⁻ (𝓕 f) =ᵐ[volume] f := by
  have hfhatc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hgc : Continuous (𝓕⁻ (𝓕 f)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) ?_
    exact h'f.comp_neg
  -- pairing against Schwartz functions
  have key : ∀ φ : 𝓢(V, ℂ), (∫ x, φ x • (𝓕⁻ (𝓕 f)) x) = ∫ x, φ x • f x := by
    intro φ
    set ψ : 𝓢(V, ℂ) := 𝓕⁻ φ with hψ_def
    have hψcoe : ⇑ψ = 𝓕⁻ ⇑φ := by
      rw [hψ_def, SchwartzMap.fourierInv_coe]
    have hφψ : 𝓕 ⇑ψ = ⇑φ := by
      rw [hψ_def, ← SchwartzMap.fourier_coe]
      exact congrArg DFunLike.coe (FourierTransform.fourier_fourierInv_eq φ)
    -- the doubly-integrable oscillatory kernel
    have hker : Integrable (Function.uncurry fun (x : V) (w : V) =>
        (φ x * Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) • (𝓕 f) w)
        ((volume : Measure V).prod volume) := by
      have hdom : Integrable (fun p : V × V => ‖φ p.1‖ * ‖(𝓕 f) p.2‖)
          ((volume : Measure V).prod volume) :=
        φ.integrable.norm.mul_prod h'f.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        refine Continuous.smul ?_ (hfhatc.comp continuous_snd)
        refine Continuous.mul (φ.continuous.comp continuous_fst) ?_
        refine Complex.continuous_exp.comp ?_
        refine Continuous.mul ?_ continuous_const
        refine Complex.continuous_ofReal.comp ?_
        exact continuous_const.mul (Continuous.inner continuous_snd continuous_fst)
      · simp only [Function.uncurry]
        rw [norm_smul, norm_mul, Complex.norm_exp]
        have hre : ((((2 * Real.pi * ⟪p.2, p.1⟫ : ℝ) : ℂ)) * Complex.I).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.exp_zero, mul_one]
    calc (∫ x, φ x • (𝓕⁻ (𝓕 f)) x)
        = ∫ x, ∫ w,
            (φ x * Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) •
              (𝓕 f) w := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only []
          rw [Real.fourierInv_eq' (𝓕 f) x]
          calc φ x • ∫ v, Complex.exp (((2 * Real.pi * ⟪v, x⟫ : ℝ) : ℂ) * Complex.I) •
                (𝓕 f) v
              = ∫ v, φ x • (Complex.exp (((2 * Real.pi * ⟪v, x⟫ : ℝ) : ℂ) * Complex.I) •
                  (𝓕 f) v) :=
                (MeasureTheory.integral_smul _ _).symm
            _ = ∫ w, (φ x * Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) •
                  (𝓕 f) w := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
                simp only []
                rw [smul_smul]
      _ = ∫ w, ∫ x,
            (φ x * Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) •
              (𝓕 f) w :=
          integral_integral_swap hker
      _ = ∫ w, ⇑ψ w • (𝓕 f) w := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only []
          calc (∫ x, (φ x *
                Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) • (𝓕 f) w)
              = (∫ x, φ x *
                  Complex.exp (((2 * Real.pi * ⟪w, x⟫ : ℝ) : ℂ) * Complex.I)) •
                  (𝓕 f) w :=
                integral_smul_const _ _
            _ = ⇑ψ w • (𝓕 f) w := by
                congr 1
                rw [hψcoe, Real.fourierInv_eq']
                refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
                simp only []
                rw [smul_eq_mul, real_inner_comm, mul_comm]
      _ = ∫ x, (𝓕 ⇑ψ) x • f x := by
          have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
            (e := Real.fourierChar) (L := innerₗ V) (μ := volume) (ν := volume)
            Real.continuous_fourierChar (by exact continuous_inner) ψ.integrable hf
          rw [innerₗ_flip_eq'] at h
          exact h.symm
      _ = ∫ x, φ x • f x := by
          rw [hφψ]
  -- conclude by testing against smooth compactly supported functions
  refine ae_eq_of_integral_contDiff_smul_eq hgc.locallyIntegrable hf.locallyIntegrable
    fun r r_diff r_supp => ?_
  have hr₁ : HasCompactSupport (Complex.ofRealCLM ∘ r) := r_supp.comp_left rfl
  have hr₂ := Complex.ofRealCLM.contDiff.comp r_diff
  have hpair := key (hr₁.toSchwartzMap hr₂)
  have hval : ∀ (v : V → E) (x : V),
      (hr₁.toSchwartzMap hr₂) x • v x = r x • v x := fun v x => by
    change ((r x : ℝ) : ℂ) • v x = r x • v x
    simp
  calc ∫ x, r x • (𝓕⁻ (𝓕 f)) x
      = ∫ x, (hr₁.toSchwartzMap hr₂) x • (𝓕⁻ (𝓕 f)) x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          (hval (𝓕⁻ (𝓕 f)) x).symm)
    _ = ∫ x, (hr₁.toSchwartzMap hr₂) x • f x := hpair
    _ = ∫ x, r x • f x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hval f x)

end MeasureTheory
