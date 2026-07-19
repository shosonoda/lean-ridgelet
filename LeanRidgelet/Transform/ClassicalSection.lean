/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Transform.FourierDilation

/-!
# The preactivation shear and the classical section integral

For a fixed input `x`, the involution `(a, z) ↦ (a, ⟨a,x⟩ - z)` of parameter space exchanges the
bias variable with the preactivation value.  This file proves that it preserves Lebesgue measure
and uses it to study the classical section integral

`φ_x(z) = ∫ γ(a, ⟨a,x⟩ - z) da`,

which represents the paper Fourier transform of the Fourier--dilation core `T_pt[γ](x, ·)`:
`φ_x = (2π)^{m-1} (T_pt[γ](x,·))♯`.  This identity is the 1D Fourier-inversion step in the
manuscript's proof that the Hilbert-space synthesis operator agrees with the classical network
integral (Theorem `thm:bdd.S`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace LeanRidgelet

open LeanRidgelet.Fourier

/-! ### The preactivation shear -/

/-- The preactivation shear `(a, z) ↦ (a, ⟨a,x⟩ - z)` as a linear map. -/
def preactivationShearLinear {m : ℕ} (x : InputSpace m) :
    (InputSpace m × ℝ) →ₗ[ℝ] InputSpace m × ℝ :=
  (LinearMap.fst ℝ (InputSpace m) ℝ).prod
    (((innerₗ (InputSpace m)).flip x ∘ₗ LinearMap.fst ℝ (InputSpace m) ℝ) -
      LinearMap.snd ℝ (InputSpace m) ℝ)

@[simp]
theorem preactivationShearLinear_apply {m : ℕ} (x : InputSpace m)
    (p : InputSpace m × ℝ) :
    preactivationShearLinear x p = (p.1, inner ℝ p.1 x - p.2) := rfl

theorem involutive_preactivationShearLinear {m : ℕ} (x : InputSpace m) :
    Function.Involutive (preactivationShearLinear x) := by
  intro p
  simp

/-- The preactivation shear as a continuous linear equivalence; it is an involution. -/
def preactivationShear {m : ℕ} (x : InputSpace m) :
    (InputSpace m × ℝ) ≃L[ℝ] InputSpace m × ℝ :=
  (LinearEquiv.ofInvolutive (preactivationShearLinear x)
    (involutive_preactivationShearLinear x)).toContinuousLinearEquiv

@[simp]
theorem preactivationShear_apply {m : ℕ} (x : InputSpace m) (p : InputSpace m × ℝ) :
    preactivationShear x p = (p.1, inner ℝ p.1 x - p.2) := rfl

/-- The preactivation shear preserves Lebesgue measure: it is the identity on the input factor
and a measure-preserving reflection on each bias fiber. -/
theorem measurePreserving_preactivationShear {m : ℕ} (x : InputSpace m) :
    MeasurePreserving (fun p : InputSpace m × ℝ ↦ (p.1, inner ℝ p.1 x - p.2))
      volume volume := by
  rw [Measure.volume_eq_prod]
  have hgm : Measurable (Function.uncurry
      fun (a : InputSpace m) (z : ℝ) ↦ inner ℝ a x - z) := by
    have hcont : Continuous fun p : InputSpace m × ℝ ↦ inner ℝ p.1 x - p.2 := by
      fun_prop
    exact hcont.measurable
  have hfiber : ∀ᵐ a ∂(volume : Measure (InputSpace m)),
      Measure.map (fun z : ℝ ↦ inner ℝ a x - z) volume = volume := by
    filter_upwards with a
    exact (Measure.measurePreserving_sub_left volume (inner ℝ a x)).map_eq
  exact MeasurePreserving.skew_product (f := id)
    (g := fun (a : InputSpace m) (z : ℝ) ↦ inner ℝ a x - z)
    (MeasurePreserving.id (volume : Measure (InputSpace m))) hgm hfiber

/-- Transport of integrals along the preactivation shear. -/
theorem integral_comp_preactivationShear {m : ℕ} (x : InputSpace m)
    (F : InputSpace m × ℝ → ℂ) :
    (∫ p : InputSpace m × ℝ, F (p.1, inner ℝ p.1 x - p.2)) = ∫ p, F p :=
  (measurePreserving_preactivationShear x).integral_comp
    (preactivationShear x).toHomeomorph.measurableEmbedding F

/-- Transport of integrability along the preactivation shear. -/
theorem integrable_comp_preactivationShear {m : ℕ} (x : InputSpace m)
    {F : InputSpace m × ℝ → ℂ} (hF : Integrable F) :
    Integrable (fun p : InputSpace m × ℝ ↦ F (p.1, inner ℝ p.1 x - p.2)) := by
  have h := ((measurePreserving_preactivationShear x).integrable_comp_emb
    (preactivationShear x).toHomeomorph.measurableEmbedding).2 hF
  exact h

/-- The parameter distribution composed with the preactivation shear, as a Schwartz function. -/
def shearedParameterSchwartz {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (x : InputSpace m) : SchwartzMap (InputSpace m × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (preactivationShear x) γ

@[simp]
theorem shearedParameterSchwartz_apply {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (x : InputSpace m) (p : InputSpace m × ℝ) :
    shearedParameterSchwartz γ x p = γ (p.1, inner ℝ p.1 x - p.2) := rfl

/-! ### The classical section integral -/

/-- The classical section integral `φ_x(z) = ∫ γ(a, ⟨a,x⟩ - z) da`. -/
def shearedParameterIntegral {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (x : InputSpace m) (z : ℝ) : ℂ :=
  ∫ a : InputSpace m, γ (a, inner ℝ a x - z)

/-- A bias-uniform integrable majorant for a parameter Schwartz function. -/
theorem exists_norm_le_one_add_norm_fst {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : InputSpace m) (z : ℝ),
      ‖γ (a, z)‖ ≤ C * (1 + ‖a‖) ^ (-((m : ℝ) + 1)) := by
  refine ⟨2 ^ (m + 1) * (Finset.Iic ((m + 1 : ℕ), (0 : ℕ))).sup
    (fun mn ↦ SchwartzMap.seminorm ℝ mn.1 mn.2) γ, by positivity, ?_⟩
  intro a z
  have hbound := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := ((m + 1 : ℕ), (0 : ℕ))) le_rfl le_rfl γ (a, z)
  rw [norm_iteratedFDeriv_zero] at hbound
  have hbase : (0 : ℝ) < 1 + ‖a‖ := by positivity
  have hchain : ‖γ (a, z)‖ * (1 + ‖a‖) ^ (m + 1) ≤
      2 ^ (m + 1) * (Finset.Iic ((m + 1 : ℕ), (0 : ℕ))).sup
        (fun mn ↦ SchwartzMap.seminorm ℝ mn.1 mn.2) γ := by
    calc
      ‖γ (a, z)‖ * (1 + ‖a‖) ^ (m + 1) ≤
          ‖γ (a, z)‖ * (1 + ‖(a, z)‖) ^ (m + 1) := by
        gcongr
        exact norm_fst_le (a, z)
      _ = (1 + ‖(a, z)‖) ^ (m + 1) * ‖γ (a, z)‖ := mul_comm _ _
      _ ≤ _ := hbound
  have hpow : (1 + ‖a‖) ^ (-((m : ℝ) + 1)) = ((1 + ‖a‖) ^ (m + 1))⁻¹ := by
    rw [show -((m : ℝ) + 1) = -(((m + 1 : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_neg hbase.le, Real.rpow_natCast]
  rw [hpow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr hchain

/-- The bias-uniform Schwartz majorant is integrable on the input space. -/
theorem integrable_const_mul_one_add_norm_input {m : ℕ} (C : ℝ) :
    Integrable (fun a : InputSpace m ↦ C * (1 + ‖a‖) ^ (-((m : ℝ) + 1))) := by
  have hfin : ((Module.finrank ℝ (InputSpace m) : ℝ)) < (m : ℝ) + 1 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hint := integrable_one_add_norm (E := InputSpace m) (μ := volume)
    (r := (m : ℝ) + 1) hfin
  exact hint.const_mul C

/-- Each bias slice of the sheared parameter distribution is integrable in the input. -/
theorem integrable_shearedParameterIntegral_slice {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (z : ℝ) :
    Integrable (fun a : InputSpace m ↦ γ (a, inner ℝ a x - z)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_one_add_norm_fst (shearedParameterSchwartz γ x)
  have hmajor := integrable_const_mul_one_add_norm_input (m := m) C
  apply hmajor.mono
  · have hcont : Continuous fun a : InputSpace m ↦ γ (a, inner ℝ a x - z) := by
      apply γ.continuous.comp
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with a
    have hval := hC a z
    rw [shearedParameterSchwartz_apply] at hval
    calc
      ‖γ (a, inner ℝ a x - z)‖ ≤ C * (1 + ‖a‖) ^ (-((m : ℝ) + 1)) := hval
      _ ≤ ‖C * (1 + ‖a‖) ^ (-((m : ℝ) + 1))‖ := le_abs_self _

/-- The sheared Schwartz function is integrable on parameter space. -/
theorem integrable_shearedParameterSchwartz {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) :
    Integrable (fun p : InputSpace m × ℝ ↦ γ (p.1, inner ℝ p.1 x - p.2)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (InputSpace m × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hint := (shearedParameterSchwartz γ x).integrable (μ := volume)
  refine hint.congr ?_
  filter_upwards with p
  rw [shearedParameterSchwartz_apply]

/-- The classical section integral is integrable in the bias variable. -/
theorem integrable_shearedParameterIntegral {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) :
    Integrable (shearedParameterIntegral γ x) := by
  have hint := integrable_shearedParameterSchwartz γ x
  rw [Measure.volume_eq_prod] at hint
  exact hint.integral_prod_right

/-- The classical section integral is continuous in the bias variable. -/
theorem continuous_shearedParameterIntegral {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) :
    Continuous (shearedParameterIntegral γ x) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_one_add_norm_fst (shearedParameterSchwartz γ x)
  have hmajor := integrable_const_mul_one_add_norm_input (m := m) C
  apply continuousAt_of_dominated
  · filter_upwards with z
    have hcont : Continuous fun a : InputSpace m ↦ γ (a, inner ℝ a x - z) := by
      apply γ.continuous.comp
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with z
    filter_upwards with a
    have hval := hC a z
    rw [shearedParameterSchwartz_apply] at hval
    exact hval
  · exact hmajor
  · filter_upwards with a
    have hcont : Continuous fun z : ℝ ↦ γ (a, inner ℝ a x - z) := by
      apply γ.continuous.comp
      fun_prop
    exact hcont.continuousAt

/-- The paper inverse Fourier transform of the classical section integral is the
Fourier--dilation core: the manuscript identity `φ_x = (2π)^{m-1} (T_pt[γ](x,·))♯` before
inversion. -/
theorem inverse_paperFourier_shearedParameterIntegral {m : ℕ} [NeZero m]
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ z : ℝ, shearedParameterIntegral γ x z * Complex.exp (Complex.I * (z * ω)) =
      (2 * Real.pi : ℂ) ^ (m - 1) * fourierDilationTransformCore γ x ω := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (InputSpace m × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  set H : InputSpace m × ℝ → ℂ :=
    fun p ↦ γ (p.1, inner ℝ p.1 x - p.2) * Complex.exp (Complex.I * (p.2 * ω)) with hH_def
  have hH : Integrable H := by
    rw [hH_def]
    have hkernel : AEStronglyMeasurable (fun p : InputSpace m × ℝ ↦
        Complex.exp (Complex.I * ((p.2 : ℂ) * (ω : ℂ)))) volume := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    have hbound : ∀ᵐ p : InputSpace m × ℝ ∂volume,
        ‖Complex.exp (Complex.I * ((p.2 : ℂ) * (ω : ℂ)))‖ ≤ 1 := by
      filter_upwards with p
      rw [Complex.norm_exp]
      simp
    exact (integrable_shearedParameterSchwartz γ x).mul_unimodular hkernel hbound
  have hstep1 : (∫ z : ℝ, shearedParameterIntegral γ x z *
      Complex.exp (Complex.I * (z * ω))) = ∫ z : ℝ, ∫ a : InputSpace m, H (a, z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [shearedParameterIntegral, ← integral_mul_const]
  have hstep2 : (∫ z : ℝ, ∫ a : InputSpace m, H (a, z)) = ∫ p, H p := by
    rw [Measure.volume_eq_prod] at hH ⊢
    exact (integral_prod_symm H hH).symm
  have hstep3 : (∫ p, H p) =
      ∫ p : InputSpace m × ℝ, γ p * fourierDilationKernel x ω p := by
    calc
      (∫ p, H p) = ∫ p : InputSpace m × ℝ,
          γ (p.1, inner ℝ p.1 x - p.2) *
            fourierDilationKernel x ω (p.1, inner ℝ p.1 x - p.2) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [hH_def]
        have hker : fourierDilationKernel x ω (p.1, inner ℝ p.1 x - p.2) =
            Complex.exp (Complex.I * ((p.2 : ℂ) * (ω : ℂ))) := by
          unfold fourierDilationKernel
          congr 1
          push_cast
          ring
        rw [hker]
      _ = ∫ p : InputSpace m × ℝ, γ p * fourierDilationKernel x ω p :=
        integral_comp_preactivationShear x
          (fun q : InputSpace m × ℝ ↦ γ q * fourierDilationKernel x ω q)
  have hcore : (∫ p : InputSpace m × ℝ, γ p * fourierDilationKernel x ω p) =
      (2 * Real.pi : ℂ) ^ m * fourierDilationTransformCore γ x ω := by
    rw [fourierDilationTransformCore, ← mul_assoc, mul_inv_cancel₀
      (pow_ne_zero m two_mul_pi_complex_ne_zero), one_mul]
  rw [hstep1, hstep2, hstep3, hcore, ← mul_assoc]
  congr 1
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := two_mul_pi_complex_ne_zero
  have hm : m = (m - 1) + 1 := (Nat.succ_pred_eq_of_pos (NeZero.pos m)).symm
  rw [hm, pow_succ, show (m - 1 + 1) - 1 = m - 1 by omega]
  rw [show (2 * (Real.pi : ℂ))⁻¹ * ((2 * (Real.pi : ℂ)) ^ (m - 1) * (2 * (Real.pi : ℂ))) =
      ((2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ)) ^ (m - 1) by
    ring]
  rw [inv_mul_cancel₀ hπ, one_mul]

/-- The kernel identity `φ_x(z) = (2π)^{m-1} (T_pt[γ](x,·))♯(z)`: the classical section
integral is the paper Fourier transform of the Fourier--dilation coefficient vector. -/
theorem shearedParameterIntegral_eq_paperFourierSchwartz {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (z : ℝ) :
    shearedParameterIntegral γ x z =
      (2 * Real.pi : ℂ) ^ (m - 1) *
        paperFourierSchwartz
          (FiberCore.toSchwartz (fourierDilationTransformFiberCore s t γ x)) z := by
  have hg : Integrable (fun ω : ℝ ↦
      (2 * Real.pi : ℂ) ^ (m - 1) * fourierDilationTransformCore γ x ω) := by
    have hint := (FiberCore.toSchwartz
      (fourierDilationTransformFiberCore s t γ x)).integrable (μ := volume)
    refine (hint.const_mul ((2 * Real.pi : ℂ) ^ (m - 1))).congr ?_
    filter_upwards with ω
    rw [fourierDilationTransformFiberCore_apply]
  have hmain := paperFourier_inversion_of_integrable
    (continuous_shearedParameterIntegral γ x)
    (integrable_shearedParameterIntegral γ x) hg
    (fun ω ↦ inverse_paperFourier_shearedParameterIntegral γ x ω) z
  rw [hmain, paperFourierSchwartz_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  rw [fourierDilationTransformFiberCore_apply,
    show -Complex.I * ((z : ℂ) * (ω : ℂ)) = -Complex.I * ((ω : ℂ) * (z : ℂ)) by ring]
  ring

end LeanRidgelet
