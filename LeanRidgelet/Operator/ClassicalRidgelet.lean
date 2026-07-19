/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Operator.Ridgelet
public import LeanRidgelet.Space.RidgeletFunction

/-!
# Agreement of the Hilbert-space ridgelet transform with the classical integral

The manuscript defines the classical ridgelet transform on a test class by

`R[f;ρ](a,b) = ∫ f(x) conj(ρ(⟨a,x⟩ - b)) dx`

and its rigorous Hilbert-space version by `R[f;ρ] = T*[f ⊗ h_ρ]`.  In the transported
coordinate model, `T[R_h[f]]` is the tensor section `x ↦ f(x) • h`; this file proves that the
classical integral, with `ρ` the classical ridgelet function of spectrum `ρ♯ = |ω|^m conj h`,
equals the inverse-coordinate integral formula (13) evaluated on that tensor section.  Together
with `fourierDilationTransform_ridgeletOperator_apply_ae`, this identifies `ridgeletOperator`
with the classical ridgelet integral on Schwartz data.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace LeanRidgelet

open LeanRidgelet.Fourier

/-- The classical ridgelet function `ρ = 𝓕⁻¹_paper[ρ♯]` of a Schwartz coefficient vector,
with manuscript spectrum `ρ♯(ω) = |ω|^m conj h(ω)`. -/
def classicalRidgeletFunction (m : ℕ) (h : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∫ ω : ℝ, ridgeletSpectrumCoreFn m h ω * Complex.exp (Complex.I * (z * ω))

/-- The classical ridgelet transform `R[f;ρ](a,b) = ∫ f(x) conj(ρ(⟨a,x⟩-b)) dx`. -/
def classicalRidgeletIntegral {m : ℕ} (f : InputSpace m → ℂ) (ρ : ℝ → ℂ)
    (p : InputSpace m × ℝ) : ℂ :=
  ∫ x : InputSpace m, f x * conj (ρ (inner ℝ p.1 x - p.2))

/-- The manuscript ridgelet spectrum is integrable for Schwartz coefficient vectors. -/
theorem integrable_ridgeletSpectrumCoreFn (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    Integrable (ridgeletSpectrumCoreFn m h) := by
  apply (h.integrable_pow_mul volume m).mono
  · apply Continuous.aestronglyMeasurable
    unfold ridgeletSpectrumCoreFn
    fun_prop
  · filter_upwards with ω
    unfold ridgeletSpectrumCoreFn
    rw [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (abs_nonneg ω) m), Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ω) m) (norm_nonneg (h ω)))]
    simp [Real.norm_eq_abs]

/-- Conjugating the classical ridgelet function produces the forward-phase spectrum integral
against `|ω|^m h(ω)`. -/
theorem conj_classicalRidgeletFunction (m : ℕ) (h : SchwartzMap ℝ ℂ) (u : ℝ) :
    conj (classicalRidgeletFunction m h u) =
      (2 * Real.pi : ℂ)⁻¹ *
        ∫ ω : ℝ, ((|ω| ^ m : ℝ) : ℂ) * h ω * Complex.exp (-Complex.I * (u * ω)) := by
  unfold classicalRidgeletFunction
  rw [map_mul, ← integral_conj]
  rw [conj_two_mul_pi_inv]
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  rw [map_mul]
  congr 1
  · unfold ridgeletSpectrumCoreFn
    rw [map_mul]
    simp [Complex.conj_ofReal]
  · rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/--
**Agreement with the classical ridgelet integral** (manuscript Definition of `R[f;ρ]` and
Lemma `lem:fourier`, classical part).  For a Schwartz function `f` and a Schwartz coefficient
vector `h`, the classical ridgelet transform with respect to the classical ridgelet function of
spectrum `|ω|^m conj h` equals, at every parameter point, the inverse-coordinate integral
formula (13) applied to the tensor section `(x,ω) ↦ f(x) h(ω)` — the coordinate representative
of `T[R_h[f]]`.
-/
theorem classicalRidgeletIntegral_eq_inverseTensorIntegral {m : ℕ}
    (f : SchwartzMap (InputSpace m) ℂ) (h : SchwartzMap ℝ ℂ) (p : InputSpace m × ℝ) :
    classicalRidgeletIntegral (f : InputSpace m → ℂ) (classicalRidgeletFunction m h) p =
      (2 * Real.pi : ℂ)⁻¹ *
        ∫ z : InputSpace m × ℝ, f z.1 * h z.2 * inverseFourierDilationKernel p z := by
  set g : ℝ → ℂ := fun ω ↦ ((|ω| ^ m : ℝ) : ℂ) * h ω with hg_def
  have hg : Integrable g := by
    apply (integrable_ridgeletSpectrumCoreFn m h).mono
    · apply Continuous.aestronglyMeasurable
      rw [hg_def]
      fun_prop
    · filter_upwards with ω
      rw [hg_def]
      unfold ridgeletSpectrumCoreFn
      simp only [norm_mul, Complex.norm_conj]
      exact le_rfl
  have hprod : Integrable (fun z : InputSpace m × ℝ ↦ f z.1 * g z.2) := by
    rw [Measure.volume_eq_prod]
    exact MeasureTheory.Integrable.mul_prod (f.integrable (μ := volume)) hg
  have hjoint : Integrable (fun z : InputSpace m × ℝ ↦
      f z.1 * g z.2 * Complex.exp (-Complex.I * ((z.2 : ℂ) *
        ((inner ℝ p.1 z.1 - p.2 : ℝ) : ℂ)))) := by
    have hker_meas : AEStronglyMeasurable (fun z : InputSpace m × ℝ ↦
        Complex.exp (-Complex.I * ((z.2 : ℂ) *
          ((inner ℝ p.1 z.1 - p.2 : ℝ) : ℂ)))) volume := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    have hker_bd : ∀ᵐ z : InputSpace m × ℝ ∂volume,
        ‖Complex.exp (-Complex.I * ((z.2 : ℂ) *
          ((inner ℝ p.1 z.1 - p.2 : ℝ) : ℂ)))‖ ≤ 1 := by
      filter_upwards with z
      rw [Complex.norm_exp]
      simp
    exact hprod.mul_unimodular hker_meas hker_bd
  have hpoint : ∀ x : InputSpace m,
      f x * conj (classicalRidgeletFunction m h (inner ℝ p.1 x - p.2)) =
        (2 * Real.pi : ℂ)⁻¹ *
          ∫ ω : ℝ, f x * g ω * Complex.exp (-Complex.I * ((ω : ℂ) *
            ((inner ℝ p.1 x - p.2 : ℝ) : ℂ))) := by
    intro x
    rw [conj_classicalRidgeletFunction]
    rw [show f x * ((2 * Real.pi : ℂ)⁻¹ * ∫ ω : ℝ, ((|ω| ^ m : ℝ) : ℂ) * h ω *
        Complex.exp (-Complex.I * (((inner ℝ p.1 x - p.2 : ℝ) : ℂ) * (ω : ℂ)))) =
        (2 * Real.pi : ℂ)⁻¹ * (f x * ∫ ω : ℝ, ((|ω| ^ m : ℝ) : ℂ) * h ω *
          Complex.exp (-Complex.I * (((inner ℝ p.1 x - p.2 : ℝ) : ℂ) * (ω : ℂ)))) by ring]
    rw [← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    rw [hg_def]
    rw [show -Complex.I * (((inner ℝ p.1 x - p.2 : ℝ) : ℂ) * (ω : ℂ)) =
        -Complex.I * ((ω : ℂ) * ((inner ℝ p.1 x - p.2 : ℝ) : ℂ)) by ring]
    ring
  calc
    classicalRidgeletIntegral (f : InputSpace m → ℂ) (classicalRidgeletFunction m h) p =
        ∫ x : InputSpace m, (2 * Real.pi : ℂ)⁻¹ *
          ∫ ω : ℝ, f x * g ω * Complex.exp (-Complex.I * ((ω : ℂ) *
            ((inner ℝ p.1 x - p.2 : ℝ) : ℂ))) := by
      unfold classicalRidgeletIntegral
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (2 * Real.pi : ℂ)⁻¹ * ∫ x : InputSpace m,
          ∫ ω : ℝ, f x * g ω * Complex.exp (-Complex.I * ((ω : ℂ) *
            ((inner ℝ p.1 x - p.2 : ℝ) : ℂ))) := integral_const_mul _ _
    _ = (2 * Real.pi : ℂ)⁻¹ *
          ∫ z : InputSpace m × ℝ, f z.1 * g z.2 * Complex.exp (-Complex.I * ((z.2 : ℂ) *
            ((inner ℝ p.1 z.1 - p.2 : ℝ) : ℂ))) := by
      congr 1
      rw [Measure.volume_eq_prod] at hjoint ⊢
      exact (integral_prod _ hjoint).symm
    _ = (2 * Real.pi : ℂ)⁻¹ *
          ∫ z : InputSpace m × ℝ, f z.1 * h z.2 * inverseFourierDilationKernel p z := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [hg_def]
      unfold inverseFourierDilationKernel
      push_cast
      ring

/-- The classical ridgelet integral agrees with the inverse coordinate-transform formula (13)
on any Schwartz representative of the tensor section `(x,ω) ↦ f(x) h(ω)`. -/
theorem classicalRidgeletIntegral_eq_inverseFourierDilationTransformCore {m : ℕ}
    (f : SchwartzMap (InputSpace m) ℂ) (h : SchwartzMap ℝ ℂ)
    (u : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hu : ∀ z : InputSpace m × ℝ, u z = f z.1 * h z.2) (p : InputSpace m × ℝ) :
    classicalRidgeletIntegral (f : InputSpace m → ℂ) (classicalRidgeletFunction m h) p =
      inverseFourierDilationTransformCore u p := by
  rw [classicalRidgeletIntegral_eq_inverseTensorIntegral f h p,
    inverseFourierDilationTransformCore]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [hu z]

/-- The repository ridgelet distribution `ρ = 𝓕⁻¹_paper[ρ♯]` acts on test functions by
integration against the classical ridgelet function.  This identifies
`classicalRidgeletFunction` as the pointwise realization of `ridgeletFunctionCore`. -/
theorem ridgeletFunctionCore_apply_classical (m : ℕ) (h φ : SchwartzMap ℝ ℂ) :
    ridgeletFunctionCore m h φ =
      ∫ z : ℝ, φ z * classicalRidgeletFunction m h z := by
  unfold ridgeletFunctionCore paperFourierInvDistribution
  simp only [ContinuousLinearMap.comp_apply, FourierTransform.fourierInvCLM_apply]
  rw [TemperedDistribution.fourierInv_apply, temperedDistributionDilation_apply]
  unfold ridgeletSpectrumCore
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  have habs : ((|2 * Real.pi| : ℝ) : ℂ)⁻¹ = (2 * Real.pi : ℂ)⁻¹ := by
    rw [abs_of_pos (by positivity)]
    norm_cast
  rw [habs]
  have hψ : ∀ ω : ℝ,
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realDilationCLE (2 * Real.pi) two_mul_pi_ne_zero).symm (𝓕⁻ φ)) ω =
      ∫ z : ℝ, φ z * Complex.exp (Complex.I * (z * ω)) := by
    intro ω
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    change (𝓕⁻ φ) ((realDilationCLE (2 * Real.pi) two_mul_pi_ne_zero).symm ω) = _
    rw [realDilationCLE_symm_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with z
    rw [Circle.smul_def, Real.fourierChar_apply]
    have hreal : 2 * Real.pi * inner ℝ z ((2 * Real.pi)⁻¹ * ω) = z * ω := by
      simp only [RCLike.inner_apply, conj_trivial]
      field_simp
      try ring
    rw [show ((2 * Real.pi * inner ℝ z ((2 * Real.pi)⁻¹ * ω) : ℝ) : ℂ) * Complex.I =
        Complex.I * ((z : ℂ) * (ω : ℂ)) by
      rw [hreal]
      push_cast
      ring]
    rw [smul_eq_mul, mul_comm]
  have hswap : (∫ ω : ℝ, (∫ z : ℝ, φ z * Complex.exp (Complex.I * (z * ω))) *
      ridgeletSpectrumCoreL2 m h ω) =
      ∫ z : ℝ, φ z * (∫ ω : ℝ, ridgeletSpectrumCoreFn m h ω *
        Complex.exp (Complex.I * (z * ω))) := by
    have hjoint : Integrable (fun q : ℝ × ℝ ↦
        φ q.1 * ridgeletSpectrumCoreFn m h q.2 *
          Complex.exp (Complex.I * ((q.1 : ℂ) * (q.2 : ℂ)))) (volume.prod volume) := by
      have hprod : Integrable (fun q : ℝ × ℝ ↦
          φ q.1 * ridgeletSpectrumCoreFn m h q.2) (volume.prod volume) :=
        MeasureTheory.Integrable.mul_prod (φ.integrable (μ := volume))
          (integrable_ridgeletSpectrumCoreFn m h)
      have hker_meas : AEStronglyMeasurable (fun q : ℝ × ℝ ↦
          Complex.exp (Complex.I * ((q.1 : ℂ) * (q.2 : ℂ)))) (volume.prod volume) := by
        apply Continuous.aestronglyMeasurable
        fun_prop
      have hker_bd : ∀ᵐ q : ℝ × ℝ ∂(volume.prod volume),
          ‖Complex.exp (Complex.I * ((q.1 : ℂ) * (q.2 : ℂ)))‖ ≤ 1 := by
        filter_upwards with q
        rw [Complex.norm_exp]
        simp
      exact hprod.mul_unimodular hker_meas hker_bd
    calc
      (∫ ω : ℝ, (∫ z : ℝ, φ z * Complex.exp (Complex.I * (z * ω))) *
          ridgeletSpectrumCoreL2 m h ω) =
          ∫ ω : ℝ, ∫ z : ℝ, φ z * ridgeletSpectrumCoreFn m h ω *
            Complex.exp (Complex.I * ((z : ℂ) * (ω : ℂ))) := by
        apply integral_congr_ae
        have hcoe := (memLp_ridgeletSpectrumCoreFn m h).coeFn_toLp
        filter_upwards [hcoe] with ω hω
        rw [show (ridgeletSpectrumCoreL2 m h : ℝ → ℂ) ω =
            ridgeletSpectrumCoreFn m h ω from hω]
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = ∫ z : ℝ, ∫ ω : ℝ, φ z * ridgeletSpectrumCoreFn m h ω *
            Complex.exp (Complex.I * ((z : ℂ) * (ω : ℂ))) := by
        apply integral_integral_swap
        exact hjoint.swap
      _ = ∫ z : ℝ, φ z * (∫ ω : ℝ, ridgeletSpectrumCoreFn m h ω *
            Complex.exp (Complex.I * ((z : ℂ) * (ω : ℂ)))) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        ring
  calc
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ ω : ℝ, (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realDilationCLE (2 * Real.pi) two_mul_pi_ne_zero).symm (𝓕⁻ φ)) ω *
          ridgeletSpectrumCoreL2 m h ω =
        (2 * Real.pi : ℂ)⁻¹ *
          ∫ ω : ℝ, (∫ z : ℝ, φ z * Complex.exp (Complex.I * (z * ω))) *
            ridgeletSpectrumCoreL2 m h ω := by
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      rw [hψ ω]
    _ = (2 * Real.pi : ℂ)⁻¹ * ∫ z : ℝ, φ z * (∫ ω : ℝ, ridgeletSpectrumCoreFn m h ω *
          Complex.exp (Complex.I * (z * ω))) := by rw [hswap]
    _ = ∫ z : ℝ, φ z * classicalRidgeletFunction m h z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      unfold classicalRidgeletFunction
      ring

/-- The tensor section `(x, ω) ↦ f(x) h(ω)` in the inverse-transform integral is the
coordinate representative of the Hilbert-space ridgelet transform: the unitary coordinate of
`ridgeletOperator` at input `x` is the fiber class of the Schwartz function `f x • h`. -/
theorem fourierDilationTransform_ridgeletOperator_toLp_apply_ae
    (m : ℕ) [NeZero m] (s t : ℝ) (h : FiberCore m s t)
    (f : SchwartzMap (InputSpace m) ℂ) :
    (fourierDilationTransform m s t
        (ridgeletOperator m s t (h : FiberSpace m s t) (f.toLp 2 volume)) :
      InputSpace m → FiberSpace m s t) =ᵐ[volume]
      fun x ↦ ((f x • h : FiberCore m s t) : FiberSpace m s t) := by
  filter_upwards [fourierDilationTransform_ridgeletOperator_apply_ae m s t
    (h : FiberSpace m s t) (f.toLp 2 volume), f.coeFn_toLp 2 volume] with x h1 h2
  rw [h1]
  rw [show (f.toLp 2 volume : InputSpace m → ℂ) x = f x from h2]
  exact (UniformSpace.Completion.coe_smul (f x) h).symm

end LeanRidgelet
