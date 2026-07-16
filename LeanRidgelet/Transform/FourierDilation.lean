/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Fourier.Convention
public import LeanRidgelet.Space.Parameter
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier--dilation transform

This file introduces the test-function formulas for the Fourier--dilation coordinate transform
from Section 2.2 of the L2 manuscript. The change-of-variables and extension arguments are stated
as named theorems so that later operator theory can use their final interfaces while the measure-
theoretic proofs are completed separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform InnerProductSpace RealInnerProductSpace SchwartzMap

namespace LeanRidgelet

open LeanRidgelet.Fourier

/-- Equation (12): the unitary Fourier--dilation transform in the transported coordinate model. -/
def fourierDilationTransform (m : ℕ) [NeZero m] (s t : ℝ) :
    ParameterSpace m s t ≃ₗᵢ[ℂ]
      BochnerL2 (InputSpace m) (FiberSpace m s t) volume :=
  parameterCoordinateEquiv m s t

/-- Equation (13) at the Hilbert-space level; the test-function integral formula is given below. -/
def inverseFourierDilationTransform (m : ℕ) [NeZero m] (s t : ℝ) :
    BochnerL2 (InputSpace m) (FiberSpace m s t) volume ≃ₗᵢ[ℂ]
      ParameterSpace m s t :=
  (fourierDilationTransform m s t).symm

@[simp]
theorem inverseFourierDilationTransform_apply_fourierDilationTransform
    (m : ℕ) [NeZero m] (s t : ℝ) (γ : ParameterSpace m s t) :
    inverseFourierDilationTransform m s t (fourierDilationTransform m s t γ) = γ :=
  (fourierDilationTransform m s t).symm_apply_apply γ

/-- The dilation `Dω[x] = ωx` on the input space. -/
def frequencyDilation {m : ℕ} (ω : ℝ) (x : InputSpace m) : InputSpace m :=
  ω • x

/-- The pullback coordinate map `κ(x,ω) = (-Dω[x],ω)`. -/
def fourierDilationCoordinate {m : ℕ} (x : InputSpace m) (ω : ℝ) :
    InputSpace m × ℝ :=
  (-frequencyDilation ω x, ω)

/-- The oscillatory kernel `exp(iω(a·x-b))` of the Fourier--dilation transform. -/
def fourierDilationKernel {m : ℕ} (x : InputSpace m) (ω : ℝ)
    (p : InputSpace m × ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω * (inner ℝ p.1 x - p.2)))

/-- The Fourier--dilation transform on Schwartz parameter distributions, equation (10)'s
coordinate formula before Hilbert-space extension. -/
def fourierDilationTransformCore {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ m)⁻¹ *
    ∫ p : InputSpace m × ℝ, γ p * fourierDilationKernel x ω p

theorem integrable_fourierDilationTransformCore_integrand {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    Integrable (fun p : InputSpace m × ℝ ↦ γ p * fourierDilationKernel x ω p) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (InputSpace m × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hkernel : AEStronglyMeasurable (fourierDilationKernel x ω) :=
    (by unfold fourierDilationKernel; fun_prop :
      Continuous (fourierDilationKernel x ω)).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂volume, ‖fourierDilationKernel x ω p‖ ≤ 1 := by
    filter_upwards with p
    unfold fourierDilationKernel
    rw [Complex.norm_exp]
    simp
  simpa only [mul_comm] using γ.integrable.bdd_mul hkernel hbound

theorem fourierDilationTransformCore_add {m : ℕ}
    (γ η : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    fourierDilationTransformCore (γ + η) x ω =
      fourierDilationTransformCore γ x ω + fourierDilationTransformCore η x ω := by
  simp only [fourierDilationTransformCore, add_apply, add_mul,
    integral_add (integrable_fourierDilationTransformCore_integrand γ x ω)
      (integrable_fourierDilationTransformCore_integrand η x ω), mul_add]

theorem fourierDilationTransformCore_smul {m : ℕ} (c : ℂ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    fourierDilationTransformCore (c • γ) x ω =
      c * fourierDilationTransformCore γ x ω := by
  simp only [fourierDilationTransformCore, smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]
  ring

/-- The test-function Fourier--dilation transform as an unbundled linear map. -/
def fourierDilationTransformCoreLinearMap (m : ℕ) :
    SchwartzMap (InputSpace m × ℝ) ℂ →ₗ[ℂ] (InputSpace m × ℝ → ℂ) where
  toFun γ z := fourierDilationTransformCore γ z.1 z.2
  map_add' γ η := by
    funext z
    exact fourierDilationTransformCore_add γ η z.1 z.2
  map_smul' c γ := by
    funext z
    exact fourierDilationTransformCore_smul c γ z.1 z.2

/-- The parameter product equipped with its Euclidean `L²` product norm. -/
abbrev ParameterProductL2 (m : ℕ) := WithLp 2 (InputSpace m × ℝ)

/-- The canonical continuous linear equivalence from the Euclidean product model to the ordinary
product used by parameter Schwartz functions. -/
def parameterProductEquiv (m : ℕ) :
    ParameterProductL2 m ≃L[ℝ] InputSpace m × ℝ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (InputSpace m) ℝ

/-- Transport a parameter Schwartz function to the Euclidean product model. -/
def parameterSchwartzL2 {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    SchwartzMap (ParameterProductL2 m) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (parameterProductEquiv m) γ

@[simp]
theorem parameterSchwartzL2_apply {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (p : ParameterProductL2 m) :
    parameterSchwartzL2 γ p = γ (WithLp.ofLp p) := rfl

theorem integral_norm_sq_parameterSchwartzL2 {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    (∫ p : ParameterProductL2 m, ‖parameterSchwartzL2 γ p‖ ^ 2) =
      ∫ p : InputSpace m × ℝ, ‖γ p‖ ^ 2 := by
  simpa only [parameterSchwartzL2_apply] using
    (WithLp.volume_preserving_ofLp (InputSpace m) ℝ).integral_comp
      (parameterProductEquiv m).toHomeomorph.measurableEmbedding
      (fun p : InputSpace m × ℝ => ‖γ p‖ ^ 2)

/-- The Fourier frequency corresponding to the dilation coordinates `(x, ω)`. -/
def parameterFrequency {m : ℕ} (x : InputSpace m) (ω : ℝ) :
    ParameterProductL2 m :=
  WithLp.toLp 2 (fourierDilationCoordinate x ω)

theorem paperFourierIntegralInner_parameterFrequency {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    paperFourierIntegralInner (parameterSchwartzL2 γ) (parameterFrequency x ω) =
      ∫ p : InputSpace m × ℝ, γ p * fourierDilationKernel x ω p := by
  rw [← (WithLp.volume_preserving_ofLp (InputSpace m) ℝ).integral_comp
    (parameterProductEquiv m).toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with p
  simp only [parameterSchwartzL2_apply]
  unfold parameterFrequency fourierDilationCoordinate frequencyDilation fourierDilationKernel
  rw [WithLp.prod_inner_apply]
  rw [inner_neg_right, inner_smul_right, RCLike.inner_apply]
  simp only [conj_trivial, neg_mul]
  push_cast
  rw [mul_comm (Complex.exp _) (γ _)]
  congr 2
  ring

/-- Weighted dilation change of variables in integral form. This is the identity obtained by
pushing `|ω|^m dx dω` forward along `(x, ω) ↦ (-ωx, ω)`. It does not require global
injectivity: the exceptional fiber `ω = 0` is null, and the remaining fibers use Haar-measure
scaling. -/
theorem integral_fourierDilationCoordinate_mul {m : ℕ} [NeZero m]
    (f : InputSpace m × ℝ → ℝ) (hf : Integrable f)
    (hf_cont : Continuous f) (hf_nonneg : ∀ z, 0 ≤ f z) :
    (∫ z, f z) =
      ∫ z : InputSpace m × ℝ,
        f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m := by
  let g : InputSpace m × ℝ → ℝ := fun z =>
    f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m
  have hg_cont : Continuous g := by
    unfold g fourierDilationCoordinate frequencyDilation
    fun_prop
  have hsections : ∀ᵐ w : ℝ ∂volume,
      Integrable (fun x : InputSpace m => f (x, w)) := hf.prod_left_ae
  have hw_ne : ∀ᵐ w : ℝ ∂volume, w ≠ 0 := by
    rw [ae_iff]
    simp
  have hinner : ∀ᵐ w : ℝ ∂volume,
      (∫ x : InputSpace m, g (x, w)) = ∫ x : InputSpace m, f (x, w) := by
    filter_upwards [hsections, hw_ne] with w hfw hw
    unfold g fourierDilationCoordinate frequencyDilation
    dsimp only
    rw [integral_mul_const]
    have hscale :=
      Measure.integral_comp_smul volume (fun x : InputSpace m => f (x, w)) (-w)
    simp only [neg_smul, finrank_euclideanSpace_fin, smul_eq_mul] at hscale
    rw [hscale]
    have habs : |((-w) ^ m)⁻¹| * |w| ^ m = 1 := by
      rw [abs_inv, abs_pow, abs_neg]
      field_simp [abs_ne_zero.mpr hw]
    calc
      (|((-w) ^ m)⁻¹| * ∫ x : InputSpace m, f (x, w)) * |w| ^ m =
          (|((-w) ^ m)⁻¹| * |w| ^ m) * ∫ x : InputSpace m, f (x, w) := by ring
      _ = ∫ x : InputSpace m, f (x, w) := by rw [habs, one_mul]
  have hg_sections : ∀ᵐ w : ℝ ∂volume,
      Integrable (fun x : InputSpace m => g (x, w)) := by
    filter_upwards [hsections, hw_ne] with w hfw hw
    unfold g fourierDilationCoordinate frequencyDilation
    simpa only [neg_smul] using
      (hfw.comp_smul (neg_ne_zero.mpr hw)).mul_const (|w| ^ m)
  have hnorm_inner : ∀ᵐ w : ℝ ∂volume,
      (∫ x : InputSpace m, ‖g (x, w)‖) =
        ∫ x : InputSpace m, ‖f (x, w)‖ := by
    filter_upwards [hinner] with w hw
    calc
      (∫ x : InputSpace m, ‖g (x, w)‖) = ∫ x : InputSpace m, g (x, w) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        unfold g
        exact mul_nonneg (hf_nonneg _) (pow_nonneg (abs_nonneg _) _)
      _ = ∫ x : InputSpace m, f (x, w) := hw
      _ = ∫ x : InputSpace m, ‖f (x, w)‖ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
  have hg : Integrable g := by
    rw [Measure.volume_eq_prod]
    rw [integrable_prod_iff' hg_cont.aestronglyMeasurable]
    refine ⟨hg_sections, ?_⟩
    exact hf.integral_norm_prod_right.congr <|
      hnorm_inner.mono fun _ hw => hw.symm
  change (∫ z, f z) = ∫ z, g z
  rw [Measure.volume_eq_prod]
  rw [integral_prod_symm f hf, integral_prod_symm g hg]
  exact integral_congr_ae <| hinner.mono fun _ hw => hw.symm

theorem integrable_norm_sq_paperFourier_parameter {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    Integrable (fun z : InputSpace m × ℝ =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2) := by
  let ψ := parameterSchwartzL2 γ
  let h := 𝓕 ψ
  have hbase : Integrable (fun ξ : ParameterProductL2 m => ‖h ξ‖ ^ 2) := by
    have hint : Integrable h (volume : Measure (ParameterProductL2 m)) := h.integrable
    have hmul := hint.norm.bdd_mul h.continuous.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        simpa only [Real.norm_eq_abs, abs_norm] using SchwartzMap.norm_le_seminorm ℝ h ξ)
    simpa only [Real.norm_eq_abs, abs_norm, pow_two] using hmul
  have hc : (2 * Real.pi)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscale : Integrable (fun ξ : ParameterProductL2 m =>
      ‖h ((2 * Real.pi)⁻¹ • ξ)‖ ^ 2) := hbase.comp_smul hc
  have hcomp :=
    (WithLp.volume_preserving_toLp (InputSpace m) ℝ).integrable_comp_of_integrable hscale
  refine hcomp.congr ?_
  filter_upwards with z
  rw [paperFourierIntegralInner_eq_mathlib]
  rfl

theorem continuous_norm_sq_paperFourier_parameter {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    Continuous (fun z : InputSpace m × ℝ =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2) := by
  have hcont : Continuous (fun z : InputSpace m × ℝ =>
      ‖𝓕 (parameterSchwartzL2 γ)
        ((2 * Real.pi)⁻¹ • WithLp.toLp 2 z)‖ ^ 2) := by fun_prop
  convert hcont using 1
  ext z
  rw [paperFourierIntegralInner_eq_mathlib]
  rfl

theorem integral_norm_sq_paperFourier_parameter {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    (∫ z : InputSpace m × ℝ,
        ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2) =
      (2 * Real.pi) ^ (m + 1) * ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2 := by
  have hmap := (WithLp.volume_preserving_toLp (InputSpace m) ℝ).integral_comp
    (parameterProductEquiv m).symm.toHomeomorph.measurableEmbedding
    (fun ξ : ParameterProductL2 m =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ) ξ‖ ^ 2)
  calc
    _ = ∫ ξ : ParameterProductL2 m,
        ‖paperFourierIntegralInner (parameterSchwartzL2 γ) ξ‖ ^ 2 := hmap
    _ = (2 * Real.pi) ^ Module.finrank ℝ (ParameterProductL2 m) *
        ∫ ξ : ParameterProductL2 m, ‖parameterSchwartzL2 γ ξ‖ ^ 2 :=
      paper_plancherel_schwartz_inner (parameterSchwartzL2 γ)
    _ = (2 * Real.pi) ^ (m + 1) *
        ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2 := by
      rw [integral_norm_sq_parameterSchwartzL2]
      congr 2
      calc
        Module.finrank ℝ (ParameterProductL2 m) =
            Module.finrank ℝ (InputSpace m × ℝ) :=
          (WithLp.linearEquiv 2 ℝ (InputSpace m × ℝ)).finrank_eq
        _ = m + 1 := by
          rw [Module.finrank_prod, finrank_euclideanSpace_fin]
          simp

theorem integral_norm_sq_paperFourier_parameter_coordinate {m : ℕ} [NeZero m]
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    (∫ z : InputSpace m × ℝ,
        ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2) =
      ∫ z : InputSpace m × ℝ,
        ‖paperFourierIntegralInner (parameterSchwartzL2 γ)
          (parameterFrequency z.1 z.2)‖ ^ 2 * |z.2| ^ m := by
  exact integral_fourierDilationCoordinate_mul
    (fun z : InputSpace m × ℝ =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2)
    (integrable_norm_sq_paperFourier_parameter γ)
    (continuous_norm_sq_paperFourier_parameter γ) (fun _ => sq_nonneg _)

theorem fourierDilationTransformCore_eq_paperFourier {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    fourierDilationTransformCore γ x ω =
      ((2 * Real.pi : ℂ) ^ m)⁻¹ *
        paperFourierIntegralInner (parameterSchwartzL2 γ) (parameterFrequency x ω) := by
  rw [fourierDilationTransformCore,
    paperFourierIntegralInner_parameterFrequency]

theorem norm_sq_fourierDilationTransformCore_eq {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    ‖fourierDilationTransformCore γ x ω‖ ^ 2 =
      (((2 * Real.pi) ^ m)⁻¹) ^ 2 *
        ‖paperFourierIntegralInner (parameterSchwartzL2 γ)
          (parameterFrequency x ω)‖ ^ 2 := by
  rw [fourierDilationTransformCore_eq_paperFourier, norm_mul, norm_inv, norm_pow]
  have hpi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hpi]
  ring

/-- Equation (11): Plancherel plus the dilation Jacobian on the Schwartz core. -/
theorem fourierDilationTransformCore_norm_sq {m : ℕ} [NeZero m]
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    (∫ p : InputSpace m × ℝ, ‖γ p‖ ^ 2) =
      (2 * Real.pi) ^ (m - 1) *
        ∫ z : InputSpace m × ℝ,
          ‖fourierDilationTransformCore γ z.1 z.2‖ ^ 2 * |z.2| ^ m := by
  let A : ℝ := 2 * Real.pi
  let F : InputSpace m × ℝ → ℝ := fun z =>
    ‖paperFourierIntegralInner (parameterSchwartzL2 γ)
      (parameterFrequency z.1 z.2)‖ ^ 2 * |z.2| ^ m
  have hcoord := integral_norm_sq_paperFourier_parameter_coordinate γ
  have hplanch := integral_norm_sq_paperFourier_parameter γ
  have hF : (∫ z : InputSpace m × ℝ, F z) =
      A ^ (m + 1) * ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2 := by
    rw [← hplanch, hcoord]
  have hcoreint :
      (∫ z : InputSpace m × ℝ,
          ‖fourierDilationTransformCore γ z.1 z.2‖ ^ 2 * |z.2| ^ m) =
        (((A ^ m)⁻¹) ^ 2) * ∫ z : InputSpace m × ℝ, F z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_sq_fourierDilationTransformCore_eq]
    change ((((A ^ m)⁻¹) ^ 2 *
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ)
        (parameterFrequency z.1 z.2)‖ ^ 2) * |z.2| ^ m) =
      (((A ^ m)⁻¹) ^ 2) * F z
    unfold F
    ring
  change (∫ p : InputSpace m × ℝ, ‖γ p‖ ^ 2) =
    A ^ (m - 1) * ∫ z : InputSpace m × ℝ,
      ‖fourierDilationTransformCore γ z.1 z.2‖ ^ 2 * |z.2| ^ m
  rw [hcoreint, hF]
  have hA : A ≠ 0 := by
    unfold A
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hm : 0 < m := NeZero.pos m
  have hpow : A ^ (m - 1) * A ^ (m + 1) = (A ^ m) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  symm
  calc
    A ^ (m - 1) * ((A ^ m)⁻¹ ^ 2 *
        (A ^ (m + 1) * ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2)) =
      (A ^ (m - 1) * A ^ (m + 1) * (A ^ m)⁻¹ ^ 2) *
        ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2 := by ring
    _ = ∫ z : InputSpace m × ℝ, ‖γ z‖ ^ 2 := by
      rw [hpow]
      field_simp [hA]

/-- The kernel in the inverse coordinate formula (13). -/
def inverseFourierDilationKernel {m : ℕ} (p : InputSpace m × ℝ)
    (z : InputSpace m × ℝ) : ℂ :=
  Complex.exp (-Complex.I * (z.2 * (inner ℝ p.1 z.1 - p.2))) * |z.2| ^ m

/-- The inverse Fourier--dilation formula (13) on a Schwartz coordinate function. -/
def inverseFourierDilationTransformCore {m : ℕ}
    (q : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∫ z : InputSpace m × ℝ, q z * inverseFourierDilationKernel p z

theorem integrable_inverseFourierDilationTransformCore_integrand {m : ℕ}
    (q : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    Integrable (fun z : InputSpace m × ℝ ↦ q z * inverseFourierDilationKernel p z) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (InputSpace m × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  apply (q.integrable_pow_mul volume m).mono
  · apply Continuous.aestronglyMeasurable
    unfold inverseFourierDilationKernel
    fun_prop
  · filter_upwards with z
    have hkernel : ‖inverseFourierDilationKernel p z‖ = |z.2| ^ m := by
      unfold inverseFourierDilationKernel
      rw [norm_mul, Complex.norm_exp]
      simp
    rw [norm_mul, hkernel, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg z) m) (norm_nonneg (q z)))]
    rw [mul_comm]
    gcongr
    simpa only [Real.norm_eq_abs] using norm_snd_le z

theorem inverseFourierDilationTransformCore_add {m : ℕ}
    (q r : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    inverseFourierDilationTransformCore (q + r) p =
      inverseFourierDilationTransformCore q p + inverseFourierDilationTransformCore r p := by
  simp only [inverseFourierDilationTransformCore, add_apply, add_mul,
    integral_add (integrable_inverseFourierDilationTransformCore_integrand q p)
      (integrable_inverseFourierDilationTransformCore_integrand r p), mul_add]

theorem inverseFourierDilationTransformCore_smul {m : ℕ} (c : ℂ)
    (q : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    inverseFourierDilationTransformCore (c • q) p =
      c * inverseFourierDilationTransformCore q p := by
  simp only [inverseFourierDilationTransformCore, smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]
  ring

/-- The test-function inverse formula as an unbundled linear map. -/
def inverseFourierDilationTransformCoreLinearMap (m : ℕ) :
    SchwartzMap (InputSpace m × ℝ) ℂ →ₗ[ℂ] (InputSpace m × ℝ → ℂ) where
  toFun q := inverseFourierDilationTransformCore q
  map_add' q r := by
    funext p
    exact inverseFourierDilationTransformCore_add q r p
  map_smul' c q := by
    funext p
    exact inverseFourierDilationTransformCore_smul c q p

end LeanRidgelet
