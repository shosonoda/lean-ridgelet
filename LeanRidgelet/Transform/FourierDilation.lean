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
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Unitary coordinate transform and its Fourier construction

This file introduces the concrete Fourier construction of the manuscript's unitary coordinate
transform `T`. “Fourier--dilation” describes the construction and remains in the internal Lean
identifiers; the mathematical interface is the unitary coordinate transform. The change-of-
variables and extension arguments are stated as named theorems so that later operator theory can
use their final interfaces while the measure-theoretic proofs are completed separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform InnerProductSpace RealInnerProductSpace SchwartzMap

namespace LeanRidgelet

open LeanRidgelet.Fourier

/-- The unitary coordinate transform `T` in the transported coordinate model. -/
def fourierDilationTransform (m : ℕ) [NeZero m] (s t : ℝ) :
    ParameterSpace m s t ≃ₗᵢ[ℂ]
      BochnerL2 (InputSpace m) (FiberSpace m s t) volume :=
  parameterCoordinateEquiv m s t

/-- The Hilbert-space inverse `T⁻¹ = T*`; the test-function Fourier expression is given below. -/
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

/-- The Fourier construction of `T` on Schwartz parameter distributions, before Hilbert-space
extension. -/
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

/-- The Fourier--dilation frequency line is antilipschitz because its last coordinate is `ω`. -/
theorem antilipschitzWith_parameterFrequency {m : ℕ} (x : InputSpace m) :
    AntilipschitzWith 1 (parameterFrequency x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro ω ν
  rw [NNReal.coe_one, one_mul]
  rw [← sq_le_sq₀ (dist_nonneg) (dist_nonneg)]
  simp only [dist_eq_norm, parameterFrequency, fourierDilationCoordinate, frequencyDilation,
    ← WithLp.coe_symm_linearEquiv, WithLp.prod_norm_sq_eq_of_L2]
  norm_num

/-- The frequency line as a real continuous linear map. -/
def parameterFrequencyCLM {m : ℕ} (x : InputSpace m) :
    ℝ →L[ℝ] ParameterProductL2 m :=
  LinearMap.toContinuousLinearMap {
    toFun := parameterFrequency x
    map_add' := by
      intro ω ν
      apply WithLp.ofLp_injective 2
      simp [parameterFrequency, fourierDilationCoordinate, frequencyDilation, add_smul, add_comm]
    map_smul' := by
      intro c ω
      apply WithLp.ofLp_injective 2
      simp [parameterFrequency, fourierDilationCoordinate, frequencyDilation, mul_smul]
  }

@[simp]
theorem parameterFrequencyCLM_apply {m : ℕ} (x : InputSpace m) (ω : ℝ) :
    parameterFrequencyCLM x ω = parameterFrequency x ω :=
  rfl

/-- Restrict the Fourier transform of a parameter Schwartz function to the frequency line
`ω ↦ (-ωx, ω)`. The last coordinate makes this restriction a Schwartz function of `ω`. -/
def parameterFourierRestriction {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (parameterFrequencyCLM x).hasTemperateGrowth
    (antilipschitzWith_parameterFrequency x) (𝓕 (parameterSchwartzL2 γ))

@[simp]
theorem parameterFourierRestriction_apply {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    parameterFourierRestriction γ x ω =
      𝓕 (parameterSchwartzL2 γ) (parameterFrequency x ω) :=
  rfl

/-- Multiplication by `(2π)⁻¹` is antilipschitz with constant `2π`. -/
theorem antilipschitzWith_paperFrequencyScale :
    AntilipschitzWith (⟨2 * Real.pi, by positivity⟩ : NNReal)
      (fun ω : ℝ ↦ (2 * Real.pi)⁻¹ • ω) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro ω ν
  change |ω - ν| ≤ (2 * Real.pi) * |(2 * Real.pi)⁻¹ * ω - (2 * Real.pi)⁻¹ * ν|
  rw [← mul_sub, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp [Real.pi_ne_zero]
  exact le_rfl

/-- The integral Fourier--dilation formula, bundled as an element of the Schwartz fiber core. -/
def fourierDilationTransformFiberCore {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) : FiberCore m s t :=
  ((2 * Real.pi : ℂ) ^ m)⁻¹ •
    SchwartzMap.compCLMOfAntilipschitz ℂ (by fun_prop)
      antilipschitzWith_paperFrequencyScale (parameterFourierRestriction γ x)

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

private theorem integrable_fourierDilationCoordinate_mul_aux {m : ℕ} [NeZero m]
    (f : InputSpace m × ℝ → ℝ) (hf : Integrable f) (hf_cont : Continuous f) :
    Integrable (fun z : InputSpace m × ℝ =>
      f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m) := by
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
  have hg_sections : ∀ᵐ w : ℝ ∂volume,
      Integrable (fun x : InputSpace m => g (x, w)) := by
    filter_upwards [hsections, hw_ne] with w hfw hw
    unfold g fourierDilationCoordinate frequencyDilation
    simpa only [neg_smul] using
      (hfw.comp_smul (neg_ne_zero.mpr hw)).mul_const (|w| ^ m)
  have hnorm_inner : ∀ᵐ w : ℝ ∂volume,
      (∫ x : InputSpace m, ‖g (x, w)‖) =
        ∫ x : InputSpace m, ‖f (x, w)‖ := by
    filter_upwards [hsections, hw_ne] with w hfw hw
    unfold g fourierDilationCoordinate frequencyDilation
    dsimp only
    rw [show (∫ x : InputSpace m,
        ‖f (-(w • x), w) * |w| ^ m‖) =
          (∫ x : InputSpace m, ‖f (-(w • x), w)‖) * |w| ^ m by
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg w) m)]
      exact integral_mul_const _ _]
    have hscale := Measure.integral_comp_smul volume
      (fun x : InputSpace m => ‖f (x, w)‖) (-w)
    simp only [neg_smul, finrank_euclideanSpace_fin, smul_eq_mul] at hscale
    rw [hscale]
    have habs : |((-w) ^ m)⁻¹| * |w| ^ m = 1 := by
      rw [abs_inv, abs_pow, abs_neg]
      field_simp [abs_ne_zero.mpr hw]
    calc
      (|((-w) ^ m)⁻¹| * ∫ x : InputSpace m, ‖f (x, w)‖) * |w| ^ m =
          (|((-w) ^ m)⁻¹| * |w| ^ m) *
            ∫ x : InputSpace m, ‖f (x, w)‖ := by ring
      _ = ∫ x : InputSpace m, ‖f (x, w)‖ := by rw [habs, one_mul]
  rw [Measure.volume_eq_prod]
  rw [integrable_prod_iff' hg_cont.aestronglyMeasurable]
  refine ⟨hg_sections, ?_⟩
  exact hf.integral_norm_prod_right.congr <|
    hnorm_inner.mono fun _ hw => hw.symm

/-- Weighted dilation change of variables in integral form. This is the identity obtained by
pushing `|ω|^m dx dω` forward along `(x, ω) ↦ (-ωx, ω)`. It does not require global
injectivity: the exceptional fiber `ω = 0` is null, and the remaining fibers use Haar-measure
scaling. -/
theorem integral_fourierDilationCoordinate_mul {m : ℕ} [NeZero m]
    (f : InputSpace m × ℝ → ℝ) (hf : Integrable f)
    (hf_cont : Continuous f) :
    (∫ z, f z) =
      ∫ z : InputSpace m × ℝ,
        f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m := by
  let g : InputSpace m × ℝ → ℝ := fun z =>
    f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m
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
  have hg : Integrable g := by
    exact integrable_fourierDilationCoordinate_mul_aux f hf hf_cont
  change (∫ z, f z) = ∫ z, g z
  rw [Measure.volume_eq_prod]
  rw [integral_prod_symm f hf, integral_prod_symm g hg]
  exact integral_congr_ae <| hinner.mono fun _ hw => hw.symm

/-- Integrability of the weighted pullback appearing in the Fourier--dilation change of
variables. This is the integrability component used internally by
`integral_fourierDilationCoordinate_mul`, exposed for later Bochner `L²` arguments. -/
theorem integrable_fourierDilationCoordinate_mul {m : ℕ} [NeZero m]
    (f : InputSpace m × ℝ → ℝ) (hf : Integrable f)
    (hf_cont : Continuous f) :
    Integrable (fun z : InputSpace m × ℝ =>
      f (fourierDilationCoordinate z.1 z.2) * |z.2| ^ m) := by
  exact integrable_fourierDilationCoordinate_mul_aux f hf hf_cont

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
    (continuous_norm_sq_paperFourier_parameter γ)

theorem integrable_norm_sq_paperFourier_parameter_coordinate {m : ℕ} [NeZero m]
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    Integrable (fun z : InputSpace m × ℝ =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ)
        (parameterFrequency z.1 z.2)‖ ^ 2 * |z.2| ^ m) := by
  exact integrable_fourierDilationCoordinate_mul
    (fun z : InputSpace m × ℝ =>
      ‖paperFourierIntegralInner (parameterSchwartzL2 γ) (WithLp.toLp 2 z)‖ ^ 2)
    (integrable_norm_sq_paperFourier_parameter γ)
    (continuous_norm_sq_paperFourier_parameter γ)

theorem fourierDilationTransformCore_eq_paperFourier {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    fourierDilationTransformCore γ x ω =
      ((2 * Real.pi : ℂ) ^ m)⁻¹ *
        paperFourierIntegralInner (parameterSchwartzL2 γ) (parameterFrequency x ω) := by
  rw [fourierDilationTransformCore,
    paperFourierIntegralInner_parameterFrequency]

@[simp]
theorem fourierDilationTransformFiberCore_apply {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) (ω : ℝ) :
    FiberCore.toSchwartz (fourierDilationTransformFiberCore s t γ x) ω =
      fourierDilationTransformCore γ x ω := by
  unfold FiberCore.toSchwartz
  rw [fourierDilationTransformCore_eq_paperFourier, paperFourierIntegralInner_eq_mathlib]
  simp only [fourierDilationTransformFiberCore, smul_apply, smul_eq_mul,
    SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply,
    parameterFourierRestriction_apply]
  rw [SchwartzMap.fourier_coe]
  have hfrequency :
      parameterFrequency x ((2 * Real.pi)⁻¹ * ω) =
        (2 * Real.pi)⁻¹ • parameterFrequency x ω := by
    apply WithLp.ofLp_injective 2
    simp [parameterFrequency, fourierDilationCoordinate, frequencyDilation, mul_smul]
    ring
  rw [hfrequency]
  rfl

/-- The Fourier--dilation core formula embedded in the completed fiber space. -/
def fourierDilationTransformFiber {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) : FiberSpace m s t :=
  (fourierDilationTransformFiberCore s t γ x : FiberSpace m s t)

theorem norm_sq_fourierDilationTransformFiber {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) :
    ‖fourierDilationTransformFiber s t γ x‖ ^ 2 =
      fiberNormSq m s t (fourierDilationTransformFiberCore s t γ x) := by
  rw [fourierDilationTransformFiber, UniformSpace.Completion.norm_coe,
    FiberCore.norm_sq_eq_fiberNormSq]
  rfl

theorem norm_sq_fourierDilationTransformFiber_eq_base_add_sobolev
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (x : InputSpace m) :
    ‖fourierDilationTransformFiber s t γ x‖ ^ 2 =
      fiberBaseNormSq m (fourierDilationTransformFiberCore s t γ x) +
        fiberSobolevNormSq s t (fourierDilationTransformFiberCore s t γ x) := by
  rw [norm_sq_fourierDilationTransformFiber, fiberNormSq]

/-- Bundle the fiber-valued core formula as a Bochner `L²` coordinate once its analytic
membership has been established. -/
def fourierDilationTransformCoreL2 {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    BochnerL2 (InputSpace m) (FiberSpace m s t) volume :=
  hγ.toLp (fourierDilationTransformFiber s t γ)

theorem fourierDilationTransformCoreL2_apply_ae {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    (fourierDilationTransformCoreL2 s t γ hγ :
        InputSpace m → FiberSpace m s t) =ᵐ[volume]
      fourierDilationTransformFiber s t γ :=
  hγ.coeFn_toLp

/-- The parameter-space element represented by a concrete Schwartz core formula whose
fiber-valued transform belongs to Bochner `L²`. This uses the inverse transported unitary rather
than storing membership as a field of a new assumption object. -/
def parameterSchwartzRealization {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    ParameterSpace m s t :=
  inverseFourierDilationTransform m s t (fourierDilationTransformCoreL2 s t γ hγ)

/-- Compatibility of the concrete core formula with the transported unitary model. -/
theorem fourierDilationTransform_parameterSchwartzRealization
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    fourierDilationTransform m s t (parameterSchwartzRealization s t γ hγ) =
      fourierDilationTransformCoreL2 s t γ hγ :=
  (fourierDilationTransform m s t).apply_symm_apply _

theorem fourierDilationTransform_parameterSchwartzRealization_apply_ae
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume) :
    (fourierDilationTransform m s t (parameterSchwartzRealization s t γ hγ) :
        InputSpace m → FiberSpace m s t) =ᵐ[volume]
      fourierDilationTransformFiber s t γ := by
  rw [fourierDilationTransform_parameterSchwartzRealization]
  exact fourierDilationTransformCoreL2_apply_ae s t γ hγ

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

theorem integrable_norm_sq_fourierDilationTransformCore_mul {m : ℕ} [NeZero m]
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    Integrable (fun z : InputSpace m × ℝ =>
      ‖fourierDilationTransformCore γ z.1 z.2‖ ^ 2 * |z.2| ^ m) := by
  have h := (integrable_norm_sq_paperFourier_parameter_coordinate γ).const_mul
    ((((2 * Real.pi) ^ m)⁻¹) ^ 2)
  refine h.congr ?_
  filter_upwards with z
  rw [norm_sq_fourierDilationTransformCore_eq]
  ring

theorem integrable_fiberBaseNormSq_fourierDilationTransformFiberCore
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    Integrable (fun x : InputSpace m =>
      fiberBaseNormSq m (fourierDilationTransformFiberCore s t γ x)) := by
  have hprod := integrable_norm_sq_fourierDilationTransformCore_mul γ
  rw [Measure.volume_eq_prod] at hprod
  have hinter := hprod.integral_prod_left
  have hscaled := hinter.const_mul ((2 * Real.pi) ^ (m - 1))
  refine hscaled.congr ?_
  filter_upwards with x
  unfold fiberBaseNormSq
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  change ‖fourierDilationTransformCore γ x ω‖ ^ 2 * |ω| ^ m =
    ‖FiberCore.toSchwartz (fourierDilationTransformFiberCore s t γ x) ω‖ ^ 2 * |ω| ^ m
  rw [fourierDilationTransformFiberCore_apply]

/-- Plancherel plus the dilation Jacobian for the unitary-coordinate formula on the Schwartz
core. -/
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

theorem integral_fiberBaseNormSq_fourierDilationTransformFiberCore
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    (∫ x : InputSpace m,
        fiberBaseNormSq m (fourierDilationTransformFiberCore s t γ x)) =
      ∫ p : InputSpace m × ℝ, ‖γ p‖ ^ 2 := by
  let F : InputSpace m × ℝ → ℝ := fun z =>
    ‖fourierDilationTransformCore γ z.1 z.2‖ ^ 2 * |z.2| ^ m
  have hF : Integrable F := integrable_norm_sq_fourierDilationTransformCore_mul γ
  have hFprod : Integrable F (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hF
  calc
    (∫ x : InputSpace m,
        fiberBaseNormSq m (fourierDilationTransformFiberCore s t γ x)) =
        ∫ x : InputSpace m, (2 * Real.pi) ^ (m - 1) * ∫ ω : ℝ, F (x, ω) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold fiberBaseNormSq F
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      change ‖FiberCore.toSchwartz
        (fourierDilationTransformFiberCore s t γ x) ω‖ ^ 2 * |ω| ^ m =
          ‖fourierDilationTransformCore γ x ω‖ ^ 2 * |ω| ^ m
      rw [fourierDilationTransformFiberCore_apply]
    _ = (2 * Real.pi) ^ (m - 1) * ∫ x : InputSpace m, ∫ ω : ℝ, F (x, ω) := by
      rw [integral_const_mul]
    _ = (2 * Real.pi) ^ (m - 1) * ∫ z : InputSpace m × ℝ, F z := by
      congr 1
      rw [Measure.volume_eq_prod]
      exact (integral_prod F hFprod).symm
    _ = ∫ p : InputSpace m × ℝ, ‖γ p‖ ^ 2 := by
      symm
      exact fourierDilationTransformCore_norm_sq γ

/-- Once strong measurability is known, Bochner `L²` membership of the Fourier--dilation core is
equivalent to integrability of the Sobolev term; the base term is always integrable. -/
theorem memLp_fourierDilationTransformFiber_iff_integrable_sobolev
    {m : ℕ} [NeZero m] (s t : ℝ)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : AEStronglyMeasurable (fourierDilationTransformFiber s t γ) volume) :
    MemLp (fourierDilationTransformFiber s t γ) 2 volume ↔
      Integrable (fun x : InputSpace m =>
        fiberSobolevNormSq s t (fourierDilationTransformFiberCore s t γ x)) := by
  let B : InputSpace m → ℝ := fun x =>
    fiberBaseNormSq m (fourierDilationTransformFiberCore s t γ x)
  let W : InputSpace m → ℝ := fun x =>
    fiberSobolevNormSq s t (fourierDilationTransformFiberCore s t γ x)
  have hB : Integrable B :=
    integrable_fiberBaseNormSq_fourierDilationTransformFiberCore s t γ
  constructor
  · intro hmem
    have hnorm : Integrable (fun x : InputSpace m =>
        ‖fourierDilationTransformFiber s t γ x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hγ).1 hmem
    have hdifference := hnorm.sub hB
    refine hdifference.congr ?_
    filter_upwards with x
    change ‖fourierDilationTransformFiber s t γ x‖ ^ 2 - B x = W x
    rw [norm_sq_fourierDilationTransformFiber_eq_base_add_sobolev]
    unfold B W
    ring
  · intro hW
    apply (memLp_two_iff_integrable_sq_norm hγ).2
    have hsum : Integrable (fun x => B x + W x) := hB.add hW
    refine hsum.congr ?_
    filter_upwards with x
    rw [norm_sq_fourierDilationTransformFiber_eq_base_add_sobolev]

/-- The kernel in the inverse coordinate formula (13). -/
def inverseFourierDilationKernel {m : ℕ} (p : InputSpace m × ℝ)
    (z : InputSpace m × ℝ) : ℂ :=
  Complex.exp (-Complex.I * (z.2 * (inner ℝ p.1 z.1 - p.2))) * |z.2| ^ m

/-- The Fourier expression for the inverse coordinate transform on a Schwartz test function. -/
def inverseFourierDilationTransformCore {m : ℕ}
    (u : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ∫ z : InputSpace m × ℝ, u z * inverseFourierDilationKernel p z

theorem integrable_inverseFourierDilationTransformCore_integrand {m : ℕ}
    (u : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    Integrable (fun z : InputSpace m × ℝ ↦ u z * inverseFourierDilationKernel p z) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (InputSpace m × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  apply (u.integrable_pow_mul volume m).mono
  · apply Continuous.aestronglyMeasurable
    unfold inverseFourierDilationKernel
    fun_prop
  · filter_upwards with z
    have hkernel : ‖inverseFourierDilationKernel p z‖ = |z.2| ^ m := by
      unfold inverseFourierDilationKernel
      rw [norm_mul, Complex.norm_exp]
      simp
    rw [norm_mul, hkernel, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg z) m) (norm_nonneg (u z)))]
    rw [mul_comm]
    gcongr
    simpa only [Real.norm_eq_abs] using norm_snd_le z

theorem inverseFourierDilationTransformCore_add {m : ℕ}
    (u v : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    inverseFourierDilationTransformCore (u + v) p =
      inverseFourierDilationTransformCore u p + inverseFourierDilationTransformCore v p := by
  simp only [inverseFourierDilationTransformCore, add_apply, add_mul,
    integral_add (integrable_inverseFourierDilationTransformCore_integrand u p)
      (integrable_inverseFourierDilationTransformCore_integrand v p), mul_add]

theorem inverseFourierDilationTransformCore_smul {m : ℕ} (c : ℂ)
    (u : SchwartzMap (InputSpace m × ℝ) ℂ) (p : InputSpace m × ℝ) :
    inverseFourierDilationTransformCore (c • u) p =
      c * inverseFourierDilationTransformCore u p := by
  simp only [inverseFourierDilationTransformCore, smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]
  ring

/-- The test-function inverse formula as an unbundled linear map. -/
def inverseFourierDilationTransformCoreLinearMap (m : ℕ) :
    SchwartzMap (InputSpace m × ℝ) ℂ →ₗ[ℂ] (InputSpace m × ℝ → ℂ) where
  toFun u := inverseFourierDilationTransformCore u
  map_add' u v := by
    funext p
    exact inverseFourierDilationTransformCore_add u v p
  map_smul' c u := by
    funext p
    exact inverseFourierDilationTransformCore_smul c u p

end LeanRidgelet
