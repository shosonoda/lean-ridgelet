/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Parameter
public import LeanRidgelet.Fourier.PaperDistribution
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Activation--fiber duality

This file formalizes the continuous pairing between the activation space `A_{s,t}` and the fiber
space `H_{s,t}` from equations (8)--(9) of the L2 manuscript. The weighted Bessel coordinate is
first defined on the Schwartz core and then extended continuously to the completed fiber space.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal FourierTransform InnerProductSpace SchwartzMap

namespace LeanRidgelet

open Fourier

/-- The weighted Bessel coordinate `⟨ω⟩⁻ˢ⟨∂ω⟩ᵗh` occurring in the dual estimate. -/
def fiberDualCoordinateFn (s t : ℝ) (h : SchwartzMap ℝ ℂ) (ω : ℝ) : ℂ :=
  japaneseBracketPow (-s) ω * schwartzBesselPotential t h ω

theorem memLp_fiberDualCoordinateFn (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    MemLp (fiberDualCoordinateFn s t h) 2 volume := by
  let g : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s)) (schwartzBesselPotential t h)
  have hg : MemLp g 2 volume := g.memLp 2 volume
  have hfun : (g : ℝ → ℂ) = fiberDualCoordinateFn s t h := by
    funext ω
    rw [show g ω =
      SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s))
        (schwartzBesselPotential t h) ω from rfl]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_temperedWeight (-s))]
    simp [fiberDualCoordinateFn, temperedWeight, smul_eq_mul]
  rw [← hfun]
  exact hg

/-- The weighted Bessel coordinate of a Schwartz fiber, regarded as an `L²` element. -/
def fiberDualCoordinateCoreValue (s t : ℝ) (h : SchwartzMap ℝ ℂ) : L2 ℝ volume :=
  (memLp_fiberDualCoordinateFn s t h).toLp (fiberDualCoordinateFn s t h)

/-- The Schwartz representative of the weighted Bessel coordinate of a fiber-core element. -/
def fiberDualSchwartzCoordinate (s t : ℝ) (h : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s)) (schwartzBesselPotential t h)

/-- The `L²` core coordinate is the canonical `L²` realization of its Schwartz representative. -/
theorem fiberDualCoordinateCoreValue_eq_toLp (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t h =
      (fiberDualSchwartzCoordinate s t h).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [
    (memLp_fiberDualCoordinateFn s t h).coeFn_toLp,
    (fiberDualSchwartzCoordinate s t h).coeFn_toLp 2 volume] with ω hleft hright
  unfold fiberDualCoordinateCoreValue
  rw [hleft, hright]
  unfold fiberDualSchwartzCoordinate
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_temperedWeight (-s))]
  simp [fiberDualCoordinateFn, temperedWeight]

/-- A Schwartz preimage for the weighted Bessel coordinate map. -/
def fiberDualSchwartzPreimage (s t : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  schwartzBesselPotential (-t) (SchwartzMap.smulLeftCLM ℂ (temperedWeight s) f)

theorem fiberDualCoordinateCoreValue_fiberDualSchwartzPreimage (s t : ℝ)
    (f : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t (fiberDualSchwartzPreimage s t f) =
      f.toLp 2 volume := by
  have hbessel :
      schwartzBesselPotential t (fiberDualSchwartzPreimage s t f) =
        SchwartzMap.smulLeftCLM ℂ (temperedWeight s) f := by
    unfold fiberDualSchwartzPreimage schwartzBesselPotential
    rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (hasTemperateGrowth_paperBesselSymbol t) (hasTemperateGrowth_paperBesselSymbol (-t))]
    have hsymbol : paperBesselSymbol t * paperBesselSymbol (-t) = 1 := by
      simpa only [mul_comm] using paperBesselSymbol_neg_mul t
    rw [hsymbol]
    change SchwartzMap.fourierMultiplierCLM ℂ (fun _ : ℝ ↦ 1)
      (SchwartzMap.smulLeftCLM ℂ (temperedWeight s) f) = _
    rw [SchwartzMap.fourierMultiplierCLM_const]
    simp
  unfold fiberDualCoordinateCoreValue
  apply Lp.ext
  have hleft := (memLp_fiberDualCoordinateFn s t
    (fiberDualSchwartzPreimage s t f)).coeFn_toLp
  filter_upwards [hleft, f.coeFn_toLp 2 volume] with ω hleftω hfω
  change fiberDualCoordinateCoreValue s t (fiberDualSchwartzPreimage s t f) ω = f.toLp 2 volume ω
  unfold fiberDualCoordinateCoreValue
  rw [hleftω, hfω]
  unfold fiberDualCoordinateFn
  rw [hbessel, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_temperedWeight s)]
  simp only [temperedWeight, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← japaneseBracketPow_add]
  simp

theorem fiberDualCoordinateCoreValue_add (s t : ℝ) (h r : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t (h + r) =
      fiberDualCoordinateCoreValue s t h + fiberDualCoordinateCoreValue s t r := by
  apply Lp.ext
  unfold fiberDualCoordinateCoreValue
  grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
  filter_upwards with ω
  simp [fiberDualCoordinateFn, mul_add]

theorem fiberDualCoordinateCoreValue_smul (s t : ℝ) (c : ℂ) (h : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t (c • h) = c • fiberDualCoordinateCoreValue s t h := by
  apply Lp.ext
  unfold fiberDualCoordinateCoreValue
  grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
  filter_upwards with ω
  simp [fiberDualCoordinateFn]
  ring

/-- The weighted Bessel coordinate as a linear map on the Schwartz fiber core. -/
def fiberDualCoordinateCore (m : ℕ) (s t : ℝ) : FiberCore m s t →ₗ[ℂ] L2 ℝ volume where
  toFun := fiberDualCoordinateCoreValue s t
  map_add' := fiberDualCoordinateCoreValue_add s t
  map_smul' := fiberDualCoordinateCoreValue_smul s t

theorem norm_fiberDualCoordinateCore_sq (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    ‖fiberDualCoordinateCore m s t h‖ ^ 2 = fiberSobolevNormSq s t h := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [L2.inner_def]
  rw [← integral_re (L2.integrable_inner _ _)]
  unfold fiberSobolevNormSq
  apply integral_congr_ae
  have hcoe :
      (fiberDualCoordinateCore m s t h : ℝ → ℂ) =ᵐ[volume]
        fiberDualCoordinateFn s t h := by
    change fiberDualCoordinateCoreValue s t h =ᵐ[volume]
      fiberDualCoordinateFn s t h
    exact (memLp_fiberDualCoordinateFn s t h).coeFn_toLp
  filter_upwards [hcoe] with ω hω
  rw [hω]
  simp only [inner_self_eq_norm_sq]
  unfold fiberDualCoordinateFn
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (le_of_lt (japaneseBracketPow_pos (-s) ω)), mul_pow]
  rw [japaneseBracketPow_sq]
  rw [show 2 * -s = -2 * s by ring]
  ring

theorem norm_fiberDualCoordinateCore_le (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) : ‖fiberDualCoordinateCore m s t h‖ ≤ ‖h‖ := by
  have hcoord := norm_fiberDualCoordinateCore_sq m s t h
  have hq : ‖h‖ ^ 2 = fiberNormSq m s t h := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact fiberInner_self_re m s t h
  have hbase := fiberBaseNormSq_nonneg m h
  rw [fiberNormSq] at hq
  nlinarith [norm_nonneg (fiberDualCoordinateCore m s t h), norm_nonneg h]

/-- The contractive weighted Bessel coordinate map on the Schwartz fiber core. -/
def fiberDualCoordinateCoreL (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberCore m s t →L[ℂ] L2 ℝ volume :=
  LinearMap.mkContinuous (fiberDualCoordinateCore m s t) 1 fun h ↦ by
    simpa using norm_fiberDualCoordinateCore_le m s t h

/-- The weighted Bessel coordinate map, extended to the completed fiber Hilbert space. -/
def fiberDualCoordinate (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →L[ℂ] L2 ℝ volume :=
  (fiberDualCoordinateCoreL m s t).extend
    (UniformSpace.Completion.toComplL : FiberCore m s t →L[ℂ] FiberSpace m s t)

@[simp]
theorem fiberDualCoordinate_coe (m : ℕ) [NeZero m] (s t : ℝ) (h : FiberCore m s t) :
    fiberDualCoordinate m s t (h : FiberSpace m s t) = fiberDualCoordinateCore m s t h := by
  apply ContinuousLinearMap.extend_eq
  · exact UniformSpace.Completion.denseRange_coe
  · simpa only [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformInducing_coe (FiberCore m s t))

/-! ### The dilation-Jacobian coordinate -/

/-- The square-root coordinate `|ω|^(m/2) h(ω)` used to realize the first term of the fiber norm.
Writing the weight as a real square root also covers odd dimensions without asserting smoothness at
the origin. -/
def fiberBaseCoordinateFn (m : ℕ) (h : SchwartzMap ℝ ℂ) (ω : ℝ) : ℂ :=
  (Real.sqrt (|ω| ^ m) : ℂ) * h ω

theorem memLp_fiberBaseCoordinateFn (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    MemLp (fiberBaseCoordinateFn m h) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by
    unfold fiberBaseCoordinateFn
    fun_prop)).2
  convert integrable_norm_sq_mul_abs_pow m h using 1
  funext ω
  unfold fiberBaseCoordinateFn
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (pow_nonneg (abs_nonneg ω) m)]
  ring

/-- The square-root weighted coordinate of a Schwartz fiber, regarded as an `L²` element. -/
def fiberBaseCoordinateCoreValue (m : ℕ) (h : SchwartzMap ℝ ℂ) : L2 ℝ volume :=
  (memLp_fiberBaseCoordinateFn m h).toLp (fiberBaseCoordinateFn m h)

theorem fiberBaseCoordinateCoreValue_add (m : ℕ) (h r : SchwartzMap ℝ ℂ) :
    fiberBaseCoordinateCoreValue m (h + r) =
      fiberBaseCoordinateCoreValue m h + fiberBaseCoordinateCoreValue m r := by
  apply Lp.ext
  unfold fiberBaseCoordinateCoreValue
  grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
  filter_upwards with ω
  simp [fiberBaseCoordinateFn, mul_add]

theorem fiberBaseCoordinateCoreValue_smul (m : ℕ) (c : ℂ) (h : SchwartzMap ℝ ℂ) :
    fiberBaseCoordinateCoreValue m (c • h) = c • fiberBaseCoordinateCoreValue m h := by
  apply Lp.ext
  unfold fiberBaseCoordinateCoreValue
  grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
  filter_upwards with ω
  simp [fiberBaseCoordinateFn]
  ring

/-- The square-root weighted coordinate as a linear map on Schwartz space. -/
def fiberBaseCoordinateSchwartzLinear (m : ℕ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] L2 ℝ volume where
  toFun := fiberBaseCoordinateCoreValue m
  map_add' := fiberBaseCoordinateCoreValue_add m
  map_smul' := fiberBaseCoordinateCoreValue_smul m

theorem sqrt_abs_pow_le_japaneseBracketPow (m : ℕ) (ω : ℝ) :
    Real.sqrt (|ω| ^ m) ≤ japaneseBracketPow (m : ℝ) ω := by
  rw [← Real.sqrt_sq (le_of_lt (japaneseBracketPow_pos (m : ℝ) ω))]
  apply Real.sqrt_le_sqrt
  rw [japaneseBracketPow_sq]
  unfold japaneseBracketPow
  rw [show (2 * (m : ℝ)) / 2 = (m : ℝ) by ring, Real.rpow_natCast]
  have hbase : |ω| ≤ 1 + ‖ω‖ ^ 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|ω| - 1 / 2)]
  exact pow_le_pow_left₀ (abs_nonneg ω) hbase m

/-- A smooth Japanese-bracket majorant for the possibly nonsmooth square-root weight. -/
def fiberBaseCoordinateMajorant (m : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] L2 ℝ volume :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L
    SchwartzMap.smulLeftCLM ℂ (temperedWeight (m : ℝ))

theorem norm_fiberBaseCoordinateSchwartzLinear_le_majorant
    (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    ‖fiberBaseCoordinateSchwartzLinear m h‖ ≤ ‖fiberBaseCoordinateMajorant m h‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [
    (memLp_fiberBaseCoordinateFn m h).coeFn_toLp,
    (SchwartzMap.smulLeftCLM ℂ (temperedWeight (m : ℝ)) h).coeFn_toLp 2 volume]
      with ω hleft hright
  rw [show fiberBaseCoordinateSchwartzLinear m h ω = fiberBaseCoordinateFn m h ω by
    exact hleft]
  rw [show fiberBaseCoordinateMajorant m h ω =
      SchwartzMap.smulLeftCLM ℂ (temperedWeight (m : ℝ)) h ω by exact hright]
  unfold fiberBaseCoordinateFn
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight (m : ℝ))]
  simp only [temperedWeight, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (japaneseBracketPow_pos (m : ℝ) ω)]
  exact mul_le_mul_of_nonneg_right (sqrt_abs_pow_le_japaneseBracketPow m ω)
    (norm_nonneg (h ω))

/-- The square-root weighted coordinate is continuous for the Schwartz topology.  Continuity is
proved by domination with a smooth Japanese-bracket multiplier, rather than by treating
`|ω|^(m/2)` as a Schwartz multiplier. -/
def fiberBaseCoordinateSchwartz (m : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] L2 ℝ volume where
  toLinearMap := fiberBaseCoordinateSchwartzLinear m
  cont := by
    apply continuous_of_continuousAt_zero (fiberBaseCoordinateSchwartzLinear m)
    rw [Metric.continuousAt_iff']
    intro ε hε
    have hmajor := (Metric.continuousAt_iff'.mp
      ((fiberBaseCoordinateMajorant m).continuous.continuousAt :
        ContinuousAt (fiberBaseCoordinateMajorant m) (0 : SchwartzMap ℝ ℂ))) ε hε
    filter_upwards [hmajor] with h hh
    simpa only [map_zero, dist_zero_right] using
      lt_of_le_of_lt (norm_fiberBaseCoordinateSchwartzLinear_le_majorant m h)
        (by simpa only [map_zero, dist_zero_right] using hh)

/-- The square-root weighted coordinate on the fiber core. -/
def fiberBaseCoordinateCore (m : ℕ) (s t : ℝ) :
    FiberCore m s t →ₗ[ℂ] L2 ℝ volume where
  toFun := fiberBaseCoordinateCoreValue m
  map_add' := fiberBaseCoordinateCoreValue_add m
  map_smul' := fiberBaseCoordinateCoreValue_smul m

theorem norm_fiberBaseCoordinateCore_sq (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    ‖fiberBaseCoordinateCore m s t h‖ ^ 2 =
      ∫ ω : ℝ, ‖FiberCore.toSchwartz h ω‖ ^ 2 * |ω| ^ m := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [L2.inner_def]
  rw [← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  have hcoe :
      (fiberBaseCoordinateCore m s t h : ℝ → ℂ) =ᵐ[volume]
        fiberBaseCoordinateFn m h := by
    change fiberBaseCoordinateCoreValue m h =ᵐ[volume]
      fiberBaseCoordinateFn m h
    exact (memLp_fiberBaseCoordinateFn m h).coeFn_toLp
  filter_upwards [hcoe] with ω hω
  rw [hω]
  simp only [inner_self_eq_norm_sq]
  unfold fiberBaseCoordinateFn
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (pow_nonneg (abs_nonneg ω) m)]
  change |ω| ^ m * ‖FiberCore.toSchwartz h ω‖ ^ 2 =
    ‖FiberCore.toSchwartz h ω‖ ^ 2 * |ω| ^ m
  ring

theorem norm_fiberBaseCoordinateCore_le (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) : ‖fiberBaseCoordinateCore m s t h‖ ≤ ‖h‖ := by
  have hcoord := norm_fiberBaseCoordinateCore_sq m s t h
  have hq : ‖h‖ ^ 2 = fiberNormSq m s t h :=
    FiberCore.norm_sq_eq_fiberNormSq m s t h
  have hcoefficient : 1 ≤ (2 * Real.pi) ^ (m - 1) := by
    apply one_le_pow₀
    nlinarith [Real.one_le_pi_div_two]
  have hbaseInt : 0 ≤
      ∫ ω : ℝ, ‖FiberCore.toSchwartz h ω‖ ^ 2 * |ω| ^ m := by
    apply integral_nonneg
    intro ω
    positivity
  have hsob := fiberSobolevNormSq_nonneg s t h
  have hq' : ‖h‖ ^ 2 =
      (2 * Real.pi) ^ (m - 1) *
        (∫ ω : ℝ, ‖FiberCore.toSchwartz h ω‖ ^ 2 * |ω| ^ m) +
        fiberSobolevNormSq s t h := by
    simpa only [fiberNormSq, fiberBaseNormSq, FiberCore.toSchwartz] using hq
  nlinarith [norm_nonneg (fiberBaseCoordinateCore m s t h), norm_nonneg h]

/-- The contractive square-root weighted coordinate map on the fiber core. -/
def fiberBaseCoordinateCoreL (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberCore m s t →L[ℂ] L2 ℝ volume :=
  LinearMap.mkContinuous (fiberBaseCoordinateCore m s t) 1 fun h ↦ by
    simpa using norm_fiberBaseCoordinateCore_le m s t h

/-- The square-root weighted coordinate, extended to the completed fiber Hilbert space. -/
def fiberBaseCoordinate (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →L[ℂ] L2 ℝ volume :=
  (fiberBaseCoordinateCoreL m s t).extend
    (UniformSpace.Completion.toComplL : FiberCore m s t →L[ℂ] FiberSpace m s t)

@[simp]
theorem fiberBaseCoordinate_coe (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    fiberBaseCoordinate m s t (h : FiberSpace m s t) =
      fiberBaseCoordinateCore m s t h := by
  apply ContinuousLinearMap.extend_eq
  · exact UniformSpace.Completion.denseRange_coe
  · simpa only [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformInducing_coe (FiberCore m s t))

/-- The weighted Bessel coordinate map has dense range in its `L²` coordinate space. -/
theorem denseRange_fiberDualCoordinate (m : ℕ) [NeZero m] (s t : ℝ) :
    DenseRange (fiberDualCoordinate m s t) := by
  apply (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).mono
  intro y hy
  rcases hy with ⟨f, rfl⟩
  let h : FiberCore m s t := fiberDualSchwartzPreimage s t f
  refine ⟨(h : FiberSpace m s t), ?_⟩
  rw [fiberDualCoordinate_coe]
  exact fiberDualCoordinateCoreValue_fiberDualSchwartzPreimage s t f

theorem norm_fiberDualCoordinate_le (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) : ‖fiberDualCoordinate m s t h‖ ≤ ‖h‖ := by
  refine (denseRange_fiberCore_coe m s t).induction_on h ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro h
    simpa using norm_fiberDualCoordinateCore_le m s t h

theorem norm_star_L2 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : L2 α μ) :
    ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (star f : L2 α μ) 2 μ = eLpNorm (star fun x ↦ f x) 2 μ :=
      eLpNorm_congr_ae (Lp.coeFn_star f)
    _ = eLpNorm f 2 μ := eLpNorm_star

/-- The activation-induced functional `L_σ` on the coefficient Hilbert space. -/
def activationFiberFunctional (m : ℕ) [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) :
    FiberSpace m s t →L[ℂ] ℂ :=
  ((2 * Real.pi : ℂ) ^ (m - 1)) •
    ((innerSL ℂ (star σ)).comp (fiberDualCoordinate m s t))

@[simp]
theorem activationFiberFunctional_coe (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberCore m s t) :
    activationFiberFunctional m s t σ (h : FiberSpace m s t) =
      (2 * Real.pi : ℂ) ^ (m - 1) *
        inner ℂ (star σ) (fiberDualCoordinateCoreValue s t h) := by
  simp [activationFiberFunctional, fiberDualCoordinateCore]

theorem activationFiberFunctional_add (m : ℕ) [NeZero m] (s t : ℝ)
    (σ τ : ActivationSpace s t) :
    activationFiberFunctional m s t (σ + τ) =
      activationFiberFunctional m s t σ + activationFiberFunctional m s t τ := by
  have hstar : star (σ + τ) = star σ + star τ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (σ + τ), Lp.coeFn_star σ, Lp.coeFn_star τ,
      Lp.coeFn_add σ τ, Lp.coeFn_add (star σ) (star τ)] with ω hστ hσ hτ hst hstarst
    rw [hστ, hstarst]
    change star ((σ + τ) ω) = (star σ) ω + (star τ) ω
    rw [hst, hσ, hτ]
    simp
  ext h
  simp [activationFiberFunctional, hstar]

theorem activationFiberFunctional_smul (m : ℕ) [NeZero m] (s t : ℝ)
    (c : ℂ) (σ : ActivationSpace s t) :
    activationFiberFunctional m s t (c • σ) = c • activationFiberFunctional m s t σ := by
  have hstar : star (c • σ) = conj c • star σ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • σ), Lp.coeFn_star σ, Lp.coeFn_smul c σ,
      Lp.coeFn_smul (conj c) (star σ)] with ω hcσ hσ hcs hstarcs
    rw [hcσ, hstarcs]
    change star ((c • σ) ω) = conj c * (star σ) ω
    rw [hcs, hσ]
    simp
  ext h
  simp [activationFiberFunctional, hstar]
  ring

/-- The operator-norm form of the activation--coefficient dual estimate. -/
theorem norm_activationFiberFunctional_le (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    ‖activationFiberFunctional m s t σ‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro h
    calc
      ‖activationFiberFunctional m s t σ h‖ =
          (2 * Real.pi) ^ (m - 1) *
            ‖inner ℂ (star σ) (fiberDualCoordinate m s t h)‖ := by
        simp [activationFiberFunctional, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      _ ≤ (2 * Real.pi) ^ (m - 1) *
          (‖star σ‖ * ‖fiberDualCoordinate m s t h‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = (2 * Real.pi) ^ (m - 1) *
          (‖σ‖ * ‖fiberDualCoordinate m s t h‖) := by
        rw [norm_star_L2]
      _ ≤ (2 * Real.pi) ^ (m - 1) * (‖σ‖ * ‖h‖) := by
        gcongr
        exact norm_fiberDualCoordinate_le m s t h
      _ = (2 * Real.pi) ^ (m - 1) * ‖σ‖ * ‖h‖ := by ring

/-- The continuous linear map `A_{s,t} → H_{s,t}*` induced by the Fourier pairing. -/
def activationFiberDualMap (m : ℕ) [NeZero m] (s t : ℝ) :
    ActivationSpace s t →L[ℂ] FiberSpace m s t →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := activationFiberFunctional m s t
      map_add' := activationFiberFunctional_add m s t
      map_smul' := activationFiberFunctional_smul m s t }
    ((2 * Real.pi) ^ (m - 1))
    (norm_activationFiberFunctional_le m s t)

@[simp]
theorem activationFiberDualMap_apply (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    activationFiberDualMap m s t σ = activationFiberFunctional m s t σ :=
  rfl

end LeanRidgelet
