/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Parameter
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
open scoped ComplexConjugate ENNReal InnerProductSpace SchwartzMap

namespace LeanRidgelet

/-- The weighted Bessel coordinate `⟨ω⟩⁻ˢ⟨∂ω⟩ᵗq` occurring in the dual estimate. -/
def fiberDualCoordinateFn (s t : ℝ) (q : SchwartzMap ℝ ℂ) (ω : ℝ) : ℂ :=
  japaneseBracketPow (-s) ω * schwartzBesselPotential t q ω

theorem memLp_fiberDualCoordinateFn (s t : ℝ) (q : SchwartzMap ℝ ℂ) :
    MemLp (fiberDualCoordinateFn s t q) 2 volume := by
  let g : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s)) (schwartzBesselPotential t q)
  have hg : MemLp g 2 volume := g.memLp 2 volume
  have hfun : (g : ℝ → ℂ) = fiberDualCoordinateFn s t q := by
    funext ω
    rw [show g ω =
      SchwartzMap.smulLeftCLM ℂ (temperedWeight (-s))
        (schwartzBesselPotential t q) ω from rfl]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_temperedWeight (-s))]
    simp [fiberDualCoordinateFn, temperedWeight, smul_eq_mul]
  rw [← hfun]
  exact hg

/-- The weighted Bessel coordinate of a Schwartz fiber, regarded as an `L²` element. -/
def fiberDualCoordinateCoreValue (s t : ℝ) (q : SchwartzMap ℝ ℂ) : L2 ℝ volume :=
  (memLp_fiberDualCoordinateFn s t q).toLp (fiberDualCoordinateFn s t q)

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

theorem fiberDualCoordinateCoreValue_add (s t : ℝ) (q r : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t (q + r) =
      fiberDualCoordinateCoreValue s t q + fiberDualCoordinateCoreValue s t r := by
  apply Lp.ext
  unfold fiberDualCoordinateCoreValue
  grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
  filter_upwards with ω
  simp [fiberDualCoordinateFn, mul_add]

theorem fiberDualCoordinateCoreValue_smul (s t : ℝ) (c : ℂ) (q : SchwartzMap ℝ ℂ) :
    fiberDualCoordinateCoreValue s t (c • q) = c • fiberDualCoordinateCoreValue s t q := by
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
    (q : FiberCore m s t) :
    ‖fiberDualCoordinateCore m s t q‖ ^ 2 = fiberSobolevNormSq s t q := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [L2.inner_def]
  rw [← integral_re (L2.integrable_inner _ _)]
  unfold fiberSobolevNormSq
  apply integral_congr_ae
  have hcoe :
      (fiberDualCoordinateCore m s t q : ℝ → ℂ) =ᵐ[volume]
        fiberDualCoordinateFn s t q := by
    change fiberDualCoordinateCoreValue s t q =ᵐ[volume]
      fiberDualCoordinateFn s t q
    exact (memLp_fiberDualCoordinateFn s t q).coeFn_toLp
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
    (q : FiberCore m s t) : ‖fiberDualCoordinateCore m s t q‖ ≤ ‖q‖ := by
  have hcoord := norm_fiberDualCoordinateCore_sq m s t q
  have hq : ‖q‖ ^ 2 = fiberNormSq m s t q := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact fiberInner_self_re m s t q
  have hbase := fiberBaseNormSq_nonneg m q
  rw [fiberNormSq] at hq
  nlinarith [norm_nonneg (fiberDualCoordinateCore m s t q), norm_nonneg q]

/-- The contractive weighted Bessel coordinate map on the Schwartz fiber core. -/
def fiberDualCoordinateCoreL (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberCore m s t →L[ℂ] L2 ℝ volume :=
  LinearMap.mkContinuous (fiberDualCoordinateCore m s t) 1 fun q ↦ by
    simpa using norm_fiberDualCoordinateCore_le m s t q

/-- The weighted Bessel coordinate map, extended to the completed fiber Hilbert space. -/
def fiberDualCoordinate (m : ℕ) [NeZero m] (s t : ℝ) :
    FiberSpace m s t →L[ℂ] L2 ℝ volume :=
  (fiberDualCoordinateCoreL m s t).extend
    (UniformSpace.Completion.toComplL : FiberCore m s t →L[ℂ] FiberSpace m s t)

@[simp]
theorem fiberDualCoordinate_coe (m : ℕ) [NeZero m] (s t : ℝ) (q : FiberCore m s t) :
    fiberDualCoordinate m s t (q : FiberSpace m s t) = fiberDualCoordinateCore m s t q := by
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
  let q : FiberCore m s t := fiberDualSchwartzPreimage s t f
  refine ⟨(q : FiberSpace m s t), ?_⟩
  rw [fiberDualCoordinate_coe]
  exact fiberDualCoordinateCoreValue_fiberDualSchwartzPreimage s t f

theorem norm_fiberDualCoordinate_le (m : ℕ) [NeZero m] (s t : ℝ)
    (q : FiberSpace m s t) : ‖fiberDualCoordinate m s t q‖ ≤ ‖q‖ := by
  refine (denseRange_fiberCore_coe m s t).induction_on q ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro q
    simpa using norm_fiberDualCoordinateCore_le m s t q

theorem norm_star_L2 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : L2 α μ) :
    ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    eLpNorm (star f : L2 α μ) 2 μ = eLpNorm (star fun x ↦ f x) 2 μ :=
      eLpNorm_congr_ae (Lp.coeFn_star f)
    _ = eLpNorm f 2 μ := eLpNorm_star

/-- Equation (8): the activation-induced functional on the fiber Hilbert space. -/
def activationFiberFunctional (m : ℕ) [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) :
    FiberSpace m s t →L[ℂ] ℂ :=
  ((2 * Real.pi : ℂ) ^ (m - 1)) •
    ((innerSL ℂ (star σ)).comp (fiberDualCoordinate m s t))

@[simp]
theorem activationFiberFunctional_coe (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (q : FiberCore m s t) :
    activationFiberFunctional m s t σ (q : FiberSpace m s t) =
      (2 * Real.pi : ℂ) ^ (m - 1) *
        inner ℂ (star σ) (fiberDualCoordinateCoreValue s t q) := by
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
  ext q
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
  ext q
  simp [activationFiberFunctional, hstar]
  ring

/-- Equation (9), the operator-norm form of the activation--fiber dual estimate. -/
theorem norm_activationFiberFunctional_le (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    ‖activationFiberFunctional m s t σ‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro q
    calc
      ‖activationFiberFunctional m s t σ q‖ =
          (2 * Real.pi) ^ (m - 1) *
            ‖inner ℂ (star σ) (fiberDualCoordinate m s t q)‖ := by
        simp [activationFiberFunctional, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      _ ≤ (2 * Real.pi) ^ (m - 1) *
          (‖star σ‖ * ‖fiberDualCoordinate m s t q‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = (2 * Real.pi) ^ (m - 1) *
          (‖σ‖ * ‖fiberDualCoordinate m s t q‖) := by
        rw [norm_star_L2]
      _ ≤ (2 * Real.pi) ^ (m - 1) * (‖σ‖ * ‖q‖) := by
        gcongr
        exact norm_fiberDualCoordinate_le m s t q
      _ = (2 * Real.pi) ^ (m - 1) * ‖σ‖ * ‖q‖ := by ring

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
