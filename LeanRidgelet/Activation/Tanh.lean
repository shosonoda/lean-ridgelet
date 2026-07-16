/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Activation
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Hyperbolic-tangent activation

This file realizes the classical hyperbolic tangent as an activation coordinate in `A_{0,t}`.
The condition `1 / 2 < t` makes `⟨x⟩⁻ᵗ tanh x` square-integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- The weighted `L²` coordinate associated with the classical hyperbolic tangent. -/
def tanhWeightedFn (t : ℝ) (x : ℝ) : ℂ :=
  Complex.ofReal (japaneseBracketPow (-t) x * Real.tanh x)

theorem continuous_tanhWeightedFn (t : ℝ) : Continuous (tanhWeightedFn t) := by
  have hj : Continuous (japaneseBracketPow (-t) : ℝ → ℝ) := by
    unfold japaneseBracketPow
    apply Continuous.rpow_const
    · fun_prop
    · intro x
      left
      positivity
  have htanh : Continuous Real.tanh := by
    convert Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne') using 1
    funext x
    simpa only [Pi.div_apply] using Real.tanh_eq_sinh_div_cosh x
  exact Complex.continuous_ofReal.comp (hj.mul htanh)

theorem memLp_tanhWeightedFn (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    MemLp (tanhWeightedFn t) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_tanhWeightedFn t).aestronglyMeasurable).2
  apply (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := 2 * t) (by simp; linarith)).mono'
  · exact (continuous_tanhWeightedFn t).norm.pow 2 |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖tanhWeightedFn t x‖)]
    simp only [tanhWeightedFn, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (japaneseBracketPow_pos _ _)]
    have htanh : |Real.tanh x| ≤ 1 := (Real.abs_tanh_lt_one x).le
    rw [mul_pow]
    calc
      japaneseBracketPow (-t) x ^ 2 * |Real.tanh x| ^ 2 ≤
          japaneseBracketPow (-t) x ^ 2 * 1 ^ 2 := by gcongr
      _ = (1 + ‖x‖ ^ 2) ^ (-(2 * t) / 2) := by
        rw [japaneseBracketPow_sq]
        unfold japaneseBracketPow
        rw [show (2 * -t) / 2 = -(2 * t) / 2 by ring]
        simp

/-- The hyperbolic tangent as an activation coordinate in `A_{0,t}`. -/
def tanhActivation (t : ℝ) (ht : (1 : ℝ) / 2 < t) : ActivationSpace 0 t :=
  (memLp_tanhWeightedFn t ht).toLp (tanhWeightedFn t)

theorem tanhActivation_coe_ae (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    tanhActivation t ht =ᵐ[volume] tanhWeightedFn t :=
  (memLp_tanhWeightedFn t ht).coeFn_toLp

theorem tanhActivation_ne_zero (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    tanhActivation t ht ≠ 0 := by
  intro hσ
  have hzero : tanhActivation t ht =ᵐ[volume] (0 : ℝ → ℂ) :=
    Lp.eq_zero_iff_ae_eq_zero.mp hσ
  have hae : tanhWeightedFn t =ᵐ[volume] (0 : ℝ → ℂ) :=
    (tanhActivation_coe_ae t ht).symm.trans hzero
  have hfun : tanhWeightedFn t = 0 :=
    (Continuous.ae_eq_iff_eq volume (continuous_tanhWeightedFn t) continuous_zero).mp hae
  have hvalue := congrFun hfun 1
  have hweight : japaneseBracketPow (-t) (1 : ℝ) ≠ 0 :=
    (japaneseBracketPow_pos (-t) 1).ne'
  have htanh_one : Real.tanh 1 ≠ 0 := by
    intro hone
    have h := Real.tanh_injective (hone.trans Real.tanh_zero.symm)
    norm_num at h
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hweight htanh_one) hvalue

/-- The tempered-distribution realization of the hyperbolic tangent. -/
def tanhTemperedDistribution (t : ℝ) (ht : (1 : ℝ) / 2 < t) :
    TemperedDistribution ℝ ℂ :=
  activationDistribution 0 t (tanhActivation t ht)

/-- The distribution realization acts by integration against the classical `tanh` function. -/
theorem tanhTemperedDistribution_apply (t : ℝ) (ht : (1 : ℝ) / 2 < t)
    (g : SchwartzMap ℝ ℂ) :
    tanhTemperedDistribution t ht g =
      ∫ x : ℝ, g x * Complex.ofReal (Real.tanh x) := by
  have hbessel : paperBesselSymbol 0 = fun _ : ℝ ↦ 1 := by
    funext ξ
    simp [paperBesselSymbol]
  unfold tanhTemperedDistribution activationDistribution temperedWeightMultiplier
    paperBesselPotential
  simp only [neg_zero, ContinuousLinearMap.comp_apply]
  rw [hbessel, TemperedDistribution.fourierMultiplierCLM_const]
  simp only [one_smul, ContinuousLinearMap.id_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [tanhActivation_coe_ae t ht] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight t), hx]
  change temperedWeight t x * g x * tanhWeightedFn t x =
    g x * Complex.ofReal (Real.tanh x)
  rw [show temperedWeight t x * g x * tanhWeightedFn t x =
    g x * (temperedWeight t x * tanhWeightedFn t x) by ring]
  congr 1
  unfold tanhWeightedFn temperedWeight
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← mul_assoc, ← japaneseBracketPow_add]
  simp

theorem memActivationSpace_tanhTemperedDistribution (t : ℝ)
    (ht : (1 : ℝ) / 2 < t) :
    MemActivationSpace 0 t (tanhTemperedDistribution t ht) :=
  memActivationSpace_activationDistribution 0 t (tanhActivation t ht)

end LeanRidgelet
