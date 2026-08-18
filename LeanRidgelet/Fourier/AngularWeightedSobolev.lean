/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.ToMathlib.WeightedSobolevOneDim

/-!
# The weighted Sobolev identity in the angular convention

`LeanRidgelet.ToMathlib.WeightedSobolevOneDim` proves, in Mathlib's Fourier convention, that the
`L²` norm of the `k`-th derivative of a function on the line is the `L²` norm of its Fourier
transform weighted by the `k`-th power of the frequency.  This file restates it in the angular
convention of this development, where the weight is the bare `k`-th power of the frequency and the
conversion factor is the one the angular Plancherel theorem already fixes.  It lives outside
`ToMathlib` because the convention bridge is project material and `ToMathlib` imports only Mathlib.

The identity is what turns a derivative bound on a ridgelet-type transform in an additive parameter
into a bound in a frequency-weighted coefficient space; the development plan records how the
smoothness index enters there.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LeanRidgelet.Fourier

/-- In the angular convention `g♯ ζ = ∫ z, e^{-i z ζ} g z dz` the Fourier transform of the
`k`-th derivative is `(iζ)^k` times the transform: the `2π` of
`Real.fourier_iteratedDeriv` is cancelled by the frequency rescaling of the bridge
`angularFourierIntegralInner_eq_fourier`. -/
theorem angularFourierIntegralInner_iteratedDeriv {g : ℝ → ℂ} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (ζ : ℝ) :
    angularFourierIntegralInner (iteratedDeriv k g) ζ
      = (Complex.I * ζ) ^ k • angularFourierIntegralInner g ζ := by
  have hF := congrFun (Real.fourier_iteratedDeriv hg hint hk) (((2 * Real.pi)⁻¹ : ℝ) • ζ)
  rw [angularFourierIntegralInner_eq_fourier, hF, angularFourierIntegralInner_eq_fourier]
  congr 2
  rw [smul_eq_mul]
  push_cast
  field_simp

/-- **The one-variable weighted Sobolev identity in the angular convention**, `lintegral` form:
`∫ ‖|ζ|^k g♯ ζ‖² dζ = 2π ∫ ‖g^{(k)} x‖² dx`.

The weight is the bare `|ζ|^k` and the whole normalization sits in the constant `2π`, which is
the Plancherel constant `(2π)^{dim ℝ}` of
`LeanRidgelet.Fourier.lintegral_enorm_angularFourierIntegralInner_sq`. -/
theorem lintegral_enorm_pow_smul_angularFourierIntegralInner_sq {g : ℝ → ℂ} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (hmem : MemLp (iteratedDeriv k g) 2 volume) :
    ∫⁻ ζ : ℝ, ‖(|ζ| ^ k : ℝ) • angularFourierIntegralInner g ζ‖ₑ ^ 2
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x : ℝ, ‖iteratedDeriv k g x‖ₑ ^ 2 := by
  have hnorm : ∀ ζ : ℝ, ‖(|ζ| ^ k : ℝ) • angularFourierIntegralInner g ζ‖ₑ
      = ‖angularFourierIntegralInner (iteratedDeriv k g) ζ‖ₑ := by
    intro ζ
    refine (MeasureTheory.enorm_eq_enorm_of_norm_eq ?_).symm
    rw [angularFourierIntegralInner_iteratedDeriv hg hint hk ζ, norm_smul, norm_smul, norm_pow,
      norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
      abs_abs, one_mul]
  calc ∫⁻ ζ : ℝ, ‖(|ζ| ^ k : ℝ) • angularFourierIntegralInner g ζ‖ₑ ^ 2
      = ∫⁻ ζ : ℝ, ‖angularFourierIntegralInner (iteratedDeriv k g) ζ‖ₑ ^ 2 :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun ζ => by
          beta_reduce
          rw [hnorm ζ])
    _ = ENNReal.ofReal ((2 * Real.pi) ^ Module.finrank ℝ ℝ) *
          ∫⁻ x : ℝ, ‖iteratedDeriv k g x‖ₑ ^ 2 :=
        lintegral_enorm_angularFourierIntegralInner_sq (hint k hk) hmem
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x : ℝ, ‖iteratedDeriv k g x‖ₑ ^ 2 := by
        rw [Module.finrank_self, pow_one]

/-- **The one-variable weighted Sobolev identity in the angular convention**, `eLpNorm` form:
`‖|ζ|^k g♯‖_{L²} = √(2π) ‖g^{(k)}‖_{L²}`. The constant is the square root of the Plancherel
constant `2π` of the angular convention; no new normalization is introduced. -/
theorem eLpNorm_pow_smul_angularFourierIntegralInner {g : ℝ → ℂ} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (hmem : MemLp (iteratedDeriv k g) 2 volume) :
    eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • angularFourierIntegralInner g ζ) 2 volume
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * eLpNorm (iteratedDeriv k g) 2 volume := by
  have hconst : ENNReal.ofReal (2 * Real.pi) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_pos (by positivity)]
  rw [MeasureTheory.eLpNorm_two_eq_rpow, MeasureTheory.eLpNorm_two_eq_rpow,
    lintegral_enorm_pow_smul_angularFourierIntegralInner_sq hg hint hk hmem,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hconst]

/-- The frequency-weighted angular Fourier transform of a function whose `k`-th derivative is
square-integrable is itself square-integrable. -/
theorem memLp_two_pow_smul_angularFourierIntegralInner {g : ℝ → ℂ} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (hmem : MemLp (iteratedDeriv k g) 2 volume) :
    MemLp (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • angularFourierIntegralInner g ζ) 2 volume := by
  have hg0 : Integrable g volume := by
    have h := hint 0 (by simp)
    rwa [iteratedDeriv_zero] at h
  have hcont : Continuous (angularFourierIntegralInner g) :=
    continuous_angularFourierIntegralInner hg0
  have hweight : Continuous fun ζ : ℝ => (|ζ| ^ k : ℝ) := by fun_prop
  refine ⟨(hweight.smul hcont).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_pow_smul_angularFourierIntegralInner hg hint hk hmem]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmem.eLpNorm_lt_top

/-- **The one-variable weighted Sobolev identity in the angular convention for Schwartz
functions**: `‖|ζ|^k g♯‖_{L²} = √(2π) ‖g^{(k)}‖_{L²}`, with every hypothesis automatic. -/
theorem eLpNorm_pow_smul_angularFourierIntegralInner_of_schwartz (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • angularFourierIntegralInner (⇑g) ζ) 2 volume
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
        eLpNorm (iteratedDeriv k ⇑g) 2 volume :=
  eLpNorm_pow_smul_angularFourierIntegralInner (N := ⊤) (g.smooth ⊤)
    (fun n _ => SchwartzMap.integrable_iteratedDeriv n g) le_top
    (SchwartzMap.memLp_two_iteratedDeriv k g)

/-- The frequency-weighted angular Fourier transform of a Schwartz function on `ℝ` is
square-integrable. -/
theorem memLp_two_pow_smul_angularFourierIntegralInner_of_schwartz (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    MemLp (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • angularFourierIntegralInner (⇑g) ζ) 2 volume :=
  memLp_two_pow_smul_angularFourierIntegralInner (N := ⊤) (g.smooth ⊤)
    (fun n _ => SchwartzMap.integrable_iteratedDeriv n g) le_top
    (SchwartzMap.memLp_two_iteratedDeriv k g)

end LeanRidgelet.Fourier
