/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.PaperDistribution
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The paper Fourier transform on `L²(ℝ)`

The paper-normalized Fourier transform `f ↦ f♯` extends from the Schwartz class to a continuous
linear map on `L²(ℝ)` with `‖f♯‖ = √(2π) ‖f‖`.  This file performs the extension, proves
compatibility with the distributional paper Fourier transform, and derives injectivity.  It is
used to define the manuscript isometry coordinates of concrete activations such as `tanh` and
ReLU.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate FourierTransform
open FourierTransform MeasureTheory TemperedDistribution

namespace LeanRidgelet.Fourier

/-! ### The paper Fourier transform on `L²(ℝ)` -/

/-- The paper-normalized Schwartz Fourier transform, bundled as a continuous linear map. -/
def paperFourierSchwartzCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realDilationCLE (2 * Real.pi)⁻¹ (inv_ne_zero two_mul_pi_ne_zero)) ∘L
    FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)

@[simp]
theorem paperFourierSchwartzCLM_apply (f : SchwartzMap ℝ ℂ) :
    paperFourierSchwartzCLM f = paperFourierSchwartz f := rfl

/-- The `L²` norm of a one-dimensional Schwartz function as an integral. -/
theorem norm_schwartz_toLp_two_sq (g : SchwartzMap ℝ ℂ) :
    ‖g.toLp 2 volume‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp 2 volume] with x hx
  rw [hx, inner_self_eq_norm_sq]

/-- Plancherel bound for the paper Schwartz transform in the `L²` norm. -/
theorem norm_toLp_paperFourierSchwartz_le (f : SchwartzMap ℝ ℂ) :
    ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L
        paperFourierSchwartzCLM).toLinearMap f‖ ≤
      Real.sqrt (2 * Real.pi) *
        ‖(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap f‖ := by
  have hsq : ‖(paperFourierSchwartz f).toLp 2 volume‖ ^ 2 =
      2 * Real.pi * ‖f.toLp 2 volume‖ ^ 2 := by
    rw [norm_schwartz_toLp_two_sq, norm_schwartz_toLp_two_sq]
    have hplancherel := paper_plancherel_schwartz_inner (V := ℝ) f
    rw [Module.finrank_self, pow_one] at hplancherel
    rw [← hplancherel]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [paperFourierSchwartz_eq_paperFourierIntegralInner]
  have hle : ‖(paperFourierSchwartz f).toLp 2 volume‖ =
      Real.sqrt (2 * Real.pi) * ‖f.toLp 2 volume‖ := by
    have h1 : (0 : ℝ) ≤ ‖(paperFourierSchwartz f).toLp 2 volume‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * ‖f.toLp 2 volume‖ := by positivity
    apply sq_eq_sq₀ h1 h2 |>.mp
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hsq]
  exact le_of_eq hle

/-- The paper Fourier transform on `L²(ℝ)`, extended from the Schwartz class by density. -/
def paperFourierLp : L2 ℝ volume →L[ℂ] L2 ℝ volume :=
  LinearMap.extendOfNorm
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L paperFourierSchwartzCLM).toLinearMap
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

theorem denseRange_toLpCLM_toLinearMap :
    DenseRange (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

/-- The `L²` paper Fourier transform agrees with the Schwartz transform on the Schwartz class. -/
theorem paperFourierLp_toLp (f : SchwartzMap ℝ ℂ) :
    paperFourierLp (f.toLp 2 volume) = (paperFourierSchwartz f).toLp 2 volume := by
  have h := LinearMap.extendOfNorm_eq
    (f := (SchwartzMap.toLpCLM ℂ ℂ 2 volume ∘L paperFourierSchwartzCLM).toLinearMap)
    (e := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap)
    denseRange_toLpCLM_toLinearMap
    ⟨Real.sqrt (2 * Real.pi), norm_toLp_paperFourierSchwartz_le⟩ f
  simpa [paperFourierLp] using h

/-- The `L²` paper Fourier transform agrees with the distributional paper Fourier transform. -/
theorem toTemperedDistribution_paperFourierLp (f : L2 ℝ volume) :
    Lp.toTemperedDistributionCLM ℂ volume 2 (paperFourierLp f) =
      paperFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).induction_on f
    ?_ ?_
  · apply isClosed_eq
    · exact ((Lp.toTemperedDistributionCLM ℂ volume 2).comp paperFourierLp).continuous
    · exact (paperFourierDistribution.comp
        (Lp.toTemperedDistributionCLM ℂ volume 2)).continuous
  · intro g
    change Lp.toTemperedDistributionCLM ℂ volume 2 (paperFourierLp (g.toLp 2 volume)) =
      paperFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 (g.toLp 2 volume))
    rw [paperFourierLp_toLp]
    change Lp.toTemperedDistribution ((paperFourierSchwartz g).toLp 2 volume) =
      paperFourierDistribution (Lp.toTemperedDistribution (g.toLp 2 volume))
    rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
    exact (paperFourierDistribution_toTemperedDistributionCLM_eq g).symm

/-- The `L²` paper Fourier transform is injective. -/
theorem paperFourierLp_injective : Function.Injective paperFourierLp := by
  intro f g hfg
  have hdist : Lp.toTemperedDistributionCLM ℂ volume 2 f =
      Lp.toTemperedDistributionCLM ℂ volume 2 g := by
    have h1 := toTemperedDistribution_paperFourierLp f
    have h2 := toTemperedDistribution_paperFourierLp g
    have h3 : paperFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 f) =
        paperFourierDistribution (Lp.toTemperedDistributionCLM ℂ volume 2 g) := by
      rw [← h1, ← h2, hfg]
    have h4 := congrArg paperFourierInvDistribution h3
    rwa [paperFourierInvDistribution_paperFourierDistribution,
      paperFourierInvDistribution_paperFourierDistribution] at h4
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℝ)))
  exact hdist

end LeanRidgelet.Fourier
