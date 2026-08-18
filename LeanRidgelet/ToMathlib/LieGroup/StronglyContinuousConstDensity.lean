/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.ContinuousConstDensityPreimage
public import LeanRidgelet.ToMathlib.LieGroup.Schur
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Strong continuity of constant-density pullback representations

A continuously parametrized family of continuous self-maps that rescales a regular measure by a
finite positive constant acts strongly continuously on `L²` after multiplication by the inverse
square root of that constant.  The proof follows Mathlib's measure-preserving argument: first prove
continuity on indicators using convergence of preimages in symmetric-difference measure, extend to
simple functions, and finally use their density together with the fact that every represented
operator is an isometry.

The theorem is phrased for an already bundled unitary representation plus its a.e. action formula.
Thus it applies both to quasi-regular representations and to independently constructed unitary
models without imposing a second construction API.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
  {μ : Measure X} [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

namespace UnitaryRepresentation

/-- A determinant-corrected pullback formula with continuously varying positive constant density
is strongly continuous on scalar `L²`. -/
theorem isStronglyContinuous_of_const_density
    (π : UnitaryRepresentation G (Lp ℂ 2 μ)) (r : G → C(X, X)) (c : G → ℝ≥0)
    (hr : Continuous r) (hc : Continuous c) (hc_ne : ∀ g, c g ≠ 0)
    (hmap : ∀ g, μ.map (r g) = (c g : ℝ≥0∞) • μ)
    (happly : ∀ (g : G) (f : Lp ℂ 2 μ),
      ((π g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) f) =ᵐ[μ]
        fun x ↦ (((c g).sqrt : ℂ)⁻¹) • f (r g x)) :
    π.IsStronglyContinuous := by
  have hsqrt : Continuous fun g ↦ (c g).sqrt := by
    have hsqrt' : Continuous (NNReal.sqrt : ℝ≥0 → ℝ≥0) := by
      rw [show NNReal.sqrt = fun x : ℝ≥0 ↦ x ^ (1 / (2 : ℝ)) from
        funext NNReal.sqrt_eq_rpow]
      exact NNReal.continuous_rpow_const (show 0 ≤ (1 / (2 : ℝ)) by norm_num)
    exact hsqrt'.comp hc
  have hsqrt_complex : Continuous fun g ↦ ((c g).sqrt : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hsqrt)
  have hweight : Continuous fun g ↦ (((c g).sqrt : ℂ)⁻¹) :=
    hsqrt_complex.inv₀ fun g ↦ by simp [hc_ne g]
  have hjoint : Continuous fun fg : Lp ℂ 2 μ × G ↦
      (π fg.2 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) fg.1 := by
    refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (MeasureTheory.Lp.simpleFunc.dense (p := (2 : ℝ≥0∞)) (by norm_num)) ?_
      fun g ↦ (Unitary.linearIsometryEquiv (π g)).lipschitz
    intro f hf
    lift f to Lp.simpleFunc ℂ 2 μ using hf
    induction f using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
    | add hfm hgm _ ihf ihg =>
        convert ihf.add ihg using 1
        funext y
        exact (π y : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ).map_add _ _
    | @indicatorConst v s hs hμs =>
        rw [Lp.simpleFunc.coe_indicatorConst]
        have hpre_meas : ∀ g : G, MeasurableSet ((r g) ⁻¹' s) := fun g ↦
          hs.preimage (r g).continuous.measurable
        have hpre_top : ∀ g : G, μ ((r g) ⁻¹' s) ≠ ∞ := by
          intro g
          rw [measure_preimage_eq_nnreal_smul (hmap g) hs]
          exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hμs.lt_top).ne
        have hindicator : Continuous fun g ↦
            indicatorConstLp (μ := μ) 2 (hpre_meas g) (hpre_top g) v :=
          continuous_indicatorConstLp_set (by norm_num) fun g ↦
            tendsto_measure_symmDiff_preimage_nhds_zero_of_map_eq_nnreal_smul
              (hr.tendsto g) (hc.tendsto g) (.of_forall hmap) (hmap g) hs hμs.ne
        have heq : (fun g ↦
              (π g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
                (indicatorConstLp (μ := μ) 2 hs hμs.ne v)) =
            fun g ↦ (((c g).sqrt : ℂ)⁻¹) •
              indicatorConstLp (μ := μ) 2 (hpre_meas g) (hpre_top g) v := by
          funext g
          apply Lp.ext
          have hqmp : Measure.QuasiMeasurePreserving (r g) μ μ := by
            refine ⟨(r g).continuous.measurable, ?_⟩
            rw [hmap g]
            exact Measure.AbsolutelyContinuous.rfl.smul_left _
          have horiginal := hqmp.ae_eq
            (indicatorConstLp_coeFn (μ := μ) (p := (2 : ℝ≥0∞))
              (hs := hs) (hμs := hμs.ne) (c := v))
          have hpre := indicatorConstLp_coeFn (μ := μ) (p := (2 : ℝ≥0∞))
            (hs := hpre_meas g) (hμs := hpre_top g) (c := v)
          have hsmul := Lp.coeFn_smul (((c g).sqrt : ℂ)⁻¹)
            (indicatorConstLp (μ := μ) 2 (hpre_meas g) (hpre_top g) v)
          filter_upwards [happly g (indicatorConstLp (μ := μ) 2 hs hμs.ne v),
            horiginal, hpre, hsmul] with x hx horiginalx hprex hsmulx
          simp only [Function.comp_apply] at horiginalx
          simp only [Pi.smul_apply] at hsmulx
          rw [hx, hsmulx, horiginalx, hprex]
          rfl
        rw [heq]
        exact hweight.smul hindicator
  intro f
  exact hjoint.comp (continuous_const.prodMk continuous_id)

end UnitaryRepresentation
