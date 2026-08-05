/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Data.Real.Sign

/-!
# The Dirichlet integral

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib knows the function `Real.sinc x = sin x / x` and its elementary bounds, but not the
**Dirichlet integral**
$$`\int_0^\infty \frac{\sin t}{t}\,dt=\frac\pi2,`
which only exists as an improper (not Lebesgue) integral. This file proves it, together with
the two companion facts that any application to conditionally convergent Fourier integrals
needs: a *uniform* bound on the partial integrals, and the behaviour of the tail
$`\int_a^\infty\sin u/u\,du` as `a → 0`.

## Main results

* `MeasureTheory.tendsto_intervalIntegral_sin_div_atTop` (**the Dirichlet integral**):
  `∫₀^R sin t / t dt → π/2` as `R → ∞`. Proved by the Laplace representation
  `1/t = ∫₀^∞ e^{-ut} du`, Fubini on `(0, R] × (0, ∞)`, the elementary primitive of
  `t ↦ e^{-ut} sin t`, the arctangent integral `∫₀^∞ du/(1+u²) = π/2`, and the `O(1/R)` bound on
  the remaining error term.
* `MeasureTheory.abs_intervalIntegral_sin_div_le`: the uniform bound
  `|∫_a^b sin u / u du| ≤ 3` for all `0 ≤ a ≤ b`, from `|sin u / u| ≤ 1` on short intervals and
  integration by parts (`|∫_a^b sin u/u du| ≤ 2/a` for `1 ≤ a`) on long ones.
* `MeasureTheory.sinDivTail`, `MeasureTheory.continuous_sinDivTail`,
  `MeasureTheory.tendsto_intervalIntegral_sin_div_atTop_left`,
  `MeasureTheory.abs_sinDivTail_le`, `MeasureTheory.tendsto_sinDivTail_nhds_zero`: the tail
  `∫_a^∞ sin u / u du` as an explicit function of `a`, its limit description, its uniform bound,
  and its limit `π/2` as `a → 0`.
* `MeasureTheory.intervalIntegral_sin_mul_div_eq`: the scaling and oddness relation
  `∫_ε^R sin(tω)/t dt = sign ω ⬝ ∫_{ε|ω|}^{R|ω|} sin u / u du`, which turns the above into the
  frequency-dependent statements used by principal-value Fourier computations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace MeasureTheory

/-- Laplace representation of `1/t` for `t > 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(u * t)) = t⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -t) (by linarith) 0
  rw [show (∫ u in Ioi (0 : ℝ), Real.exp (-(u * t)))
      = ∫ u in Ioi (0 : ℝ), Real.exp (-t * u) from by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [neg_mul, mul_comm]] at *
  rw [h]
  simp

/-- The exact primitive of `t ↦ e^{-ut} sin t`. -/
theorem intervalIntegral_exp_neg_mul_sin (u R : ℝ) :
    (∫ t in (0 : ℝ)..R, Real.exp (-(u * t)) * Real.sin t)
      = (1 - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)) / (1 + u ^ 2) := by
  have hA : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  set F : ℝ → ℝ := fun t =>
    -(Real.exp (-(u * t)) * (u * Real.sin t + Real.cos t)) / (1 + u ^ 2) with hF_def
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.exp (-(u * t)) * Real.sin t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(u * t)))
        (Real.exp (-(u * t)) * -u) t := by
      have h := (((hasDerivAt_id t).const_mul u).neg).exp
      simpa using h
    have h2 : HasDerivAt (fun t : ℝ => u * Real.sin t + Real.cos t)
        (u * Real.cos t + -Real.sin t) t :=
      ((Real.hasDerivAt_sin t).const_mul u).add (Real.hasDerivAt_cos t)
    have h3 := ((h1.mul h2).neg).div_const (1 + u ^ 2)
    refine h3.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [hF_def]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

/-- Joint integrability of the Laplace kernel on `(0, R] × (0, ∞)`. -/
theorem integrable_exp_neg_mul_sin_prod {R : ℝ} (_hR : 0 ≤ R) :
    Integrable (Function.uncurry fun (t u : ℝ) => Real.exp (-(u * t)) * Real.sin t)
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have haesm : AEStronglyMeasurable
      (Function.uncurry fun (t u : ℝ) => Real.exp (-(u * t)) * Real.sin t)
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Continuous.aestronglyMeasurable ?_
    exact (Real.continuous_exp.comp (by fun_prop)).mul (Real.continuous_sin.comp continuous_fst)
  have hexp : ∀ t : ℝ, 0 < t →
      IntegrableOn (fun u : ℝ => Real.exp (-(u * t))) (Ioi 0) volume := by
    intro t ht0
    have h : IntegrableOn (fun u : ℝ => Real.exp (-t * u)) (Ioi 0) volume :=
      integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [mul_comm]
  have hsinle : ∀ t : ℝ, 0 < t → |Real.sin t| ≤ t := by
    intro t ht0
    have h := Real.abs_sinc_le_one t
    rw [Real.sinc_of_ne_zero ht0.ne', abs_div, abs_of_pos ht0] at h
    exact (div_le_one ht0).mp h
  have hfiber : ∀ t : ℝ, 0 < t →
      Integrable (fun u : ℝ => Real.exp (-(u * t)) * Real.sin t)
        (volume.restrict (Ioi (0 : ℝ))) := fun t ht0 => (hexp t ht0).mul_const _
  have hbd : ∀ t ∈ Ioc (0 : ℝ) R,
      (∫ u in Ioi (0 : ℝ), ‖Real.exp (-(u * t)) * Real.sin t‖) ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hcongr : (∫ u in Ioi (0 : ℝ), ‖Real.exp (-(u * t)) * Real.sin t‖)
        = (∫ u in Ioi (0 : ℝ), Real.exp (-(u * t))) * |Real.sin t| := by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [hcongr, integral_exp_neg_mul_Ioi_zero ht0, inv_mul_le_iff₀ ht0, mul_one]
    exact hsinle t ht0
  rw [integrable_prod_iff haesm]
  refine ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    exact hfiber t ht.1
  · refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ haesm.norm.integral_prod_right' ?_
    · refine integrableOn_const ?_
      exact measure_Ioc_lt_top.ne
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hnn : (0 : ℝ) ≤ ∫ u in Ioi (0 : ℝ), ‖Real.exp (-(u * t)) * Real.sin t‖ :=
        integral_nonneg fun u => norm_nonneg _
      exact (abs_of_nonneg hnn).trans_le (hbd t ht)


/-- The Laplace (Fubini) form of the Dirichlet partial integral. -/
theorem intervalIntegral_sin_div_eq_integral_Ioi {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, Real.sin t / t)
      = ∫ u in Ioi (0 : ℝ),
          (1 - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)) / (1 + u ^ 2) := by
  have hstep1 : (∫ t in (0 : ℝ)..R, Real.sin t / t)
      = ∫ t in Ioc (0 : ℝ) R, ∫ u in Ioi (0 : ℝ), Real.exp (-(u * t)) * Real.sin t := by
    rw [intervalIntegral.integral_of_le hR]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [integral_mul_const, integral_exp_neg_mul_Ioi_zero ht0, div_eq_inv_mul]
  have hstep2 : (∫ t in Ioc (0 : ℝ) R, ∫ u in Ioi (0 : ℝ), Real.exp (-(u * t)) * Real.sin t)
      = ∫ u in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) R, Real.exp (-(u * t)) * Real.sin t :=
    integral_integral_swap (integrable_exp_neg_mul_sin_prod hR)
  have hstep3 : ∀ u : ℝ, (∫ t in Ioc (0 : ℝ) R, Real.exp (-(u * t)) * Real.sin t)
      = (1 - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)) / (1 + u ^ 2) := by
    intro u
    rw [← intervalIntegral.integral_of_le hR]
    exact intervalIntegral_exp_neg_mul_sin u R
  rw [hstep1, hstep2]
  exact integral_congr_ae (Filter.Eventually.of_forall hstep3)

/-- The elementary bound `(1 + u) / (1 + u²) ≤ 3/2`. -/
theorem one_add_div_one_add_sq_le (u : ℝ) : (1 + u) / (1 + u ^ 2) ≤ 3 / 2 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (u - 1), sq_nonneg u]

/-- **The Dirichlet integral**: `∫₀^R sin t / t dt → π/2` as `R → ∞`. -/
theorem tendsto_intervalIntegral_sin_div_atTop :
    Filter.Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.sin t / t) atTop
      (𝓝 (Real.pi / 2)) := by
  have hπ : (∫ u in Ioi (0 : ℝ), ((1 : ℝ) + u ^ 2)⁻¹) = Real.pi / 2 := by
    rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have hint1 : IntegrableOn (fun u : ℝ => ((1 : ℝ) + u ^ 2)⁻¹) (Ioi 0) volume :=
    integrable_inv_one_add_sq.integrableOn
  -- the error term
  set E : ℝ → ℝ := fun R => ∫ u in Ioi (0 : ℝ),
    Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R) / (1 + u ^ 2) with hE_def
  have hexpint : ∀ R : ℝ, 0 < R →
      IntegrableOn (fun u : ℝ => (3 / 2) * Real.exp (-(u * R))) (Ioi 0) volume := by
    intro R hR
    have h : IntegrableOn (fun u : ℝ => Real.exp (-R * u)) (Ioi 0) volume :=
      integrableOn_exp_mul_Ioi (a := -R) (by linarith) 0
    have h' : IntegrableOn (fun u : ℝ => Real.exp (-(u * R))) (Ioi 0) volume := by
      refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
      simp [mul_comm]
    exact h'.const_mul _
  have hpt : ∀ R : ℝ, 0 < R → ∀ u : ℝ, 0 < u →
      ‖Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R) / (1 + u ^ 2)‖
        ≤ (3 / 2) * Real.exp (-(u * R)) := by
    intro R hR u hu
    have hA : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have hnum : |Real.cos R + u * Real.sin R| ≤ 1 + u := by
      have h1 : |Real.cos R| ≤ 1 := Real.abs_cos_le_one R
      have h2 : |u * Real.sin R| ≤ u := by
        rw [abs_mul, abs_of_pos hu]
        exact mul_le_of_le_one_right hu.le (Real.abs_sin_le_one R)
      exact (abs_add_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos hA, div_le_iff₀ hA]
    calc Real.exp (-(u * R)) * |Real.cos R + u * Real.sin R|
        ≤ Real.exp (-(u * R)) * (1 + u) :=
          mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
      _ ≤ Real.exp (-(u * R)) * ((3 / 2) * (1 + u ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [← div_le_iff₀ (by positivity : (0:ℝ) < 1 + u ^ 2)] at *
          exact one_add_div_one_add_sq_le u
      _ = (3 / 2) * Real.exp (-(u * R)) * (1 + u ^ 2) := by ring
  have hEbd : ∀ R : ℝ, 0 < R → ‖E R‖ ≤ (3 / 2) / R := by
    intro R hR
    have h := norm_integral_le_of_norm_le (hexpint R hR)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun u hu => hpt R hR u hu))
    refine h.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero hR]
    ring
  -- the partial integrals differ from `π/2` by the error term
  have hsplit : ∀ R : ℝ, 0 < R → (∫ t in (0 : ℝ)..R, Real.sin t / t) = Real.pi / 2 - E R := by
    intro R hR
    rw [intervalIntegral_sin_div_eq_integral_Ioi hR.le, ← hπ, hE_def]
    have hcongr : ∀ u : ℝ,
        (1 - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)) / (1 + u ^ 2)
          = ((1 : ℝ) + u ^ 2)⁻¹
            - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R) / (1 + u ^ 2) := by
      intro u
      field_simp
    rw [show (∫ u in Ioi (0 : ℝ),
        (1 - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)) / (1 + u ^ 2))
        = ∫ u in Ioi (0 : ℝ), (((1 : ℝ) + u ^ 2)⁻¹
          - Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R) / (1 + u ^ 2)) from
      integral_congr_ae (Filter.Eventually.of_forall hcongr)]
    refine integral_sub hint1 ?_
    refine Integrable.mono' (hexpint R hR) ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).restrict
      exact ((by fun_prop : Continuous fun u : ℝ =>
        Real.exp (-(u * R)) * (Real.cos R + u * Real.sin R)).div
        (by fun_prop : Continuous fun u : ℝ => 1 + u ^ 2) fun u => by positivity)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun u hu => hpt R hR u hu)
  -- conclude by squeezing the error term
  have hEtendsto : Filter.Tendsto E atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun R : ℝ => (3 / 2) / R) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
      exact hEbd R hR
    · have h : Filter.Tendsto (fun R : ℝ => (3 / 2) * R⁻¹) atTop (𝓝 ((3 / 2) * 0)) :=
        Filter.Tendsto.const_mul _ tendsto_inv_atTop_zero
      rw [mul_zero] at h
      refine h.congr fun R => ?_
      ring
  have hfinal : Filter.Tendsto (fun R : ℝ => Real.pi / 2 - E R) atTop (𝓝 (Real.pi / 2)) := by
    have h := (tendsto_const_nhds (x := Real.pi / 2) (f := (atTop : Filter ℝ))).sub hEtendsto
    rw [sub_zero] at h
    exact h
  refine hfinal.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  exact (hsplit R hR).symm


/-- `|sin u / u| ≤ 1`. -/
theorem abs_sin_div_le_one (u : ℝ) : |Real.sin u / u| ≤ 1 := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · have h := Real.abs_sinc_le_one u
    rwa [Real.sinc_of_ne_zero hu] at h

/-- `u ↦ sin u / u` is interval integrable (it agrees with the continuous `sinc` off `0`). -/
theorem intervalIntegrable_sin_div (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.sin u / u) volume a b := by
  have hc : IntervalIntegrable Real.sinc volume a b :=
    Real.continuous_sinc.intervalIntegrable a b
  have hae : ∀ᵐ u : ℝ ∂volume, Real.sinc u = Real.sin u / u := by
    have hnull : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      refine mem_ae_iff.mpr ?_
      rw [show {u : ℝ | u ≠ 0}ᶜ = {(0 : ℝ)} from by ext u; simp]
      exact Real.volume_singleton
    filter_upwards [hnull] with u hu
    exact Real.sinc_of_ne_zero hu
  exact ⟨hc.1.congr_fun_ae (ae_restrict_of_ae hae), hc.2.congr_fun_ae (ae_restrict_of_ae hae)⟩

/-- Integration by parts gives the decay `|∫_a^b sin u / u du| ≤ 2/a` for `1 ≤ a ≤ b`. -/
theorem abs_intervalIntegral_sin_div_le_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |∫ u in a..b, Real.sin u / u| ≤ 2 / a := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have hmem : ∀ x ∈ Set.uIcc a b, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha0 hx.1
  -- integration by parts with `u = x⁻¹`, `v = -cos x`
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := fun x hx =>
    hasDerivAt_inv (hmem x hx).ne'
  have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _
    have h := (Real.hasDerivAt_cos x).neg
    rw [neg_neg] at h
    exact h
  have hu' : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹) volume a b := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
    exact pow_ne_zero 2 (hmem x hx).ne'
  have hv' : IntervalIntegrable Real.sin volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : (∫ x in a..b, x⁻¹ * Real.sin x) = ∫ u in a..b, Real.sin u / u := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [div_eq_inv_mul]
  -- the remaining integral is bounded by `∫ x⁻²`
  have hsq : (∫ x in a..b, (x ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
    have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
      intro x hx
      have h := (hasDerivAt_inv (hmem x hx).ne').neg
      rw [neg_neg] at h
      exact h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    · ring
    · refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
      exact pow_ne_zero 2 (hmem x hx).ne'
  have hrem : |∫ x in a..b, -(x ^ 2)⁻¹ * -Real.cos x| ≤ a⁻¹ - b⁻¹ := by
    have hbd : ∀ x ∈ Set.Icc a b, |(-(x ^ 2)⁻¹ * -Real.cos x)| ≤ (x ^ 2)⁻¹ := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hmem x (by rw [Set.uIcc_of_le hab]; exact hx)
      rw [neg_mul_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (x ^ 2)⁻¹)]
      calc (x ^ 2)⁻¹ * |Real.cos x| ≤ (x ^ 2)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (by positivity)
        _ = (x ^ 2)⁻¹ := by ring
    have hint1 : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹ * -Real.cos x) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_))
        (by fun_prop)
      exact pow_ne_zero 2 (hmem x hx).ne'
    have hint2 : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
      refine ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
      exact pow_ne_zero 2 (hmem x hx).ne'
    rw [abs_le]
    constructor
    · rw [neg_le, ← hsq, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on hab hint1.neg hint2 fun x hx => ?_
      have := hbd x hx
      rw [abs_le] at this
      linarith [this.1]
    · rw [← hsq]
      refine intervalIntegral.integral_mono_on hab hint1 hint2 fun x hx => ?_
      have := hbd x hx
      rw [abs_le] at this
      linarith [this.2]
  rw [← hlhs, hparts]
  have h1 : |b⁻¹ * -Real.cos b| ≤ b⁻¹ := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < b⁻¹), abs_neg]
    calc b⁻¹ * |Real.cos b| ≤ b⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one b) (by positivity)
      _ = b⁻¹ := by ring
  have h2 : |a⁻¹ * -Real.cos a| ≤ a⁻¹ := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < a⁻¹), abs_neg]
    calc a⁻¹ * |Real.cos a| ≤ a⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one a) (by positivity)
      _ = a⁻¹ := by ring
  have hab' : b⁻¹ ≤ a⁻¹ := by gcongr
  calc |b⁻¹ * -Real.cos b - a⁻¹ * -Real.cos a - ∫ x in a..b, -(x ^ 2)⁻¹ * -Real.cos x|
      ≤ |b⁻¹ * -Real.cos b| + |a⁻¹ * -Real.cos a| +
        |∫ x in a..b, -(x ^ 2)⁻¹ * -Real.cos x| := by
        refine le_trans (abs_sub _ _) ?_
        gcongr
        exact abs_sub _ _
    _ ≤ b⁻¹ + a⁻¹ + (a⁻¹ - b⁻¹) := by gcongr
    _ = 2 / a := by field_simp; ring


/-- **Uniform bound on the partial Dirichlet integrals**: `|∫_a^b sin u / u du| ≤ 3` for all
`0 ≤ a ≤ b`. -/
theorem abs_intervalIntegral_sin_div_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |∫ u in a..b, Real.sin u / u| ≤ 3 := by
  have hshort : ∀ c d : ℝ, |c - d| ≤ 1 →
      |∫ u in d..c, Real.sin u / u| ≤ 1 := by
    intro c d hcd
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1) (f := fun u : ℝ => Real.sin u / u) (a := d) (b := c)
      (fun x _ => by rw [Real.norm_eq_abs]; exact abs_sin_div_le_one x)
    rw [Real.norm_eq_abs] at h
    calc |∫ u in d..c, Real.sin u / u| ≤ 1 * |c - d| := h
      _ ≤ 1 := by rw [one_mul]; exact hcd
  set c : ℝ := max a 1 with hc_def
  have hac : a ≤ c := le_max_left _ _
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hca : |c - a| ≤ 1 := by
    rcases le_total a 1 with h | h
    · rw [hc_def, max_eq_right h, abs_of_nonneg (by linarith)]
      linarith
    · rw [hc_def, max_eq_left h]
      simp
  by_cases hb : c ≤ b
  · have hsum : (∫ u in a..c, Real.sin u / u) + (∫ u in c..b, Real.sin u / u)
        = ∫ u in a..b, Real.sin u / u :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_sin_div a c) (intervalIntegrable_sin_div c b)
    have h1 : |∫ u in a..c, Real.sin u / u| ≤ 1 := hshort c a hca
    have h2 : |∫ u in c..b, Real.sin u / u| ≤ 2 / c :=
      abs_intervalIntegral_sin_div_le_of_one_le hc1 hb
    have h3 : (2 : ℝ) / c ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc |∫ u in a..b, Real.sin u / u|
        = |(∫ u in a..c, Real.sin u / u) + (∫ u in c..b, Real.sin u / u)| := by rw [hsum]
      _ ≤ |∫ u in a..c, Real.sin u / u| + |∫ u in c..b, Real.sin u / u| := abs_add_le _ _
      _ ≤ 1 + 2 := by linarith
      _ = 3 := by norm_num
  · -- then `b < c`, so `b ≤ 1` and the whole interval is short
    have hb1 : |b - a| ≤ 1 := by
      have hbc : b < c := lt_of_not_ge hb
      rcases le_total a 1 with h | h
      · rw [hc_def, max_eq_right h] at hbc
        rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [hc_def, max_eq_left h] at hbc
        exact absurd hab (not_le.mpr hbc)
    exact le_trans (hshort b a hb1) (by norm_num)

/-- The tail of the Dirichlet integral, `∫_a^∞ sin u / u du`, expressed through the Dirichlet
value `π/2`. -/
def sinDivTail (a : ℝ) : ℝ := Real.pi / 2 - ∫ u in (0 : ℝ)..a, Real.sin u / u

/-- The Dirichlet tail is continuous. -/
theorem continuous_sinDivTail : Continuous sinDivTail := by
  unfold sinDivTail
  exact continuous_const.sub
    (intervalIntegral.continuous_primitive intervalIntegrable_sin_div 0)

/-- The tail is the limit of the partial integrals `∫_a^R sin u / u du` as `R → ∞`. -/
theorem tendsto_intervalIntegral_sin_div_atTop_left (a : ℝ) :
    Filter.Tendsto (fun R : ℝ => ∫ u in a..R, Real.sin u / u) atTop (𝓝 (sinDivTail a)) := by
  have hsplit : ∀ R : ℝ, (∫ u in a..R, Real.sin u / u)
      = (∫ u in (0 : ℝ)..R, Real.sin u / u) - ∫ u in (0 : ℝ)..a, Real.sin u / u := by
    intro R
    have h := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := fun u : ℝ => Real.sin u / u)
      (intervalIntegrable_sin_div 0 a) (intervalIntegrable_sin_div a R)
    linarith [h]
  have h := tendsto_intervalIntegral_sin_div_atTop.sub
    (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..a, Real.sin u / u) (f := (atTop : Filter ℝ)))
  refine h.congr fun R => (hsplit R).symm

/-- The Dirichlet tail is uniformly bounded. -/
theorem abs_sinDivTail_le {a : ℝ} (ha : 0 ≤ a) : |sinDivTail a| ≤ 3 := by
  have hlim : Filter.Tendsto (fun R : ℝ => |∫ u in a..R, Real.sin u / u|) atTop
      (𝓝 |sinDivTail a|) :=
    (continuous_abs.tendsto _).comp (tendsto_intervalIntegral_sin_div_atTop_left a)
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop a] with R hR
  exact abs_intervalIntegral_sin_div_le ha hR

/-- The Dirichlet tail tends to the Dirichlet value `π/2` as the inner cut-off shrinks. -/
theorem tendsto_sinDivTail_nhds_zero :
    Filter.Tendsto sinDivTail (𝓝 (0 : ℝ)) (𝓝 (Real.pi / 2)) := by
  have h0 : Filter.Tendsto (fun a : ℝ => ∫ u in (0 : ℝ)..a, Real.sin u / u) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun a : ℝ => |a|) ?_ ?_
    · refine Filter.Eventually.of_forall fun a => ?_
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := 1) (f := fun u : ℝ => Real.sin u / u) (a := (0 : ℝ)) (b := a)
        (fun x _ => by rw [Real.norm_eq_abs]; exact abs_sin_div_le_one x)
      simpa using h
    · have h := continuous_abs.tendsto (0 : ℝ)
      simpa using h
  have h := (tendsto_const_nhds (x := Real.pi / 2) (f := (𝓝 (0 : ℝ)))).sub h0
  rw [sub_zero] at h
  exact h

/-- Scaling and oddness of the partial Dirichlet integrals in the frequency variable. -/
theorem intervalIntegral_sin_mul_div_eq (ω : ℝ) (hω : ω ≠ 0) (ε R : ℝ) (hε : 0 < ε)
    (hεR : ε ≤ R) :
    (∫ t in ε..R, Real.sin (t * ω) / t)
      = Real.sign ω * ∫ u in (ε * |ω|)..(R * |ω|), Real.sin u / u := by
  have key : ∀ c : ℝ, 0 < c →
      (∫ t in ε..R, Real.sin (t * c) / t) = ∫ u in (ε * c)..(R * c), Real.sin u / u := by
    intro c hc
    have hcongr : (∫ t in ε..R, Real.sin (t * c) / t)
        = ∫ t in ε..R, c * (Real.sin (t * c) / (t * c)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hεR] at ht
      have ht0 : t ≠ 0 := by
        have : 0 < t := lt_of_lt_of_le hε ht.1
        exact this.ne'
      field_simp
    rw [hcongr, intervalIntegral.integral_const_mul]
    have hsub := intervalIntegral.integral_comp_mul_right
      (f := fun u : ℝ => Real.sin u / u) (a := ε) (b := R) hc.ne'
    rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · have habs : |ω| = -ω := abs_of_neg hneg
    have hodd : (∫ t in ε..R, Real.sin (t * ω) / t)
        = -∫ t in ε..R, Real.sin (t * (-ω)) / t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [mul_neg, Real.sin_neg]
      ring
    rw [hodd, key (-ω) (by linarith), habs, Real.sign_of_neg hneg]
    ring
  · rw [key ω hpos, abs_of_pos hpos, Real.sign_of_pos hpos, one_mul]

end MeasureTheory
