/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# L1 theory: Fourier data of the truncated powers

The truncated powers `z₊^k` contain the unit step (`k = 0`) and the ReLU (`k = 1`). By the
Gel'fand--Shilov formula `(z₊^k)^ = k!/(iζ)^{k+1} + π i^k δ^{(k)}` their Fourier data away from
the origin is `k!/(iζ)^{k+1}` (`truncatedPowerFourier`, defined in `LeanRidgelet.L1.Defs`):
the Dirac part sits at the origin and is therefore invisible in the Lizorkin quotient.

## Main results

* `LeanRidgelet.l1_truncatedPower_hasFourierAwayFromOrigin`: the Gel'fand--Shilov identity in
  the form `HasFourierAwayFromOrigin (truncatedPower k) (truncatedPowerFourier k)`.

The pairing identity is proved by induction on the power: the base case computes the half-line
integral of an angular Fourier transform through finite truncations, Fubini's theorem and the
Riemann--Lebesgue lemma; the inductive step trades one power of `z` for one derivative of the
test function and integrates by parts on the real line.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-- The angular-convention derivative rule for Schwartz functions: `(φ')^ (ζ) = i ζ φ̂ (ζ)`. -/
theorem angularFourier1D_deriv (φ : SchwartzMap ℝ ℂ) :
    angularFourier1D (deriv (⇑φ)) =
      fun ζ : ℝ => Complex.I * (ζ : ℂ) * angularFourier1D (⇑φ) ζ := by
  have hd : Integrable (deriv (⇑φ)) volume :=
    SchwartzMap.integrable (SchwartzMap.derivCLM ℂ ℂ φ)
  have hder := Real.fourier_deriv (SchwartzMap.integrable φ) φ.differentiable hd
  funext ζ
  rw [angularFourier1D_eq_mathlib (deriv (⇑φ)) ζ, hder,
    angularFourier1D_eq_mathlib (⇑φ) ζ]
  simp only [smul_eq_mul]
  have hsc : (2 * (Real.pi : ℂ) * Complex.I * (((2 * Real.pi)⁻¹ * ζ : ℝ) : ℂ)) =
      Complex.I * (ζ : ℂ) := by
    push_cast
    field_simp
  rw [← hsc]

/-- Half-line integral of the angular Fourier transform of a Schwartz function supported away
from the origin: `∫_{0}^{∞} φ̂(z) dz = ∫ (iζ)⁻¹ φ(ζ) dζ`. This is the step-function
(`k = 0`) case of the Gel'fand--Shilov pairing. -/
theorem setIntegral_Ioi_angularFourier1D (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ z in Set.Ioi (0 : ℝ), angularFourier1D (⇑φ) z =
      ∫ ζ : ℝ, (Complex.I * (ζ : ℂ))⁻¹ * φ ζ := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_abs_of_tsupport_subset hφ
  set h : ℝ → ℂ := fun ζ => (Complex.I * (ζ : ℂ))⁻¹ * φ ζ with hh_def
  have hkermeas : AEStronglyMeasurable (fun ζ : ℝ => (Complex.I * (ζ : ℂ))⁻¹) volume :=
    ((Complex.measurable_ofReal.const_mul Complex.I).inv).aestronglyMeasurable
  have hkerbound : ∀ ζ ∈ tsupport ⇑φ, ‖(Complex.I * (ζ : ℂ))⁻¹‖ ≤ δ⁻¹ := by
    intro ζ hζ
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact inv_anti₀ hδ (hsep ζ hζ)
  have hint : Integrable h volume :=
    integrable_mul_of_bound_on_tsupport hkermeas (SchwartzMap.integrable φ) hkerbound
  have hexpnorm : ∀ w : ℂ, w.re = 0 → ‖Complex.exp w‖ = 1 := by
    intro w hw
    rw [Complex.norm_exp, hw, Real.exp_zero]
  have hint2 : ∀ R : ℝ,
      Integrable (fun ζ : ℝ => Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ) volume := by
    intro R
    refine hint.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · refine le_of_eq (hexpnorm _ ?_)
      simp [Complex.mul_re]
  -- the truncated identity
  have happly : ∀ z : ℝ, angularFourier1D (⇑φ) z =
      ∫ ζ : ℝ, Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ := by
    intro z
    rw [angularFourier1D_coe_schwartz]
    exact Fourier.angularFourierSchwartz_apply φ z
  have htrunc : ∀ R : ℝ, 0 ≤ R →
      ∫ z in (0 : ℝ)..R, angularFourier1D (⇑φ) z =
        (∫ ζ : ℝ, h ζ) -
          ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
    intro R hR
    have hF : Integrable
        (Function.uncurry fun (z ζ : ℝ) => Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ)
        ((volume.restrict (Set.Ioc 0 R)).prod volume) := by
      have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) R) volume :=
        integrableOn_const (by simp)
      have hdom : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖φ p.2‖)
          ((volume.restrict (Set.Ioc 0 R)).prod volume) :=
        Integrable.mul_prod hone (SchwartzMap.integrable φ).norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · rw [Function.uncurry_apply_pair, norm_mul, hexpnorm _ (by simp [Complex.mul_re]),
          one_mul]
    calc ∫ z in (0 : ℝ)..R, angularFourier1D (⇑φ) z
        = ∫ z in Set.Ioc (0 : ℝ) R,
            ∫ ζ : ℝ, Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ := by
          rw [intervalIntegral.integral_of_le hR]
          exact integral_congr_ae (Filter.Eventually.of_forall fun z => happly z)
      _ = ∫ ζ : ℝ, ∫ z in Set.Ioc (0 : ℝ) R,
            Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) * φ ζ :=
          integral_integral_swap hF
      _ = ∫ ζ : ℝ, (∫ z in Set.Ioc (0 : ℝ) R,
            Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ)))) * φ ζ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
          simp only [integral_mul_const]
      _ = (∫ ζ : ℝ, h ζ) -
            ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
          rw [← integral_sub hint (hint2 R)]
          refine integral_congr_ae ?_
          have h0 : ∀ᵐ ζ : ℝ ∂volume, ζ ≠ 0 := by
            refine ae_iff.mpr ?_
            simp
          filter_upwards [h0] with ζ hζ0
          have hc : (-Complex.I * (ζ : ℂ)) ≠ 0 := by
            simp [Complex.ext_iff, hζ0]
          have hker : (∫ z in Set.Ioc (0 : ℝ) R,
              Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ)))) =
              (Complex.exp (-Complex.I * (ζ : ℂ) * (R : ℂ)) - 1) / (-Complex.I * (ζ : ℂ)) := by
            rw [← intervalIntegral.integral_of_le hR]
            have hcongr : ∀ z ∈ Set.uIcc (0 : ℝ) R,
                Complex.exp (-Complex.I * ((ζ : ℂ) * (z : ℂ))) =
                  Complex.exp ((-Complex.I * (ζ : ℂ)) * (z : ℂ)) := by
              intro z _
              ring_nf
            rw [intervalIntegral.integral_congr hcongr, integral_exp_mul_complex hc]
            simp [mul_comm]
          rw [hker, hh_def]
          have hIζ : (Complex.I * (ζ : ℂ)) ≠ 0 := by
            simp [Complex.ext_iff, hζ0]
          field_simp
          ring_nf
  -- limits as `R → ∞`
  have hlhs : Filter.Tendsto (fun R : ℝ => ∫ z in (0 : ℝ)..R, angularFourier1D (⇑φ) z)
      Filter.atTop (𝓝 (∫ z in Set.Ioi (0 : ℝ), angularFourier1D (⇑φ) z)) := by
    refine intervalIntegral_tendsto_integral_Ioi 0 ?_ Filter.tendsto_id
    rw [angularFourier1D_coe_schwartz]
    exact (SchwartzMap.integrable _).integrableOn
  have hrl : Filter.Tendsto
      (fun R : ℝ => ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ)
      Filter.atTop (𝓝 0) := by
    have hid : ∀ R : ℝ,
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ = angularFourier1D h R := by
      intro R
      unfold angularFourier1D Fourier.angularFourierIntegralInner
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    have hcomp : Filter.Tendsto (fun R : ℝ => (2 * Real.pi)⁻¹ • R)
        Filter.atTop (Filter.cocompact ℝ) := by
      have h1 : Filter.Tendsto (fun R : ℝ => (2 * Real.pi)⁻¹ • R)
          Filter.atTop Filter.atTop := by
        simpa [smul_eq_mul] using
          (Filter.tendsto_id (α := ℝ)).const_mul_atTop
            (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)
      refine h1.mono_right ?_
      rw [cocompact_eq_atBot_atTop]
      exact le_sup_right
    have := (Real.zero_at_infty_fourier h).comp hcomp
    refine this.congr fun R => ?_
    rw [Function.comp_apply, ← angularFourier1D_eq_mathlib h R, hid R]
  have hrhs : Filter.Tendsto
      (fun R : ℝ => (∫ ζ : ℝ, h ζ) -
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ)
      Filter.atTop (𝓝 ((∫ ζ : ℝ, h ζ) - 0)) :=
    tendsto_const_nhds.sub hrl
  have heq : (fun R : ℝ => ∫ z in (0 : ℝ)..R, angularFourier1D (⇑φ) z) =ᶠ[Filter.atTop]
      fun R : ℝ => (∫ ζ : ℝ, h ζ) -
        ∫ ζ : ℝ, Complex.exp (-Complex.I * (R : ℂ) * (ζ : ℂ)) * h ζ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    exact htrunc R hR
  have hfinal := tendsto_nhds_unique (hlhs.congr' heq) hrhs
  simpa [hh_def] using hfinal

/-- The Gel'fand--Shilov pairing for truncated powers: for a Schwartz test function supported
away from the origin, `∫ k!/(iζ)^{k+1} φ(ζ) dζ = ∫_{0}^{∞} z^k φ̂(z) dz`. -/
theorem truncatedPowerFourier_pairing (k : ℕ) (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ) :
    ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ ζ =
      ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * angularFourier1D (⇑φ) z := by
  induction k generalizing φ with
  | zero =>
    have h0 := setIntegral_Ioi_angularFourier1D φ hφ
    simp only [truncatedPowerFourier, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
      pow_zero, one_mul, one_div]
    exact h0.symm
  | succ k ih =>
    obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_abs_of_tsupport_subset hφ
    set φ' : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ with hφ'_def
    have hcoe : ⇑φ' = deriv (⇑φ) := rfl
    have hφ'supp : tsupport ⇑φ' ⊆ {(0 : ℝ)}ᶜ := by
      rw [hcoe]
      exact tsupport_deriv_subset.trans hφ
    have hmeasT : ∀ n : ℕ, AEStronglyMeasurable (truncatedPowerFourier n) volume := by
      intro n
      refine Measurable.aestronglyMeasurable ?_
      unfold truncatedPowerFourier
      exact measurable_const.div ((Complex.measurable_ofReal.const_mul Complex.I).pow_const _)
    have hbound : ∀ n : ℕ, ∀ ζ ∈ tsupport ⇑φ,
        ‖truncatedPowerFourier n ζ‖ ≤ (n.factorial : ℝ) / δ ^ (n + 1) := by
      intro n ζ hζ
      have hδζ : δ ≤ |ζ| := hsep ζ hζ
      simp only [truncatedPowerFourier]
      rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_natCast]
      have h1 : (0 : ℝ) < δ ^ (n + 1) := pow_pos hδ _
      have h2 : δ ^ (n + 1) ≤ |ζ| ^ (n + 1) := pow_le_pow_left₀ hδ.le hδζ _
      gcongr
      exact hδζ
    -- integration by parts: `∫ T_{k+1} φ = -i ∫ T_k φ'`
    have hu : ∀ ζ ∈ tsupport ⇑φ,
        HasDerivAt (truncatedPowerFourier k)
          ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ) ζ := by
      intro ζ hζ
      have hζ0 : ζ ≠ 0 := by simpa using hφ hζ
      have hIζ : Complex.I * Complex.ofRealCLM ζ ≠ 0 := by
        simp [Complex.ext_iff, hζ0]
      have h4 := ((((Complex.ofRealCLM.hasDerivAt (x := ζ)).const_mul Complex.I).pow
        (k + 1)).inv (pow_ne_zero _ hIζ)).const_mul ((k.factorial : ℕ) : ℂ)
      have hF : truncatedPowerFourier k =ᶠ[𝓝 ζ] fun y : ℝ =>
          ((k.factorial : ℕ) : ℂ) * ((fun t : ℝ =>
            (Complex.I * Complex.ofRealCLM t) ^ (k + 1)) y)⁻¹ := by
        filter_upwards with t
        simp [truncatedPowerFourier, div_eq_mul_inv]
      have h5 := h4.congr_of_eventuallyEq hF
      have hIζ' : (Complex.I * (ζ : ℂ)) ≠ 0 := by
        simp [Complex.ext_iff, hζ0]
      have hval : ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ) =
          ((k.factorial : ℕ) : ℂ) *
            (-(((k + 1 : ℕ) : ℂ) * (Complex.I * Complex.ofRealCLM ζ) ^ (k + 1 - 1) *
              (Complex.I * Complex.ofRealCLM 1)) /
              ((fun y : ℝ => Complex.I * Complex.ofRealCLM y) ^ (k + 1)) ζ ^ 2) := by
        simp only [truncatedPowerFourier, Complex.ofRealCLM_apply, Pi.pow_apply,
          Nat.add_sub_cancel, Complex.ofReal_one, mul_one]
        push_cast [Nat.factorial_succ]
        field_simp
        ring
      rw [hval]
      exact h5
    have hv : ∀ ζ ∈ tsupport (truncatedPowerFourier k),
        HasDerivAt (⇑φ) (deriv (⇑φ) ζ) ζ :=
      fun ζ _ => (φ.differentiable ζ).hasDerivAt
    have hint1 : Integrable (truncatedPowerFourier k * deriv (⇑φ)) volume := by
      have := integrable_mul_of_bound_on_tsupport (hmeasT k)
        (hcoe ▸ SchwartzMap.integrable φ' : Integrable (deriv (⇑φ)) volume)
        (fun ζ hζ => hbound k ζ (tsupport_deriv_subset hζ))
      exact this
    have hint2 : Integrable
        ((fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) * ⇑φ) volume := by
      have := integrable_mul_of_bound_on_tsupport
        (((hmeasT (k + 1)).const_mul (-Complex.I)))
        (SchwartzMap.integrable φ)
        (fun ζ hζ => by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
          exact hbound (k + 1) ζ hζ)
      exact this
    have hint3 : Integrable (truncatedPowerFourier k * ⇑φ) volume := by
      have := integrable_mul_of_bound_on_tsupport (hmeasT k)
        (SchwartzMap.integrable φ) (hbound k)
      exact this
    have hibp0 := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv hint1 hint2 hint3
    have hpull : ∫ ζ : ℝ, (fun t : ℝ => -Complex.I * truncatedPowerFourier (k + 1) t) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      ring
    have hibp : ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ' ζ := by
      have h5 : ∫ ζ : ℝ, truncatedPowerFourier k ζ * deriv (⇑φ) ζ
          = Complex.I * ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ := by
        rw [hibp0, hpull]
        ring
      rw [← hcoe] at h5
      rw [h5, ← mul_assoc]
      simp [Complex.I_mul_I]
    -- the derivative shift on the Fourier side
    have hstep : -Complex.I * ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * angularFourier1D (⇑φ') z
        = ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ (k + 1) * angularFourier1D (⇑φ) z := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      have hd : angularFourier1D (⇑φ') z = Complex.I * (z : ℂ) * angularFourier1D (⇑φ) z := by
        rw [hcoe, angularFourier1D_deriv φ]
      simp only [hd]
      have hII : -Complex.I * Complex.I = 1 := by simp [Complex.I_mul_I]
      calc -Complex.I * ((z : ℂ) ^ k * (Complex.I * (z : ℂ) * angularFourier1D (⇑φ) z))
          = (-Complex.I * Complex.I) * ((z : ℂ) ^ (k + 1) * angularFourier1D (⇑φ) z) := by
            ring
        _ = (z : ℂ) ^ (k + 1) * angularFourier1D (⇑φ) z := by rw [hII, one_mul]
    calc ∫ ζ : ℝ, truncatedPowerFourier (k + 1) ζ * φ ζ
        = -Complex.I * ∫ ζ : ℝ, truncatedPowerFourier k ζ * φ' ζ := hibp
      _ = -Complex.I * ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ k * angularFourier1D (⇑φ') z := by
          rw [ih φ' hφ'supp]
      _ = ∫ z in Set.Ioi (0 : ℝ), (z : ℂ) ^ (k + 1) * angularFourier1D (⇑φ) z := hstep

/-- Section 6.1 with Gel'fand--Shilov: the truncated power `z₊^k` (step function, ReLU, ...) is
a Lizorkin distribution whose Fourier transform away from the origin is the function
`k! / (iζ)^{k+1}`; the point mass `π i^k δ^{(k)}` at the origin is invisible away from `0`. -/
theorem l1_truncatedPower_hasFourierAwayFromOrigin (k : ℕ) :
    HasFourierAwayFromOrigin (truncatedPower k) (truncatedPowerFourier k) := by
  have habs : ∀ z : ℝ, ‖truncatedPower k z‖ ≤ (1 + |z|) ^ k := by
    intro z
    by_cases hz : 0 < z
    · simp only [truncatedPower, if_pos hz, Complex.norm_real, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg z) (le_add_of_nonneg_left zero_le_one) k
    · simp only [truncatedPower, if_neg hz, norm_zero]
      positivity
  have hmeas : Measurable (truncatedPower k) := by
    unfold truncatedPower
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (Complex.measurable_ofReal.comp (measurable_id.pow_const k)) measurable_const
  refine ⟨?_, ⟨1, k, fun z => by simpa using habs z⟩, ?_, ?_⟩
  · -- local integrability of the truncated power
    have hg : MeasureTheory.LocallyIntegrable (fun z : ℝ => ((1 + |z|) ^ k : ℝ)) volume :=
      Continuous.locallyIntegrable (by fun_prop)
    refine hg.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have h1 : (0 : ℝ) ≤ 1 + |z| := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg h1] using habs z
  · -- local integrability of the Fourier data away from the origin
    refine ContinuousOn.locallyIntegrableOn ?_ (measurableSet_singleton (0 : ℝ)).compl
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact Continuous.continuousOn (by fun_prop)
    · intro ζ hζ
      have hζ0 : ζ ≠ 0 := hζ
      exact pow_ne_zero _ (by simp [Complex.ext_iff, hζ0])
  · -- the pairing identity
    intro φ hφ
    rw [truncatedPowerFourier_pairing k φ hφ]
    have h1 : ∫ z : ℝ, truncatedPower k z * angularFourier1D (⇑φ) z =
        ∫ z in Set.Ioi (0 : ℝ), truncatedPower k z * angularFourier1D (⇑φ) z := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      have hz' : ¬ 0 < z := by simpa [Set.mem_Ioi] using hz
      simp [truncatedPower, if_neg hz']
    rw [h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    have hz0 : 0 < z := hz
    simp [truncatedPower, if_pos hz0]

end LeanRidgelet
