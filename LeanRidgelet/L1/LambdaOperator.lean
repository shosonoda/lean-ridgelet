/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs
public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.ToMathlib.FourierInversion
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# L1 theory: the Lambda operator as a Fourier multiplier (step A-3)

On Schwartz functions the standard Lambda-operator power `Λ^m` acts as the Fourier multiplier
`|2πξ|^m`, that is, as the article's `|ω|^m` in the angular convention `ω = 2πξ`.

## Main results

* `LeanRidgelet.lambdaOperatorPow_eq_fourier_multiplier`:
  `Λ^m φ (z) = ∫ |2πξ|^m 𝓕φ(ξ) e^{2πizξ} dξ` in the Mathlib convention.
* `LeanRidgelet.lambdaOperatorPow_eq_angular`: the same identity in the angular convention.
* `LeanRidgelet.hasFourierAwayFromOrigin_angularFourierInv`: the inverse angular Fourier
  transform of an integrable function carries that function as its Fourier data away from the
  origin — the function-level substitute for the duality `𝒪_M ≅ 𝒪'_C`.
* `LeanRidgelet.hasFourierAwayFromOrigin_lambdaOperatorPow`: the Fourier data of `Λ^m φ` away
  from the origin is `|ζ|^m φ̂(ζ)`.
* `LeanRidgelet.integrable_lambdaOperatorPow`: `Λ^m φ` is integrable for every `m ≥ 1` — for
  even `m` it is Schwartz, for odd `m` it is the Hilbert transform of a derivative, whose
  integral vanishes (`MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero`).
* `LeanRidgelet.angularFourier1D_lambdaOperatorPow`: consequently the honest angular Fourier
  integral of `Λ^m φ` is `|ζ|^m φ̂(ζ)` at every frequency.

The even case is Fourier inversion together with the derivative rule
`𝓕[∂^m φ] = (2πiξ)^m 𝓕φ`; the odd case additionally uses the Fourier symbol `-i sign ξ` of the
principal-value Hilbert transform, proved in `LeanRidgelet.ToMathlib.HilbertTransform` from the
Dirichlet integral of `LeanRidgelet.ToMathlib.DirichletIntegral`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The symbol identities -/

/-- `sign ξ ⬝ (2πξ) = |2πξ|`. -/
theorem sign_mul_two_pi_mul (ξ : ℝ) :
    Real.sign ξ * (2 * Real.pi * ξ) = |2 * Real.pi * ξ| := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg (by nlinarith [Real.pi_pos])]
    ring
  · subst h
    simp
  · rw [Real.sign_of_pos h, abs_of_pos (by positivity)]
    ring

/-- The even-order symbol identity behind the multiplier property of `Λ^m`. -/
theorem lambda_symbol_even {m : ℕ} (hm : Even m) (ξ : ℝ) :
    (-1 : ℂ) ^ (m / 2) * (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ m
      = ((|2 * Real.pi * ξ| ^ m : ℝ) : ℂ) := by
  obtain ⟨k, hk⟩ := hm
  have hm2 : m = 2 * k := by omega
  subst hm2
  have hA : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2
      = -(((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * (ξ : ℂ)) ^ 2 * hI
  have hsigns : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hRHS : ((|2 * Real.pi * ξ| ^ (2 * k) : ℝ) : ℂ)
      = (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k := by
    rw [(even_two_mul k).pow_abs, Complex.ofReal_pow, pow_mul]
  rw [show 2 * k / 2 = k from by omega, hRHS, pow_mul, hA,
    neg_pow (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) k, ← mul_assoc, hsigns, one_mul]

/-- The odd-order symbol identity behind the multiplier property of `Λ^m`. -/
theorem lambda_symbol_odd {m : ℕ} (hm : ¬ Even m) (ξ : ℝ) :
    (-1 : ℂ) ^ (m / 2) * (-Complex.I * ((Real.sign ξ : ℝ) : ℂ)) *
        (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ m
      = ((|2 * Real.pi * ξ| ^ m : ℝ) : ℂ) := by
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hm
  subst hk
  have hA : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ 2
      = -(((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * (ξ : ℂ)) ^ 2 * hI
  have hsigns : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hRHS : ((|2 * Real.pi * ξ| ^ (2 * k + 1) : ℝ) : ℂ)
      = (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k * ((|2 * Real.pi * ξ| : ℝ) : ℂ) := by
    rw [pow_succ, Complex.ofReal_mul, (even_two_mul k).pow_abs, Complex.ofReal_pow, pow_mul]
  have hLHS : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ (2 * k + 1)
      = ((-1 : ℂ) ^ k * (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k) *
        (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) := by
    rw [pow_succ, pow_mul, hA, neg_pow (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) k]
  have hsign : ((Real.sign ξ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * (ξ : ℂ))
      = ((|2 * Real.pi * ξ| : ℝ) : ℂ) := by
    rw [← sign_mul_two_pi_mul ξ]
    push_cast
    ring
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [show (2 * k + 1) / 2 = k from by omega, hRHS, hLHS]
  calc (-1 : ℂ) ^ k * (-Complex.I * ((Real.sign ξ : ℝ) : ℂ)) *
        (((-1 : ℂ) ^ k * (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k) *
          (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)))
      = (((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k)) * (-(Complex.I * Complex.I)) *
          ((((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k) *
          (((Real.sign ξ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * (ξ : ℂ))) := by ring
    _ = ((((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k) *
          (((Real.sign ξ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * (ξ : ℂ))) := by
        rw [hsigns, hI]
        ring
    _ = ((((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) ^ k) * ((|2 * Real.pi * ξ| : ℝ) : ℂ) := by
        rw [hsign]

/-! ## The multiplier property in the Mathlib convention -/

/-- **Step A-3, the Fourier multiplier property of the Lambda operator**: on Schwartz functions
`Λ^m` acts as the Fourier multiplier `|2πξ|^m` — the manuscript's `|ω|^m` in the angular
convention `ω = 2πξ`. -/
theorem lambdaOperatorPow_eq_fourier_multiplier (m : ℕ) (φ : SchwartzMap ℝ ℂ) (z : ℝ) :
    lambdaOperatorPow m (⇑φ) z
      = ∫ ξ : ℝ, ((|2 * Real.pi * ξ| ^ m : ℝ) : ℂ) * 𝓕 (⇑φ) ξ *
          Complex.exp (((2 * Real.pi * (z * ξ) : ℝ) : ℂ) * Complex.I) := by
  classical
  set Φ : SchwartzMap ℝ ℂ := (⇑(SchwartzMap.derivCLM ℂ ℂ))^[m] φ with hΦ_def
  have hΦ : ⇑Φ = iteratedDeriv m (⇑φ) := coe_iterate_schwartz_derivCLM m φ
  have hderiv : ∀ ξ : ℝ,
      𝓕 (⇑Φ) ξ = (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ m * 𝓕 (⇑φ) ξ := by
    intro ξ
    have h : 𝓕 (iteratedDeriv m (⇑φ)) =
        fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ m • 𝓕 (⇑φ) x := by
      refine Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤) (fun k _ => ?_) le_top
      rw [← coe_iterate_schwartz_derivCLM k φ]
      exact SchwartzMap.integrable _
    rw [hΦ, h]
    simp [smul_eq_mul]
  by_cases hm : Even m
  · have hval : lambdaOperatorPow m (⇑φ) z = (-1 : ℂ) ^ (m / 2) * Φ z := by
      unfold lambdaOperatorPow
      rw [if_pos hm, hΦ]
    rw [hval, MeasureTheory.schwartz_eq_integral_fourier Φ z, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [hderiv ξ, ← lambda_symbol_even hm ξ]
    ring
  · have hval : lambdaOperatorPow m (⇑φ) z
        = (-1 : ℂ) ^ (m / 2) * MeasureTheory.pvHilbertTransform (⇑Φ) z := by
      unfold lambdaOperatorPow
      rw [if_neg hm, hΦ]
    rw [hval, MeasureTheory.pvHilbertTransform_schwartz Φ z, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [hderiv ξ, ← lambda_symbol_odd hm ξ]
    ring

/-! ## Transport to the angular convention -/

/-- The angular Fourier transform of a Schwartz function, as a Schwartz function. -/
def angularSchwartz (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ)
    (hasTemperateGrowth_const_mul (2 * Real.pi)⁻¹)
    (antilipschitzWith_const_mul (by positivity : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0)) (𝓕 φ)

theorem coe_angularSchwartz (φ : SchwartzMap ℝ ℂ) :
    ⇑(angularSchwartz φ) = angularFourier1D (⇑φ) := by
  funext ζ
  rw [angularSchwartz, SchwartzMap.compCLMOfAntilipschitz_apply]
  simp only [Function.comp_apply]
  rw [angularFourier1D, Fourier.angularFourierIntegralInner_eq_fourier, smul_eq_mul,
    SchwartzMap.fourier_coe]

/-- The spectral density `|ζ|^m φ̂(ζ)` of a Schwartz function is integrable. -/
theorem integrable_abs_pow_mul_angularFourier1D (m : ℕ) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun ζ : ℝ => ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ) volume := by
  have h := (angularSchwartz φ).integrable_pow_mul volume m
  rw [coe_angularSchwartz] at h
  refine Integrable.mono' h ?_ (Filter.Eventually.of_forall fun ζ => ?_)
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
    · rw [← coe_angularSchwartz]
      exact (angularSchwartz φ).continuous.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs]

/-- The angular inverse-Fourier representation of the Lambda operator on Schwartz functions:
the angular-convention form of `lambdaOperatorPow_eq_fourier_multiplier`. -/
theorem lambdaOperatorPow_eq_angular (m : ℕ) (φ : SchwartzMap ℝ ℂ) (z : ℝ) :
    lambdaOperatorPow m (⇑φ) z
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ ζ : ℝ, ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ *
          Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set g : ℝ → ℂ := fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ *
    Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) with hg_def
  have hsub : (∫ ξ : ℝ, g ((2 * Real.pi) * ξ)) = |(2 * Real.pi)⁻¹| • ∫ ζ : ℝ, g ζ :=
    MeasureTheory.Measure.integral_comp_mul_left g (2 * Real.pi)
  rw [lambdaOperatorPow_eq_fourier_multiplier m φ z]
  have hcongr : ∀ ξ : ℝ, ((|2 * Real.pi * ξ| ^ m : ℝ) : ℂ) * 𝓕 (⇑φ) ξ *
      Complex.exp (((2 * Real.pi * (z * ξ) : ℝ) : ℂ) * Complex.I) = g ((2 * Real.pi) * ξ) := by
    intro ξ
    rw [hg_def]
    simp only []
    have hang : angularFourier1D (⇑φ) (2 * Real.pi * ξ) = 𝓕 (⇑φ) ξ := by
      rw [angularFourier1D, Fourier.angularFourierIntegralInner_eq_fourier, smul_eq_mul,
        show (2 * Real.pi)⁻¹ * (2 * Real.pi * ξ) = ξ from by field_simp]
    rw [hang]
    congr 2
    push_cast
    ring
  rw [show (∫ ξ : ℝ, ((|2 * Real.pi * ξ| ^ m : ℝ) : ℂ) * 𝓕 (⇑φ) ξ *
        Complex.exp (((2 * Real.pi * (z * ξ) : ℝ) : ℂ) * Complex.I))
      = ∫ ξ : ℝ, g ((2 * Real.pi) * ξ) from
    integral_congr_ae (Filter.Eventually.of_forall hcongr), hsub,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]

/-- **The inverse angular Fourier transform of an integrable function carries that function as
its Fourier data away from the origin.** At function level this is the substitute for the
Fourier duality `𝒪_M ≅ 𝒪'_C` by which the manuscript produces the solution `u` of the
backprojection equation of `thm:eq.ac`: the witness is bounded and continuous rather than
slowly increasing and smooth, which is all the Fourier data pairing needs. -/
theorem hasFourierAwayFromOrigin_angularFourierInv {A : ℝ → ℂ} (hA : Integrable A volume) :
    HasFourierAwayFromOrigin
      (fun z : ℝ => ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ ζ : ℝ, A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ))) A := by
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  set u : ℝ → ℂ := fun z : ℝ => ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ ζ : ℝ, A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) with hu_def
  have hAm : AEStronglyMeasurable A volume := hA.aestronglyMeasurable
  have hcont : Continuous u := by
    have hc : Continuous fun z : ℝ =>
        ∫ ζ : ℝ, A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) := by
      refine continuous_of_dominated (bound := fun ζ : ℝ => ‖A ζ‖) ?_ ?_ hA.norm ?_
      · intro z
        exact hAm.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · intro z
        refine Filter.Eventually.of_forall fun ζ => ?_
        rw [norm_mul, hexp1, mul_one]
      · refine Filter.Eventually.of_forall fun ζ => ?_
        exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    exact hc.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  have hbdd : ∀ z : ℝ, ‖u z‖ ≤ (2 * Real.pi)⁻¹ * ∫ ζ : ℝ, ‖A ζ‖ := by
    intro z
    rw [hu_def]
    simp only []
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only []
    rw [norm_mul, hexp1, mul_one]
  refine ⟨hcont.locallyIntegrable, ⟨(2 * Real.pi)⁻¹ * ∫ ζ : ℝ, ‖A ζ‖, 0, fun z => by
      simpa using hbdd z⟩, hA.locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro θ _
  -- the pairing identity, by Fubini and the angular inversion formula
  have hΘint : Integrable (angularFourier1D (⇑θ)) volume := by
    rw [angularFourier1D_coe_schwartz]
    exact SchwartzMap.integrable _
  have hΘcont : Continuous (angularFourier1D (⇑θ)) := by
    rw [angularFourier1D_coe_schwartz]
    exact (Fourier.angularFourierSchwartz θ).continuous
  have hjoint : Integrable (Function.uncurry fun (z ζ : ℝ) =>
      A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) * angularFourier1D (⇑θ) z)
      ((volume : Measure ℝ).prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖angularFourier1D (⇑θ) p.1‖ * ‖A p.2‖)
        ((volume : Measure ℝ).prod volume) := hΘint.norm.mul_prod hA.norm
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
      · exact hAm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · exact (hΘcont.comp continuous_fst).aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [norm_mul, norm_mul, hexp1, mul_one]
      exact le_of_eq (mul_comm _ _)
  have hinv : ∀ ζ : ℝ, (∫ z : ℝ, angularFourier1D (⇑θ) z *
      Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ))) = ((2 * Real.pi : ℝ) : ℂ) * θ ζ := by
    intro ζ
    have h := Fourier.integral_angularFourierIntegralInner_mul_exp (⇑θ) ζ
    rw [Module.finrank_self, pow_one] at h
    have hθinv : 𝓕⁻ (𝓕 (⇑θ)) ζ = θ ζ := by
      have hint : Integrable (𝓕 (⇑θ)) volume := by
        rw [← SchwartzMap.fourier_coe]
        exact SchwartzMap.integrable _
      exact congrFun (θ.continuous.fourierInv_fourier_eq (SchwartzMap.integrable _) hint) ζ
    rw [hθinv] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [angularFourier1D, MeasureTheory.inner_real_eq_mul]
  calc (∫ ζ : ℝ, A ζ * θ ζ)
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ ζ : ℝ, A ζ * (((2 * Real.pi : ℝ) : ℂ) * θ ζ) := by
        rw [← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only []
        rw [Complex.real_smul]
        push_cast
        field_simp
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ ζ : ℝ, ∫ z : ℝ,
          A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) * angularFourier1D (⇑θ) z := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only []
        rw [← hinv ζ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        ring
    _ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ z : ℝ, ∫ ζ : ℝ,
          A ζ * Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ)) * angularFourier1D (⇑θ) z := by
        rw [integral_integral_swap hjoint]
    _ = ∫ z : ℝ, u z * angularFourier1D (⇑θ) z := by
        rw [← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hu_def]
        rw [Complex.real_smul, Complex.real_smul, integral_mul_const]
        ring

/-- **The Fourier data of the Lambda operator away from the origin**: on Schwartz functions the
Fourier data of `Λ^m φ` is the multiplier `|ζ|^m φ̂(ζ)`. This is the spectral form of the
backprojection equation of the structure theorem `thm:eq.ac`. -/
theorem hasFourierAwayFromOrigin_lambdaOperatorPow (m : ℕ) (φ : SchwartzMap ℝ ℂ) :
    HasFourierAwayFromOrigin (lambdaOperatorPow m (⇑φ))
      (fun ζ => ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ) := by
  have heq : (fun z : ℝ => ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ ζ : ℝ, ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ *
        Complex.exp (Complex.I * ((z * ζ : ℝ) : ℂ))) = lambdaOperatorPow m (⇑φ) := by
    funext z
    exact (lambdaOperatorPow_eq_angular m φ z).symm
  rw [← heq]
  exact hasFourierAwayFromOrigin_angularFourierInv (integrable_abs_pow_mul_angularFourier1D m φ)

/-- **For even `m` the filtered Schwartz function is again Schwartz**, hence integrable:
`Λ^m φ = (-1)^{m/2} φ^{(m)}`. For odd `m` the Hilbert transform intervenes and integrability is
a genuine decay estimate; see `LeanRidgelet.L1.BumpRidgelet` for the remaining gap. -/
theorem integrable_lambdaOperatorPow_of_even {m : ℕ} (hm : Even m) (φ : SchwartzMap ℝ ℂ) :
    Integrable (lambdaOperatorPow m (⇑φ)) volume := by
  have heq : lambdaOperatorPow m (⇑φ)
      = fun z => (-1 : ℂ) ^ (m / 2) * (⇑((⇑(SchwartzMap.derivCLM ℂ ℂ))^[m] φ)) z := by
    funext z
    unfold lambdaOperatorPow
    rw [if_pos hm, coe_iterate_schwartz_derivCLM]
  rw [heq]
  exact (SchwartzMap.integrable _).const_mul _

/-- The integral of an iterated derivative of a Schwartz function vanishes. -/
theorem integral_iteratedDeriv_schwartz_eq_zero {m : ℕ} (hm : m ≠ 0) (φ : SchwartzMap ℝ ℂ) :
    (∫ z : ℝ, iteratedDeriv m (⇑φ) z) = 0 := by
  have hderiv : 𝓕 (iteratedDeriv m (⇑φ)) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ m • 𝓕 (⇑φ) x := by
    refine Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤) (fun k _ => ?_) le_top
    rw [← coe_iterate_schwartz_derivCLM k φ]
    exact SchwartzMap.integrable _
  have h0 := Real.fourier_apply_zero (iteratedDeriv m (⇑φ))
  rw [← h0, hderiv]
  simp [zero_pow hm]

/-- **`Λ^m` maps Schwartz functions into `L¹` for every `m ≥ 1`.** For even `m` the filtered
function is again Schwartz; for odd `m` it is the Hilbert transform of `φ^{(m)}`, whose integral
vanishes because it is a derivative, so the decay improves from `O(1/x)` to `O(1/x²)` and
`MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero` applies. -/
theorem integrable_lambdaOperatorPow (m : ℕ) [NeZero m] (φ : SchwartzMap ℝ ℂ) :
    Integrable (lambdaOperatorPow m (⇑φ)) volume := by
  classical
  by_cases hm : Even m
  · exact integrable_lambdaOperatorPow_of_even hm φ
  · set Φ : SchwartzMap ℝ ℂ := (⇑(SchwartzMap.derivCLM ℂ ℂ))^[m] φ with hΦ_def
    have hΦ : ⇑Φ = iteratedDeriv m (⇑φ) := coe_iterate_schwartz_derivCLM m φ
    have hzero : (∫ z : ℝ, Φ z) = 0 := by
      rw [hΦ]
      exact integral_iteratedDeriv_schwartz_eq_zero (NeZero.ne m) φ
    have heq : lambdaOperatorPow m (⇑φ)
        = fun z => (-1 : ℂ) ^ (m / 2) * MeasureTheory.pvHilbertTransform (⇑Φ) z := by
      funext z
      unfold lambdaOperatorPow
      rw [if_neg hm, hΦ]
    rw [heq]
    exact (MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero Φ hzero).const_mul _

/-- **The classical multiplier identity for the Lambda operator.** Once `Λ^m φ` is integrable —
automatic for even `m`, where `Λ^m φ = ± φ^{(m)}` — its honest angular Fourier integral is the
multiplier `|ζ|^m φ̂(ζ)` at *every* frequency, not only as Fourier data away from the origin.
This is what `cor:const.ap` needs, since the admissibility constant is defined through the
Fourier integral of the ridgelet function. -/
theorem angularFourier1D_lambdaOperatorPow (m : ℕ) (φ : SchwartzMap ℝ ℂ)
    (hint : Integrable (lambdaOperatorPow m (⇑φ)) volume) (ζ : ℝ) :
    angularFourier1D (lambdaOperatorPow m (⇑φ)) ζ
      = ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) ζ := by
  set A : ℝ → ℂ := fun w => ((|w| ^ m : ℝ) : ℂ) * angularFourier1D (⇑φ) w with hA_def
  have hAint : Integrable A volume := integrable_abs_pow_mul_angularFourier1D m φ
  have hAcont : Continuous A := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp (by fun_prop)
    · rw [angularFourier1D_coe_schwartz]
      exact (Fourier.angularFourierSchwartz φ).continuous
  have hfg : ∀ ω : ℝ, (2 * Real.pi : ℂ)⁻¹ *
      ∫ z : ℝ, A z * Complex.exp (Complex.I * (z * ω)) = lambdaOperatorPow m (⇑φ) ω := by
    intro ω
    rw [lambdaOperatorPow_eq_angular m φ ω, Complex.real_smul]
    have hcast : ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) = (2 * Real.pi : ℂ)⁻¹ := by push_cast; ring
    rw [hcast]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hA_def]
    congr 2
    push_cast
    ring
  have h := Fourier.angularFourier_inversion_of_integrable hAcont hAint hint hfg ζ
  rw [angularFourier1D_apply]
  change (∫ z : ℝ, Complex.exp (-Complex.I * ((z * ζ : ℝ) : ℂ)) * lambdaOperatorPow m (⇑φ) z)
    = A ζ
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only []
  rw [mul_comm]
  congr 2
  push_cast
  ring

end LeanRidgelet
