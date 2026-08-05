/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.LambdaOperator
public import LeanRidgelet.L1.Reconstruction
public import LeanRidgelet.ToMathlib.PolarCoordinates
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# L1 theory: reconstruction through the Radon transform (`thm:formula.radon`)

## Main results

* `LeanRidgelet.l1_radon_filtered_backprojection`: **Radon's classical inversion formula**
  `R† Λ^{m-1} R f = 2 (2π)^{m-1} f` for Schwartz `f`. The Radon section of a Schwartz function
  is Schwartz (`LeanRidgelet.ToMathlib.RadonTransform`), so the multiplier property of
  `Λ^{m-1}` applies; the Fourier slice theorem turns the filtered section at `⟨u, x⟩` into a ray
  integral, which the general polar-coordinate formula of
  `LeanRidgelet.ToMathlib.PolarCoordinates` reassembles over the sphere into two copies of the
  inverse Fourier integral.
* `LeanRidgelet.l1_reconstruction_formula_radon`: the ridgelet half — under the backprojection
  admissibility `eq:radon.ac` in spectral form, the truncated ridgelet reconstruction of a
  Schwartz function converges at every point to `2 (2π)^{m-1} f(x)`.

## Deviations from the article

* The filter is the standard Lambda-operator power `Λ^{m-1}`, not the article's `eq:bp`; see
  the docstring of `LeanRidgelet.lambdaOperatorPow`.
* The normalization of `eq:radon.ac` is `∫ û = 2`, not the article's `∫ û = -1`. The
  truncation limit is `(2π)^{m-1} ∫ û ⬝ f(x)`, and the article's own approximate-identity
  kernel `k(z) = 𝓗u(z)/z` has `∫ k = ∫ û / 2`; both routes force `∫ û = 2`.
* At function level the radon route also needs vanishing moments of `ψ`, for the same
  Lizorkin-quotient reason as `l1_reconstruction_formula`.
* The fractional Laplacian identity `cor:radon.d` is deferred to the distributional pass.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Radon's classical inversion formula -/

open Metric Set in
/-- **Radon's inversion formula as filtered backprojection** (plan item A-4): for a Schwartz
function on `ℝ^m`, `R† Λ^{m-1} R f = 2 (2π)^{m-1} f`, with the standard Lambda-operator power
(one-dimensional multiplier `|ω|^{m-1}`). The manuscript uses this classical identity as a known
result (Helgason).

The proof follows the route recorded in the development plan. The Radon section of a Schwartz
function *is* a Schwartz function (`MeasureTheory.radonTransform_eq_radonSchwartzSection`), so
the multiplier property of `Λ^{m-1}` (`lambdaOperatorPow_eq_fourier_multiplier`, which for even
`m` rests on the Fourier symbol `-i sign ξ` of the principal-value Hilbert transform) applies to
it and, through the Fourier slice theorem, turns the filtered section at `⟪u, x⟫` into the
frequency integral `∫ |2πω|^{m-1} 𝓕f(ω u) e^{2πi⟪ω u, x⟫} dω` along the ray through `u`. Splitting
that integral at the origin and reflecting the negative half gives two rays, each of which the
polar-coordinate formula (`MeasureTheory.integral_eq_integral_toSphere_integral_Ioi`) reassembles
over the sphere into `∫_{ℝ^m} 𝓕f(ξ) e^{2πi⟪ξ, x⟫} dξ` — the second one after the reflection
`ξ ↦ -ξ`, which the Lebesgue measure preserves, so that no antipodal symmetry of the sphere
measure is needed. Fourier inversion evaluates each copy as `f x`, whence the constant
`2 (2π)^{m-1}`. -/
theorem l1_radon_filtered_backprojection (m : ℕ) [NeZero m]
    (f : SchwartzMap (InputSpace m) ℂ) (x : InputSpace m) :
    dualRadonTransform
        (fun v => lambdaOperatorPow (m - 1) (radonTransform (⇑f) v)) x
      = ((2 * (2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x := by
  classical
  have hdim : Module.finrank ℝ (InputSpace m) = m := finrank_euclideanSpace_fin
  haveI : Nontrivial (InputSpace m) := by
    refine Module.nontrivial_of_finrank_pos (R := ℝ) ?_
    rw [hdim]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  -- the spectral integrand of the inversion formula
  set G : InputSpace m → ℂ := fun ξ =>
    Complex.exp (((2 * Real.pi * (inner ℝ ξ x : ℝ) : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑f) ξ with hG_def
  have hFint : Integrable (𝓕 (⇑f)) volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  have hFcont : Continuous (𝓕 (⇑f)) := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.continuous _
  have hGcont : Continuous G := by
    rw [hG_def]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hFcont
  have hGint : Integrable G volume := by
    refine hFint.norm.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · refine AEStronglyMeasurable.mul ?_ hFint.aestronglyMeasurable
      exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · rw [hG_def]
      simp only []
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hGnegint : Integrable (fun ξ => G (-ξ)) volume := by
    have h := (Measure.measurePreserving_neg (volume : Measure (InputSpace m))).integrable_comp
      hGint.aestronglyMeasurable
    exact h.mpr hGint
  -- Fourier inversion evaluates the spectral integral
  have hinv : (∫ ξ, G ξ) = f x := by
    have h := congrFun (f.continuous.fourierInv_fourier_eq (SchwartzMap.integrable f) hFint) x
    rw [Real.fourierInv_eq'] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hG_def]
    simp only [smul_eq_mul]
  have hinvneg : (∫ ξ, G (-ξ)) = f x := by
    rw [MeasureTheory.integral_neg_eq_self (μ := (volume : Measure (InputSpace m))) G, hinv]
  -- the filtered section at a unit direction
  have hterm : ∀ u : sphere (0 : InputSpace m) 1,
      lambdaOperatorPow (m - 1) (radonTransform (⇑f) (u : InputSpace m))
          (inner ℝ (u : InputSpace m) x)
        = (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) *
            ((∫ ω in Ioi (0 : ℝ), ω ^ (m - 1) • G (ω • (u : InputSpace m)))
              + ∫ ω in Ioi (0 : ℝ), ω ^ (m - 1) • G ((-ω) • (u : InputSpace m))) := by
    intro u
    have hu : ‖(u : InputSpace m)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    rw [MeasureTheory.radonTransform_eq_radonSchwartzSection f hu,
      lambdaOperatorPow_eq_fourier_multiplier (m - 1) (MeasureTheory.radonSchwartzSection f hu)
        (inner ℝ (u : InputSpace m) x)]
    -- identify the integrand with the spectral integrand
    have hker : ∀ ω : ℝ,
        ((|2 * Real.pi * ω| ^ (m - 1) : ℝ) : ℂ) *
            𝓕 (⇑(MeasureTheory.radonSchwartzSection f hu)) ω *
            Complex.exp ((((2 * Real.pi * ((inner ℝ (u : InputSpace m) x : ℝ) * ω)) : ℝ) : ℂ) *
              Complex.I)
          = (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) *
              (((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m))) := by
      intro ω
      rw [MeasureTheory.fourier_radonSchwartzSection f hu]
      have hinner : (inner ℝ (ω • (u : InputSpace m)) x : ℝ)
          = (inner ℝ (u : InputSpace m) x : ℝ) * ω := by
        rw [real_inner_smul_left]
        ring
      have habs : (|2 * Real.pi * ω| ^ (m - 1) : ℝ)
          = ((2 * Real.pi) ^ (m - 1) : ℝ) * (|ω| ^ (m - 1) : ℝ) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), mul_pow]
      rw [habs, hG_def]
      simp only []
      rw [hinner]
      push_cast
      ring
    rw [show (∫ ω : ℝ, ((|2 * Real.pi * ω| ^ (m - 1) : ℝ) : ℂ) *
          𝓕 (⇑(MeasureTheory.radonSchwartzSection f hu)) ω *
          Complex.exp ((((2 * Real.pi * ((inner ℝ (u : InputSpace m) x : ℝ) * ω)) : ℝ) : ℂ) *
            Complex.I))
        = ∫ ω : ℝ, (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) *
            (((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m))) from
      integral_congr_ae (Filter.Eventually.of_forall hker), integral_const_mul]
    congr 1
    -- the frequency integrand is integrable
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    obtain ⟨C, hC⟩ := MeasureTheory.schwartz_norm_le_one_add_norm_rpow (𝓕 f) (m + 1)
    have hC0 : 0 ≤ C := by
      have h0 := hC 0
      rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h0
      exact le_trans (norm_nonneg _) h0
    have hbd : ∀ ω : ℝ, ‖((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m))‖
        ≤ C * (1 + ‖ω‖) ^ (-(2 : ℝ)) := by
      intro ω
      have hnormsmul : ‖ω • (u : InputSpace m)‖ = |ω| := by
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
      have hG : ‖G (ω • (u : InputSpace m))‖ = ‖𝓕 (⇑f) (ω • (u : InputSpace m))‖ := by
        rw [hG_def]
        simp only []
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      have hFbd : ‖𝓕 (⇑f) (ω • (u : InputSpace m))‖ ≤ C * (1 + |ω|) ^ (-((m + 1 : ℕ) : ℝ)) := by
        have h := hC (ω • (u : InputSpace m))
        rw [SchwartzMap.fourier_coe] at h
        rwa [hnormsmul] at h
      have hpow : (|ω| ^ (m - 1) : ℝ) ≤ (1 + |ω|) ^ ((m - 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (abs_nonneg ω) (by linarith [abs_nonneg ω]) _
      have hcomb : ((1 + |ω|) ^ ((m - 1 : ℕ) : ℝ)) * (1 + |ω|) ^ (-((m + 1 : ℕ) : ℝ))
          = (1 + |ω|) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          push_cast [Nat.cast_sub hm1]
          ring
        rw [this]
        push_cast
        ring
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hG,
        Real.norm_eq_abs]
      calc (|ω| ^ (m - 1) : ℝ) * ‖𝓕 (⇑f) (ω • (u : InputSpace m))‖
          ≤ ((1 + |ω|) ^ ((m - 1 : ℕ) : ℝ)) * (C * (1 + |ω|) ^ (-((m + 1 : ℕ) : ℝ))) := by
            refine mul_le_mul hpow hFbd (norm_nonneg _) (by positivity)
        _ = C * (((1 + |ω|) ^ ((m - 1 : ℕ) : ℝ)) * (1 + |ω|) ^ (-((m + 1 : ℕ) : ℝ))) := by ring
        _ = C * (1 + |ω|) ^ (-(2 : ℝ)) := by rw [hcomb]
    have hsplitint : Integrable
        (fun ω : ℝ => ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m))) volume := by
      refine Integrable.mono' (g := fun ω : ℝ => C * (1 + ‖ω‖) ^ (-(2 : ℝ))) ?_ ?_
        (Filter.Eventually.of_forall hbd)
      · refine Integrable.const_mul ?_ C
        refine integrable_one_add_norm ?_
        rw [Module.finrank_self]
        norm_num
      · refine AEStronglyMeasurable.mul ?_ ?_
        · exact (Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable
        · exact (hGcont.comp (by fun_prop)).aestronglyMeasurable
    -- split at the origin and reflect the negative half
    have hIic : (∫ ω in Iic (0 : ℝ), ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m)))
        = ∫ ω in Ioi (0 : ℝ), ((|(-ω)| ^ (m - 1) : ℝ) : ℂ) * G ((-ω) • (u : InputSpace m)) := by
      have h := integral_comp_neg_Ioi (0 : ℝ)
        (fun ω : ℝ => ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m)))
      rw [neg_zero] at h
      exact h.symm
    calc (∫ ω : ℝ, ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m)))
        = (∫ ω in Ioi (0 : ℝ), ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m)))
            + ∫ ω in Iic (0 : ℝ), ((|ω| ^ (m - 1) : ℝ) : ℂ) * G (ω • (u : InputSpace m)) := by
          rw [← compl_Ioi (a := (0 : ℝ))]
          exact (integral_add_compl measurableSet_Ioi hsplitint).symm
      _ = (∫ ω in Ioi (0 : ℝ), ω ^ (m - 1) • G (ω • (u : InputSpace m)))
            + ∫ ω in Ioi (0 : ℝ), ω ^ (m - 1) • G ((-ω) • (u : InputSpace m)) := by
          rw [hIic]
          congr 1
          · refine setIntegral_congr_fun measurableSet_Ioi fun ω hω => ?_
            rw [abs_of_pos hω, Complex.real_smul]
          · refine setIntegral_congr_fun measurableSet_Ioi fun ω hω => ?_
            rw [abs_neg, abs_of_pos hω, Complex.real_smul]
  -- assemble over the sphere by polar coordinates
  have hA : Integrable
      (fun u : sphere (0 : InputSpace m) 1 =>
        ∫ r in Ioi (0 : ℝ), r ^ (m - 1) • G (r • (u : InputSpace m)))
      (volume : Measure (InputSpace m)).toSphere := by
    have h := MeasureTheory.integrable_toSphere_integral_Ioi
      (volume : Measure (InputSpace m)) hGint
    rwa [hdim] at h
  have hB : Integrable
      (fun u : sphere (0 : InputSpace m) 1 =>
        ∫ r in Ioi (0 : ℝ), r ^ (m - 1) • G ((-r) • (u : InputSpace m)))
      (volume : Measure (InputSpace m)).toSphere := by
    have h := MeasureTheory.integrable_toSphere_integral_Ioi
      (volume : Measure (InputSpace m)) hGnegint
    rw [hdim] at h
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [← neg_smul]
  have hpolarA : (∫ u : sphere (0 : InputSpace m) 1,
      (∫ r in Ioi (0 : ℝ), r ^ (m - 1) • G (r • (u : InputSpace m)))
        ∂(volume : Measure (InputSpace m)).toSphere) = ∫ ξ, G ξ := by
    have h := MeasureTheory.integral_eq_integral_toSphere_integral_Ioi
      (volume : Measure (InputSpace m)) hGint
    rw [hdim] at h
    exact h.symm
  have hpolarB : (∫ u : sphere (0 : InputSpace m) 1,
      (∫ r in Ioi (0 : ℝ), r ^ (m - 1) • G ((-r) • (u : InputSpace m)))
        ∂(volume : Measure (InputSpace m)).toSphere) = ∫ ξ, G (-ξ) := by
    have h := MeasureTheory.integral_eq_integral_toSphere_integral_Ioi
      (volume : Measure (InputSpace m)) hGnegint
    rw [hdim] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [neg_smul]
  unfold dualRadonTransform
  rw [integral_congr_ae (Filter.Eventually.of_forall hterm), integral_const_mul,
    integral_add hA hB, hpolarA, hpolarB, hinv, hinvneg]
  push_cast
  ring

/-! ## The ridgelet half of `thm:formula.radon` -/

/-- Theorem 5.7 (`thm:formula.radon`), the reconstruction formula via the Radon transform:
under the backprojection admissibility `eq:radon.ac`, the truncated ridgelet reconstruction
of a Schwartz function converges at every point to `2 (2π)^{m-1} f(x)` — the value of the
filtered backprojection `R† Λ^{m-1} R f` (stated separately as
`l1_radon_filtered_backprojection`). The proof computes the admissibility constant from the
backprojection data, `K_{ψ,η} = (2π)^{m-1} ∫ û = 2 (2π)^{m-1}`, and applies the
reconstruction formula `l1_reconstruction_formula` to the resulting admissible pair.

**Corrections and amendments to the article.**
* (2026-07-21) The statement uses the standard Lambda-operator power (multiplier
  `|ω|^{m-1}`); see `lambdaOperatorPow`.
* (2026-07-23) **Normalization of `eq:radon.ac` corrected to `∫ û = 2`**, replacing the
  article's `∫ û = -1`, settling the check recorded here previously. The truncation limit is
  `K_{ψ,η} f(x)` with `K_{ψ,η} = (2π)^{m-1} ∫ û` (by `tendsto_truncatedDualRidgeletTransform`
  and the spectral form of the backprojection equation), so the claimed agreement with the
  filtered backprojection `2 (2π)^{m-1} f` forces `∫ û = 2`. The article's own
  approximate-identity computation, redone with consistent constants, confirms this: for its
  kernel `k(z) = 𝓗u(z)/z` one has `∫ k = -π 𝓗²u(0) = π u(0) = ∫ û / 2`, so the
  normalization `∫ k = 1` also forces `∫ û = 2` (the article's chain
  `∫ k = -∫ 𝓗u(z)/(0-z) dz = -u(0) = 1` drops the factor `π` of the principal-value kernel
  and is inconsistent with `∫ û = -1`).
* (2026-07-22/23) As with `l1_reconstruction_formula`, the activation carries an explicit
  polynomial growth degree `k`, matched by a finite `k`-th moment and vanishing moments of
  `ψ`, and its Fourier data away from the origin is hypothesized
  (`HasFourierAwayFromOrigin`). The backprojection equation enters through its spectral form
  `conj (ψ̂ ζ) Fη ζ = |ζ|^m û(ζ)` on `ζ ≠ 0` together with `û ∈ L¹`; the physical form
  `Λ^m u = conj (ψ~) ⋆ η` reduces to it once the `L¹` Hilbert symbol is available (plan item
  A-3), and the smoothness and realness of `u` are not needed at this level. -/
theorem l1_reconstruction_formula_radon (m k : ℕ) [NeZero m]
    {ψ η Fη u : ℝ → ℂ} {Cη : ℝ} (f : SchwartzMap (InputSpace m) ℂ)
    (hψ : Integrable ψ volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hψvm : ∀ j ≤ k, (∫ s : ℝ, (s : ℂ) ^ j * ψ s) = 0)
    (hη : HasFourierAwayFromOrigin η Fη)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (hbp : ∀ ζ : ℝ, ζ ≠ 0 → conj (angularFourier1D ψ ζ) * Fη ζ
      = ((|ζ| ^ m : ℝ) : ℂ) * angularFourier1D u ζ)
    (huhat : Integrable (angularFourier1D u) volume)
    (hnorm : (∫ ζ, angularFourier1D u ζ) = 2) :
    ∀ x, Filter.Tendsto
      (fun q : ℝ × ℝ =>
        truncatedDualRidgeletTransform m 1 η
          (euclideanRidgeletTransform m 1 ψ (⇑f)) q.1 q.2 x)
      ridgeletTruncationFilter
      (𝓝 (((2 * (2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) * f x)) := by
  intro x
  -- the Schwartz data of the signal
  have hf : Integrable (⇑f) volume := f.integrable
  have hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume := by
    have h1 := f.integrable_pow_mul volume k
    have h2 : Integrable (fun y : InputSpace m =>
        (2 : ℝ) ^ k * (‖f y‖ + ‖y‖ ^ k * ‖f y‖)) volume :=
      (f.integrable.norm.add h1).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((by fun_prop : Continuous fun y : InputSpace m =>
        (1 + ‖y‖) ^ k)).aestronglyMeasurable.mul f.continuous.norm.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 := add_pow_le_two_pow_mul k (a := (1 : ℝ)) (b := ‖y‖) one_pos.le
        (norm_nonneg y)
      calc (1 + ‖y‖) ^ k * ‖f y‖ ≤ 2 ^ k * (1 ^ k + ‖y‖ ^ k) * ‖f y‖ := by
            gcongr
        _ = 2 ^ k * (‖f y‖ + ‖y‖ ^ k * ‖f y‖) := by ring
  have hfhat : Integrable (Fourier.angularFourierIntegralInner (⇑f)) volume := by
    have hne : ((2 * Real.pi : ℝ))⁻¹ ≠ 0 := by positivity
    have h𝓕 : Integrable (𝓕 (⇑f)) volume := by
      have h := (𝓕 f).integrable (μ := (volume : Measure (InputSpace m)))
      rwa [SchwartzMap.fourier_coe] at h
    have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure (InputSpace m))
      (𝓕 (⇑f)) hne).mpr h𝓕
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    exact (Fourier.angularFourierIntegralInner_eq_fourier (⇑f) ξ).symm
  -- the admissibility data of a spectral backprojection pair, and the corrected normalization
  have hKint : IntegrableOn
      (fun ζ => conj (angularFourier1D ψ ζ) * Fη ζ / ((|ζ| ^ m : ℝ) : ℂ))
      {(0 : ℝ)}ᶜ volume :=
    integrableOn_admissibilityIntegrand_of_backprojection hbp huhat.integrableOn
  have hK : admissibilityConstant m ψ Fη
      = ((2 * (2 * Real.pi) ^ (m - 1) : ℝ) : ℂ) := by
    rw [admissibilityConstant_of_backprojection hbp, restrict_compl_singleton, hnorm]
    push_cast
    ring
  -- assemble the admissible pair and apply the reconstruction formula
  have hKne : admissibilityConstant m ψ Fη ≠ 0 := by
    rw [hK]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hadm : IsAdmissiblePair m ψ η Fη := ⟨hψ, hη, hKint, hKne⟩
  have h := (l1_reconstruction_formula m k hadm hηk hψk hψvm hf hfk hfhat).2 x
    f.continuous.continuousAt
  rwa [hK] at h

end LeanRidgelet
