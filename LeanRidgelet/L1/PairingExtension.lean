/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs
public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.Transform.ClassicalSection
public import LeanRidgelet.ToMathlib.ProdShear
public import LeanRidgelet.ToMathlib.WeightedL1Smoothing
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# L1 theory: absolute convergence and the pairing extension (step T4)

At function level the reconstruction pairing converges absolutely only when the polynomial
growth of the activation is matched by moments of the ridgelet function and of the signal.
This file proves the absolute-convergence layer and the analytic core of the reconstruction
formula: the extension of the defining pairing of `HasFourierAwayFromOrigin` from Schwartz test
functions supported away from the origin to weighted-`L¹` functions with vanishing moments.

## Main results

* `LeanRidgelet.integrable_reflectedConjConvolution_integrand`,
  `LeanRidgelet.norm_reflectedConjConvolution_le`: the convolution kernel
  `w = conj (ψ~) ⋆ η` converges absolutely at every point and satisfies
  `‖w z‖ ≤ C_η ⬝ M_k(ψ) ⬝ (1 + |z|)^k`.
* `LeanRidgelet.integral_euclideanRidgeletTransform_mul_activation`: `eq:convdz` in Euclidean
  coordinates, `∫ R_ψ f (a, b) η (t - b) db = ‖a‖ ∫ f y ⬝ w (t - ⟨a, y⟩) dy`.
* `LeanRidgelet.hasFourierAwayFromOrigin_pairing_extension`: **step T4**,
  `∫ η Ξ = (2π)⁻¹ ∫_{ζ ≠ 0} Fη(ζ) Ξ̂(-ζ) dζ` for a weighted-`L¹` function `Ξ` with vanishing
  moments up to the growth degree of `η`.

The polynomial part of `η` is invisible on both sides of the pairing extension: on the right
because the integral omits the origin, on the left because the vanishing moments annihilate
polynomials. The two limit theorems it rests on — the weighted approximate identity and the
vanishing-moment cancellation for wide smoothing — are in
`LeanRidgelet.ToMathlib.WeightedL1Smoothing`.

## Deviations from the article

The moment hypotheses are necessary at function level and have no counterpart in the article,
which pairs in `𝒮₀'(ℝ)`: for growth degree `k ≥ 1` (already the ReLU) there are `f ∈ L¹` with
`f̂ ∈ L¹` whose truncated reconstruction integrand fails to be Bochner integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## The absolute-convergence layer -/

/-- Under a `k`-th moment bound on `ψ` and polynomial growth of degree `k` of `η`, the
defining integrand of the convolution `conj (ψ~) ⋆ η` is integrable at every point. -/
theorem integrable_reflectedConjConvolution_integrand (k : ℕ) {ψ η : ℝ → ℂ} {Cη : ℝ}
    (hψm : AEStronglyMeasurable ψ volume) (hηm : AEStronglyMeasurable η volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k) (z : ℝ) :
    Integrable (fun t : ℝ => conj (ψ (-t)) * η (z - t)) volume := by
  have hCη : 0 ≤ Cη := polynomiallyBounded_nonneg_const hηk
  have hmajneg : Integrable (fun t : ℝ => (1 + |t|) ^ k * ‖ψ (-t)‖) volume := by
    have h := hψk.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [abs_neg]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => conj (ψ (-t)) * η (z - t)) volume := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => conj (ψ (-t))) volume :=
      RCLike.continuous_conj.comp_aestronglyMeasurable
        (hψm.comp_quasiMeasurePreserving
          (Measure.measurePreserving_neg volume).quasiMeasurePreserving)
    have h2 : AEStronglyMeasurable (fun t : ℝ => η (z - t)) volume :=
      hηm.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving
    exact h1.mul h2
  refine ((hmajneg.const_mul (Cη * (1 + |z|) ^ k)).mono' hmeas
    (Filter.Eventually.of_forall fun t => ?_))
  have hb : ‖η (z - t)‖ ≤ Cη * ((1 + |z|) ^ k * (1 + |t|) ^ k) := by
    have h1 : (1 + |z - t|) ^ k ≤ ((1 + |z|) * (1 + |t|)) ^ k := by
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have := one_add_abs_add_le_mul z (-t)
      simpa [sub_eq_add_neg, abs_neg] using this
    calc ‖η (z - t)‖ ≤ Cη * (1 + |z - t|) ^ k := hηk _
      _ ≤ Cη * ((1 + |z|) * (1 + |t|)) ^ k := by
          exact mul_le_mul_of_nonneg_left h1 hCη
      _ = Cη * ((1 + |z|) ^ k * (1 + |t|) ^ k) := by rw [mul_pow]
  calc ‖conj (ψ (-t)) * η (z - t)‖ = ‖ψ (-t)‖ * ‖η (z - t)‖ := by
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ ‖ψ (-t)‖ * (Cη * ((1 + |z|) ^ k * (1 + |t|) ^ k)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = Cη * (1 + |z|) ^ k * ((1 + |t|) ^ k * ‖ψ (-t)‖) := by ring

/-- Under matched moment and growth hypotheses, the convolution `w = conj (ψ~) ⋆ η` obeys the
growth bound `‖w z‖ ≤ Cη ⋅ (∫ (1+|s|)^k ‖ψ s‖ ds) ⋅ (1+|z|)^k` at every point. -/
theorem norm_reflectedConjConvolution_le (k : ℕ) {ψ η : ℝ → ℂ} {Cη : ℝ}
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k) (z : ℝ) :
    ‖reflectedConjConvolution ψ η z‖ ≤
      Cη * (∫ s : ℝ, (1 + |s|) ^ k * ‖ψ s‖) * (1 + |z|) ^ k := by
  have hCη : 0 ≤ Cη := polynomiallyBounded_nonneg_const hηk
  have hmajneg : Integrable (fun t : ℝ => (1 + |t|) ^ k * ‖ψ (-t)‖) volume := by
    have h := hψk.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [abs_neg]
  have hconv : reflectedConjConvolution ψ η z = ∫ t : ℝ, conj (ψ (-t)) * η (z - t) := by
    simp only [reflectedConjConvolution, convolution_def, ContinuousLinearMap.mul_apply']
  rw [hconv]
  have hpt : ∀ t : ℝ, ‖conj (ψ (-t)) * η (z - t)‖ ≤
      Cη * (1 + |z|) ^ k * ((1 + |t|) ^ k * ‖ψ (-t)‖) := by
    intro t
    have h1 : (1 + |z - t|) ^ k ≤ ((1 + |z|) * (1 + |t|)) ^ k := by
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have := one_add_abs_add_le_mul z (-t)
      simpa [sub_eq_add_neg, abs_neg] using this
    calc ‖conj (ψ (-t)) * η (z - t)‖ = ‖ψ (-t)‖ * ‖η (z - t)‖ := by
          rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖ψ (-t)‖ * (Cη * ((1 + |z|) * (1 + |t|)) ^ k) := by
          refine mul_le_mul_of_nonneg_left ((hηk _).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h1 hCη
      _ = Cη * (1 + |z|) ^ k * ((1 + |t|) ^ k * ‖ψ (-t)‖) := by
          rw [mul_pow]; ring
  calc ‖∫ t : ℝ, conj (ψ (-t)) * η (z - t)‖
      ≤ ∫ t : ℝ, ‖conj (ψ (-t)) * η (z - t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Cη * (1 + |z|) ^ k * ((1 + |t|) ^ k * ‖ψ (-t)‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hmajneg.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = Cη * (1 + |z|) ^ k * ∫ t : ℝ, (1 + |t|) ^ k * ‖ψ (-t)‖ := integral_const_mul _ _
    _ = Cη * (∫ s : ℝ, (1 + |s|) ^ k * ‖ψ s‖) * (1 + |z|) ^ k := by
        have hg : (∫ t : ℝ, (1 + |t|) ^ k * ‖ψ (-t)‖)
            = ∫ s : ℝ, (1 + |s|) ^ k * ‖ψ s‖ := by
          rw [← MeasureTheory.integral_neg_eq_self (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          simp [abs_neg]
        rw [hg]
        ring

/-- The bias pairing of the ridgelet transform against a polynomially growing activation
factors through the convolution kernel `w = conj (ψ~) ⋆ η` (`eq:convdz` in Euclidean
coordinates): `∫ b, R_ψ f (a, b) ⋅ η (t - b) db = ‖a‖ ⋅ ∫ y, f y ⋅ w (t - ⟨a, y⟩) dy`,
absolutely convergent under matched `k`-th moments of `ψ` and `f`. -/
theorem integral_euclideanRidgeletTransform_mul_activation (m k : ℕ)
    {ψ η : ℝ → ℂ} {f : InputSpace m → ℂ} {Cη : ℝ}
    (hf : Integrable f volume)
    (hfk : Integrable (fun y : InputSpace m => (1 + ‖y‖) ^ k * ‖f y‖) volume)
    (hψm : AEStronglyMeasurable ψ volume) (hηm : AEStronglyMeasurable η volume)
    (hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (a : InputSpace m) (t : ℝ) :
    ∫ b, euclideanRidgeletTransform m 1 ψ f (a, b) * η (t - b)
      = ((‖a‖ : ℝ) : ℂ) * ∫ y, f y * reflectedConjConvolution ψ η (t - inner ℝ a y) := by
  have hCη : 0 ≤ Cη := polynomiallyBounded_nonneg_const hηk
  -- the base kernel in the sheared variables `(y, s)` with `s` the preactivation
  set F : InputSpace m × ℝ → ℂ := fun q =>
    f q.1 * conj (ψ q.2) * η (t - inner ℝ q.1 a + q.2) with hF_def
  have hFmeas : AEStronglyMeasurable F volume := by
    have h1 : AEStronglyMeasurable (fun q : InputSpace m × ℝ => f q.1) volume := by
      rw [Measure.volume_eq_prod]
      exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    have h2 : AEStronglyMeasurable (fun q : InputSpace m × ℝ => conj (ψ q.2)) volume := by
      rw [Measure.volume_eq_prod]
      exact RCLike.continuous_conj.comp_aestronglyMeasurable
        (hψm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    have h3 : AEStronglyMeasurable
        (fun q : InputSpace m × ℝ => η (t - inner ℝ q.1 a + q.2)) volume := by
      have hshift : (fun q : InputSpace m × ℝ => η (t - inner ℝ q.1 a + q.2))
          = (fun q : InputSpace m × ℝ => η (t - q.2)) ∘
            (fun q : InputSpace m × ℝ => (q.1, inner ℝ q.1 a - q.2)) := by
        funext q
        simp only [Function.comp_apply]
        ring_nf
      rw [hshift]
      have hinner : AEStronglyMeasurable
          (fun q : InputSpace m × ℝ => η (t - q.2)) volume := by
        rw [Measure.volume_eq_prod]
        exact (hηm.comp_quasiMeasurePreserving
          (Measure.measurePreserving_sub_left volume t).quasiMeasurePreserving
          ).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      exact hinner.comp_quasiMeasurePreserving
        (measurePreserving_preactivationShear a).quasiMeasurePreserving
    exact (h1.mul h2).mul h3
  have hFint : Integrable F volume := by
    have hmaj : Integrable (fun q : InputSpace m × ℝ =>
        ((1 + ‖q.1‖) ^ k * ‖f q.1‖) * ((1 + |q.2|) ^ k * ‖ψ q.2‖)) volume := by
      rw [Measure.volume_eq_prod]
      exact Integrable.mul_prod hfk hψk
    refine ((hmaj.const_mul (Cη * (1 + |t|) ^ k * (1 + ‖a‖) ^ k)).mono' hFmeas
      (Filter.Eventually.of_forall fun q => ?_))
    have hip : |inner ℝ q.1 a| ≤ ‖q.1‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h1 : 1 + |t - inner ℝ q.1 a + q.2| ≤
        (1 + |t|) * ((1 + ‖a‖) * (1 + ‖q.1‖)) * (1 + |q.2|) := by
      have ha : 1 + |t - inner ℝ q.1 a + q.2| ≤
          (1 + |t - inner ℝ q.1 a|) * (1 + |q.2|) := one_add_abs_add_le_mul _ _
      have hb : 1 + |t - inner ℝ q.1 a| ≤ (1 + |t|) * (1 + |inner ℝ q.1 a|) := by
        have := one_add_abs_add_le_mul t (-(inner ℝ q.1 a))
        simpa [sub_eq_add_neg, abs_neg] using this
      have hc : 1 + |inner ℝ q.1 a| ≤ (1 + ‖a‖) * (1 + ‖q.1‖) := by
        have h2 : |inner ℝ q.1 a| ≤ ‖q.1‖ * ‖a‖ := hip
        nlinarith [norm_nonneg q.1, norm_nonneg a]
      calc 1 + |t - inner ℝ q.1 a + q.2|
          ≤ (1 + |t - inner ℝ q.1 a|) * (1 + |q.2|) := ha
        _ ≤ ((1 + |t|) * ((1 + ‖a‖) * (1 + ‖q.1‖))) * (1 + |q.2|) := by
            refine mul_le_mul_of_nonneg_right (hb.trans ?_) (by positivity)
            exact mul_le_mul_of_nonneg_left hc (by positivity)
    have hηb : ‖η (t - inner ℝ q.1 a + q.2)‖ ≤
        Cη * ((1 + |t|) * ((1 + ‖a‖) * (1 + ‖q.1‖)) * (1 + |q.2|)) ^ k := by
      refine (hηk _).trans (mul_le_mul_of_nonneg_left ?_ hCη)
      exact pow_le_pow_left₀ (by positivity) h1 k
    calc ‖F q‖ = ‖f q.1‖ * ‖ψ q.2‖ * ‖η (t - inner ℝ q.1 a + q.2)‖ := by
          rw [hF_def]
          simp only [norm_mul, RCLike.norm_conj]
      _ ≤ ‖f q.1‖ * ‖ψ q.2‖ *
          (Cη * ((1 + |t|) * ((1 + ‖a‖) * (1 + ‖q.1‖)) * (1 + |q.2|)) ^ k) := by
          exact mul_le_mul_of_nonneg_left hηb (by positivity)
      _ = Cη * (1 + |t|) ^ k * (1 + ‖a‖) ^ k *
          (((1 + ‖q.1‖) ^ k * ‖f q.1‖) * ((1 + |q.2|) ^ k * ‖ψ q.2‖)) := by
          rw [mul_pow, mul_pow, mul_pow]
          ring
  -- transport along the preactivation shear to the `(y, b)` kernel
  have hKint : Integrable (fun p : InputSpace m × ℝ =>
      f p.1 * conj (ψ (inner ℝ a p.1 - p.2)) * η (t - p.2)) volume := by
    have h := integrable_comp_preactivationShear a hFint
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    rw [hF_def]
    simp only []
    rw [real_inner_comm a p.1]
    ring_nf
  -- Fubini: swap the bias and input integrals
  have hswap : ∫ b, ∫ y, f y * conj (ψ (inner ℝ a y - b)) * η (t - b)
      = ∫ y, ∫ b, f y * conj (ψ (inner ℝ a y - b)) * η (t - b) := by
    rw [Measure.volume_eq_prod] at hKint
    exact (integral_integral_swap hKint).symm
  -- identify the left-hand side, extracting the norm factor
  have hlhs : ∫ b, euclideanRidgeletTransform m 1 ψ f (a, b) * η (t - b)
      = ((‖a‖ : ℝ) : ℂ) * ∫ b, ∫ y, f y * conj (ψ (inner ℝ a y - b)) * η (t - b) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    unfold euclideanRidgeletTransform
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    have hone : ((‖a‖ ^ (1 : ℝ) : ℝ) : ℂ) = ((‖a‖ : ℝ) : ℂ) :=
      congrArg Complex.ofReal (Real.rpow_one _)
    rw [hone]
    ring
  -- identify the fiber integral with the convolution kernel
  have hfiber : ∀ y : InputSpace m,
      ∫ b, f y * conj (ψ (inner ℝ a y - b)) * η (t - b)
        = f y * reflectedConjConvolution ψ η (t - inner ℝ a y) := by
    intro y
    have hconv : reflectedConjConvolution ψ η (t - inner ℝ a y)
        = ∫ τ : ℝ, conj (ψ (-τ)) * η ((t - inner ℝ a y) - τ) := by
      simp only [reflectedConjConvolution, convolution_def, ContinuousLinearMap.mul_apply']
    have htrans : ∫ b, conj (ψ (inner ℝ a y - b)) * η (t - b)
        = ∫ τ : ℝ, conj (ψ (-τ)) * η ((t - inner ℝ a y) - τ) := by
      rw [← MeasureTheory.integral_add_right_eq_self
        (fun b : ℝ => conj (ψ (inner ℝ a y - b)) * η (t - b)) (inner ℝ a y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      dsimp only
      have h1 : inner ℝ a y - (τ + inner ℝ a y) = -τ := by ring
      have h2 : t - (τ + inner ℝ a y) = t - inner ℝ a y - τ := by ring
      rw [h1, h2]
    calc ∫ b, f y * conj (ψ (inner ℝ a y - b)) * η (t - b)
        = ∫ b, f y * (conj (ψ (inner ℝ a y - b)) * η (t - b)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          ring
      _ = f y * ∫ b, conj (ψ (inner ℝ a y - b)) * η (t - b) := integral_const_mul _ _
      _ = f y * reflectedConjConvolution ψ η (t - inner ℝ a y) := by
          rw [htrans, hconv]
  -- assemble
  calc ∫ b, euclideanRidgeletTransform m 1 ψ f (a, b) * η (t - b)
      = ((‖a‖ : ℝ) : ℂ) * ∫ b, ∫ y, f y * conj (ψ (inner ℝ a y - b)) * η (t - b) := hlhs
    _ = ((‖a‖ : ℝ) : ℂ) * ∫ y, ∫ b, f y * conj (ψ (inner ℝ a y - b)) * η (t - b) := by
        rw [hswap]
    _ = ((‖a‖ : ℝ) : ℂ) * ∫ y, f y * reflectedConjConvolution ψ η (t - inner ℝ a y) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hfiber)]

/-! ## The pairing extension (step T4) -/

set_option maxHeartbeats 1600000 in
-- The proof is a single long assembly of Fubini swaps, changes of variables, and
-- dominated-convergence estimates; it needs more than the default heartbeat budget.
open Filter in
open scoped ContDiff in
/-- **Pairing extension for Fourier data away from the origin** (step T4 of the
reconstruction plan): for an activation `η` of polynomial growth degree `k` with Fourier data
`Fη` away from the origin, and a weighted-`L¹` function `Ξ` with vanishing moments up to `k`,
the pairing `∫ η Ξ` is computed by `Fη` against the spectral data of `Ξ`:
`∫ η(z) Ξ(z) dz = (2π)⁻¹ ∫_{ζ≠0} Fη(ζ) Ξ̂(-ζ) dζ`, provided the right-hand side converges
absolutely.

The point masses at the origin of the distributional Fourier transform of `η` — its
polynomial part — are invisible on both sides: on the right because the integral omits the
origin, on the left because the vanishing moments of `Ξ` annihilate polynomials. This is the
function-level realization of the dual pairing of the Lizorkin quotient `𝒮'(ℝ)/𝒫`.

Proof: the defining pairing of `HasFourierAwayFromOrigin` is applied to the Schwartz test
functions `φ_{n,ℓ} = c_n ⋅ (κ_ℓ ⋆ χ)` where `χ(ζ) = Ξ̂(-ζ)`, `κ_ℓ` is a compactly supported
mollifier, and `c_n = b(ζ/n) - b(nζ)` a smooth cutoff vanishing near the origin and tapering
at `|ζ| ~ n`; the transform identity
`angularFourier1D φ_{n,ℓ} (z) = ∫ Ξ(r) κ̂_ℓ(r) ĉ_n(z-r) dr` holds by two absolutely
convergent Fubini computations. As `ℓ → ∞` the frequency side converges by dominated
convergence with majorant `|Fη ⋅ χ|` (compactly supported away from the origin), the time
side with majorant built from `κ̂_ℓ ≤ 1`. As `n → ∞`, `ĉ_n(s) = n b̂(ns) - n⁻¹ b̂(s/n)`
splits the time side into a taper term, which converges to `2π ∫ η Ξ` by the weighted
approximate identity (`MeasureTheory.tendsto_integral_weight_norm_smoothing_sub`, with
kernel `(2π)⁻¹ b̂` of unit integral), and a low-cut term, which vanishes by the
vanishing-moment cancellation
(`MeasureTheory.tendsto_integral_mul_smoothing_of_vanishing_moments`). -/
theorem hasFourierAwayFromOrigin_pairing_extension (k : ℕ)
    {η Fη : ℝ → ℂ} (hη : HasFourierAwayFromOrigin η Fη)
    {Cη : ℝ} (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    {Ξ : ℝ → ℂ} (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume)
    (hΞvm : ∀ j ≤ k, (∫ r : ℝ, (r : ℂ) ^ j * Ξ r) = 0)
    (hFΞ : IntegrableOn (fun ζ : ℝ => Fη ζ * angularFourier1D Ξ (-ζ)) {(0 : ℝ)}ᶜ volume) :
    ∫ z : ℝ, η z * Ξ z =
      (2 * Real.pi)⁻¹ * ∫ ζ in {(0 : ℝ)}ᶜ, Fη ζ * angularFourier1D Ξ (-ζ) := by
  classical
  obtain ⟨hηloc, hηpoly, hFηloc, hpair⟩ := hη
  have hCη : 0 ≤ Cη := by
    have h := hηk 0
    have h2 : ‖η 0‖ ≤ Cη := by simpa using h
    exact le_trans (norm_nonneg _) h2
  -- strongly measurable representatives satisfying the growth bound pointwise
  set Ξ' : ℝ → ℂ := hΞm.mk Ξ with hΞ'_def
  have hΞ'sm : StronglyMeasurable Ξ' := hΞm.stronglyMeasurable_mk
  have hΞ'ae : Ξ =ᵐ[volume] Ξ' := hΞm.ae_eq_mk
  have hη₀m : AEStronglyMeasurable η volume := hηloc.aestronglyMeasurable
  set η₀ : ℝ → ℂ := hη₀m.mk η with hη₀_def
  have hη₀sm : StronglyMeasurable η₀ := hη₀m.stronglyMeasurable_mk
  have hη₀ae : η =ᵐ[volume] η₀ := hη₀m.ae_eq_mk
  set η' : ℝ → ℂ := fun z => if ‖η₀ z‖ ≤ Cη * (1 + |z|) ^ k then η₀ z else 0 with hη'_def
  have hη'sm : StronglyMeasurable η' := by
    refine StronglyMeasurable.ite ?_ hη₀sm stronglyMeasurable_const
    exact measurableSet_le hη₀sm.measurable.norm (by fun_prop)
  have hη'k : ∀ z, ‖η' z‖ ≤ Cη * (1 + |z|) ^ k := by
    intro z
    rw [hη'_def]
    simp only []
    split_ifs with h
    · exact h
    · rw [norm_zero]
      positivity
  have hη'ae : η =ᵐ[volume] η' := by
    filter_upwards [hη₀ae] with z hz
    rw [hη'_def]
    simp only []
    rw [if_pos]
    · exact hz
    · rw [← hz]
      exact hηk z
  -- transfer the statement to the representatives
  have hΞ'hat : ∀ ζ : ℝ, angularFourier1D Ξ ζ = angularFourier1D Ξ' ζ := fun ζ =>
    integral_congr_ae (by filter_upwards [hΞ'ae] with r h; rw [h])
  have hgoalL : (∫ z : ℝ, η z * Ξ z) = ∫ z : ℝ, η' z * Ξ' z := by
    refine integral_congr_ae ?_
    filter_upwards [hη'ae, hΞ'ae] with z h1 h2
    rw [h1, h2]
  have hgoalR : (∫ ζ in {(0 : ℝ)}ᶜ, Fη ζ * angularFourier1D Ξ (-ζ))
      = ∫ ζ in {(0 : ℝ)}ᶜ, Fη ζ * angularFourier1D Ξ' (-ζ) := by
    refine setIntegral_congr_fun (measurableSet_singleton (0 : ℝ)).compl fun ζ _ => ?_
    rw [hΞ'hat]
  rw [hgoalL, hgoalR]
  -- transfer the hypotheses
  have hΞ'k : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ' r‖) volume := by
    refine hΞk.congr ?_
    filter_upwards [hΞ'ae] with r h
    rw [h]
  have hΞ'vm : ∀ j ≤ k, (∫ r : ℝ, (r : ℂ) ^ j * Ξ' r) = 0 := by
    intro j hj
    rw [← hΞvm j hj]
    refine integral_congr_ae ?_
    filter_upwards [hΞ'ae] with r h
    rw [h]
  have hFΞ' : IntegrableOn (fun ζ : ℝ => Fη ζ * angularFourier1D Ξ' (-ζ))
      {(0 : ℝ)}ᶜ volume := by
    refine hFΞ.congr_fun (fun ζ _ => ?_) (measurableSet_singleton (0 : ℝ)).compl
    try simp only []
    rw [hΞ'hat]
  have hpair' : ∀ φ : SchwartzMap ℝ ℂ, tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ →
      (∫ ζ : ℝ, Fη ζ * φ ζ) = ∫ z : ℝ, η' z * angularFourier1D (⇑φ) z := by
    intro φ hφ
    rw [hpair φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hη'ae] with z h
    rw [h]
  have hΞ'int : Integrable Ξ' volume := by
    refine hΞ'k.mono' hΞ'sm.aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
    have h1 : (1 : ℝ) ≤ (1 + |r|) ^ k := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg r))
    nlinarith [norm_nonneg (Ξ' r)]
  have hinner_mul : ∀ a c : ℝ, (inner ℝ a c : ℝ) = a * c := by
    intro a c
    rw [RCLike.inner_apply, conj_trivial]
    ring
  -- ==================== bump machinery ====================
  set b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hb_def
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [hb_def])
  have hbzero : ∀ ζ : ℝ, 2 ≤ |ζ| → b ζ = 0 := fun ζ hζ =>
    b.zero_of_le_dist (by simpa [Real.dist_eq, hb_def] using hζ)
  have hbCsm : ContDiff ℝ ∞ (fun ζ : ℝ => ((b ζ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbCsupp : HasCompactSupport fun ζ : ℝ => ((b ζ : ℝ) : ℂ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) fun ζ hζ => ?_
    have h2 : 2 ≤ |ζ| := by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hζ
      linarith
    simp [hbzero ζ h2]
  set bS : SchwartzMap ℝ ℂ := hbCsupp.toSchwartzMap hbCsm with hbS_def
  have hbS_coe : ⇑bS = fun ζ : ℝ => ((b ζ : ℝ) : ℂ) := rfl
  set bhat : SchwartzMap ℝ ℂ := Fourier.angularFourierSchwartz bS with hbhat_def
  have hbhat_coe : angularFourier1D (⇑bS) = ⇑bhat := angularFourier1D_coe_schwartz bS
  -- total transform mass of the bump
  have hbhat_int_eq : (∫ s : ℝ, bhat s) = ((2 * Real.pi : ℝ) : ℂ) := by
    have hb1 : ∀ s : ℝ, bhat s = 𝓕 (⇑bS) ((2 * Real.pi)⁻¹ * s) := by
      intro s
      rw [← congrFun hbhat_coe s]
      have h := Fourier.angularFourierIntegralInner_eq_fourier (⇑bS) s
      simpa [angularFourier1D, smul_eq_mul] using h
    have hFint : Integrable (𝓕 (⇑bS)) volume := by
      rw [← SchwartzMap.fourier_coe]
      exact SchwartzMap.integrable _
    have hinv : (∫ w : ℝ, 𝓕 (⇑bS) w) = bS 0 := by
      have h1 : 𝓕⁻ (𝓕 ⇑bS) = ⇑bS :=
        bS.continuous.fourierInv_fourier_eq (SchwartzMap.integrable _) hFint
      have h2 : 𝓕⁻ (𝓕 ⇑bS) 0 = ∫ w : ℝ, 𝓕 (⇑bS) w := by
        rw [Real.fourierInv_eq]
        simp
      rw [← h2, h1]
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    calc (∫ s : ℝ, bhat s)
        = ∫ s : ℝ, 𝓕 (⇑bS) (s / (2 * Real.pi)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          simp only []
          rw [hb1 s, div_eq_inv_mul]
      _ = (2 * Real.pi) • ∫ w : ℝ, 𝓕 (⇑bS) w := by
          have h := MeasureTheory.integral_comp_sub_div_smul (𝓕 (⇑bS)) 0 hπ
          rw [← h]
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          simp only []
          rw [sub_zero]
      _ = ((2 * Real.pi : ℝ) : ℂ) := by
          rw [hinv, hbS_coe]
          simp only []
          rw [hb0]
          simp [Complex.real_smul]
  -- ==================== mollifier machinery ====================
  set κb : ℕ → ContDiffBump (0 : ℝ) := fun ℓ =>
    ⟨((ℓ : ℝ) + 2)⁻¹ / 2, ((ℓ : ℝ) + 2)⁻¹, by positivity, by
      have h : (0 : ℝ) < ((ℓ : ℝ) + 2)⁻¹ := by positivity
      linarith [half_lt_self h]⟩ with hκb_def
  have hκrOut : Tendsto (fun ℓ : ℕ => (κb ℓ).rOut) atTop (𝓝 0) := by
    have h : Tendsto (fun ℓ : ℕ => ((ℓ : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
      refine Tendsto.inv_tendsto_atTop ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hκb_def] using h
  set κC : ℕ → ℝ → ℂ := fun ℓ ν => (((κb ℓ).normed volume ν : ℝ) : ℂ) with hκC_def
  set κhat : ℕ → ℝ → ℂ := fun ℓ => angularFourier1D (κC ℓ) with hκhat_def
  have hκCint : ∀ ℓ : ℕ, Integrable (κC ℓ) volume := by
    intro ℓ
    rw [hκC_def]
    exact ((κb ℓ).integrable_normed).ofReal
  have hκhat_bound : ∀ ℓ (r : ℝ), ‖κhat ℓ r‖ ≤ 1 := by
    intro ℓ r
    rw [hκhat_def]
    simp only []
    rw [angularFourier1D]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have h1 : (∫ x : ℝ, ‖Complex.exp (-Complex.I * (inner ℝ x r : ℝ)) * κC ℓ x‖)
        = ∫ x : ℝ, (κb ℓ).normed volume x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [norm_mul, Complex.norm_exp]
      simp only [hκC_def]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((κb ℓ).nonneg_normed x)]
      have hre : (-Complex.I * ((inner ℝ x r : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre]
      simp
    rw [h1, (κb ℓ).integral_normed]
  -- the mollifier transforms tend to one pointwise
  have hκhat_tendsto : ∀ r : ℝ, Tendsto (fun ℓ : ℕ => κhat ℓ r) atTop (𝓝 1) := by
    intro r
    have hg : Continuous fun ν : ℝ => Complex.exp (-Complex.I * ((-ν * r : ℝ) : ℂ)) := by
      fun_prop
    have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      hκrOut hg 0
    have hval : ∀ ℓ : ℕ, ((κb ℓ).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun ν : ℝ => Complex.exp (-Complex.I * ((-ν * r : ℝ) : ℂ))) 0 = κhat ℓ r := by
      intro ℓ
      rw [convolution_def, hκhat_def]
      simp only []
      rw [angularFourier1D, Fourier.angularFourierIntegralInner]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, hκC_def]
      rw [Complex.real_smul, hinner_mul]
      have harg : -(0 - t) * r = t * r := by ring
      rw [harg]
      ring
    have h2 := h.congr hval
    have h3 : Complex.exp (-Complex.I * ((-(0:ℝ) * r : ℝ) : ℂ)) = 1 := by
      norm_num
    rw [h3] at h2
    exact h2
  -- ==================== cutoff machinery ====================
  set cC : ℕ → ℝ → ℂ := fun n ζ => (((b (ζ / n) - b (n * ζ) : ℝ)) : ℂ) with hcC_def
  have hcCsm : ∀ n : ℕ, ContDiff ℝ ∞ (cC n) := by
    intro n
    refine Complex.ofRealCLM.contDiff.comp (ContDiff.sub ?_ ?_)
    · exact b.contDiff.comp (contDiff_id.div_const _)
    · exact b.contDiff.comp (contDiff_const.mul contDiff_id)
  have hcCsupp : ∀ n : ℕ, 1 ≤ n → HasCompactSupport (cC n) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * n)) fun ζ hζ => ?_
    have h2 : 2 * (n : ℝ) < |ζ| := by
      simpa [Real.dist_eq] using hζ
    have hz1 : b (ζ / n) = 0 := by
      refine hbzero _ ?_
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hz2 : b (n * ζ) = 0 := by
      refine hbzero _ ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
      nlinarith [abs_nonneg ζ]
    rw [hcC_def]
    simp [hz1, hz2]
  have hcC_away : ∀ n : ℕ, 1 ≤ n → tsupport (cC n) ⊆ {(0 : ℝ)}ᶜ := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hzero : ∀ ζ : ℝ, |ζ| ≤ (n : ℝ)⁻¹ → cC n ζ = 0 := by
      intro ζ hζ
      have h1 : b (ζ / n) = 1 := by
        refine b.one_of_mem_closedBall ?_
        simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, hb_def]
        rw [abs_div, abs_of_pos hn0, div_le_one hn0]
        calc |ζ| ≤ (n : ℝ)⁻¹ := hζ
          _ ≤ 1 := by
              rw [inv_le_one_iff₀]
              right
              exact hn1
          _ ≤ (n : ℝ) := hn1
      have h2 : b (n * ζ) = 1 := by
        refine b.one_of_mem_closedBall ?_
        simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, hb_def]
        rw [abs_mul, abs_of_pos hn0]
        calc (n : ℝ) * |ζ| ≤ (n : ℝ) * (n : ℝ)⁻¹ := by
              exact mul_le_mul_of_nonneg_left hζ hn0.le
          _ = 1 := mul_inv_cancel₀ hn0.ne'
      rw [hcC_def]
      simp [h1, h2]
    have hsub : Function.support (cC n) ⊆ {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} := by
      intro ζ hζ
      by_contra h
      simp only [Set.mem_setOf_eq, not_le] at h
      exact hζ (hzero ζ h.le)
    have hclosed : IsClosed {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} :=
      isClosed_le continuous_const continuous_abs
    refine subset_trans (closure_minimal hsub hclosed) fun ζ hζ => ?_
    simp only [Set.mem_setOf_eq] at hζ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h0
    rw [h0] at hζ
    simp only [abs_zero] at hζ
    have : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    linarith
  -- transform of the cutoffs through the bump transform
  set chat : ℕ → ℝ → ℂ := fun n => angularFourier1D (cC n) with hchat_def
  have hbCint : Integrable (fun ζ : ℝ => ((b ζ : ℝ) : ℂ)) volume := by
    rw [← hbS_coe]
    exact SchwartzMap.integrable bS
  have hchat_eq : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ,
      chat n s = (n : ℝ) • bhat ((n : ℝ) * s) - (n : ℝ)⁻¹ • bhat (s / n) := by
    intro n hn s
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    -- integrability of the two pieces
    have hb'1 : Integrable (fun ζ : ℝ => ((b (ζ / n) : ℝ) : ℂ)) volume := by
      have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℝ)
        (fun ζ : ℝ => ((b ζ : ℝ) : ℂ)) (inv_ne_zero hn0.ne')).mpr hbCint
      refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
      simp only []
      rw [smul_eq_mul, ← div_eq_inv_mul]
    have hb'2 : Integrable (fun ζ : ℝ => ((b ((n : ℝ) * ζ) : ℝ) : ℂ)) volume := by
      have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℝ)
        (fun ζ : ℝ => ((b ζ : ℝ) : ℂ)) hn0.ne').mpr hbCint
      refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
      simp only []
      rw [smul_eq_mul]
    have hexp_meas : AEStronglyMeasurable
        (fun ζ : ℝ => Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ))) volume := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have hexp_bd : ∀ ζ : ℝ, ‖Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ))‖ ≤ 1 := by
      intro ζ
      rw [Complex.norm_exp]
      have hre : (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre]
      simp
    have hi1 : Integrable (fun ζ : ℝ =>
        Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) * ((b (ζ / n) : ℝ) : ℂ))
        volume := by
      refine Integrable.bdd_mul (c := 1) hb'1 hexp_meas
        (Filter.Eventually.of_forall fun ζ => hexp_bd ζ)
    have hi2 : Integrable (fun ζ : ℝ =>
        Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) * ((b ((n : ℝ) * ζ) : ℝ) : ℂ))
        volume := by
      refine Integrable.bdd_mul (c := 1) hb'2 hexp_meas
        (Filter.Eventually.of_forall fun ζ => hexp_bd ζ)
    -- the two scaled transforms
    have hT1 : (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
        ((b (ζ / n) : ℝ) : ℂ)) = (n : ℝ) • bhat ((n : ℝ) * s) := by
      have h := MeasureTheory.integral_comp_sub_div_smul
        (fun v : ℝ => Complex.exp (-Complex.I * ((inner ℝ ((n : ℝ) * v) s : ℝ) : ℂ)) *
          ((b v : ℝ) : ℂ)) 0 hn0
      calc (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
            ((b (ζ / n) : ℝ) : ℂ))
          = ∫ w : ℝ, Complex.exp
              (-Complex.I * ((inner ℝ ((n : ℝ) * ((w - 0) / n)) s : ℝ) : ℂ)) *
              ((b ((w - 0) / n) : ℝ) : ℂ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            simp only []
            have h1 : (n : ℝ) * ((w - 0) / n) = w := by
              rw [sub_zero]
              field_simp
            rw [h1, sub_zero]
        _ = (n : ℝ) • ∫ v : ℝ, Complex.exp
              (-Complex.I * ((inner ℝ ((n : ℝ) * v) s : ℝ) : ℂ)) * ((b v : ℝ) : ℂ) := h
        _ = (n : ℝ) • bhat ((n : ℝ) * s) := by
            congr 1
            rw [← congrFun hbhat_coe ((n : ℝ) * s), angularFourier1D,
              Fourier.angularFourierIntegralInner]
            refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
            simp only [hbS_coe]
            rw [hinner_mul, hinner_mul]
            have h2 : (n : ℝ) * v * s = v * ((n : ℝ) * s) := by ring
            rw [h2]
    have hT2 : (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
        ((b ((n : ℝ) * ζ) : ℝ) : ℂ)) = (n : ℝ)⁻¹ • bhat (s / n) := by
      have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      have h := MeasureTheory.integral_comp_sub_div_smul
        (fun v : ℝ => Complex.exp (-Complex.I * ((inner ℝ (v / n) s : ℝ) : ℂ)) *
          ((b v : ℝ) : ℂ)) 0 hninv
      calc (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
            ((b ((n : ℝ) * ζ) : ℝ) : ℂ))
          = ∫ w : ℝ, Complex.exp
              (-Complex.I * ((inner ℝ (((w - 0) / (n : ℝ)⁻¹) / n) s : ℝ) : ℂ)) *
              ((b ((w - 0) / (n : ℝ)⁻¹) : ℝ) : ℂ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            simp only []
            have h1 : (w - 0) / (n : ℝ)⁻¹ = (n : ℝ) * w := by
              rw [sub_zero, div_eq_mul_inv, inv_inv, mul_comm]
            rw [h1]
            have h2 : (n : ℝ) * w / n = w := by
              field_simp
            rw [h2]
        _ = (n : ℝ)⁻¹ • ∫ v : ℝ, Complex.exp
              (-Complex.I * ((inner ℝ (v / n) s : ℝ) : ℂ)) * ((b v : ℝ) : ℂ) := h
        _ = (n : ℝ)⁻¹ • bhat (s / n) := by
            congr 1
            rw [← congrFun hbhat_coe (s / n), angularFourier1D,
              Fourier.angularFourierIntegralInner]
            refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
            simp only [hbS_coe]
            rw [hinner_mul, hinner_mul]
            have h2 : v / n * s = v * (s / n) := by ring
            rw [h2]
    -- assemble
    rw [hchat_def]
    simp only []
    rw [angularFourier1D, Fourier.angularFourierIntegralInner]
    have hsplit : (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) * cC n ζ)
        = (∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
            ((b (ζ / n) : ℝ) : ℂ)) -
          ∫ ζ : ℝ, Complex.exp (-Complex.I * ((inner ℝ ζ s : ℝ) : ℂ)) *
            ((b ((n : ℝ) * ζ) : ℝ) : ℂ) := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only [hcC_def]
      push_cast
      ring
    rw [hsplit, hT1, hT2]
  -- ==================== global measure bookkeeping ====================
  have hrestrict : (volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ = volume := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.restrict_apply hs, ← Set.sdiff_eq, measure_sdiff_null']
    exact measure_mono_null Set.inter_subset_right (measure_singleton 0)
  have hFηm : AEStronglyMeasurable Fη volume := by
    have h := hFηloc.aestronglyMeasurable
    rwa [hrestrict] at h
  -- ==================== cutoff support and limit facts ====================
  have hcC_zero_small : ∀ n : ℕ, 1 ≤ n → ∀ ζ : ℝ, |ζ| ≤ (n : ℝ)⁻¹ → cC n ζ = 0 := by
    intro n hn ζ hζ
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : b (ζ / n) = 1 := by
      refine b.one_of_mem_closedBall ?_
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, hb_def]
      rw [abs_div, abs_of_pos hn0, div_le_one hn0]
      calc |ζ| ≤ (n : ℝ)⁻¹ := hζ
        _ ≤ 1 := by
            rw [inv_le_one_iff₀]
            right
            exact hn1
        _ ≤ (n : ℝ) := hn1
    have h2 : b (n * ζ) = 1 := by
      refine b.one_of_mem_closedBall ?_
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, hb_def]
      rw [abs_mul, abs_of_pos hn0]
      calc (n : ℝ) * |ζ| ≤ (n : ℝ) * (n : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left hζ hn0.le
        _ = 1 := mul_inv_cancel₀ hn0.ne'
    rw [hcC_def]
    simp [h1, h2]
  have hcC_zero_big : ∀ n : ℕ, 1 ≤ n → ∀ ζ : ℝ, 2 * (n : ℝ) < |ζ| → cC n ζ = 0 := by
    intro n hn ζ h2
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hz1 : b (ζ / n) = 0 := by
      refine hbzero _ ?_
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hz2 : b (n * ζ) = 0 := by
      refine hbzero _ ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
      nlinarith [abs_nonneg ζ]
    rw [hcC_def]
    simp [hz1, hz2]
  have hcC0 : ∀ ζ : ℝ, cC 0 ζ = 0 := by
    intro ζ
    rw [hcC_def]
    norm_num
  have hcCsupp' : ∀ n : ℕ, HasCompactSupport (cC n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1) fun ζ _ => hcC0 ζ
    · exact hcCsupp n hn
  have hcC_le_one : ∀ (n : ℕ) (ζ : ℝ), ‖cC n ζ‖ ≤ 1 := by
    intro n ζ
    rw [hcC_def]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_sub_le_iff]
    constructor
    · linarith [b.nonneg (x := (n : ℝ) * ζ), b.le_one (x := ζ / n)]
    · linarith [b.nonneg (x := ζ / n), b.le_one (x := (n : ℝ) * ζ)]
  have hcC_to_one : ∀ ζ : ℝ, ζ ≠ 0 → Tendsto (fun n : ℕ => cC n ζ) atTop (𝓝 1) := by
    intro ζ hζ
    have habs : 0 < |ζ| := abs_pos.mpr hζ
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N1, hN1⟩ := exists_nat_ge |ζ|
    obtain ⟨N2, hN2⟩ := exists_nat_ge (2 / |ζ|)
    filter_upwards [Filter.eventually_ge_atTop (max N1 (max N2 1))] with n hn
    have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hnpos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h1 : b (ζ / n) = 1 := by
      refine b.one_of_mem_closedBall ?_
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, hb_def]
      rw [abs_div, abs_of_pos hn0, div_le_one hn0]
      calc |ζ| ≤ (N1 : ℝ) := hN1
        _ ≤ (n : ℝ) := by exact_mod_cast hn1
    have h2 : b ((n : ℝ) * ζ) = 0 := by
      refine hbzero _ ?_
      rw [abs_mul, abs_of_pos hn0]
      have hle : 2 / |ζ| ≤ (n : ℝ) := le_trans hN2 (by exact_mod_cast hn2)
      calc (2 : ℝ) = 2 / |ζ| * |ζ| := by field_simp
        _ ≤ (n : ℝ) * |ζ| := by gcongr
    rw [hcC_def]
    simp [h1, h2]
  -- the cutoffs and their transforms as Schwartz functions
  have hcS_mk : ∀ n : ℕ, ∃ ψ : SchwartzMap ℝ ℂ, ⇑ψ = cC n := fun n =>
    ⟨(hcCsupp' n).toSchwartzMap (hcCsm n), rfl⟩
  -- weighted integrability of Schwartz functions
  have hschwartz_wint : ∀ θ : SchwartzMap ℝ ℂ,
      Integrable (fun u : ℝ => (1 + |u|) ^ k * ‖θ u‖) volume := by
    intro θ
    have h1 := θ.integrable_pow_mul volume k
    have h2 : Integrable (fun u : ℝ => (2 : ℝ) ^ k * (‖θ u‖ + ‖u‖ ^ k * ‖θ u‖))
        volume := (θ.integrable.norm.add h1).const_mul _
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact ((by fun_prop : Continuous fun u : ℝ =>
        (1 + |u|) ^ k)).aestronglyMeasurable.mul θ.continuous.norm.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h3 := add_pow_le_two_pow_mul k (a := (1 : ℝ)) (b := |u|) one_pos.le (abs_nonneg u)
      calc (1 + |u|) ^ k * ‖θ u‖ ≤ 2 ^ k * (1 ^ k + |u| ^ k) * ‖θ u‖ := by
            gcongr
        _ = 2 ^ k * (‖θ u‖ + ‖u‖ ^ k * ‖θ u‖) := by
            rw [Real.norm_eq_abs]
            ring
  -- ==================== the target spectral factor ====================
  set χt : ℝ → ℂ := fun ζ => angularFourier1D Ξ' (-ζ) with hχt_def
  have hχtc : Continuous χt := by
    have h : Continuous (angularFourier1D Ξ') :=
      Fourier.continuous_angularFourierIntegralInner hΞ'int
    exact h.comp continuous_neg
  set Mχ : ℝ := ∫ r : ℝ, ‖Ξ' r‖ with hMχ_def
  have hMχ0 : 0 ≤ Mχ := integral_nonneg fun r => norm_nonneg _
  have hχt_bound : ∀ ζ : ℝ, ‖χt ζ‖ ≤ Mχ := by
    intro ζ
    rw [hχt_def]
    simp only []
    rw [angularFourier1D]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [hMχ_def]
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    simp only []
    rw [norm_mul, Complex.norm_exp]
    have hre : (-Complex.I * ((inner ℝ x (-ζ) : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre]
    simp
  have hFΞglobal : Integrable (fun ζ : ℝ => Fη ζ * χt ζ) volume := by
    have h : Integrable (fun ζ : ℝ => Fη ζ * angularFourier1D Ξ' (-ζ))
        ((volume : Measure ℝ).restrict {(0 : ℝ)}ᶜ) := hFΞ'
    rw [hrestrict] at h
    exact h
  -- ==================== mollified spectral factor ====================
  set conv : ℕ → ℝ → ℂ := fun ℓ =>
    (κb ℓ).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χt with hconv_def
  have hconvsm : ∀ ℓ : ℕ, ContDiff ℝ ∞ (conv ℓ) := fun ℓ =>
    HasCompactSupport.contDiff_convolution_left _ (κb ℓ).hasCompactSupport_normed
      (κb ℓ).contDiff_normed hχtc.locallyIntegrable
  have hconv_bound : ∀ ℓ (ζ : ℝ), ‖conv ℓ ζ‖ ≤ Mχ := by
    intro ℓ ζ
    rw [hconv_def]
    simp only []
    rw [convolution_def]
    calc ‖∫ t : ℝ, ContinuousLinearMap.lsmul ℝ ℝ ((κb ℓ).normed volume t) (χt (ζ - t))‖
        ≤ ∫ t : ℝ, (κb ℓ).normed volume t * Mχ := by
          refine norm_integral_le_of_norm_le ((κb ℓ).integrable_normed.mul_const _) ?_
          refine Filter.Eventually.of_forall fun t => ?_
          rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ((κb ℓ).nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hχt_bound _) ((κb ℓ).nonneg_normed t)
      _ = Mχ := by
          rw [integral_mul_const, (κb ℓ).integral_normed, one_mul]
  have hconv_tendsto : ∀ ζ : ℝ, Tendsto (fun ℓ : ℕ => conv ℓ ζ) atTop (𝓝 (χt ζ)) := by
    intro ζ
    exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      hκrOut hχtc ζ
  have hκhatc : ∀ ℓ : ℕ, Continuous (κhat ℓ) := by
    intro ℓ
    rw [hκhat_def]
    exact Fourier.continuous_angularFourierIntegralInner (hκCint ℓ)
  -- ==================== spectral representation of the mollified factor ====================
  have hconv_rep : ∀ ℓ (ζ : ℝ), conv ℓ ζ =
      ∫ r : ℝ, Ξ' r * κhat ℓ r * Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ)) := by
    intro ℓ ζ
    have hF : Integrable (Function.uncurry fun t r : ℝ =>
        (κb ℓ).normed volume t •
          (Complex.exp (Complex.I * ((r * (ζ - t) : ℝ) : ℂ)) * Ξ' r))
        ((volume : Measure ℝ).prod volume) := by
      have hdom : Integrable (fun p : ℝ × ℝ => (κb ℓ).normed volume p.1 * ‖Ξ' p.2‖)
          ((volume : Measure ℝ).prod volume) :=
        (κb ℓ).integrable_normed.mul_prod hΞ'int.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine AEStronglyMeasurable.smul
          (((κb ℓ).continuous_normed.comp continuous_fst).aestronglyMeasurable) ?_
        refine AEStronglyMeasurable.mul ?_
          (hΞ'sm.comp_measurable measurable_snd).aestronglyMeasurable
        refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · simp only [Function.uncurry]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((κb ℓ).nonneg_normed _),
          norm_mul, Complex.norm_exp]
        have hre : (Complex.I * ((p.2 * (ζ - p.1) : ℝ) : ℂ)).re = 0 := by
          simp [Complex.mul_re]
        rw [hre]
        simp
    calc conv ℓ ζ
        = ∫ t : ℝ, (κb ℓ).normed volume t • χt (ζ - t) := by
          rw [hconv_def]
          simp only []
          rw [convolution_def]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [ContinuousLinearMap.lsmul_apply]
      _ = ∫ t : ℝ, ∫ r : ℝ, (κb ℓ).normed volume t •
            (Complex.exp (Complex.I * ((r * (ζ - t) : ℝ) : ℂ)) * Ξ' r) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only []
          rw [integral_smul]
          congr 1
          rw [hχt_def]
          simp only []
          rw [angularFourier1D, Fourier.angularFourierIntegralInner]
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          rw [hinner_mul]
          have harg : -Complex.I * ((r * -(ζ - t) : ℝ) : ℂ)
              = Complex.I * ((r * (ζ - t) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [harg]
      _ = ∫ r : ℝ, ∫ t : ℝ, (κb ℓ).normed volume t •
            (Complex.exp (Complex.I * ((r * (ζ - t) : ℝ) : ℂ)) * Ξ' r) :=
          integral_integral_swap hF
      _ = ∫ r : ℝ, Ξ' r * κhat ℓ r * Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          have hexp : ∀ t : ℝ, Complex.exp (Complex.I * ((r * (ζ - t) : ℝ) : ℂ))
              = Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ((inner ℝ t r : ℝ) : ℂ)) := by
            intro t
            rw [← Complex.exp_add, hinner_mul]
            congr 1
            push_cast
            ring
          calc (∫ t : ℝ, (κb ℓ).normed volume t •
                (Complex.exp (Complex.I * ((r * (ζ - t) : ℝ) : ℂ)) * Ξ' r))
              = ∫ t : ℝ, (Ξ' r * Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) *
                  (Complex.exp (-Complex.I * ((inner ℝ t r : ℝ) : ℂ)) * κC ℓ t) := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
                simp only []
                rw [hexp t, Complex.real_smul]
                simp only [hκC_def]
                ring
            _ = (Ξ' r * Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) * κhat ℓ r := by
                rw [integral_const_mul]
                congr 1
            _ = Ξ' r * κhat ℓ r * Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ)) := by
                ring
  -- ==================== the Schwartz test functions ====================
  have hφS_mk : ∀ n ℓ : ℕ, ∃ φ : SchwartzMap ℝ ℂ,
      ⇑φ = fun ζ : ℝ => cC n ζ * conv ℓ ζ := by
    intro n ℓ
    have hsm : ContDiff ℝ ∞ fun ζ : ℝ => cC n ζ * conv ℓ ζ := (hcCsm n).mul (hconvsm ℓ)
    have hsupp : HasCompactSupport fun ζ : ℝ => cC n ζ * conv ℓ ζ :=
      (hcCsupp' n).mul_right
    exact ⟨hsupp.toSchwartzMap hsm, rfl⟩
  choose φS hφS_coe using hφS_mk
  have hφaway : ∀ n : ℕ, 1 ≤ n → ∀ ℓ : ℕ, tsupport ⇑(φS n ℓ) ⊆ {(0 : ℝ)}ᶜ := by
    intro n hn ℓ
    rw [hφS_coe n ℓ]
    refine subset_trans ?_ (hcC_away n hn)
    exact closure_mono (Function.support_mul_subset_left _ _)
  have hEqnl : ∀ n : ℕ, 1 ≤ n → ∀ ℓ : ℕ,
      (∫ ζ : ℝ, Fη ζ * (φS n ℓ) ζ) = ∫ z : ℝ, η' z * angularFourier1D (⇑(φS n ℓ)) z :=
    fun n hn ℓ => hpair' (φS n ℓ) (hφaway n hn ℓ)
  -- ==================== the transform identity ====================
  have hTI : ∀ n ℓ : ℕ, ∀ z : ℝ,
      angularFourier1D (⇑(φS n ℓ)) z = ∫ r : ℝ, Ξ' r * κhat ℓ r * chat n (z - r) := by
    intro n ℓ z
    have hcCn_int : Integrable (fun ζ : ℝ => ‖cC n ζ‖) volume :=
      (hcCsm n).continuous.norm.integrable_of_hasCompactSupport (hcCsupp' n).norm
    have hU : Integrable (Function.uncurry fun ζ r : ℝ =>
        (Complex.exp (-Complex.I * ((inner ℝ ζ z : ℝ) : ℂ)) * cC n ζ *
          Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) * (κhat ℓ r * Ξ' r))
        ((volume : Measure ℝ).prod volume) := by
      have hdom : Integrable (fun p : ℝ × ℝ => ‖cC n p.1‖ * ‖Ξ' p.2‖)
          ((volume : Measure ℝ).prod volume) := hcCn_int.mul_prod hΞ'int.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine AEStronglyMeasurable.mul ?_ ?_
        · refine Continuous.aestronglyMeasurable ?_
          refine Continuous.mul (Continuous.mul ?_
            ((hcCsm n).continuous.comp continuous_fst)) ?_
          · fun_prop
          · fun_prop
        · exact ((hκhatc ℓ).comp continuous_snd).aestronglyMeasurable.mul
            (hΞ'sm.comp_measurable measurable_snd).aestronglyMeasurable
      · simp only [Function.uncurry]
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
        have hre1 : (-Complex.I * ((inner ℝ p.1 z : ℝ) : ℂ)).re = 0 := by
          simp [Complex.mul_re]
        have hre2 : (Complex.I * ((p.2 * p.1 : ℝ) : ℂ)).re = 0 := by
          simp [Complex.mul_re]
        rw [hre1, hre2]
        simp only [Real.exp_zero, one_mul, mul_one]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖κhat ℓ p.2‖ * ‖Ξ' p.2‖ ≤ 1 * ‖Ξ' p.2‖ :=
              mul_le_mul_of_nonneg_right (hκhat_bound ℓ p.2) (norm_nonneg _)
          _ = ‖Ξ' p.2‖ := one_mul _
    rw [angularFourier1D]
    calc Fourier.angularFourierIntegralInner (⇑(φS n ℓ)) z
        = ∫ ζ : ℝ, ∫ r : ℝ,
            (Complex.exp (-Complex.I * ((inner ℝ ζ z : ℝ) : ℂ)) * cC n ζ *
              Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) * (κhat ℓ r * Ξ' r) := by
          rw [Fourier.angularFourierIntegralInner]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
          simp only [hφS_coe]
          rw [hconv_rep ℓ ζ]
          rw [← mul_assoc, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          ring
      _ = ∫ r : ℝ, ∫ ζ : ℝ,
            (Complex.exp (-Complex.I * ((inner ℝ ζ z : ℝ) : ℂ)) * cC n ζ *
              Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) * (κhat ℓ r * Ξ' r) :=
          integral_integral_swap hU
      _ = ∫ r : ℝ, Ξ' r * κhat ℓ r * chat n (z - r) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          rw [integral_mul_const]
          have hmid : (∫ ζ : ℝ,
              Complex.exp (-Complex.I * ((inner ℝ ζ z : ℝ) : ℂ)) * cC n ζ *
                Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))) = chat n (z - r) := by
            rw [hchat_def]
            simp only []
            rw [angularFourier1D, Fourier.angularFourierIntegralInner]
            refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
            simp only []
            rw [hinner_mul, hinner_mul]
            have hmerge : Complex.exp (-Complex.I * ((ζ * z : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((r * ζ : ℝ) : ℂ))
                = Complex.exp (-Complex.I * ((ζ * (z - r) : ℝ) : ℂ)) := by
              rw [← Complex.exp_add]
              congr 1
              push_cast
              ring
            rw [mul_right_comm, hmerge]
          rw [hmid]
          ring
  -- ==================== weighted product integrability ====================
  have hGθint : ∀ (θ : SchwartzMap ℝ ℂ) {c : ℝ}, 0 < c →
      Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖θ (s / c)‖) volume := by
    intro θ c hc
    have hW := hschwartz_wint θ
    have hWc : Integrable (fun s : ℝ => (1 + |s / c|) ^ k * ‖θ (s / c)‖) volume := by
      have h := (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℝ)
        (fun u : ℝ => (1 + |u|) ^ k * ‖θ u‖) (inv_ne_zero hc.ne')).mpr hW
      refine h.congr (Filter.Eventually.of_forall fun s => ?_)
      simp only []
      rw [smul_eq_mul, ← div_eq_inv_mul]
    have hM1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
    have hMc : c ≤ max 1 c := le_max_right _ _
    refine (hWc.const_mul (max 1 c ^ k)).mono' ?_
      (Filter.Eventually.of_forall fun s => ?_)
    · exact ((by fun_prop : Continuous fun s : ℝ =>
        (1 + |s|) ^ k)).aestronglyMeasurable.mul
        ((θ.continuous.comp (by fun_prop : Continuous fun s : ℝ =>
          s / c)).norm.aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : 1 + |s| ≤ max 1 c * (1 + |s / c|) := by
        have h2 : |s| = c * |s / c| := by
          rw [abs_div, abs_of_pos hc]
          field_simp
        rw [h2]
        nlinarith [abs_nonneg (s / c)]
      calc (1 + |s|) ^ k * ‖θ (s / c)‖
          ≤ (max 1 c * (1 + |s / c|)) ^ k * ‖θ (s / c)‖ := by gcongr
        _ = max 1 c ^ k * ((1 + |s / c|) ^ k * ‖θ (s / c)‖) := by
            rw [mul_pow]
            ring
  have hunc : ∀ (g : ℝ → ℂ) (Cg : ℝ), StronglyMeasurable g →
      (∀ z : ℝ, ‖g z‖ ≤ Cg * (1 + |z|) ^ k) →
      ∀ (θ : SchwartzMap ℝ ℂ) (β : ℝ → ℂ), Continuous β → (∀ r : ℝ, ‖β r‖ ≤ 1) →
      ∀ {c : ℝ}, 0 < c →
      Integrable (Function.uncurry fun z r : ℝ => g z * (Ξ' r * β r * θ ((z - r) / c)))
        ((volume : Measure ℝ).prod volume) := by
    intro g Cg hgm hgk θ β hβc hβ1 c hc
    have hCg : 0 ≤ Cg := le_trans (norm_nonneg (g 0)) (by simpa using hgk 0)
    have hF : Integrable (fun r : ℝ => Cg * ((1 + |r|) ^ k * ‖Ξ' r‖)) volume :=
      hΞ'k.const_mul _
    have hG : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖θ (s / c)‖) volume := hGθint θ hc
    have hdom := MeasureTheory.Integrable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hF hG
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul
        (hgm.comp_measurable measurable_fst).aestronglyMeasurable ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hΞ'sm.comp_measurable measurable_snd).aestronglyMeasurable.mul
          ((hβc.comp continuous_snd).aestronglyMeasurable)
      · refine Continuous.aestronglyMeasurable ?_
        exact θ.continuous.comp (by fun_prop)
    · simp only [Function.uncurry, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [norm_mul, norm_mul, norm_mul]
      have hgrow : ‖g p.1‖ ≤ Cg * ((1 + |p.2|) ^ k * (1 + |p.1 - p.2|) ^ k) := by
        refine le_trans (hgk p.1) ?_
        have h1 : (1 + |p.1|) ^ k ≤ ((1 + |p.2|) * (1 + |p.1 - p.2|)) ^ k := by
          refine pow_le_pow_left₀ (by positivity) ?_ k
          have h2 := one_add_abs_add_le_mul_one_add_abs p.2 (p.1 - p.2)
          have h3 : p.2 + (p.1 - p.2) = p.1 := by ring
          rw [h3] at h2
          exact h2
        calc Cg * (1 + |p.1|) ^ k
            ≤ Cg * ((1 + |p.2|) * (1 + |p.1 - p.2|)) ^ k := by gcongr
          _ = Cg * ((1 + |p.2|) ^ k * (1 + |p.1 - p.2|) ^ k) := by
              rw [mul_pow]
      calc ‖g p.1‖ * (‖Ξ' p.2‖ * ‖β p.2‖ * ‖θ ((p.1 - p.2) / c)‖)
          ≤ (Cg * ((1 + |p.2|) ^ k * (1 + |p.1 - p.2|) ^ k)) *
              (‖Ξ' p.2‖ * 1 * ‖θ ((p.1 - p.2) / c)‖) := by
            refine mul_le_mul hgrow ?_ (by positivity) (by positivity)
            gcongr
            exact hβ1 p.2
        _ = Cg * ((1 + |p.2|) ^ k * ‖Ξ' p.2‖) *
              ((1 + |p.1 - p.2|) ^ k * ‖θ ((p.1 - p.2) / c)‖) := by ring
  -- ==================== transform-side kernel facts ====================
  have hchatc : ∀ n : ℕ, Continuous (chat n) := by
    intro n
    rw [hchat_def]
    exact Fourier.continuous_angularFourierIntegralInner
      ((hcCsm n).continuous.integrable_of_hasCompactSupport (hcCsupp' n))
  have hchat_wint : ∀ n : ℕ,
      Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖chat n s‖) volume := by
    intro n
    obtain ⟨ψ, hψ⟩ := hcS_mk n
    have hcoe : chat n = ⇑(Fourier.angularFourierSchwartz ψ) := by
      rw [hchat_def]
      simp only []
      rw [← hψ]
      exact angularFourier1D_coe_schwartz ψ
    rw [hcoe]
    exact hschwartz_wint (Fourier.angularFourierSchwartz ψ)
  -- ==================== the time-side inner pairing ====================
  set Hn : ℕ → ℝ → ℂ := fun n r => ∫ z : ℝ, η' z * chat n (z - r) with hHn_def
  have hHnm : ∀ n : ℕ, AEStronglyMeasurable (Hn n) volume := by
    intro n
    suffices h : AEStronglyMeasurable
        (fun r : ℝ => ∫ z : ℝ, η' z * chat n (z - r)) volume from h
    refine AEStronglyMeasurable.integral_prod_right' (f := fun p : ℝ × ℝ =>
      η' p.2 * chat n (p.2 - p.1)) ?_
    refine AEStronglyMeasurable.mul
      (hη'sm.comp_measurable measurable_snd).aestronglyMeasurable ?_
    exact ((hchatc n).comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      p.2 - p.1)).aestronglyMeasurable
  set Nn : ℕ → ℝ := fun n => ∫ u : ℝ, (1 + |u|) ^ k * ‖chat n u‖ with hNn_def
  have hHn_bound : ∀ (n : ℕ) (r : ℝ), ‖Hn n r‖ ≤ Cη * Nn n * (1 + |r|) ^ k := by
    intro n r
    have hb1 : ‖Hn n r‖ ≤ ∫ z : ℝ, Cη * ((1 + |z|) ^ k * ‖chat n (z - r)‖) := by
      rw [hHn_def]
      simp only []
      refine norm_integral_le_of_norm_le
        ((integrable_weight_norm_comp_sub k (hchatc n).aestronglyMeasurable
          (hchat_wint n) r).const_mul Cη) ?_
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul]
      calc ‖η' z‖ * ‖chat n (z - r)‖ ≤ Cη * (1 + |z|) ^ k * ‖chat n (z - r)‖ := by
            gcongr
            exact hη'k z
        _ = Cη * ((1 + |z|) ^ k * ‖chat n (z - r)‖) := by ring
    refine le_trans hb1 ?_
    have h2 : (∫ z : ℝ, Cη * ((1 + |z|) ^ k * ‖chat n (z - r)‖))
        ≤ ∫ z : ℝ, (Cη * (1 + |r|) ^ k) * ((1 + |z - r|) ^ k * ‖chat n (z - r)‖) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
        (((hchat_wint n).comp_sub_right r).const_mul (Cη * (1 + |r|) ^ k))
        (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      have h1 : (1 + |z|) ^ k ≤ (1 + |r|) ^ k * (1 + |z - r|) ^ k := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        have h2 := one_add_abs_add_le_mul_one_add_abs r (z - r)
        have h3 : r + (z - r) = z := by ring
        rw [h3] at h2
        exact h2
      calc Cη * ((1 + |z|) ^ k * ‖chat n (z - r)‖)
          ≤ Cη * ((1 + |r|) ^ k * (1 + |z - r|) ^ k * ‖chat n (z - r)‖) := by
            gcongr
        _ = (Cη * (1 + |r|) ^ k) * ((1 + |z - r|) ^ k * ‖chat n (z - r)‖) := by ring
    refine le_trans h2 ?_
    have h3 : (∫ z : ℝ, (Cη * (1 + |r|) ^ k) * ((1 + |z - r|) ^ k * ‖chat n (z - r)‖))
        = Cη * (1 + |r|) ^ k * Nn n := by
      rw [integral_const_mul]
      congr 1
      rw [hNn_def]
      simp only []
      exact integral_sub_right_eq_self (fun u : ℝ => (1 + |u|) ^ k * ‖chat n u‖) r
    rw [h3]
    exact le_of_eq (by ring)
  -- product integrability of the full time-side integrand
  have hUnl : ∀ n : ℕ, 1 ≤ n → ∀ ℓ : ℕ, Integrable (Function.uncurry fun z r : ℝ =>
      η' z * (Ξ' r * κhat ℓ r * chat n (z - r))) ((volume : Measure ℝ).prod volume) := by
    intro n hn ℓ
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have h1 := hunc η' Cη hη'sm hη'k bhat (κhat ℓ) (hκhatc ℓ)
      (fun r => hκhat_bound ℓ r) hninv
    have h2 := hunc η' Cη hη'sm hη'k bhat (κhat ℓ) (hκhatc ℓ)
      (fun r => hκhat_bound ℓ r) hn0
    have hcomb := (h1.smul ((n : ℝ))).sub (h2.smul ((n : ℝ)⁻¹))
    refine hcomb.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.sub_apply, Pi.smul_apply]
    rw [hchat_eq n hn (p.1 - p.2)]
    have harg : (p.1 - p.2) / ((n : ℝ))⁻¹ = (n : ℝ) * (p.1 - p.2) := by
      rw [div_eq_mul_inv, inv_inv, mul_comm]
    rw [harg]
    simp only [Complex.real_smul]
    push_cast
    ring
  -- the time-side Fubini swap
  have hTS : ∀ n : ℕ, 1 ≤ n → ∀ ℓ : ℕ,
      (∫ z : ℝ, η' z * ∫ r : ℝ, Ξ' r * κhat ℓ r * chat n (z - r))
        = ∫ r : ℝ, Ξ' r * κhat ℓ r * Hn n r := by
    intro n hn ℓ
    calc (∫ z : ℝ, η' z * ∫ r : ℝ, Ξ' r * κhat ℓ r * chat n (z - r))
        = ∫ z : ℝ, ∫ r : ℝ, η' z * (Ξ' r * κhat ℓ r * chat n (z - r)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only []
          rw [← integral_const_mul]
      _ = ∫ r : ℝ, ∫ z : ℝ, η' z * (Ξ' r * κhat ℓ r * chat n (z - r)) :=
          integral_integral_swap (hUnl n hn ℓ)
      _ = ∫ r : ℝ, Ξ' r * κhat ℓ r * Hn n r := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          calc (∫ z : ℝ, η' z * (Ξ' r * κhat ℓ r * chat n (z - r)))
              = ∫ z : ℝ, (Ξ' r * κhat ℓ r) * (η' z * chat n (z - r)) := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                ring
            _ = (Ξ' r * κhat ℓ r) * ∫ z : ℝ, η' z * chat n (z - r) :=
                integral_const_mul _ _
            _ = Ξ' r * κhat ℓ r * Hn n r := rfl
  -- ==================== the mollifier limit (fixed cutoff) ====================
  have hfreql : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun ℓ : ℕ => ∫ ζ : ℝ, Fη ζ * (φS n ℓ) ζ) atTop
        (𝓝 (∫ ζ : ℝ, Fη ζ * (cC n ζ * χt ζ))) := by
    intro n hn
    have hAclosed : IsClosed {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} :=
      isClosed_le continuous_const continuous_abs
    have hAcompact : IsCompact ({ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} ∩
        Metric.closedBall (0 : ℝ) (2 * n)) :=
      (isCompact_closedBall (0 : ℝ) (2 * n)).inter_left hAclosed
    have hAsub : {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} ∩ Metric.closedBall (0 : ℝ) (2 * n)
        ⊆ {(0 : ℝ)}ᶜ := by
      intro ζ hζ
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hζ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      rw [h0] at hζ
      have h1 := hζ.1
      simp only [abs_zero] at h1
      have hpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      linarith
    have hFA : IntegrableOn Fη ({ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} ∩
        Metric.closedBall (0 : ℝ) (2 * n)) volume :=
      hFηloc.integrableOn_compact_subset hAsub hAcompact
    have hoff : ∀ ζ : ℝ, ζ ∉ {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} ∩
        Metric.closedBall (0 : ℝ) (2 * n) → cC n ζ = 0 := by
      intro ζ hζ
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall,
        Real.dist_eq, sub_zero, not_and_or, not_le] at hζ
      rcases hζ with h | h
      · exact hcC_zero_small n hn ζ h.le
      · exact hcC_zero_big n hn ζ h
    have hgint : Integrable (fun ζ : ℝ => ‖Fη ζ‖ * ‖cC n ζ‖ * Mχ) volume := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero
        (s := {ζ : ℝ | (n : ℝ)⁻¹ ≤ |ζ|} ∩ Metric.closedBall (0 : ℝ) (2 * n)) ?_ ?_
      · refine (hFA.norm.mul_const Mχ).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
        · exact ((hFηm.norm.mul
            (hcCsm n).continuous.norm.aestronglyMeasurable).mul_const Mχ).restrict
        · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          calc ‖Fη ζ‖ * ‖cC n ζ‖ * Mχ ≤ ‖Fη ζ‖ * 1 * Mχ := by
                refine mul_le_mul_of_nonneg_right ?_ hMχ0
                exact mul_le_mul_of_nonneg_left (hcC_le_one n ζ) (norm_nonneg _)
            _ = ‖Fη ζ‖ * Mχ := by ring
      · intro ζ hζ
        rw [hoff ζ hζ]
        simp
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hgint ?_
    · refine Filter.Eventually.of_forall fun ℓ => ?_
      exact hFηm.mul (φS n ℓ).continuous.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ℓ => ?_
      refine Filter.Eventually.of_forall fun ζ => ?_
      rw [norm_mul, congrFun (hφS_coe n ℓ) ζ]
      rw [norm_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_left (hconv_bound ℓ ζ) ?_
      positivity
    · refine Filter.Eventually.of_forall fun ζ => ?_
      have h1 := ((hconv_tendsto ζ).const_mul (cC n ζ)).const_mul (Fη ζ)
      refine h1.congr fun ℓ => ?_
      exact congrArg (Fη ζ * ·) (congrFun (hφS_coe n ℓ) ζ).symm
  have htimel : ∀ n : ℕ,
      Tendsto (fun ℓ : ℕ => ∫ r : ℝ, Ξ' r * κhat ℓ r * Hn n r) atTop
        (𝓝 (∫ r : ℝ, Ξ' r * Hn n r)) := by
    intro n
    have hgint : Integrable (fun r : ℝ => Cη * Nn n * ((1 + |r|) ^ k * ‖Ξ' r‖))
        volume := hΞ'k.const_mul _
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hgint ?_
    · refine Filter.Eventually.of_forall fun ℓ => ?_
      exact (hΞ'sm.aestronglyMeasurable.mul (hκhatc ℓ).aestronglyMeasurable).mul (hHnm n)
    · refine Filter.Eventually.of_forall fun ℓ => ?_
      refine Filter.Eventually.of_forall fun r => ?_
      rw [norm_mul, norm_mul]
      calc ‖Ξ' r‖ * ‖κhat ℓ r‖ * ‖Hn n r‖
          ≤ ‖Ξ' r‖ * 1 * (Cη * Nn n * (1 + |r|) ^ k) := by
            refine mul_le_mul ?_ (hHn_bound n r) (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left (hκhat_bound ℓ r) (norm_nonneg _)
        _ = Cη * Nn n * ((1 + |r|) ^ k * ‖Ξ' r‖) := by ring
    · refine Filter.Eventually.of_forall fun r => ?_
      have h1 := ((hκhat_tendsto r).const_mul (Ξ' r)).mul_const (Hn n r)
      have h2 : Ξ' r * 1 * Hn n r = Ξ' r * Hn n r := by ring
      rwa [h2] at h1
  -- equality of the two ℓ-limits
  have hEqn : ∀ n : ℕ, 1 ≤ n →
      (∫ ζ : ℝ, Fη ζ * (cC n ζ * χt ζ)) = ∫ r : ℝ, Ξ' r * Hn n r := by
    intro n hn
    refine tendsto_nhds_unique ?_ (htimel n)
    refine (hfreql n hn).congr fun ℓ => ?_
    rw [hEqnl n hn ℓ, ← hTS n hn ℓ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [hTI n ℓ z]
  -- ==================== the cutoff limit: frequency side ====================
  have hae0 : ∀ᵐ ζ : ℝ ∂(volume : Measure ℝ), ζ ≠ (0 : ℝ) := by
    refine mem_ae_iff.mpr ?_
    rw [show {ζ : ℝ | ζ ≠ (0 : ℝ)}ᶜ = {(0 : ℝ)} from by ext ζ; simp]
    exact measure_singleton 0
  have hfreqn : Tendsto (fun n : ℕ => ∫ ζ : ℝ, Fη ζ * (cC n ζ * χt ζ)) atTop
      (𝓝 (∫ ζ : ℝ, Fη ζ * χt ζ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ζ => ‖Fη ζ * χt ζ‖) ?_ ?_ hFΞglobal.norm ?_
    · refine Filter.Eventually.of_forall fun n => ?_
      exact hFηm.mul ((hcCsm n).continuous.aestronglyMeasurable.mul
        hχtc.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun n => ?_
      refine Filter.Eventually.of_forall fun ζ => ?_
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖Fη ζ‖ * (‖cC n ζ‖ * ‖χt ζ‖) ≤ ‖Fη ζ‖ * (1 * ‖χt ζ‖) := by
            gcongr
            exact hcC_le_one n ζ
        _ = ‖Fη ζ‖ * ‖χt ζ‖ := by ring
    · filter_upwards [hae0] with ζ hζ
      have h1 := ((hcC_to_one ζ hζ).mul_const (χt ζ)).const_mul (Fη ζ)
      have h2 : Fη ζ * (1 * χt ζ) = Fη ζ * χt ζ := by ring
      rwa [h2] at h1
  -- ==================== the cutoff limit: time side ====================
  -- integrability of translated dilated kernels against the truncation
  have hηθz : ∀ (θ : SchwartzMap ℝ ℂ) {c : ℝ}, 0 < c → ∀ r : ℝ,
      Integrable (fun z : ℝ => η' z * θ ((z - r) / c)) volume := by
    intro θ c hc r
    have hdom := (integrable_weight_norm_comp_sub k
      ((θ.continuous.comp (by fun_prop : Continuous fun v : ℝ =>
        v / c)).aestronglyMeasurable) (hGθint θ hc) r).const_mul Cη
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hη'sm.aestronglyMeasurable.mul ((θ.continuous.comp
        (by fun_prop : Continuous fun z : ℝ => (z - r) / c)).aestronglyMeasurable)
    · rw [norm_mul]
      calc ‖η' z‖ * ‖θ ((z - r) / c)‖ ≤ Cη * (1 + |z|) ^ k * ‖θ ((z - r) / c)‖ := by
            gcongr
            exact hη'k z
        _ = Cη * ((1 + |z|) ^ k * ‖θ ((z - r) / c)‖) := by ring
  -- τ/β decomposition of the inner pairing
  have hHn_split : ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ,
      Hn n r = (n : ℝ) • (∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
        - (n : ℝ)⁻¹ • ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ)) := by
    intro n hn r
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have hi1' : Integrable (fun z : ℝ =>
        (n : ℝ) • (η' z * bhat ((z - r) / ((n : ℝ))⁻¹))) volume :=
      ((hηθz bhat hninv r).smul ((n : ℝ))).congr
        (Filter.Eventually.of_forall fun z => rfl)
    have hi2' : Integrable (fun z : ℝ =>
        (n : ℝ)⁻¹ • (η' z * bhat ((z - r) / (n : ℝ)))) volume :=
      ((hηθz bhat hn0 r).smul ((n : ℝ)⁻¹)).congr
        (Filter.Eventually.of_forall fun z => rfl)
    calc Hn n r
        = ∫ z : ℝ, ((n : ℝ) • (η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
            - (n : ℝ)⁻¹ • (η' z * bhat ((z - r) / (n : ℝ)))) := by
          suffices h : (∫ z : ℝ, η' z * chat n (z - r))
              = ∫ z : ℝ, ((n : ℝ) • (η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
                - (n : ℝ)⁻¹ • (η' z * bhat ((z - r) / (n : ℝ)))) from h
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only []
          rw [hchat_eq n hn (z - r)]
          have harg : (z - r) / ((n : ℝ))⁻¹ = (n : ℝ) * (z - r) := by
            rw [div_eq_mul_inv, inv_inv, mul_comm]
          rw [harg]
          simp only [Complex.real_smul]
          push_cast
          ring
      _ = _ := by
          rw [integral_sub hi1' hi2', integral_smul, integral_smul]
  -- integrability in the outer variable
  have hrint : ∀ (θ : SchwartzMap ℝ ℂ) {c : ℝ}, 0 < c →
      Integrable (fun r : ℝ => Ξ' r * ∫ z : ℝ, η' z * θ ((z - r) / c)) volume := by
    intro θ c hc
    have hU := hunc η' Cη hη'sm hη'k θ (fun _ => (1 : ℂ)) continuous_const
      (fun r => by norm_num) hc
    have h := hU.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Function.uncurry]
    calc (∫ z : ℝ, η' z * (Ξ' r * 1 * θ ((z - r) / c)))
        = ∫ z : ℝ, Ξ' r * (η' z * θ ((z - r) / c)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          ring
      _ = Ξ' r * ∫ z : ℝ, η' z * θ ((z - r) / c) := integral_const_mul _ _
  have hTn_split : ∀ n : ℕ, 1 ≤ n →
      (∫ r : ℝ, Ξ' r * Hn n r)
        = (n : ℝ) • (∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
          - (n : ℝ)⁻¹ • ∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have h1' : Integrable (fun r : ℝ =>
        (n : ℝ) • (Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))) volume :=
      ((hrint bhat hninv).smul ((n : ℝ))).congr
        (Filter.Eventually.of_forall fun r => rfl)
    have h2' : Integrable (fun r : ℝ =>
        (n : ℝ)⁻¹ • (Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ)))) volume :=
      ((hrint bhat hn0).smul ((n : ℝ)⁻¹)).congr
        (Filter.Eventually.of_forall fun r => rfl)
    calc (∫ r : ℝ, Ξ' r * Hn n r)
        = ∫ r : ℝ, ((n : ℝ) • (Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
            - (n : ℝ)⁻¹ • (Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ)))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          rw [hHn_split n hn r]
          simp only [Complex.real_smul]
          push_cast
          ring
      _ = _ := by
          rw [integral_sub h1' h2', integral_smul, integral_smul]
  -- the low-frequency taper vanishes: moment cancellation (P4)
  have hβlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ •
      ∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ))) atTop
      (𝓝 (0 : ℂ)) := by
    have hP4 := MeasureTheory.tendsto_integral_mul_smoothing_of_vanishing_moments k
      bhat hη'sm hη'k hΞ'sm.aestronglyMeasurable hΞ'k hΞ'vm
    have hcomp := hP4.comp tendsto_natCast_atTop_atTop
    refine hcomp.congr fun n => ?_
    simp only [Function.comp]
    calc (∫ r : ℝ, Ξ' r * (((n : ℝ))⁻¹ * ∫ w : ℝ, η' w * bhat ((w - r) / (n : ℝ))))
        = ∫ r : ℝ, (n : ℝ)⁻¹ • (Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only [Complex.real_smul]
          push_cast
          ring
      _ = (n : ℝ)⁻¹ • ∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / (n : ℝ)) :=
          integral_smul _ _
  -- change of variables for the main term
  set Q : ℕ → ℝ → ℂ := fun n z => ∫ u : ℝ, bhat u * Ξ' (z - u / (n : ℝ)) with hQ_def
  have hQcov : ∀ n : ℕ, 1 ≤ n → ∀ z : ℝ,
      (∫ r : ℝ, Ξ' r * bhat ((z - r) / ((n : ℝ))⁻¹)) = (n : ℝ)⁻¹ • Q n z := by
    intro n hn z
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    calc (∫ r : ℝ, Ξ' r * bhat ((z - r) / ((n : ℝ))⁻¹))
        = ∫ r : ℝ, (fun w : ℝ => Ξ' (z - w) * bhat (w / ((n : ℝ))⁻¹)) (z - r) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only [sub_sub_cancel]
      _ = ∫ w : ℝ, Ξ' (z - w) * bhat (w / ((n : ℝ))⁻¹) := by
          exact integral_sub_left_eq_self
            (fun w : ℝ => Ξ' (z - w) * bhat (w / ((n : ℝ))⁻¹)) volume z
      _ = ∫ w : ℝ, (fun v : ℝ => bhat v * Ξ' (z - v / (n : ℝ)))
            ((w - 0) / ((n : ℝ))⁻¹) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          simp only [sub_zero]
          have harg : w / ((n : ℝ))⁻¹ / (n : ℝ) = w := by
            rw [div_div, inv_mul_cancel₀ hn0.ne', div_one]
          rw [harg]
          ring
      _ = ((n : ℝ))⁻¹ • ∫ v : ℝ, bhat v * Ξ' (z - v / (n : ℝ)) := by
          exact MeasureTheory.integral_comp_sub_div_smul
            (fun v : ℝ => bhat v * Ξ' (z - v / (n : ℝ))) 0 hninv
      _ = (n : ℝ)⁻¹ • Q n z := rfl
  have hAτQ : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) • (∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
        = ∫ z : ℝ, η' z * Q n z := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have hU := hunc η' Cη hη'sm hη'k bhat (fun _ => (1 : ℂ)) continuous_const
      (fun r => by norm_num) hninv
    have hswap := integral_integral_swap hU
    calc (n : ℝ) • (∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹))
        = (n : ℝ) • ∫ r : ℝ, ∫ z : ℝ,
            η' z * (Ξ' r * 1 * bhat ((z - r) / ((n : ℝ))⁻¹)) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only []
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          ring
      _ = (n : ℝ) • ∫ z : ℝ, ∫ r : ℝ,
            η' z * (Ξ' r * 1 * bhat ((z - r) / ((n : ℝ))⁻¹)) := by
          rw [← hswap]
      _ = ∫ z : ℝ, η' z * Q n z := by
          rw [← integral_smul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only []
          have hin : (∫ r : ℝ, η' z * (Ξ' r * 1 * bhat ((z - r) / ((n : ℝ))⁻¹)))
              = η' z * ((n : ℝ)⁻¹ • Q n z) := by
            rw [← hQcov n hn z, ← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
            ring
          rw [hin, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  -- weighted integrability of the smoothed function
  have huncK : ∀ n : ℕ, 1 ≤ n → Integrable (Function.uncurry fun z r : ℝ =>
      (((1 + |z|) ^ k : ℝ) : ℂ) * (bhat ((n : ℝ) * r) * Ξ' (z - r)))
      ((volume : Measure ℝ).prod volume) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have hF : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖bhat ((n : ℝ) * r)‖) volume := by
      refine (hGθint bhat hninv).congr (Filter.Eventually.of_forall fun r => ?_)
      simp only []
      have harg : r / ((n : ℝ))⁻¹ = (n : ℝ) * r := by
        rw [div_eq_mul_inv, inv_inv, mul_comm]
      rw [harg]
    have hdom := MeasureTheory.Integrable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hF hΞ'k
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · refine AEStronglyMeasurable.mul ?_ ?_
        · exact (bhat.continuous.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
            (n : ℝ) * p.2)).aestronglyMeasurable
        · exact (hΞ'sm.comp_measurable (by fun_prop : Measurable fun p : ℝ × ℝ =>
            p.1 - p.2)).aestronglyMeasurable
    · simp only [Function.uncurry, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |p.1|) ^ k)]
      have h1 : (1 + |p.1|) ^ k ≤ (1 + |p.2|) ^ k * (1 + |p.1 - p.2|) ^ k := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        have h2 := one_add_abs_add_le_mul_one_add_abs p.2 (p.1 - p.2)
        have h3 : p.2 + (p.1 - p.2) = p.1 := by ring
        rw [h3] at h2
        exact h2
      calc (1 + |p.1|) ^ k * (‖bhat ((n : ℝ) * p.2)‖ * ‖Ξ' (p.1 - p.2)‖)
          ≤ ((1 + |p.2|) ^ k * (1 + |p.1 - p.2|) ^ k) *
              (‖bhat ((n : ℝ) * p.2)‖ * ‖Ξ' (p.1 - p.2)‖) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 + |p.2|) ^ k * ‖bhat ((n : ℝ) * p.2)‖ *
              ((1 + |p.1 - p.2|) ^ k * ‖Ξ' (p.1 - p.2)‖) := by ring
  have hwQ : ∀ n : ℕ, 1 ≤ n →
      Integrable (fun z : ℝ => (((1 + |z|) ^ k : ℝ) : ℂ) * Q n z) volume := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have h := (huncK n hn).integral_prod_left
    refine (h.smul ((n : ℝ))).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply, Function.uncurry]
    have hin : (∫ r : ℝ, (((1 + |z|) ^ k : ℝ) : ℂ) * (bhat ((n : ℝ) * r) * Ξ' (z - r)))
        = (((1 + |z|) ^ k : ℝ) : ℂ) * ((n : ℝ)⁻¹ • Q n z) := by
      rw [integral_const_mul]
      congr 1
      calc (∫ r : ℝ, bhat ((n : ℝ) * r) * Ξ' (z - r))
          = ∫ r : ℝ, (fun v : ℝ => bhat v * Ξ' (z - v / (n : ℝ)))
              ((r - 0) / ((n : ℝ))⁻¹) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
            simp only [sub_zero]
            have harg1 : r / ((n : ℝ))⁻¹ = (n : ℝ) * r := by
              rw [div_eq_mul_inv, inv_inv, mul_comm]
            rw [harg1]
            have harg2 : (n : ℝ) * r / (n : ℝ) = r := by
              rw [mul_comm, mul_div_cancel_right₀ _ hn0.ne']
            rw [harg2]
        _ = ((n : ℝ))⁻¹ • ∫ v : ℝ, bhat v * Ξ' (z - v / (n : ℝ)) := by
            exact MeasureTheory.integral_comp_sub_div_smul
              (fun v : ℝ => bhat v * Ξ' (z - v / (n : ℝ))) 0 hninv
        _ = (n : ℝ)⁻¹ • Q n z := rfl
    rw [hin, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  -- integrability of the weighted smoothing difference
  have hP3int : ∀ n : ℕ, 1 ≤ n → Integrable (fun z : ℝ => (1 + |z|) ^ k *
      ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u * Ξ' (z - u / (n : ℝ))) - Ξ' z‖)
      volume := by
    intro n hn
    have hSm : AEStronglyMeasurable (fun z : ℝ =>
        ∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u * Ξ' (z - u / (n : ℝ)))
        volume := by
      refine AEStronglyMeasurable.integral_prod_right' (f := fun p : ℝ × ℝ =>
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat p.2 * Ξ' (p.1 - p.2 / (n : ℝ))) ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (continuous_const.mul (bhat.continuous.comp
          continuous_snd)).aestronglyMeasurable
      · exact (hΞ'sm.comp_measurable (by fun_prop : Measurable fun p : ℝ × ℝ =>
          p.1 - p.2 / (n : ℝ))).aestronglyMeasurable
    have hSQ : ∀ z : ℝ, (∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
        Ξ' (z - u / (n : ℝ))) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Q n z := by
      intro z
      rw [hQ_def]
      simp only []
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring
    have hdom : Integrable (fun z : ℝ => (2 * Real.pi)⁻¹ *
        ‖(((1 + |z|) ^ k : ℝ) : ℂ) * Q n z‖ + (1 + |z|) ^ k * ‖Ξ' z‖) volume :=
      ((hwQ n hn).norm.const_mul _).add hΞ'k
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine ((by fun_prop : Continuous fun z : ℝ =>
        (1 + |z|) ^ k)).aestronglyMeasurable.mul ?_
      exact (hSm.sub hΞ'sm.aestronglyMeasurable).norm
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hSQ z]
      calc (1 + |z|) ^ k * ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Q n z - Ξ' z‖
          ≤ (1 + |z|) ^ k * (‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Q n z‖ + ‖Ξ' z‖) := by
            gcongr
            exact norm_sub_le _ _
        _ = (2 * Real.pi)⁻¹ * ‖(((1 + |z|) ^ k : ℝ) : ℂ) * Q n z‖ +
              (1 + |z|) ^ k * ‖Ξ' z‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |z|) ^ k)]
            ring
  -- the main term converges to the pairing (P3)
  have hηΞint : Integrable (fun z : ℝ => η' z * Ξ' z) volume := by
    refine (hΞ'k.const_mul Cη).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hη'sm.aestronglyMeasurable.mul hΞ'sm.aestronglyMeasurable
    · rw [norm_mul]
      calc ‖η' z‖ * ‖Ξ' z‖ ≤ Cη * (1 + |z|) ^ k * ‖Ξ' z‖ := by
            gcongr
            exact hη'k z
        _ = Cη * ((1 + |z|) ^ k * ‖Ξ' z‖) := by ring
  have hQint : ∀ n : ℕ, 1 ≤ n → Integrable (fun z : ℝ => η' z * Q n z) volume := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hninv : (0 : ℝ) < ((n : ℝ))⁻¹ := by positivity
    have hU := hunc η' Cη hη'sm hη'k bhat (fun _ => (1 : ℂ)) continuous_const
      (fun r => by norm_num) hninv
    have h := hU.integral_prod_left
    refine (h.smul ((n : ℝ))).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.smul_apply, Function.uncurry]
    have hin : (∫ r : ℝ, η' z * (Ξ' r * 1 * bhat ((z - r) / ((n : ℝ))⁻¹)))
        = η' z * ((n : ℝ)⁻¹ • Q n z) := by
      rw [← hQcov n hn z, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      ring
    rw [hin, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hτlim : Tendsto (fun n : ℕ => ∫ z : ℝ, η' z * Q n z) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z)) := by
    have hKm : AEStronglyMeasurable (fun u : ℝ => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u)
        volume := (continuous_const.mul bhat.continuous).aestronglyMeasurable
    have hKk : Integrable (fun u : ℝ => (1 + |u|) ^ k *
        ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u‖) volume := by
      refine ((hschwartz_wint bhat).const_mul ((2 * Real.pi)⁻¹)).congr
        (Filter.Eventually.of_forall fun u => ?_)
      simp only []
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
      ring
    have hK1 : (∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u) = 1 := by
      rw [integral_const_mul, hbhat_int_eq, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hπ.ne']
      norm_num
    have hP3 := MeasureTheory.tendsto_integral_weight_norm_smoothing_sub k
      hΞ'sm hΞ'k hKm hKk hK1
    have hW := hP3.comp tendsto_natCast_atTop_atTop
    have hdiff : Tendsto (fun n : ℕ => (∫ z : ℝ, η' z * Q n z) -
        ((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n : ℕ => 2 * Real.pi * Cη *
        ∫ z : ℝ, (1 + |z|) ^ k *
          ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u * Ξ' (z - u / (n : ℝ)))
            - Ξ' z‖) ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have h2πΞ : Integrable (fun z : ℝ => ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z))
            volume := hηΞint.const_mul _
        have heq : (∫ z : ℝ, η' z * Q n z) -
            ((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z
            = ∫ z : ℝ, (η' z * Q n z - ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z)) := by
          rw [integral_sub (hQint n hn) h2πΞ, integral_const_mul]
        rw [heq]
        calc ‖∫ z : ℝ, (η' z * Q n z - ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z))‖
            ≤ ∫ z : ℝ, 2 * Real.pi * Cη * ((1 + |z|) ^ k *
                ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u * Ξ' (z - u / (n : ℝ)))
                  - Ξ' z‖) := by
              refine norm_integral_le_of_norm_le
                ((hP3int n hn).const_mul (2 * Real.pi * Cη))
                (Filter.Eventually.of_forall fun z => ?_)
              have hSQ : (∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
                  Ξ' (z - u / (n : ℝ))) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Q n z := by
                rw [hQ_def]
                simp only []
                rw [← integral_const_mul]
                refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
                ring
              have h2 : ((2 * Real.pi : ℝ) : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
                rw [← Complex.ofReal_mul, mul_inv_cancel₀ hπ.ne']
                norm_num
              have hkey : η' z * Q n z - ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z)
                  = ((2 * Real.pi : ℝ) : ℂ) * (η' z *
                    ((∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
                      Ξ' (z - u / (n : ℝ))) - Ξ' z)) := by
                rw [hSQ]
                calc η' z * Q n z - ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z)
                    = (((2 * Real.pi : ℝ) : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ)) *
                        (η' z * Q n z) - ((2 * Real.pi : ℝ) : ℂ) * (η' z * Ξ' z) := by
                      rw [h2, one_mul]
                  _ = ((2 * Real.pi : ℝ) : ℂ) * (η' z *
                        ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Q n z - Ξ' z)) := by ring
              rw [hkey, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hπ]
              calc 2 * Real.pi * (‖η' z‖ *
                    ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
                      Ξ' (z - u / (n : ℝ))) - Ξ' z‖)
                  ≤ 2 * Real.pi * ((Cη * (1 + |z|) ^ k) *
                      ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
                        Ξ' (z - u / (n : ℝ))) - Ξ' z‖) := by
                    gcongr
                    exact hη'k z
                _ = 2 * Real.pi * Cη * ((1 + |z|) ^ k *
                      ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u *
                        Ξ' (z - u / (n : ℝ))) - Ξ' z‖) := by ring
          _ = 2 * Real.pi * Cη * ∫ z : ℝ, (1 + |z|) ^ k *
                ‖(∫ u : ℝ, (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * bhat u * Ξ' (z - u / (n : ℝ)))
                  - Ξ' z‖ := integral_const_mul _ _
      · have h := hW.const_mul (2 * Real.pi * Cη)
        simpa using h
    have h2 := hdiff.add (tendsto_const_nhds
      (x := ((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z))
    simpa using h2
  -- time side converges to the pairing
  have htimen : Tendsto (fun n : ℕ => ∫ r : ℝ, Ξ' r * Hn n r) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z)) := by
    have hτ' : Tendsto (fun n : ℕ =>
        (n : ℝ) • (∫ r : ℝ, Ξ' r * ∫ z : ℝ, η' z * bhat ((z - r) / ((n : ℝ))⁻¹)))
        atTop (𝓝 (((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z)) := by
      refine hτlim.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact (hAτQ n hn).symm
    have hsub := hτ'.sub hβlim
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hTn_split n hn).symm
  -- ==================== final assembly ====================
  have hkey : (∫ ζ : ℝ, Fη ζ * χt ζ)
      = ((2 * Real.pi : ℝ) : ℂ) * ∫ z : ℝ, η' z * Ξ' z := by
    refine tendsto_nhds_unique ?_ htimen
    refine hfreqn.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact hEqn n hn
  have hset : (∫ ζ in {(0 : ℝ)}ᶜ, Fη ζ * angularFourier1D Ξ' (-ζ))
      = ∫ ζ : ℝ, Fη ζ * χt ζ := by
    rw [hrestrict]
  rw [hset, hkey]
  have hcancel : (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hπ.ne']
    norm_num
  rw [← mul_assoc, hcancel, one_mul]

end LeanRidgelet
