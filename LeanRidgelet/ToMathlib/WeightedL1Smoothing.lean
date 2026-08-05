/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Polynomial-weighted `L¹` smoothing estimates on the real line

This file proves polynomial-weighted `L¹` estimates that drive the pairing theory of
tempered distributions modulo polynomials (the Lizorkin quotient) at function level:

* `abs_pow_sub_pow_le_mul`: the Lipschitz bound `|x^n - y^n| ≤ n M^(n-1) |x - y|` on `[0, M]`;
* `MeasureTheory.tendsto_integral_norm_sub_comp_sub_right`: continuity of translation in
  `L¹(ℝ)`;
* `MeasureTheory.tendsto_integral_weight_norm_sub_comp_sub_right`: continuity of translation
  in polynomially weighted `L¹(ℝ)`;
* `MeasureTheory.continuous_integral_weight_norm_sub`: continuity of the weighted
  translation modulus `s ↦ ∫ (1 + |z|)^k ‖Ξ (z - s) - Ξ z‖ dz`;
* `MeasureTheory.tendsto_integral_weight_norm_smoothing_sub`: the **scaled approximate
  identity in polynomially weighted `L¹`** — for a kernel with unit integral and finite
  `k`-th moment, `∫ (1 + |z|)^k ‖∫ K(u) Ξ(z - u/c) du - Ξ z‖ dz → 0` as `c → ∞`;
* `MeasureTheory.tendsto_integral_mul_smoothing_of_vanishing_moments`: the
  **vanishing-moment cancellation for wide smoothing** — if `Ξ` has a finite `k`-th moment
  and vanishing moments up to `k`, and `η` grows at most like `(1 + |z|)^k`, then
  `∫ Ξ(r) ⬝ (c⁻¹ ∫ η(w) θ((w - r)/c) dw) dr → 0` as `c → ∞` for every Schwartz kernel `θ`.
  This is the analytic heart of the pairing theory of tempered distributions modulo
  polynomials (the Lizorkin quotient) at function level: the wide smoothing sees only the
  polynomial-like behaviour of `η`, which the vanishing moments of `Ξ` annihilate. The proof
  Taylor-expands the kernel to order `k`, splits the line at `|r| = c`, controls the outside
  by the integral tail, converts the truncated Taylor moments into tails through the
  vanishing moments, and dominates the remainder by `min(1, |r|/c)`; exactly `k` moments
  suffice.

Mathlib (as of the pinned version) provides the continuity of composition with
measure-preserving maps on `Lp` (`MeasureTheory.Lp.compMeasurePreserving_continuous`) but not
the classical translation-continuity statements themselves, nor their weighted forms. These
are stated on `ℝ` with values in a normed group and are candidates for upstreaming.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- Lipschitz bound for powers on `[0, M]`: `|x^n - y^n| ≤ n M^(n-1) |x - y|`. -/
theorem abs_pow_sub_pow_le_mul (n : ℕ) {x y M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    |x ^ n - y ^ n| ≤ n * M ^ (n - 1) * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hM : 0 ≤ M := hx.trans hxM
    have h1 : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + y * (x ^ n - y ^ n) := by ring
    have h2 : M * ((n : ℝ) * M ^ (n - 1)) ≤ (n : ℝ) * M ^ n := by
      rcases n with _ | m
      · simp
      · refine le_of_eq ?_
        rw [Nat.add_sub_cancel, pow_succ]
        push_cast
        ring
    calc |x ^ (n + 1) - y ^ (n + 1)|
        = |x ^ n * (x - y) + y * (x ^ n - y ^ n)| := by rw [h1]
      _ ≤ |x ^ n * (x - y)| + |y * (x ^ n - y ^ n)| := abs_add_le _ _
      _ = x ^ n * |x - y| + y * |x ^ n - y ^ n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx n), abs_of_nonneg hy]
      _ ≤ M ^ n * |x - y| + M * ((n : ℝ) * M ^ (n - 1) * |x - y|) := by
          gcongr
      _ = M ^ n * |x - y| + M * ((n : ℝ) * M ^ (n - 1)) * |x - y| := by ring
      _ ≤ M ^ n * |x - y| + (n : ℝ) * M ^ n * |x - y| := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * M ^ ((n + 1) - 1) * |x - y| := by
          rw [Nat.add_sub_cancel]
          push_cast
          ring

/-- Submultiplicativity of the polynomial weight `1 + |z + t| ≤ (1 + |z|) (1 + |t|)`. -/
theorem one_add_abs_add_le_mul_one_add_abs (z t : ℝ) :
    1 + |z + t| ≤ (1 + |z|) * (1 + |t|) := by
  have h1 : |z + t| ≤ |z| + |t| := abs_add_le z t
  nlinarith [abs_nonneg z, abs_nonneg t]

section Taylor

variable [NormedSpace ℝ E]

/-- Uniform Taylor remainder bound anchored at the left endpoint. Auxiliary version of
`norm_sub_taylorSum_le` for a nonnegative increment. -/
theorem norm_sub_taylorSum_le_of_nonneg {f : ℝ → E} {k : ℕ} {C a h : ℝ} (hh : 0 ≤ h)
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hC : ∀ y ∈ Set.Icc a (a + h), ‖iteratedDeriv (k + 1) f y‖ ≤ C) :
    ‖f (a + h) - ∑ j ∈ Finset.range (k + 1),
        (h ^ j / (j.factorial : ℝ)) • iteratedDeriv j f a‖
      ≤ C * h ^ (k + 1) / k.factorial := by
  rcases hh.eq_or_lt with heq | hlt
  · -- `h = 0`
    have hsum : (∑ j ∈ Finset.range (k + 1),
        (((0 : ℝ)) ^ j / (j.factorial : ℝ)) • iteratedDeriv j f a) = f a := by
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos k))]
      · simp
      · intro j _ hj0
        rw [zero_pow hj0]
        simp
    rw [← heq, add_zero, hsum, sub_self, norm_zero, zero_pow (Nat.succ_ne_zero k)]
    simp
  · -- `0 < h`
    have hab : a ≤ a + h := by linarith
    have hIcc : UniqueDiffOn ℝ (Set.Icc a (a + h)) := uniqueDiffOn_Icc (by linarith)
    have hfOn : ContDiffOn ℝ (k + 1 : ℕ) f (Set.Icc a (a + h)) := hf.contDiffOn
    have hC' : ∀ y ∈ Set.Icc a (a + h),
        ‖iteratedDerivWithin (k + 1) f (Set.Icc a (a + h)) y‖ ≤ C := by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv hIcc hf.contDiffAt hy]
      exact hC y hy
    have hmain := taylor_mean_remainder_bound hab hfOn (Set.right_mem_Icc.mpr hab) hC'
    have htay : taylorWithinEval f k (Set.Icc a (a + h)) a (a + h)
        = ∑ j ∈ Finset.range (k + 1),
            (h ^ j / (j.factorial : ℝ)) • iteratedDeriv j f a := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : (j : WithTop ℕ∞) ≤ (k + 1 : ℕ) := by
        exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj) |>.trans (Nat.le_succ k)
      rw [add_sub_cancel_left,
        iteratedDerivWithin_eq_iteratedDeriv hIcc (hf.of_le hjk).contDiffAt
          (Set.left_mem_Icc.mpr hab)]
      congr 1
      ring
    rw [htay, add_sub_cancel_left] at hmain
    exact hmain

/-- **Uniform Taylor remainder bound**: for a `C^{k+1}` function whose `(k+1)`-st derivative
is bounded by `C` on the segment from `a` to `a + h`,
`‖f (a + h) - ∑_{j ≤ k} (h^j/j!) f^{(j)}(a)‖ ≤ C |h|^{k+1} / k!`. -/
theorem norm_sub_taylorSum_le {f : ℝ → E} {k : ℕ} {C a h : ℝ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (hC : ∀ y ∈ Set.uIcc a (a + h), ‖iteratedDeriv (k + 1) f y‖ ≤ C) :
    ‖f (a + h) - ∑ j ∈ Finset.range (k + 1),
        (h ^ j / (j.factorial : ℝ)) • iteratedDeriv j f a‖
      ≤ C * |h| ^ (k + 1) / k.factorial := by
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]
    refine norm_sub_taylorSum_le_of_nonneg hh hf fun y hy => hC y ?_
    rwa [Set.uIcc_of_le (by linarith)]
  · -- reflect through the origin and use the nonnegative case
    set g : ℝ → E := fun x => f (-x) with hg_def
    have hg : ContDiff ℝ (k + 1 : ℕ) g := hf.comp contDiff_neg
    have hgC : ∀ y ∈ Set.Icc (-a) (-a + -h), ‖iteratedDeriv (k + 1) g y‖ ≤ C := by
      intro y hy
      rw [hg_def, iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul]
      refine hC (-y) ?_
      rw [Set.uIcc_of_ge (by linarith)]
      exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have haux := norm_sub_taylorSum_le_of_nonneg (by linarith : (0:ℝ) ≤ -h) hg hgC
    have h1 : g (-a + -h) = f (a + h) := by
      rw [hg_def]
      simp only []
      congr 1
      ring
    have h2 : ∀ j : ℕ, ((-h) ^ j / (j.factorial : ℝ)) • iteratedDeriv j g (-a)
        = (h ^ j / (j.factorial : ℝ)) • iteratedDeriv j f a := by
      intro j
      rw [hg_def, iteratedDeriv_comp_neg, smul_smul, neg_neg]
      congr 1
      rw [div_mul_eq_mul_div]
      congr 1
      rw [← mul_pow]
      congr 1
      ring
    rw [h1] at haux
    simp only [h2] at haux
    rw [abs_of_nonpos hh]
    exact haux

end Taylor

namespace MeasureTheory

/-- The tail of a finite integral vanishes: for integrable `g`,
`∫_{|r| > c} ‖g r‖ → 0` as `c → ∞`. -/
theorem tendsto_setIntegral_norm_abs_gt {g : ℝ → E} (hg : Integrable g volume) :
    Tendsto (fun c : ℝ => ∫ r in {r : ℝ | c < |r|}, ‖g r‖) atTop (𝓝 0) := by
  have hmeas : ∀ c : ℝ, MeasurableSet {r : ℝ | c < |r|} := fun c =>
    measurableSet_lt measurable_const continuous_abs.measurable
  have hrw : ∀ c : ℝ, (∫ r in {r : ℝ | c < |r|}, ‖g r‖)
      = ∫ r : ℝ, Set.indicator {r : ℝ | c < |r|} (fun r => ‖g r‖) r := by
    intro c
    rw [integral_indicator (hmeas c)]
  have hzero : Tendsto (fun c : ℝ =>
      ∫ r : ℝ, Set.indicator {r : ℝ | c < |r|} (fun r => ‖g r‖) r) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ r : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun r => ‖g r‖)
      (Filter.Eventually.of_forall fun c => ?_)
      (Filter.Eventually.of_forall fun c => Filter.Eventually.of_forall fun r => ?_)
      hg.norm (Filter.Eventually.of_forall fun r => ?_)
    · exact hg.norm.aestronglyMeasurable.indicator (hmeas c)
    · by_cases hr : r ∈ {r : ℝ | c < |r|}
      · rw [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_norm]
      · rw [Set.indicator_of_notMem hr, norm_zero]
        exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop |r|] with c hc
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_setOf_eq, not_lt]
      exact hc
  exact hzero.congr fun c => (hrw c).symm

/-- **Continuity of translation in `L¹(ℝ)`**: for integrable `Ξ`,
`∫ ‖Ξ (z - s) - Ξ z‖ dz → 0` as `s → 0`. -/
theorem tendsto_integral_norm_sub_comp_sub_right {Ξ : ℝ → E}
    (hΞ : Integrable Ξ volume) :
    Tendsto (fun s : ℝ => ∫ z : ℝ, ‖Ξ (z - s) - Ξ z‖) (𝓝 0) (𝓝 0) := by
  have hF : MemLp Ξ 1 volume := memLp_one_iff_integrable.mpr hΞ
  set F : Lp E 1 volume := hF.toLp Ξ with hF_def
  set g : ℝ → C(ℝ, ℝ) := fun s => ⟨fun z => z - s, by fun_prop⟩ with hg_def
  have hgm : ∀ s, MeasurePreserving (⇑(g s)) volume volume := fun s =>
    measurePreserving_sub_right volume s
  have hgc : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_snd.sub continuous_fst : Continuous fun p : ℝ × ℝ => p.2 - p.1)
  set G : ℝ → Lp E 1 volume := fun s =>
    Lp.compMeasurePreserving (⇑(g s)) (hgm s) F with hG_def
  have hGt : Tendsto G (𝓝 0) (𝓝 (G 0)) :=
    Filter.Tendsto.compMeasurePreservingLp tendsto_const_nhds (hgc.tendsto 0) hgm (hgm 0)
      ENNReal.one_ne_top
  have hnorm : Tendsto (fun s : ℝ => ‖G s - G 0‖) (𝓝 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hGt
  refine Filter.Tendsto.congr (fun s => ?_) hnorm
  -- identify the `L¹` norm of the difference with the integral
  have htrans : Integrable (fun z : ℝ => Ξ (z - s)) volume := hΞ.comp_sub_right s
  have hdiff : Integrable (fun z : ℝ => Ξ (z - s) - Ξ z) volume := htrans.sub hΞ
  have hcoe : ⇑(G s - G 0) =ᵐ[volume] fun z : ℝ => Ξ (z - s) - Ξ z := by
    have h1 : ⇑(G s) =ᵐ[volume] ⇑F ∘ ⇑(g s) := Lp.coeFn_compMeasurePreserving F (hgm s)
    have h0 : ⇑(G 0) =ᵐ[volume] ⇑F ∘ ⇑(g 0) := Lp.coeFn_compMeasurePreserving F (hgm 0)
    have hFs : (⇑F ∘ ⇑(g s)) =ᵐ[volume] fun z : ℝ => Ξ (z - s) :=
      (hgm s).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
    have hF0 : (⇑F ∘ ⇑(g 0)) =ᵐ[volume] fun z : ℝ => Ξ z := by
      refine ((hgm 0).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp).trans ?_
      have heq : (Ξ ∘ ⇑(g 0)) = fun z : ℝ => Ξ z := by
        funext z
        simp [hg_def]
      rw [heq]
    filter_upwards [Lp.coeFn_sub (G s) (G 0), h1.trans hFs, h0.trans hF0] with z hz h1z h0z
    rw [hz]
    simp only [Pi.sub_apply, h1z, h0z]
  calc ‖G s - G 0‖
      = (eLpNorm (⇑(G s - G 0)) 1 volume).toReal := by rw [Lp.norm_def]
    _ = (eLpNorm (fun z : ℝ => Ξ (z - s) - Ξ z) 1 volume).toReal := by
        rw [eLpNorm_congr_ae hcoe]
    _ = (∫⁻ z : ℝ, ‖Ξ (z - s) - Ξ z‖ₑ).toReal := by rw [eLpNorm_one_eq_lintegral_enorm]
    _ = ∫ z : ℝ, ‖Ξ (z - s) - Ξ z‖ := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hdiff, ENNReal.toReal_ofReal
          (integral_nonneg fun z => norm_nonneg _)]

/-- **Continuity of translation in polynomially weighted `L¹(ℝ)`**: if
`(1 + |z|)^k ‖Ξ z‖` is integrable, then `∫ (1 + |z|)^k ‖Ξ (z - s) - Ξ z‖ dz → 0` as
`s → 0`. -/
theorem tendsto_integral_weight_norm_sub_comp_sub_right (k : ℕ) {Ξ : ℝ → E}
    [NormedSpace ℝ E]
    (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume) :
    Tendsto (fun s : ℝ => ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖) (𝓝 0) (𝓝 0) := by
  -- the weighted function
  set Ξw : ℝ → E := fun z => (1 + |z|) ^ k • Ξ z with hΞw_def
  have hwc : Continuous fun z : ℝ => (1 + |z|) ^ k := by fun_prop
  have hΞwm : AEStronglyMeasurable Ξw volume := hwc.aestronglyMeasurable.smul hΞm
  have hΞw : Integrable Ξw volume := by
    refine hΞk.mono' hΞwm (Filter.Eventually.of_forall fun z => ?_)
    have hnorm : ‖Ξw z‖ = (1 + |z|) ^ k * ‖Ξ z‖ := by
      rw [hΞw_def]
      simp only []
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm]
  set MkΞ : ℝ := ∫ r : ℝ, (1 + |r|) ^ k * ‖Ξ r‖ with hMk_def
  -- the unweighted translation modulus of the weighted function
  have hA : Tendsto (fun s : ℝ => ∫ z : ℝ, ‖Ξw (z - s) - Ξw z‖) (𝓝 0) (𝓝 0) :=
    tendsto_integral_norm_sub_comp_sub_right hΞw
  -- the explicit weight-difference bound
  have hB : Tendsto (fun s : ℝ => (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * MkΞ)
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun s : ℝ =>
        (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * MkΞ := by fun_prop
    have h0 := hc.tendsto 0
    simpa using h0
  have hAB : Tendsto (fun s : ℝ => (∫ z : ℝ, ‖Ξw (z - s) - Ξw z‖) +
      (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * MkΞ) (𝓝 0) (𝓝 0) := by
    have h := hA.add hB
    simpa using h
  refine squeeze_zero (fun s => integral_nonneg fun z => by positivity) (fun s => ?_) hAB
  -- pointwise estimate
  have hpt : ∀ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖ ≤
      ‖Ξw (z - s) - Ξw z‖ +
        (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by
    intro z
    have hz1 : (0 : ℝ) ≤ 1 + |z| := by positivity
    have hzs1 : (0 : ℝ) ≤ 1 + |z - s| := by positivity
    -- weight comparison through the Lipschitz bound for powers
    have hxM : (1 : ℝ) + |z| ≤ (1 + |z - s|) * (1 + |s|) := by
      have h := one_add_abs_add_le_mul_one_add_abs (z - s) s
      simpa using h
    have hyM : (1 : ℝ) + |z - s| ≤ (1 + |z - s|) * (1 + |s|) := by
      nlinarith [abs_nonneg s, abs_nonneg (z - s)]
    have hdiff1 : |(1 + |z|) - (1 + |z - s|)| ≤ |s| := by
      have h2 := abs_abs_sub_abs_le_abs_sub z (z - s)
      rw [sub_sub_cancel] at h2
      have h3 : (1 + |z|) - (1 + |z - s|) = |z| - |z - s| := by ring
      rw [h3]
      exact h2
    have hpow : |(1 + |z|) ^ k - (1 + |z - s|) ^ k| ≤
        (k : ℝ) * ((1 + |z - s|) * (1 + |s|)) ^ (k - 1) * |s| := by
      refine le_trans (abs_pow_sub_pow_le_mul k hz1 hzs1 hxM hyM) ?_
      gcongr
    have hpow2 : |(1 + |z|) ^ k - (1 + |z - s|) ^ k| ≤
        (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * (1 + |z - s|) ^ k := by
      refine hpow.trans ?_
      have h1 : ((1 + |z - s|) * (1 + |s|)) ^ (k - 1) ≤ ((1 + |z - s|) * (1 + |s|)) ^ k :=
        pow_le_pow_right₀ (by nlinarith [abs_nonneg (z - s), abs_nonneg s]) (Nat.sub_le k 1)
      have h2 : ((1 + |z - s|) * (1 + |s|)) ^ k = (1 + |z - s|) ^ k * (1 + |s|) ^ k := by
        rw [mul_pow]
      have h3 : (1 + |s|) ^ k ≤ ((1 + |s|) * (1 + |s|)) ^ k := by
        refine pow_le_pow_left₀ (by positivity) ?_ k
        nlinarith [abs_nonneg s]
      calc (k : ℝ) * ((1 + |z - s|) * (1 + |s|)) ^ (k - 1) * |s|
          ≤ (k : ℝ) * ((1 + |z - s|) * (1 + |s|)) ^ k * |s| := by
            gcongr
        _ = (k : ℝ) * (1 + |s|) ^ k * |s| * (1 + |z - s|) ^ k := by
            rw [h2]; ring
        _ ≤ (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * (1 + |z - s|) ^ k := by
            gcongr
    -- split the weighted difference
    have hsplit : (1 + |z|) ^ k • Ξ (z - s) - Ξw z =
        (Ξw (z - s) - Ξw z) + ((1 + |z|) ^ k - (1 + |z - s|) ^ k) • Ξ (z - s) := by
      rw [hΞw_def]
      simp only [sub_smul]
      abel
    have habs : |(1 + |z|) ^ k| = (1 + |z|) ^ k := abs_of_nonneg (by positivity)
    calc (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖
        = ‖(1 + |z|) ^ k • Ξ (z - s) - Ξw z‖ := by
          rw [hΞw_def]
          simp only []
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, habs]
      _ ≤ ‖Ξw (z - s) - Ξw z‖ + ‖((1 + |z|) ^ k - (1 + |z - s|) ^ k) • Ξ (z - s)‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ = ‖Ξw (z - s) - Ξw z‖ + |(1 + |z|) ^ k - (1 + |z - s|) ^ k| * ‖Ξ (z - s)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖Ξw (z - s) - Ξw z‖ +
            (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| *
              ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by
          have hmul : |(1 + |z|) ^ k - (1 + |z - s|) ^ k| * ‖Ξ (z - s)‖ ≤
              (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| *
                ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by
            calc |(1 + |z|) ^ k - (1 + |z - s|) ^ k| * ‖Ξ (z - s)‖
                ≤ ((k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * (1 + |z - s|) ^ k) *
                    ‖Ξ (z - s)‖ := mul_le_mul_of_nonneg_right hpow2 (norm_nonneg _)
              _ = (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| *
                    ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by ring
          exact add_le_add le_rfl hmul
  -- integrate the estimate
  have hrhs1 : Integrable (fun z : ℝ => ‖Ξw (z - s) - Ξw z‖) volume :=
    ((hΞw.comp_sub_right s).sub hΞw).norm
  have hrhs2 : Integrable
      (fun z : ℝ => (1 + |z - s|) ^ k * ‖Ξ (z - s)‖) volume :=
    hΞk.comp_sub_right s
  calc ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖
      ≤ ∫ z : ℝ, (‖Ξw (z - s) - Ξw z‖ +
          (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| *
            ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
          (hrhs1.add ((hrhs2.const_mul _))) (Filter.Eventually.of_forall hpt)
    _ = (∫ z : ℝ, ‖Ξw (z - s) - Ξw z‖) +
          (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| *
            ∫ z : ℝ, (1 + |z - s|) ^ k * ‖Ξ (z - s)‖ := by
        rw [integral_add hrhs1 (hrhs2.const_mul _), integral_const_mul]
    _ = (∫ z : ℝ, ‖Ξw (z - s) - Ξw z‖) +
          (k : ℝ) * ((1 + |s|) * (1 + |s|)) ^ k * |s| * MkΞ := by
        rw [hMk_def]
        congr 1
        congr 1
        exact integral_sub_right_eq_self (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) s

end MeasureTheory

/-- Uniform decay of the iterated derivatives of a Schwartz function. -/
theorem schwartz_iteratedDeriv_decay (θ : SchwartzMap ℝ ℂ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ k + 1, ∀ y : ℝ,
      (1 + |y|) ^ (k + 2) * ‖iteratedDeriv j (⇑θ) y‖ ≤ B := by
  refine ⟨2 ^ (k + 2) *
      (Finset.Iic ((k + 2 : ℕ), (k + 1 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) θ,
    mul_nonneg (by positivity) (apply_nonneg _ _), ?_⟩
  intro j hj y
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := ((k + 2 : ℕ), (k + 1 : ℕ))) le_rfl hj θ y
  rwa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h

/-- `(a + b)^k ≤ 2^k (a^k + b^k)` for nonnegative reals. -/
theorem add_pow_le_two_pow_mul (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have h1 : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · calc a + b ≤ b + b := by linarith
        _ = 2 * b := by ring
        _ ≤ 2 * max a b := by
            have := le_max_right a b
            linarith
    · calc a + b ≤ a + a := by linarith
        _ = 2 * a := by ring
        _ ≤ 2 * max a b := by
            have := le_max_left a b
            linarith
  calc (a + b) ^ k ≤ (2 * max a b) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = 2 ^ k * (max a b) ^ k := mul_pow 2 (max a b) k
    _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
        have hmax : (max a b) ^ k ≤ a ^ k + b ^ k := by
          rcases max_cases a b with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq]
          · exact le_add_of_nonneg_right (pow_nonneg hb k)
          · exact le_add_of_nonneg_left (pow_nonneg ha k)
        gcongr

namespace MeasureTheory

/-- Change of variables `w ↦ (w - r) / c` for vector-valued integrals on the line. -/
theorem integral_comp_sub_div_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (r : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ w : ℝ, F ((w - r) / c) = c • ∫ v : ℝ, F v := by
  have h1 : (∫ w : ℝ, F ((w - r) / c)) = ∫ w : ℝ, F (w / c) :=
    integral_sub_right_eq_self (fun t : ℝ => F (t / c)) r
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure ℝ) F hc.le
  simp only [Module.finrank_self, pow_one] at h2
  rw [h1, ← h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp [div_eq_inv_mul])

/-- Change of variables `w ↦ (w - r) / c` for real integrals on the line. -/
theorem integral_comp_sub_div (F : ℝ → ℝ) (r : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ w : ℝ, F ((w - r) / c) = c * ∫ v : ℝ, F v := by
  have h1 : (∫ w : ℝ, F ((w - r) / c)) = ∫ w : ℝ, F (w / c) :=
    integral_sub_right_eq_self (fun t : ℝ => F (t / c)) r
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure ℝ) F hc.le
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at h2
  rw [h1, ← h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp [div_eq_inv_mul])

set_option maxHeartbeats 1000000 in
-- The proof is a single long assembly of explicit integral estimates (Taylor expansion,
-- change of variables, tail splitting); it exceeds the default heartbeat budget.
/-- **Vanishing-moment cancellation for wide smoothing**: if `Ξ` has a finite `k`-th moment
and vanishing moments up to `k`, and `η` is strongly measurable with growth at most
`(1 + |z|)^k`, then the pairing of `Ξ` with the `c`-scale smoothing of `η` by a Schwartz
kernel `θ` tends to zero as the scale `c → ∞`. -/
theorem tendsto_integral_mul_smoothing_of_vanishing_moments (k : ℕ)
    {η Ξ : ℝ → ℂ} {Cη : ℝ} (θ : SchwartzMap ℝ ℂ)
    (hηm : StronglyMeasurable η)
    (hηk : ∀ z, ‖η z‖ ≤ Cη * (1 + |z|) ^ k)
    (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume)
    (hΞvm : ∀ j ≤ k, (∫ r : ℝ, (r : ℂ) ^ j * Ξ r) = 0) :
    Filter.Tendsto (fun c : ℝ => ∫ r : ℝ, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)))
      Filter.atTop (𝓝 0) := by
  classical
  obtain ⟨B, hB0, hB⟩ := schwartz_iteratedDeriv_decay θ k
  have hCη : 0 ≤ Cη := by
    have h := hηk 0
    have h2 : ‖η 0‖ ≤ Cη := by simpa using h
    exact le_trans (norm_nonneg _) h2
  -- the iterated derivatives of the kernel
  set D : ℕ → ℝ → ℂ := fun j => iteratedDeriv j (⇑θ) with hD_def
  have hDcont : ∀ j : ℕ, Continuous (D j) := fun j =>
    (θ.smooth j).continuous_iteratedDeriv'
  -- multiplicative decay chain: `‖D j (x / c)‖ (1 + |x|)^(k+2) ≤ B c^(k+2)`
  have hDpow : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c → ∀ x : ℝ,
      ‖D j (x / c)‖ * (1 + |x|) ^ (k + 2) ≤ B * c ^ (k + 2) := by
    intro j hj c hc x
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    have hxc : 1 + |x| ≤ (1 + |x / c|) * c := by
      rw [abs_div, abs_of_pos hc0, add_mul, one_mul, div_mul_cancel₀ _ hc0.ne']
      linarith
    calc ‖D j (x / c)‖ * (1 + |x|) ^ (k + 2)
        ≤ ‖D j (x / c)‖ * ((1 + |x / c|) * c) ^ (k + 2) := by
          gcongr
      _ = ((1 + |x / c|) ^ (k + 2) * ‖D j (x / c)‖) * c ^ (k + 2) := by
          rw [mul_pow]
          ring
      _ ≤ B * c ^ (k + 2) :=
          mul_le_mul_of_nonneg_right (hB j hj (x / c)) (by positivity)
  -- pointwise integrable majorant for weighted kernels
  have hptw : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c → ∀ r w : ℝ,
      (1 + |w|) ^ k * ‖D j ((w - r) / c)‖ ≤
        (B * (1 + |r|) ^ k * c ^ (k + 2)) * (1 + (w - r) ^ 2)⁻¹ := by
    intro j hj c hc r w
    have hpos : (0 : ℝ) < 1 + (w - r) ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    have h1wk : (1 + |w|) ^ k ≤ (1 + |r|) ^ k * (1 + |w - r|) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have h := one_add_abs_add_le_mul_one_add_abs r (w - r)
      simpa using h
    have hsq : 1 + (w - r) ^ 2 ≤ (1 + |w - r|) ^ 2 := by
      nlinarith [abs_nonneg (w - r), sq_abs (w - r)]
    calc (1 + |w|) ^ k * ‖D j ((w - r) / c)‖ * (1 + (w - r) ^ 2)
        ≤ ((1 + |r|) ^ k * (1 + |w - r|) ^ k) * ‖D j ((w - r) / c)‖ *
            (1 + |w - r|) ^ 2 := by
          gcongr
      _ = (1 + |r|) ^ k * (‖D j ((w - r) / c)‖ *
            ((1 + |w - r|) ^ k * (1 + |w - r|) ^ 2)) := by ring
      _ = (1 + |r|) ^ k * (‖D j ((w - r) / c)‖ * (1 + |w - r|) ^ (k + 2)) := by
          rw [← pow_add]
      _ ≤ (1 + |r|) ^ k * (B * c ^ (k + 2)) :=
          mul_le_mul_of_nonneg_left (hDpow j hj hc (w - r)) (by positivity)
      _ = B * (1 + |r|) ^ k * c ^ (k + 2) := by ring
  -- integrability of the weighted kernels
  have hWintr : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c → ∀ r : ℝ,
      Integrable (fun w : ℝ => (1 + |w|) ^ k * ‖D j ((w - r) / c)‖) volume := by
    intro j hj c hc r
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    have hmeas : AEStronglyMeasurable
        (fun w : ℝ => (1 + |w|) ^ k * ‖D j ((w - r) / c)‖) volume := by
      have hcomp : Continuous fun w : ℝ => (w - r) / c := by fun_prop
      exact ((by fun_prop : Continuous fun w : ℝ => (1 + |w|) ^ k).mul
        ((hDcont j).comp hcomp).norm).aestronglyMeasurable
    refine Integrable.mono'
      (((integrable_inv_one_add_sq).comp_sub_right r).const_mul
        (B * (1 + |r|) ^ k * c ^ (k + 2))) hmeas
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hptw j hj hc r w
  -- integrability of the activation-weighted kernels
  have hker : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c → ∀ r : ℝ,
      Integrable (fun w : ℝ => η w * D j ((w - r) / c)) volume := by
    intro j hj c hc r
    have hmeas : AEStronglyMeasurable (fun w : ℝ => η w * D j ((w - r) / c)) volume := by
      have hcomp : Continuous fun w : ℝ => (w - r) / c := by fun_prop
      exact hηm.aestronglyMeasurable.mul
        ((hDcont j).comp hcomp).aestronglyMeasurable
    refine Integrable.mono' ((hWintr j hj hc r).const_mul Cη) hmeas
      (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul]
    calc ‖η w‖ * ‖D j ((w - r) / c)‖
        ≤ (Cη * (1 + |w|) ^ k) * ‖D j ((w - r) / c)‖ :=
          mul_le_mul_of_nonneg_right (hηk w) (norm_nonneg _)
      _ = Cη * ((1 + |w|) ^ k * ‖D j ((w - r) / c)‖) := by ring
  -- weighted moments of the derivative kernels
  set N : ℕ → ℝ := fun j => ∫ v : ℝ, (1 + |v|) ^ k * ‖D j v‖ with hN_def
  have hNint : ∀ j ≤ k + 1, Integrable (fun v : ℝ => (1 + |v|) ^ k * ‖D j v‖) volume := by
    intro j hj
    refine (hWintr j hj le_rfl 0).congr (Filter.Eventually.of_forall fun v => ?_)
    simp
  have hN0 : ∀ j : ℕ, 0 ≤ N j := fun j => integral_nonneg fun v => by positivity
  -- change-of-variables bound for the scaled weighted moments
  have hIθw : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c →
      (∫ w : ℝ, (1 + |w|) ^ k * ‖D j (w / c)‖) ≤ c ^ (k + 1) * N j := by
    intro j hj c hc
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    have hcov : (∫ w : ℝ, (1 + |w|) ^ k * ‖D j (w / c)‖)
        = c * ∫ v : ℝ, (1 + |c * v|) ^ k * ‖D j v‖ := by
      have h := integral_comp_sub_div (fun v : ℝ => (1 + |c * v|) ^ k * ‖D j v‖) 0 hc0
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      have harg : c * ((w - 0) / c) = w := by
        rw [sub_zero, mul_comm c (w / c), div_mul_cancel₀ _ hc0.ne']
      simp only [harg]
      simp only [sub_zero]
    rw [hcov]
    have hmono : (∫ v : ℝ, (1 + |c * v|) ^ k * ‖D j v‖) ≤ c ^ k * N j := by
      have hrhs : Integrable (fun v : ℝ => c ^ k * ((1 + |v|) ^ k * ‖D j v‖)) volume :=
        (hNint j hj).const_mul _
      have hle : ∀ v : ℝ, (1 + |c * v|) ^ k * ‖D j v‖ ≤
          c ^ k * ((1 + |v|) ^ k * ‖D j v‖) := by
        intro v
        have h1 : 1 + |c * v| ≤ c * (1 + |v|) := by
          rw [abs_mul, abs_of_pos hc0]
          nlinarith [abs_nonneg v]
        calc (1 + |c * v|) ^ k * ‖D j v‖ ≤ (c * (1 + |v|)) ^ k * ‖D j v‖ := by
              gcongr
          _ = c ^ k * ((1 + |v|) ^ k * ‖D j v‖) := by rw [mul_pow]; ring
      calc (∫ v : ℝ, (1 + |c * v|) ^ k * ‖D j v‖)
          ≤ ∫ v : ℝ, c ^ k * ((1 + |v|) ^ k * ‖D j v‖) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
              hrhs (Filter.Eventually.of_forall hle)
        _ = c ^ k * ∫ v : ℝ, (1 + |v|) ^ k * ‖D j v‖ := integral_const_mul _ _
        _ = c ^ k * N j := by rw [hN_def]
    calc c * ∫ v : ℝ, (1 + |c * v|) ^ k * ‖D j v‖ ≤ c * (c ^ k * N j) := by
          have := hmono
          nlinarith [hc0]
      _ = c ^ (k + 1) * N j := by rw [pow_succ]; ring
  -- norm bound for the scaled derivative integrals
  have hIjnorm : ∀ j ≤ k + 1, ∀ {c : ℝ}, 1 ≤ c →
      ‖∫ w : ℝ, η w * D j (w / c)‖ ≤ Cη * (c ^ (k + 1) * N j) := by
    intro j hj c hc
    have hWc : Integrable (fun w : ℝ => (1 + |w|) ^ k * ‖D j (w / c)‖) volume := by
      refine (hWintr j hj hc 0).congr (Filter.Eventually.of_forall fun w => ?_)
      simp
    calc ‖∫ w : ℝ, η w * D j (w / c)‖ ≤ ∫ w : ℝ, ‖η w * D j (w / c)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℝ, Cη * ((1 + |w|) ^ k * ‖D j (w / c)‖) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun w => norm_nonneg _)
            (hWc.const_mul Cη) (Filter.Eventually.of_forall fun w => ?_)
          simp only [norm_mul]
          calc ‖η w‖ * ‖D j (w / c)‖ ≤ (Cη * (1 + |w|) ^ k) * ‖D j (w / c)‖ :=
                mul_le_mul_of_nonneg_right (hηk w) (norm_nonneg _)
            _ = Cη * ((1 + |w|) ^ k * ‖D j (w / c)‖) := by ring
      _ = Cη * ∫ w : ℝ, (1 + |w|) ^ k * ‖D j (w / c)‖ := integral_const_mul _ _
      _ ≤ Cη * (c ^ (k + 1) * N j) :=
          mul_le_mul_of_nonneg_left (hIθw j hj hc) hCη
  -- the θ kernel is the zeroth derivative
  have hθD : ∀ x : ℝ, (θ : ℝ → ℂ) x = D 0 x := fun x => by
    rw [hD_def]
    simp [iteratedDeriv_zero]
  set T0 : ℝ := ∫ v : ℝ, ‖D 0 v‖ with hT0_def
  set Tk : ℝ := ∫ v : ℝ, |v| ^ k * ‖D 0 v‖ with hTk_def
  have hθint : Integrable (fun v : ℝ => ‖D 0 v‖) volume := by
    refine θ.integrable.norm.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [hθD]
  have hθkint : Integrable (fun v : ℝ => |v| ^ k * ‖D 0 v‖) volume := by
    refine (hNint 0 (Nat.zero_le _)).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((by fun_prop : Continuous fun v : ℝ => |v| ^ k).mul
        ((hDcont 0).norm)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : |v| ^ k ≤ (1 + |v|) ^ k :=
        pow_le_pow_left₀ (abs_nonneg v) (by linarith [abs_nonneg v]) k
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hT00 : 0 ≤ T0 := integral_nonneg fun v => norm_nonneg _
  have hTk0 : 0 ≤ Tk := integral_nonneg fun v => by positivity
  -- global bound for the smoothed field
  have hGout : ∀ {c : ℝ}, 1 ≤ c → ∀ r : ℝ,
      ‖c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)‖ ≤
        Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk) := by
    intro c hc r
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    have h1 : ‖∫ w : ℝ, η w * θ ((w - r) / c)‖ ≤
        Cη * ∫ w : ℝ, (1 + |w|) ^ k * ‖D 0 ((w - r) / c)‖ := by
      calc ‖∫ w : ℝ, η w * θ ((w - r) / c)‖ ≤ ∫ w : ℝ, ‖η w * θ ((w - r) / c)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ w : ℝ, Cη * ((1 + |w|) ^ k * ‖D 0 ((w - r) / c)‖) := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun w => norm_nonneg _)
              ((hWintr 0 (Nat.zero_le _) hc r).const_mul Cη)
              (Filter.Eventually.of_forall fun w => ?_)
            simp only [norm_mul, hθD]
            calc ‖η w‖ * ‖D 0 ((w - r) / c)‖
                ≤ (Cη * (1 + |w|) ^ k) * ‖D 0 ((w - r) / c)‖ :=
                  mul_le_mul_of_nonneg_right (hηk w) (norm_nonneg _)
              _ = Cη * ((1 + |w|) ^ k * ‖D 0 ((w - r) / c)‖) := by ring
        _ = Cη * ∫ w : ℝ, (1 + |w|) ^ k * ‖D 0 ((w - r) / c)‖ := integral_const_mul _ _
    have h2 : (∫ w : ℝ, (1 + |w|) ^ k * ‖D 0 ((w - r) / c)‖)
        = c * ∫ v : ℝ, (1 + |r + c * v|) ^ k * ‖D 0 v‖ := by
      have h := integral_comp_sub_div
        (fun v : ℝ => (1 + |r + c * v|) ^ k * ‖D 0 v‖) r hc0
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      have harg : r + c * ((w - r) / c) = w := by
        rw [mul_comm c ((w - r) / c), div_mul_cancel₀ _ hc0.ne']
        ring
      simp only [harg]
    have h3 : (∫ v : ℝ, (1 + |r + c * v|) ^ k * ‖D 0 v‖)
        ≤ 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk) := by
      have hrhs : Integrable (fun v : ℝ =>
          2 ^ k * ((1 + |r|) ^ k * ‖D 0 v‖ + c ^ k * (|v| ^ k * ‖D 0 v‖))) volume :=
        ((hθint.const_mul _).add (hθkint.const_mul _)).const_mul _
      have hle : ∀ v : ℝ, (1 + |r + c * v|) ^ k * ‖D 0 v‖ ≤
          2 ^ k * ((1 + |r|) ^ k * ‖D 0 v‖ + c ^ k * (|v| ^ k * ‖D 0 v‖)) := by
        intro v
        have h1v : 1 + |r + c * v| ≤ (1 + |r|) + c * |v| := by
          have := abs_add_le r (c * v)
          rw [abs_mul, abs_of_pos hc0] at this
          linarith
        have h2v : (1 + |r + c * v|) ^ k ≤ 2 ^ k * ((1 + |r|) ^ k + c ^ k * |v| ^ k) := by
          calc (1 + |r + c * v|) ^ k ≤ ((1 + |r|) + c * |v|) ^ k := by
                gcongr
            _ ≤ 2 ^ k * ((1 + |r|) ^ k + (c * |v|) ^ k) :=
                add_pow_le_two_pow_mul k (by positivity) (by positivity)
            _ = 2 ^ k * ((1 + |r|) ^ k + c ^ k * |v| ^ k) := by rw [mul_pow]
        calc (1 + |r + c * v|) ^ k * ‖D 0 v‖
            ≤ (2 ^ k * ((1 + |r|) ^ k + c ^ k * |v| ^ k)) * ‖D 0 v‖ :=
              mul_le_mul_of_nonneg_right h2v (norm_nonneg _)
          _ = 2 ^ k * ((1 + |r|) ^ k * ‖D 0 v‖ + c ^ k * (|v| ^ k * ‖D 0 v‖)) := by ring
      calc (∫ v : ℝ, (1 + |r + c * v|) ^ k * ‖D 0 v‖)
          ≤ ∫ v : ℝ, 2 ^ k * ((1 + |r|) ^ k * ‖D 0 v‖ + c ^ k * (|v| ^ k * ‖D 0 v‖)) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
              hrhs (Filter.Eventually.of_forall hle)
        _ = 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk) := by
            rw [integral_const_mul, integral_add (hθint.const_mul _) (hθkint.const_mul _),
              integral_const_mul, integral_const_mul, hT0_def, hTk_def]
    calc ‖c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)‖
        = c⁻¹ * ‖∫ w : ℝ, η w * θ ((w - r) / c)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0]
      _ ≤ c⁻¹ * (Cη * (c * (2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans h1 ?_
          rw [h2]
          refine mul_le_mul_of_nonneg_left ?_ hCη
          exact mul_le_mul_of_nonneg_left h3 hc0.le
      _ = Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk) := by
          have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0.ne'
          calc c⁻¹ * (Cη * (c * (2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk))))
              = (c⁻¹ * c) * (Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk)) := by ring
            _ = Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk) := by rw [hcc, one_mul]
  -- the arctangent mass of the majorant
  set I2 : ℝ := ∫ v : ℝ, (1 + v ^ 2)⁻¹ with hI2_def
  have hI20 : 0 ≤ I2 := integral_nonneg fun v => by positivity
  -- Taylor remainder bound for the smoothed field on `|r| ≤ c`
  have hρ : ∀ {c : ℝ}, 1 ≤ c → ∀ r : ℝ, |r| ≤ c →
      ‖(c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
        ∑ j ∈ Finset.range (k + 1),
          ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))‖ ≤
        (Cη * (B * 2 ^ (k + 2)) * I2 / k.factorial) *
          ((1 + |r|) ^ k * min 1 (|r| / c)) := by
    intro c hc r hr
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    have hker0 : ∀ j ≤ k + 1, Integrable (fun w : ℝ => η w * D j (w / c)) volume := by
      intro j hj
      refine (hker j hj hc 0).congr (Filter.Eventually.of_forall fun w => ?_)
      simp
    have hkerθ : Integrable (fun w : ℝ => η w * θ ((w - r) / c)) volume := by
      refine (hker 0 (Nat.zero_le _) hc r).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [hθD]
    -- move the finite sum inside a single integral
    have hSc : (∑ j ∈ Finset.range (k + 1),
        ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))
        = c⁻¹ * ∫ w : ℝ, η w * ∑ j ∈ Finset.range (k + 1),
            ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c) := by
      have hstep1 : ∀ j ∈ Finset.range (k + 1),
          Integrable (fun w : ℝ =>
            ((-r / c) ^ j / (j.factorial : ℝ)) • (η w * D j (w / c))) volume := fun j hj =>
        ((hker0 j (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          (Nat.le_succ k))).smul (((-r / c) ^ j / (j.factorial : ℝ)))).congr
          (Filter.Eventually.of_forall fun w => rfl)
      calc (∑ j ∈ Finset.range (k + 1),
            ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))
          = c⁻¹ * ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) • ∫ w : ℝ, η w * D j (w / c) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j hj => (mul_smul_comm _ _ _).symm
        _ = c⁻¹ * ∑ j ∈ Finset.range (k + 1),
              ∫ w : ℝ, ((-r / c) ^ j / (j.factorial : ℝ)) • (η w * D j (w / c)) := by
            congr 1
            exact Finset.sum_congr rfl fun j hj => (integral_smul _ _).symm
        _ = c⁻¹ * ∫ w : ℝ, ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) • (η w * D j (w / c)) := by
            congr 1
            exact (integral_finsetSum _ hstep1).symm
        _ = c⁻¹ * ∫ w : ℝ, η w * ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c) := by
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            simp only []
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j hj => (mul_smul_comm _ _ _).symm
    have hSumInt : Integrable (fun w : ℝ => η w *
        ∑ j ∈ Finset.range (k + 1),
          ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c)) volume := by
      have heq : (fun w : ℝ => η w * ∑ j ∈ Finset.range (k + 1),
          ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c))
          = fun w : ℝ => ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) • (η w * D j (w / c)) := by
        funext w
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j hj => mul_smul_comm _ _ _
      rw [heq]
      refine integrable_finsetSum _ fun j hj => ?_
      exact ((hker0 j (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        (Nat.le_succ k))).smul (((-r / c) ^ j / (j.factorial : ℝ)))).congr
        (Filter.Eventually.of_forall fun w => rfl)
    -- pointwise Taylor bound
    have hTay : ∀ w : ℝ, ‖θ ((w - r) / c) - ∑ j ∈ Finset.range (k + 1),
        ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c)‖ ≤
        (B * 2 ^ (k + 2) * ((1 + |w / c|) ^ (k + 2))⁻¹) * (|r| / c) ^ (k + 1) /
          k.factorial := by
      intro w
      have hCw : ∀ y ∈ Set.uIcc (w / c) (w / c + -r / c),
          ‖iteratedDeriv (k + 1) (⇑θ) y‖ ≤
            B * 2 ^ (k + 2) * ((1 + |w / c|) ^ (k + 2))⁻¹ := by
        intro y hy
        have hyd : |y - w / c| ≤ |-r / c| := by
          rcases Set.mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            exact abs_le.mpr ⟨by linarith [neg_abs_le (-r / c), abs_nonneg (-r / c)],
              by linarith [le_abs_self (-r / c), abs_nonneg (-r / c)]⟩
        have hrc1 : |-r / c| ≤ 1 := by
          rw [abs_div, abs_neg, abs_of_pos hc0, div_le_one hc0]
          exact hr
        have hwy : 1 + |w / c| ≤ 2 * (1 + |y|) := by
          have h1 : |w / c| - |y| ≤ |w / c - y| := abs_sub_abs_le_abs_sub _ _
          have h2 : |w / c - y| = |y - w / c| := abs_sub_comm _ _
          linarith [hyd, hrc1, abs_nonneg y]
        have hbb := hB (k + 1) le_rfl y
        have hp2 : (1 + |w / c|) ^ (k + 2) ≤ 2 ^ (k + 2) * (1 + |y|) ^ (k + 2) := by
          calc (1 + |w / c|) ^ (k + 2) ≤ (2 * (1 + |y|)) ^ (k + 2) :=
                pow_le_pow_left₀ (by positivity) hwy _
            _ = 2 ^ (k + 2) * (1 + |y|) ^ (k + 2) := mul_pow _ _ _
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        calc ‖iteratedDeriv (k + 1) (⇑θ) y‖ * (1 + |w / c|) ^ (k + 2)
            ≤ ‖iteratedDeriv (k + 1) (⇑θ) y‖ * (2 ^ (k + 2) * (1 + |y|) ^ (k + 2)) := by
              gcongr
          _ = ((1 + |y|) ^ (k + 2) * ‖iteratedDeriv (k + 1) (⇑θ) y‖) * 2 ^ (k + 2) := by
              ring
          _ ≤ B * 2 ^ (k + 2) := mul_le_mul_of_nonneg_right hbb (by positivity)
      have h := norm_sub_taylorSum_le (θ.smooth _) hCw
      have harg : w / c + -r / c = (w - r) / c := by ring
      rw [harg] at h
      have habs : |-r / c| = |r| / c := by
        rw [abs_div, abs_neg, abs_of_pos hc0]
      rw [habs] at h
      exact h
    -- integrable majorant of the weighted remainder
    have hmajint : Integrable (fun w : ℝ =>
        (1 + |w|) ^ k * ((1 + |w / c|) ^ (k + 2))⁻¹) volume := by
      refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (c ^ (k + 2))) ?_
        (Filter.Eventually.of_forall fun w => ?_)
      · exact ((by fun_prop : Continuous fun w : ℝ => (1 + |w|) ^ k).mul
          ((by fun_prop : Continuous fun w : ℝ => (1 + |w / c|) ^ (k + 2)).inv₀
            fun w => by positivity)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv,
          ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : 1 + |w| ≤ (1 + |w / c|) * c := by
          rw [abs_div, abs_of_pos hc0, add_mul, one_mul, div_mul_cancel₀ _ hc0.ne']
          linarith
        calc (1 + |w|) ^ k * (1 + w ^ 2) ≤ (1 + |w|) ^ k * (1 + |w|) ^ 2 := by
              gcongr
              nlinarith [abs_nonneg w, sq_abs w]
          _ = (1 + |w|) ^ (k + 2) := by rw [← pow_add]
          _ ≤ ((1 + |w / c|) * c) ^ (k + 2) := pow_le_pow_left₀ (by positivity) h1 _
          _ = c ^ (k + 2) * (1 + |w / c|) ^ (k + 2) := by rw [mul_pow]; ring
    -- assemble
    rw [hSc, ← mul_sub]
    calc ‖(↑c⁻¹ : ℂ) * ((∫ w : ℝ, η w * θ ((w - r) / c)) -
          ∫ w : ℝ, η w * ∑ j ∈ Finset.range (k + 1),
            ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c))‖
        = c⁻¹ * ‖∫ w : ℝ, (η w * θ ((w - r) / c) -
            η w * ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c))‖ := by
          rw [← integral_sub hkerθ hSumInt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_of_pos hc0]
      _ ≤ c⁻¹ * ∫ w : ℝ, (Cη * (B * 2 ^ (k + 2) * (|r| / c) ^ (k + 1) / k.factorial)) *
            ((1 + |w|) ^ k * ((1 + |w / c|) ^ (k + 2))⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (norm_integral_le_integral_norm _) ?_
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun w => norm_nonneg _)
            (hmajint.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
          simp only []
          rw [← mul_sub, norm_mul]
          calc ‖η w‖ * ‖θ ((w - r) / c) - ∑ j ∈ Finset.range (k + 1),
                ((-r / c) ^ j / (j.factorial : ℝ)) • D j (w / c)‖
              ≤ (Cη * (1 + |w|) ^ k) *
                  ((B * 2 ^ (k + 2) * ((1 + |w / c|) ^ (k + 2))⁻¹) * (|r| / c) ^ (k + 1) /
                    k.factorial) :=
                mul_le_mul (hηk w) (hTay w) (norm_nonneg _) (by positivity)
            _ = (Cη * (B * 2 ^ (k + 2) * (|r| / c) ^ (k + 1) / k.factorial)) *
                  ((1 + |w|) ^ k * ((1 + |w / c|) ^ (k + 2))⁻¹) := by ring
      _ = c⁻¹ * ((Cη * (B * 2 ^ (k + 2) * (|r| / c) ^ (k + 1) / k.factorial)) *
            ∫ w : ℝ, (1 + |w|) ^ k * ((1 + |w / c|) ^ (k + 2))⁻¹) := by
          rw [integral_const_mul]
      _ ≤ c⁻¹ * ((Cη * (B * 2 ^ (k + 2) * (|r| / c) ^ (k + 1) / k.factorial)) *
            (c ^ (k + 1) * I2)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
          have hcov2 : (∫ w : ℝ, (1 + |w|) ^ k * ((1 + |w / c|) ^ (k + 2))⁻¹)
              = c * ∫ v : ℝ, (1 + |c * v|) ^ k * ((1 + |v|) ^ (k + 2))⁻¹ := by
            have h := integral_comp_sub_div
              (fun v : ℝ => (1 + |c * v|) ^ k * ((1 + |v|) ^ (k + 2))⁻¹) 0 hc0
            rw [← h]
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            have harg : c * ((w - 0) / c) = w := by
              rw [sub_zero, mul_comm c (w / c), div_mul_cancel₀ _ hc0.ne']
            simp only [harg]
            simp only [sub_zero]
          rw [hcov2]
          have hvmono : (∫ v : ℝ, (1 + |c * v|) ^ k * ((1 + |v|) ^ (k + 2))⁻¹)
              ≤ c ^ k * I2 := by
            rw [hI2_def, ← integral_const_mul]
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun v => by positivity)
              (integrable_inv_one_add_sq.const_mul _)
              (Filter.Eventually.of_forall fun v => ?_)
            simp only []
            rw [← div_eq_mul_inv, ← div_eq_mul_inv,
              div_le_div_iff₀ (by positivity) (by positivity)]
            have h1 : 1 + |c * v| ≤ c * (1 + |v|) := by
              rw [abs_mul, abs_of_pos hc0]
              nlinarith [abs_nonneg v]
            calc (1 + |c * v|) ^ k * (1 + v ^ 2)
                ≤ (c * (1 + |v|)) ^ k * (1 + |v|) ^ 2 := by
                  gcongr
                  nlinarith [abs_nonneg v, sq_abs v]
              _ = c ^ k * ((1 + |v|) ^ k * (1 + |v|) ^ 2) := by rw [mul_pow]; ring
              _ = c ^ k * (1 + |v|) ^ (k + 2) := by rw [← pow_add]
          calc c * ∫ v : ℝ, (1 + |c * v|) ^ k * ((1 + |v|) ^ (k + 2))⁻¹
              ≤ c * (c ^ k * I2) := mul_le_mul_of_nonneg_left hvmono hc0.le
            _ = c ^ (k + 1) * I2 := by rw [pow_succ]; ring
      _ ≤ (Cη * (B * 2 ^ (k + 2)) * I2 / k.factorial) *
            ((1 + |r|) ^ k * min 1 (|r| / c)) := by
          have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
          have hmin : min 1 (|r| / c) = |r| / c := min_eq_right (by
            rw [div_le_one hc0]
            exact hr)
          have hLHS : c⁻¹ * ((Cη * (B * 2 ^ (k + 2) * (|r| / c) ^ (k + 1) / k.factorial)) *
              (c ^ (k + 1) * I2))
              = (Cη * (B * 2 ^ (k + 2)) * I2 / k.factorial) * (|r| ^ k * (|r| / c)) := by
            rw [div_pow]
            field_simp
            ring
          rw [hLHS, hmin]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_left₀ (abs_nonneg r) (by linarith [abs_nonneg r]) k
  -- moment integrands
  have hmomint : ∀ j ≤ k, Integrable (fun r : ℝ => (r : ℂ) ^ j * Ξ r) volume := by
    intro j hj
    have hmeas : AEStronglyMeasurable (fun r : ℝ => (r : ℂ) ^ j * Ξ r) volume :=
      ((Complex.continuous_ofReal.pow j).aestronglyMeasurable).mul hΞm
    refine hΞk.mono' hmeas (Filter.Eventually.of_forall fun r => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |r| ^ j ≤ (1 + |r|) ^ k :=
      le_trans (pow_le_pow_left₀ (abs_nonneg r) (le_add_of_nonneg_left zero_le_one) j)
        (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg r)) hj)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  -- the outer set, tail, and dominated remainder mass
  have hSmeas : ∀ c : ℝ, MeasurableSet {r : ℝ | c < |r|} := fun c =>
    measurableSet_lt measurable_const continuous_abs.measurable
  set τ : ℝ → ℝ := fun c => ∫ r in {r : ℝ | c < |r|}, (1 + |r|) ^ k * ‖Ξ r‖ with hτ_def
  set μf : ℝ → ℝ := fun c => ∫ r : ℝ, (1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c) with hμ_def
  have hτ0 : Tendsto τ atTop (𝓝 0) := by
    have hwc : Continuous fun r : ℝ => (1 + |r|) ^ k := by fun_prop
    have hg : Integrable (fun r : ℝ => ((1 + |r|) ^ k : ℝ) • Ξ r) volume := by
      refine hΞk.mono' (hwc.aestronglyMeasurable.smul hΞm)
        (Filter.Eventually.of_forall fun r => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := MeasureTheory.tendsto_setIntegral_norm_abs_gt hg
    refine h.congr fun c => ?_
    refine setIntegral_congr_fun (hSmeas c) fun r _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hμ0 : Tendsto μf atTop (𝓝 0) := by
    have h0 : (𝓝 (0 : ℝ)) = 𝓝 (∫ r : ℝ, (0 : ℝ)) := by simp
    rw [hμ_def, h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => (1 + |r|) ^ k * ‖Ξ r‖) ?_ ?_ hΞk ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
      exact hΞk.aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun r : ℝ => min 1 (|r| / c)).aestronglyMeasurable)
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
      refine Filter.Eventually.of_forall fun r => ?_
      have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
      have hmin0 : 0 ≤ min 1 (|r| / c) := le_min zero_le_one (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c)
          ≤ (1 + |r|) ^ k * ‖Ξ r‖ * 1 := by
            gcongr
            exact min_le_left _ _
        _ = (1 + |r|) ^ k * ‖Ξ r‖ := by ring
    · refine Filter.Eventually.of_forall fun r => ?_
      have h1 : Tendsto (fun c : ℝ => |r| / c) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have h2 : Tendsto (fun c : ℝ => min 1 (|r| / c)) atTop (𝓝 0) := by
        have h3 := Filter.Tendsto.min
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)) h1
        simpa using h3
      have h4 := h2.const_mul ((1 + |r|) ^ k * ‖Ξ r‖)
      simpa [mul_comm] using h4
  -- the constants of the final bound
  set K1 : ℝ := Cη * 2 ^ k * (T0 + Tk) +
    ∑ j ∈ Finset.range (k + 1), Cη * N j / (j.factorial : ℝ) with hK1_def
  set K2 : ℝ := Cη * (B * 2 ^ (k + 2)) * I2 / k.factorial with hK2_def
  -- the eventual bound
  have hbound : ∀ {c : ℝ}, 1 ≤ c →
      ‖∫ r : ℝ, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖ ≤
        K1 * τ c + K2 * μf c := by
    intro c hc
    have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
    -- measurability and integrability of the full integrand
    have hGm : StronglyMeasurable fun r : ℝ => ∫ w : ℝ, η w * θ ((w - r) / c) := by
      apply MeasureTheory.StronglyMeasurable.integral_prod_right
      apply StronglyMeasurable.mul
      · exact hηm.comp_measurable measurable_snd
      · exact (θ.continuous.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 - p.1) / c)).stronglyMeasurable
    have hmeasG : AEStronglyMeasurable
        (fun r : ℝ => Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))) volume :=
      hΞm.mul (hGm.const_mul _).aestronglyMeasurable
    have hΞG : Integrable
        (fun r : ℝ => Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))) volume := by
      refine Integrable.mono' (hΞk.const_mul (Cη * 2 ^ k * (T0 + c ^ k * Tk))) hmeasG
        (Filter.Eventually.of_forall fun r => ?_)
      rw [norm_mul]
      have hw1 : (1 : ℝ) ≤ (1 + |r|) ^ k :=
        one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg r))
      have h1 : (1 + |r|) ^ k * T0 + c ^ k * Tk ≤ (1 + |r|) ^ k * (T0 + c ^ k * Tk) := by
        rw [mul_add]
        refine add_le_add le_rfl ?_
        exact le_mul_of_one_le_left (by positivity) hw1
      calc ‖Ξ r‖ * ‖c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)‖
          ≤ ‖Ξ r‖ * (Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk)) :=
            mul_le_mul_of_nonneg_left (hGout hc r) (norm_nonneg _)
        _ ≤ ‖Ξ r‖ * (Cη * 2 ^ k * ((1 + |r|) ^ k * (T0 + c ^ k * Tk))) := by
            gcongr
        _ = Cη * 2 ^ k * (T0 + c ^ k * Tk) * ((1 + |r|) ^ k * ‖Ξ r‖) := by ring
    -- integrability of each Taylor-sum term
    have hSctermint : ∀ j ≤ k, Integrable (fun r : ℝ =>
        ((-r / c) ^ j / (j.factorial : ℝ)) •
          (Ξ r * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))) volume := by
      intro j hj
      have hmeas2 : AEStronglyMeasurable (fun r : ℝ =>
          ((-r / c) ^ j / (j.factorial : ℝ)) •
            (Ξ r * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))) volume := by
        refine (AEStronglyMeasurable.smul
          ((by fun_prop : Continuous fun r : ℝ =>
            (-r / c) ^ j / (j.factorial : ℝ)).aestronglyMeasurable)
          (hΞm.mul_const _)).congr (Filter.Eventually.of_forall fun r => rfl)
      refine Integrable.mono'
        (hΞk.const_mul (‖c⁻¹ * ∫ w : ℝ, η w * D j (w / c)‖ / (j.factorial : ℝ))) hmeas2
        (Filter.Eventually.of_forall fun r => ?_)
      have habsq : |-r / c| ≤ |r| := by
        rw [abs_div, abs_neg, abs_of_pos hc0]
        exact div_le_self (abs_nonneg r) hc
      have hq0 : |(-r / c) ^ j| ≤ (1 + |r|) ^ k := by
        rw [abs_pow]
        calc |(-r / c)| ^ j ≤ |r| ^ j := pow_le_pow_left₀ (abs_nonneg _) habsq j
          _ ≤ (1 + |r|) ^ k := le_trans
              (pow_le_pow_left₀ (abs_nonneg r) (le_add_of_nonneg_left zero_le_one) j)
              (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg r)) hj)
      rw [norm_smul, Real.norm_eq_abs, norm_mul, abs_div, Nat.abs_cast]
      calc |(-r / c) ^ j| / (j.factorial : ℝ) *
            (‖Ξ r‖ * ‖c⁻¹ * ∫ w : ℝ, η w * D j (w / c)‖)
          ≤ (1 + |r|) ^ k / (j.factorial : ℝ) *
              (‖Ξ r‖ * ‖c⁻¹ * ∫ w : ℝ, η w * D j (w / c)‖) := by
            gcongr
        _ = ‖c⁻¹ * ∫ w : ℝ, η w * D j (w / c)‖ / (j.factorial : ℝ) *
              ((1 + |r|) ^ k * ‖Ξ r‖) := by ring
    -- integrability of the full Taylor sum against `Ξ`
    have hScint : Integrable (fun r : ℝ => Ξ r * ∑ j ∈ Finset.range (k + 1),
        ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))) volume := by
      have heq : (fun r : ℝ => Ξ r * ∑ j ∈ Finset.range (k + 1),
          ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))
          = fun r : ℝ => ∑ j ∈ Finset.range (k + 1),
              ((-r / c) ^ j / (j.factorial : ℝ)) •
                (Ξ r * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))) := by
        funext r
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j hj => mul_smul_comm _ _ _
      rw [heq]
      exact integrable_finsetSum _ fun j hj =>
        hSctermint j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    -- integrability of the inner remainder against `Ξ`
    have hdiffint2 : Integrable (fun r : ℝ =>
        Ξ r * ((c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
          ∑ j ∈ Finset.range (k + 1), ((-r / c) ^ j / (j.factorial : ℝ)) •
            (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))) volume := by
      refine (hΞG.sub hScint).congr (Filter.Eventually.of_forall fun r => ?_)
      simp only [Pi.sub_apply]
      ring
    -- the integrable weighted remainder mass
    have hμint : Integrable
        (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c)) volume := by
      refine hΞk.mono' (hΞk.aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun r : ℝ => min 1 (|r| / c)).aestronglyMeasurable))
        (Filter.Eventually.of_forall fun r => ?_)
      have hmin0 : 0 ≤ min 1 (|r| / c) := le_min zero_le_one (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c)
          ≤ (1 + |r|) ^ k * ‖Ξ r‖ * 1 := by
            gcongr
            exact min_le_left _ _
        _ = (1 + |r|) ^ k * ‖Ξ r‖ := by ring
    -- split the line at `|r| = c`
    have hsplit := integral_add_compl (hSmeas c) hΞG
    -- decompose the inner region into Taylor sum and remainder
    have hinner_decomp : (∫ r in {r : ℝ | c < |r|}ᶜ,
        Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)))
        = (∫ r in {r : ℝ | c < |r|}ᶜ, Ξ r * ∑ j ∈ Finset.range (k + 1),
            ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))
          + ∫ r in {r : ℝ | c < |r|}ᶜ,
              Ξ r * ((c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
                ∑ j ∈ Finset.range (k + 1),
                  ((-r / c) ^ j / (j.factorial : ℝ)) •
                    (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))) := by
      rw [← integral_add hScint.integrableOn hdiffint2.integrableOn]
      refine setIntegral_congr_fun (hSmeas c).compl fun r _ => ?_
      try simp only []
      ring
    -- the outer piece
    have houter : ‖∫ r in {r : ℝ | c < |r|},
        Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖ ≤
        Cη * 2 ^ k * (T0 + Tk) * τ c := by
      calc ‖∫ r in {r : ℝ | c < |r|}, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖
          ≤ ∫ r in {r : ℝ | c < |r|},
              ‖Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ r in {r : ℝ | c < |r|},
              Cη * 2 ^ k * (T0 + Tk) * ((1 + |r|) ^ k * ‖Ξ r‖) := by
            refine setIntegral_mono_on hΞG.norm.integrableOn
              ((hΞk.const_mul _).integrableOn) (hSmeas c) fun r hr => ?_
            have hrc : c ≤ |r| := le_of_lt hr
            have hck : c ^ k ≤ (1 + |r|) ^ k := by
              calc c ^ k ≤ |r| ^ k := pow_le_pow_left₀ hc0.le hrc k
                _ ≤ (1 + |r|) ^ k :=
                  pow_le_pow_left₀ (abs_nonneg r) (le_add_of_nonneg_left zero_le_one) k
            rw [norm_mul]
            calc ‖Ξ r‖ * ‖c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)‖
                ≤ ‖Ξ r‖ * (Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + c ^ k * Tk)) :=
                  mul_le_mul_of_nonneg_left (hGout hc r) (norm_nonneg _)
              _ ≤ ‖Ξ r‖ * (Cη * 2 ^ k * ((1 + |r|) ^ k * T0 + (1 + |r|) ^ k * Tk)) := by
                  gcongr
              _ = Cη * 2 ^ k * (T0 + Tk) * ((1 + |r|) ^ k * ‖Ξ r‖) := by ring
        _ = Cη * 2 ^ k * (T0 + Tk) * τ c := by
            rw [hτ_def]
            try simp only []
            exact integral_const_mul _ _
    -- the inner remainder piece
    have hinnerρ : ‖∫ r in {r : ℝ | c < |r|}ᶜ,
        Ξ r * ((c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
          ∑ j ∈ Finset.range (k + 1), ((-r / c) ^ j / (j.factorial : ℝ)) •
            (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))‖ ≤ K2 * μf c := by
      have hK20 : 0 ≤ K2 := by
        rw [hK2_def]
        positivity
      calc ‖∫ r in {r : ℝ | c < |r|}ᶜ,
            Ξ r * ((c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
              ∑ j ∈ Finset.range (k + 1), ((-r / c) ^ j / (j.factorial : ℝ)) •
                (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))‖
          ≤ ∫ r in {r : ℝ | c < |r|}ᶜ,
              ‖Ξ r * ((c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
                ∑ j ∈ Finset.range (k + 1), ((-r / c) ^ j / (j.factorial : ℝ)) •
                  (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ r in {r : ℝ | c < |r|}ᶜ,
              K2 * ((1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c)) := by
            refine setIntegral_mono_on hdiffint2.norm.integrableOn
              ((hμint.const_mul K2).integrableOn) (hSmeas c).compl fun r hr => ?_
            have hrc : |r| ≤ c := not_lt.mp hr
            rw [norm_mul]
            calc ‖Ξ r‖ * ‖(c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)) -
                  ∑ j ∈ Finset.range (k + 1), ((-r / c) ^ j / (j.factorial : ℝ)) •
                    (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))‖
                ≤ ‖Ξ r‖ * (K2 * ((1 + |r|) ^ k * min 1 (|r| / c))) :=
                  mul_le_mul_of_nonneg_left (hρ hc r hrc) (norm_nonneg _)
              _ = K2 * ((1 + |r|) ^ k * ‖Ξ r‖ * min 1 (|r| / c)) := by ring
        _ ≤ K2 * μf c := by
            rw [hμ_def]
            try simp only []
            rw [integral_const_mul]
            refine mul_le_mul_of_nonneg_left ?_ hK20
            refine setIntegral_le_integral hμint (Filter.Eventually.of_forall fun r => ?_)
            exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
              (le_min zero_le_one (by positivity))
    -- the inner Taylor-sum piece
    have hinnerS : ‖∫ r in {r : ℝ | c < |r|}ᶜ, Ξ r * ∑ j ∈ Finset.range (k + 1),
        ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))‖ ≤
        (∑ j ∈ Finset.range (k + 1), Cη * N j / (j.factorial : ℝ)) * τ c := by
      have heq2 : (∫ r in {r : ℝ | c < |r|}ᶜ, Ξ r * ∑ j ∈ Finset.range (k + 1),
          ((-r / c) ^ j / (j.factorial : ℝ)) • (c⁻¹ * ∫ w : ℝ, η w * D j (w / c)))
          = ∑ j ∈ Finset.range (k + 1), ∫ r in {r : ℝ | c < |r|}ᶜ,
              ((-r / c) ^ j / (j.factorial : ℝ)) •
                (Ξ r * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))) := by
        rw [← integral_finsetSum _ (fun j hj =>
          (hSctermint j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).integrableOn)]
        refine setIntegral_congr_fun (hSmeas c).compl fun r _ => ?_
        try simp only []
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j hj => mul_smul_comm _ _ _
      rw [heq2, Finset.sum_mul]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      -- pull the constants out of the set integral
      have hpull1 : (∫ r in {r : ℝ | c < |r|}ᶜ,
          ((-r / c) ^ j / (j.factorial : ℝ)) •
            (Ξ r * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))))
          = ∫ r in {r : ℝ | c < |r|}ᶜ,
              ((-(c : ℂ))⁻¹ ^ j / (j.factorial : ℂ)) *
                (((r : ℂ) ^ j * Ξ r) * (c⁻¹ * ∫ w : ℝ, η w * D j (w / c))) := by
        refine setIntegral_congr_fun (hSmeas c).compl fun r _ => ?_
        try simp only []
        rw [Complex.real_smul]
        push_cast
        ring
      rw [hpull1, integral_const_mul, integral_mul_const]
      -- flip the truncated moment through the vanishing moment
      have hflip : (∫ r in {r : ℝ | c < |r|}ᶜ, (r : ℂ) ^ j * Ξ r)
          = -(∫ r in {r : ℝ | c < |r|}, (r : ℂ) ^ j * Ξ r) := by
        have h := integral_add_compl (hSmeas c) (hmomint j hjk)
        rw [hΞvm j hjk] at h
        rw [add_comm] at h
        exact add_eq_zero_iff_eq_neg.mp h
      -- norms
      rw [norm_mul, norm_mul, hflip, norm_neg]
      have hκ : ‖(-(c : ℂ))⁻¹ ^ j / (j.factorial : ℂ)‖ = c⁻¹ ^ j / (j.factorial : ℝ) := by
        rw [norm_div, norm_pow, norm_inv, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hc0, Complex.norm_natCast]
      rw [hκ]
      -- the moment estimate on the outer set
      have hmomabs : ‖∫ r in {r : ℝ | c < |r|}, (r : ℂ) ^ j * Ξ r‖ ≤
          ∫ r in {r : ℝ | c < |r|}, |r| ^ j * ‖Ξ r‖ := by
        refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
        refine setIntegral_congr_fun (hSmeas c) fun r _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      -- the scaled derivative integral estimate
      have hPj : ‖(c⁻¹ * ∫ w : ℝ, η w * D j (w / c) : ℂ)‖ ≤ Cη * (c ^ k * N j) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hc0]
        calc c⁻¹ * ‖∫ w : ℝ, η w * D j (w / c)‖
            ≤ c⁻¹ * (Cη * (c ^ (k + 1) * N j)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hIjnorm j (le_trans hjk (Nat.le_succ k)) hc
          _ = (c⁻¹ * c) * (Cη * (c ^ k * N j)) := by
              rw [pow_succ]
              ring
          _ = Cη * (c ^ k * N j) := by
              rw [inv_mul_cancel₀ hc0.ne', one_mul]
      -- the `c`-power bookkeeping
      have hcpow : c ^ k * c⁻¹ ^ j = c ^ (k - j) := by
        have hck : c ^ k = c ^ (k - j) * c ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hjk]
        rw [inv_pow, hck, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j hc0.ne'), mul_one]
      -- the truncated moment absorbs the `c`-powers into the tail
      have hmomtail : c ^ (k - j) * ∫ r in {r : ℝ | c < |r|}, |r| ^ j * ‖Ξ r‖ ≤ τ c := by
        have hjint : Integrable (fun r : ℝ => |r| ^ j * ‖Ξ r‖) volume := by
          refine hΞk.mono' ((by fun_prop : Continuous fun r : ℝ => |r| ^ j).aestronglyMeasurable.mul
            hΞm.norm) (Filter.Eventually.of_forall fun r => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have h1 : |r| ^ j ≤ (1 + |r|) ^ k := le_trans
            (pow_le_pow_left₀ (abs_nonneg r) (le_add_of_nonneg_left zero_le_one) j)
            (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg r)) hjk)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        rw [hτ_def]
        try simp only []
        rw [← integral_const_mul]
        refine setIntegral_mono_on ((hjint.const_mul _).integrableOn)
          hΞk.integrableOn (hSmeas c) fun r hr => ?_
        have hrc : c ≤ |r| := le_of_lt hr
        calc c ^ (k - j) * (|r| ^ j * ‖Ξ r‖) ≤ |r| ^ (k - j) * (|r| ^ j * ‖Ξ r‖) := by
              gcongr
          _ = |r| ^ k * ‖Ξ r‖ := by
              rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjk]
          _ ≤ (1 + |r|) ^ k * ‖Ξ r‖ := by
              have h1 : |r| ^ k ≤ (1 + |r|) ^ k :=
                pow_le_pow_left₀ (abs_nonneg r) (by linarith [abs_nonneg r]) k
              exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      -- assemble the term
      calc c⁻¹ ^ j / (j.factorial : ℝ) *
            (‖∫ r in {r : ℝ | c < |r|}, (r : ℂ) ^ j * Ξ r‖ *
              ‖(c⁻¹ * ∫ w : ℝ, η w * D j (w / c) : ℂ)‖)
          ≤ c⁻¹ ^ j / (j.factorial : ℝ) *
              ((∫ r in {r : ℝ | c < |r|}, |r| ^ j * ‖Ξ r‖) * (Cη * (c ^ k * N j))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul hmomabs hPj (norm_nonneg _) ?_
            refine integral_nonneg fun r => by positivity
        _ = (Cη * N j / (j.factorial : ℝ)) *
              (c ^ (k - j) * ∫ r in {r : ℝ | c < |r|}, |r| ^ j * ‖Ξ r‖) := by
            rw [← hcpow]
            ring
        _ ≤ (Cη * N j / (j.factorial : ℝ)) * τ c := by
            refine mul_le_mul_of_nonneg_left hmomtail ?_
            positivity
    -- assemble the eventual bound
    calc ‖∫ r : ℝ, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖
        = ‖(∫ r in {r : ℝ | c < |r|}, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c)))
            + ∫ r in {r : ℝ | c < |r|}ᶜ,
                Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖ := by rw [hsplit]
      _ ≤ ‖∫ r in {r : ℝ | c < |r|}, Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖
            + ‖∫ r in {r : ℝ | c < |r|}ᶜ,
                Ξ r * (c⁻¹ * ∫ w : ℝ, η w * θ ((w - r) / c))‖ := norm_add_le _ _
      _ ≤ Cη * 2 ^ k * (T0 + Tk) * τ c +
            ((∑ j ∈ Finset.range (k + 1), Cη * N j / (j.factorial : ℝ)) * τ c
              + K2 * μf c) := by
          refine add_le_add houter ?_
          rw [hinner_decomp]
          exact le_trans (norm_add_le _ _) (add_le_add hinnerS hinnerρ)
      _ = K1 * τ c + K2 * μf c := by
          rw [hK1_def]
          ring
  -- combine the limits
  have hcomb : Tendsto (fun c : ℝ => K1 * τ c + K2 * μf c) atTop (𝓝 0) := by
    have h := (hτ0.const_mul K1).add (hμ0.const_mul K2)
    simpa using h
  refine squeeze_zero_norm' ?_ hcomb
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
  exact hbound hc

/-- Weighted integrability of translates. -/
theorem integrable_weight_norm_comp_sub (k : ℕ) {Ξ : ℝ → E}
    (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume) (s : ℝ) :
    Integrable (fun z : ℝ => (1 + |z|) ^ k * ‖Ξ (z - s)‖) volume := by
  have h := hΞk.comp_sub_right s
  refine ((h.const_mul ((1 + |s|) ^ k)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_))
  · exact ((by fun_prop : Continuous fun z : ℝ => (1 + |z|) ^ k)).aestronglyMeasurable.mul
      ((hΞm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right volume s).quasiMeasurePreserving).norm)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (1 + |z|) ^ k ≤ (1 + |s|) ^ k * (1 + |z - s|) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have h2 := one_add_abs_add_le_mul_one_add_abs s (z - s)
      have h3 : s + (z - s) = z := by ring
      rw [h3] at h2
      exact h2
    calc (1 + |z|) ^ k * ‖Ξ (z - s)‖
        ≤ ((1 + |s|) ^ k * (1 + |z - s|) ^ k) * ‖Ξ (z - s)‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (1 + |s|) ^ k * ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by ring

/-- Weighted integrability of translation differences. -/
theorem integrable_weight_norm_sub_comp_sub (k : ℕ) {Ξ : ℝ → E}
    (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume) (s : ℝ) :
    Integrable (fun z : ℝ => (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖) volume := by
  refine ((integrable_weight_norm_comp_sub k hΞm hΞk s).add hΞk).mono' ?_
    (Filter.Eventually.of_forall fun z => ?_)
  · exact ((by fun_prop : Continuous fun z : ℝ => (1 + |z|) ^ k)).aestronglyMeasurable.mul
      (((hΞm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right volume s).quasiMeasurePreserving).sub hΞm).norm)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖
        ≤ (1 + |z|) ^ k * (‖Ξ (z - s)‖ + ‖Ξ z‖) := by
          gcongr
          exact norm_sub_le _ _
      _ = (1 + |z|) ^ k * ‖Ξ (z - s)‖ + (1 + |z|) ^ k * ‖Ξ z‖ := by ring

/-- The polynomially weighted translation modulus is continuous. -/
theorem continuous_integral_weight_norm_sub (k : ℕ) [NormedSpace ℝ E] {Ξ : ℝ → E}
    (hΞm : AEStronglyMeasurable Ξ volume)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume) :
    Continuous fun s : ℝ => ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖ := by
  -- the two-point modulus estimate
  have hkey : ∀ s s₀ : ℝ,
      |(∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖) -
        ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s₀) - Ξ z‖| ≤
        (1 + |s₀|) ^ k * ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - (s - s₀)) - Ξ z‖ := by
    intro s s₀
    rw [← integral_sub (integrable_weight_norm_sub_comp_sub k hΞm hΞk s)
      (integrable_weight_norm_sub_comp_sub k hΞm hΞk s₀)]
    have hmid : Integrable (fun z : ℝ => (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ (z - s₀)‖)
        volume := by
      refine ((integrable_weight_norm_comp_sub k hΞm hΞk s).add
        (integrable_weight_norm_comp_sub k hΞm hΞk s₀)).mono' ?_
        (Filter.Eventually.of_forall fun z => ?_)
      · refine ((by fun_prop : Continuous fun z : ℝ =>
          (1 + |z|) ^ k)).aestronglyMeasurable.mul ?_
        refine AEStronglyMeasurable.norm ?_
        exact (hΞm.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume s).quasiMeasurePreserving).sub
          (hΞm.comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume s₀).quasiMeasurePreserving)
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ (z - s₀)‖
            ≤ (1 + |z|) ^ k * (‖Ξ (z - s)‖ + ‖Ξ (z - s₀)‖) := by
              gcongr
              exact norm_sub_le _ _
          _ = (1 + |z|) ^ k * ‖Ξ (z - s)‖ + (1 + |z|) ^ k * ‖Ξ (z - s₀)‖ := by ring
    calc |∫ z : ℝ, ((1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖ -
          (1 + |z|) ^ k * ‖Ξ (z - s₀) - Ξ z‖)|
        ≤ ∫ z : ℝ, |(1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖ -
            (1 + |z|) ^ k * ‖Ξ (z - s₀) - Ξ z‖| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ (z - s₀)‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            hmid (Filter.Eventually.of_forall fun z => ?_)
          simp only []
          rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + |z|) ^ k)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : ‖Ξ (z - s) - Ξ z‖ - ‖Ξ (z - s₀) - Ξ z‖ ≤ ‖Ξ (z - s) - Ξ (z - s₀)‖ := by
            have h := norm_sub_norm_le (Ξ (z - s) - Ξ z) (Ξ (z - s₀) - Ξ z)
            have h2 : Ξ (z - s) - Ξ z - (Ξ (z - s₀) - Ξ z) = Ξ (z - s) - Ξ (z - s₀) := by
              abel
            rw [h2] at h
            exact h
          have h1' : ‖Ξ (z - s₀) - Ξ z‖ - ‖Ξ (z - s) - Ξ z‖ ≤ ‖Ξ (z - s) - Ξ (z - s₀)‖ := by
            rw [norm_sub_rev (Ξ (z - s)) (Ξ (z - s₀))]
            have h := norm_sub_norm_le (Ξ (z - s₀) - Ξ z) (Ξ (z - s) - Ξ z)
            have h2 : Ξ (z - s₀) - Ξ z - (Ξ (z - s) - Ξ z) = Ξ (z - s₀) - Ξ (z - s) := by
              abel
            rw [h2] at h
            exact h
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = ∫ y : ℝ, (1 + |y + s₀|) ^ k * ‖Ξ (y - (s - s₀)) - Ξ y‖ := by
          rw [← integral_add_right_eq_self
            (fun z : ℝ => (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ (z - s₀)‖) s₀]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only []
          have h1 : y + s₀ - s = y - (s - s₀) := by ring
          have h2 : y + s₀ - s₀ = y := by ring
          rw [h1, h2]
      _ ≤ (1 + |s₀|) ^ k * ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - (s - s₀)) - Ξ z‖ := by
          rw [← integral_const_mul]
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
            ((integrable_weight_norm_sub_comp_sub k hΞm hΞk (s - s₀)).const_mul _)
            (Filter.Eventually.of_forall fun y => ?_)
          have h1 : (1 + |y + s₀|) ^ k ≤ (1 + |s₀|) ^ k * (1 + |y|) ^ k := by
            rw [← mul_pow]
            refine pow_le_pow_left₀ (by positivity) ?_ k
            have h2 := one_add_abs_add_le_mul_one_add_abs s₀ y
            have h3 : s₀ + y = y + s₀ := by ring
            rw [h3] at h2
            exact h2
          calc (1 + |y + s₀|) ^ k * ‖Ξ (y - (s - s₀)) - Ξ y‖
              ≤ ((1 + |s₀|) ^ k * (1 + |y|) ^ k) * ‖Ξ (y - (s - s₀)) - Ξ y‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ = (1 + |s₀|) ^ k * ((1 + |y|) ^ k * ‖Ξ (y - (s - s₀)) - Ξ y‖) := by ring
  -- continuity from the modulus estimate and continuity at the origin
  rw [continuous_iff_continuousAt]
  intro s₀
  have h0 : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
      (continuous_sub_right s₀).tendsto s₀
    simpa using h
  have hω0 := (tendsto_integral_weight_norm_sub_comp_sub_right k hΞm hΞk).comp h0
  have hsq : Tendsto (fun s : ℝ => (∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖) -
      ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s₀) - Ξ z‖) (𝓝 s₀) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun s : ℝ => (1 + |s₀|) ^ k *
        ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - (s - s₀)) - Ξ z‖) (fun s => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hkey s s₀
    · have h := hω0.const_mul ((1 + |s₀|) ^ k)
      simpa [Function.comp] using h
  have hfin := hsq.add (tendsto_const_nhds
    (x := ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s₀) - Ξ z‖))
  unfold ContinuousAt
  simpa using hfin

set_option maxHeartbeats 800000 in
-- The proof is a single long assembly of Tonelli and dominated-convergence estimates.
/-- **Scaled approximate identity in polynomially weighted `L¹`**: for a kernel `K` with unit
integral and finite `k`-th moment, the scaled smoothings `∫ K(u) Ξ(z - u/c) du` converge to
`Ξ` in the polynomially weighted `L¹` norm as the scale `c → ∞`. -/
theorem tendsto_integral_weight_norm_smoothing_sub (k : ℕ) {Ξ K : ℝ → ℂ}
    (hΞm : StronglyMeasurable Ξ)
    (hΞk : Integrable (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) volume)
    (hKm : AEStronglyMeasurable K volume)
    (hKk : Integrable (fun u : ℝ => (1 + |u|) ^ k * ‖K u‖) volume)
    (hK1 : (∫ u : ℝ, K u) = 1) :
    Tendsto (fun c : ℝ => ∫ z : ℝ, (1 + |z|) ^ k *
        ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖) atTop (𝓝 0) := by
  have hone_le : ∀ x : ℝ, (1 : ℝ) ≤ (1 + |x|) ^ k := fun x =>
    one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg x))
  have hKint : Integrable K volume := by
    refine hKk.mono' hKm (Filter.Eventually.of_forall fun u => ?_)
    have h := hone_le u
    nlinarith [norm_nonneg (K u)]
  set Mk : ℝ := ∫ r : ℝ, (1 + |r|) ^ k * ‖Ξ r‖ with hMk_def
  have hMk0 : 0 ≤ Mk := integral_nonneg fun r => by positivity
  set ω : ℝ → ℝ := fun s => ∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖ with hω_def
  have hω0 : ∀ s : ℝ, 0 ≤ ω s := fun s => integral_nonneg fun z => by positivity
  have hωc : Continuous ω :=
    continuous_integral_weight_norm_sub k hΞm.aestronglyMeasurable hΞk
  have hωt : Tendsto ω (𝓝 0) (𝓝 0) :=
    tendsto_integral_weight_norm_sub_comp_sub_right k hΞm.aestronglyMeasurable hΞk
  -- global growth bound of the modulus
  have hωbound : ∀ s : ℝ, ω s ≤ 2 * ((1 + |s|) ^ k * Mk) := by
    intro s
    have h1 : (∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s)‖) ≤ (1 + |s|) ^ k * Mk := by
      calc (∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s)‖)
          ≤ ∫ z : ℝ, (1 + |s|) ^ k * ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun z => by positivity)
              ((hΞk.comp_sub_right s).const_mul _)
              (Filter.Eventually.of_forall fun z => ?_)
            have h1 : (1 + |z|) ^ k ≤ (1 + |s|) ^ k * (1 + |z - s|) ^ k := by
              rw [← mul_pow]
              refine pow_le_pow_left₀ (by positivity) ?_ k
              have h2 := one_add_abs_add_le_mul_one_add_abs s (z - s)
              have h3 : s + (z - s) = z := by ring
              rw [h3] at h2
              exact h2
            calc (1 + |z|) ^ k * ‖Ξ (z - s)‖
                ≤ ((1 + |s|) ^ k * (1 + |z - s|) ^ k) * ‖Ξ (z - s)‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
              _ = (1 + |s|) ^ k * ((1 + |z - s|) ^ k * ‖Ξ (z - s)‖) := by ring
        _ = (1 + |s|) ^ k * ∫ z : ℝ, (1 + |z - s|) ^ k * ‖Ξ (z - s)‖ :=
            integral_const_mul _ _
        _ = (1 + |s|) ^ k * Mk := by
            rw [hMk_def]
            congr 1
            exact integral_sub_right_eq_self (fun r : ℝ => (1 + |r|) ^ k * ‖Ξ r‖) s
    calc ω s ≤ (∫ z : ℝ, (1 + |z|) ^ k * ‖Ξ (z - s)‖) + Mk := by
          rw [hω_def]
          simp only []
          rw [hMk_def]
          rw [← integral_add (integrable_weight_norm_comp_sub k hΞm.aestronglyMeasurable
            hΞk s) hΞk]
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => by positivity)
            ((integrable_weight_norm_comp_sub k hΞm.aestronglyMeasurable hΞk s).add hΞk)
            (Filter.Eventually.of_forall fun z => ?_)
          calc (1 + |z|) ^ k * ‖Ξ (z - s) - Ξ z‖
              ≤ (1 + |z|) ^ k * (‖Ξ (z - s)‖ + ‖Ξ z‖) := by
                gcongr
                exact norm_sub_le _ _
            _ = (1 + |z|) ^ k * ‖Ξ (z - s)‖ + (1 + |z|) ^ k * ‖Ξ z‖ := by ring
      _ ≤ (1 + |s|) ^ k * Mk + Mk := by
          exact add_le_add h1 le_rfl
      _ ≤ 2 * ((1 + |s|) ^ k * Mk) := by
          have h2 : Mk ≤ (1 + |s|) ^ k * Mk := le_mul_of_one_le_left hMk0 (hone_le s)
          linarith
  -- integrability of the dominating integrand at each fixed scale
  have hKωint : ∀ c : ℝ, Integrable (fun u : ℝ => ‖K u‖ * ω (u / c)) volume := by
    intro c
    refine (hKk.const_mul (2 * Mk * (1 + |c⁻¹|) ^ k)).mono' ?_
      (Filter.Eventually.of_forall fun u => ?_)
    · exact hKm.norm.mul
        ((hωc.comp (by fun_prop : Continuous fun u : ℝ => u / c)).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hω0 _))]
      have h1 : (1 + |u / c|) ^ k ≤ (1 + |u|) ^ k * (1 + |c⁻¹|) ^ k := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        rw [div_eq_mul_inv, abs_mul]
        nlinarith [abs_nonneg u, abs_nonneg (c⁻¹)]
      calc ‖K u‖ * ω (u / c) ≤ ‖K u‖ * (2 * ((1 + |u / c|) ^ k * Mk)) :=
            mul_le_mul_of_nonneg_left (hωbound _) (norm_nonneg _)
        _ ≤ ‖K u‖ * (2 * ((1 + |u|) ^ k * (1 + |c⁻¹|) ^ k * Mk)) := by
            gcongr
        _ = 2 * Mk * (1 + |c⁻¹|) ^ k * ((1 + |u|) ^ k * ‖K u‖) := by ring
  -- the dominating quantity tends to zero
  have hE : Tendsto (fun c : ℝ => ∫ u : ℝ, ‖K u‖ * ω (u / c)) atTop (𝓝 0) := by
    have h0 : (𝓝 (0 : ℝ)) = 𝓝 (∫ u : ℝ, (0 : ℝ)) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => 2 * Mk * ((1 + |u|) ^ k * ‖K u‖)) ?_ ?_ (hKk.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun c => hKm.norm.mul
        ((hωc.comp (by fun_prop : Continuous fun u : ℝ => u / c)).aestronglyMeasurable)
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
      refine Filter.Eventually.of_forall fun u => ?_
      have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hω0 _))]
      have hdc : |u / c| ≤ |u| := by
        rw [abs_div, abs_of_pos hc0]
        exact div_le_self (abs_nonneg u) hc
      calc ‖K u‖ * ω (u / c) ≤ ‖K u‖ * (2 * ((1 + |u / c|) ^ k * Mk)) :=
            mul_le_mul_of_nonneg_left (hωbound _) (norm_nonneg _)
        _ ≤ ‖K u‖ * (2 * ((1 + |u|) ^ k * Mk)) := by
            gcongr
        _ = 2 * Mk * ((1 + |u|) ^ k * ‖K u‖) := by ring
    · refine Filter.Eventually.of_forall fun u => ?_
      have h1 : Tendsto (fun c : ℝ => u / c) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have h2 : Tendsto (fun c : ℝ => ω (u / c)) atTop (𝓝 0) := hωt.comp h1
      have h3 := h2.const_mul ‖K u‖
      simpa using h3
  -- the comparison with the dominating quantity at each scale `c ≥ 1`
  have hDE : ∀ {c : ℝ}, 1 ≤ c →
      (∫ z : ℝ, (1 + |z|) ^ k * ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖) ≤
        ∫ u : ℝ, ‖K u‖ * ω (u / c) := by
    intro c hc
    -- the enlarged product kernel
    set P : ℝ × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((1 + |p.1|) ^ k * (‖K p.2‖ * ‖Ξ (p.1 - p.2 / c) - Ξ p.1‖)) with hP_def
    have hΞshift : StronglyMeasurable fun p : ℝ × ℝ => Ξ (p.1 - p.2 / c) :=
      hΞm.comp_measurable (by fun_prop)
    have hKsnd : AEStronglyMeasurable (fun p : ℝ × ℝ => K p.2)
        ((volume : Measure ℝ).prod volume) :=
      hKm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hPm : AEMeasurable P ((volume : Measure ℝ).prod volume) := by
      refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      refine AEMeasurable.mul ?_ ?_
      · exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          (1 + |p.1|) ^ k)).measurable.aemeasurable
      · exact (hKsnd.norm.mul
          ((hΞshift.aestronglyMeasurable.sub
            ((hΞm.comp_measurable measurable_fst).aestronglyMeasurable)).norm)).aemeasurable
    -- the inner `z`-integral of the kernel evaluates through the modulus
    have hinner : ∀ u : ℝ, (∫⁻ z : ℝ, P (z, u)) = ENNReal.ofReal (‖K u‖ * ω (u / c)) := by
      intro u
      have hint : Integrable (fun z : ℝ => (1 + |z|) ^ k * ‖Ξ (z - u / c) - Ξ z‖) volume :=
        integrable_weight_norm_sub_comp_sub k hΞm.aestronglyMeasurable hΞk (u / c)
      calc (∫⁻ z : ℝ, P (z, u))
          = ∫⁻ z : ℝ, ENNReal.ofReal ‖K u‖ *
              ENNReal.ofReal ((1 + |z|) ^ k * ‖Ξ (z - u / c) - Ξ z‖) := by
            refine lintegral_congr fun z => ?_
            rw [hP_def]
            simp only []
            rw [← ENNReal.ofReal_mul (norm_nonneg _)]
            congr 1
            ring
        _ = ENNReal.ofReal ‖K u‖ *
              ∫⁻ z : ℝ, ENNReal.ofReal ((1 + |z|) ^ k * ‖Ξ (z - u / c) - Ξ z‖) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal ‖K u‖ * ENNReal.ofReal (ω (u / c)) := by
            rw [← ofReal_integral_eq_lintegral_ofReal hint
              (Filter.Eventually.of_forall fun z => by positivity)]
        _ = ENNReal.ofReal (‖K u‖ * ω (u / c)) :=
            (ENNReal.ofReal_mul (norm_nonneg _)).symm
    -- Tonelli
    have hswap : (∫⁻ z : ℝ, ∫⁻ u : ℝ, P (z, u)) = ∫⁻ u : ℝ, ∫⁻ z : ℝ, P (z, u) :=
      lintegral_lintegral_swap hPm
    have hRHSfin : (∫⁻ u : ℝ, ∫⁻ z : ℝ, P (z, u)) ≠ ∞ := by
      rw [lintegral_congr hinner,
        ← ofReal_integral_eq_lintegral_ofReal (hKωint c)
          (Filter.Eventually.of_forall fun u => mul_nonneg (norm_nonneg _) (hω0 _))]
      exact ENNReal.ofReal_ne_top
    -- almost every section is integrable
    have hsec : ∀ᵐ z : ℝ, Integrable (fun u : ℝ => K u * Ξ (z - u / c)) volume := by
      have hzmeas : AEMeasurable (fun z : ℝ => ∫⁻ u : ℝ, P (z, u)) volume :=
        hPm.lintegral_prod_right'
      have hzfin : ∀ᵐ z : ℝ, (∫⁻ u : ℝ, P (z, u)) < ∞ := by
        refine ae_lt_top' hzmeas ?_
        rw [hswap]
        exact hRHSfin
      filter_upwards [hzfin] with z hz
      have hd : Integrable (fun u : ℝ => K u * (Ξ (z - u / c) - Ξ z)) volume := by
        constructor
        · exact hKm.mul ((hΞm.comp_measurable
            (by fun_prop : Measurable fun u : ℝ => z - u / c)).aestronglyMeasurable.sub
            aestronglyMeasurable_const)
        · rw [hasFiniteIntegral_iff_enorm]
          refine lt_of_le_of_lt (lintegral_mono fun u => ?_) hz
          rw [hP_def]
          simp only []
          rw [enorm_mul]
          calc ‖K u‖ₑ * ‖Ξ (z - u / c) - Ξ z‖ₑ
              = ENNReal.ofReal (‖K u‖ * ‖Ξ (z - u / c) - Ξ z‖) := by
                rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
                  ofReal_norm]
            _ ≤ ENNReal.ofReal ((1 + |z|) ^ k * (‖K u‖ * ‖Ξ (z - u / c) - Ξ z‖)) := by
                refine ENNReal.ofReal_le_ofReal ?_
                exact le_mul_of_one_le_left (by positivity) (hone_le z)
      have hconst : Integrable (fun u : ℝ => K u * Ξ z) volume := hKint.mul_const _
      refine (hd.add hconst).congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]
      ring
    -- almost-everywhere pointwise comparison after integrating in `u`
    have hptae : ∀ᵐ z : ℝ, ENNReal.ofReal ((1 + |z|) ^ k *
        ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖) ≤ ∫⁻ u : ℝ, P (z, u) := by
      filter_upwards [hsec] with z hz
      have hconst : Integrable (fun u : ℝ => K u * Ξ z) volume := hKint.mul_const _
      have heq : (∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z
          = ∫ u : ℝ, K u * (Ξ (z - u / c) - Ξ z) := by
        have h2 : (∫ u : ℝ, K u * (Ξ (z - u / c) - Ξ z))
            = (∫ u : ℝ, K u * Ξ (z - u / c)) - ∫ u : ℝ, K u * Ξ z := by
          rw [← integral_sub hz hconst]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only []
          ring
        rw [h2, integral_mul_const, hK1, one_mul]
      rw [heq]
      calc ENNReal.ofReal ((1 + |z|) ^ k * ‖∫ u : ℝ, K u * (Ξ (z - u / c) - Ξ z)‖)
          = ENNReal.ofReal ((1 + |z|) ^ k) *
              ‖∫ u : ℝ, K u * (Ξ (z - u / c) - Ξ z)‖ₑ := by
            rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
        _ ≤ ENNReal.ofReal ((1 + |z|) ^ k) *
              ∫⁻ u : ℝ, ‖K u * (Ξ (z - u / c) - Ξ z)‖ₑ := by
            gcongr
            exact enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ u : ℝ, P (z, u) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun u => ?_
            rw [hP_def]
            simp only []
            rw [enorm_mul, ← ofReal_norm (K u),
              ← ofReal_norm (Ξ (z - u / c) - Ξ z),
              ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    -- assemble
    have hDmeas : AEStronglyMeasurable
        (fun z : ℝ => (1 + |z|) ^ k * ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖) volume := by
      have hGz : AEStronglyMeasurable (fun z : ℝ => ∫ u : ℝ, K u * Ξ (z - u / c)) volume := by
        refine AEStronglyMeasurable.integral_prod_right' (f := fun p : ℝ × ℝ =>
          K p.2 * Ξ (p.1 - p.2 / c)) ?_
        exact hKsnd.mul hΞshift.aestronglyMeasurable
      exact ((by fun_prop : Continuous fun z : ℝ =>
        (1 + |z|) ^ k)).aestronglyMeasurable.mul ((hGz.sub hΞm.aestronglyMeasurable).norm)
    calc (∫ z : ℝ, (1 + |z|) ^ k * ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖)
        = (∫⁻ z : ℝ, ENNReal.ofReal ((1 + |z|) ^ k *
            ‖(∫ u : ℝ, K u * Ξ (z - u / c)) - Ξ z‖)).toReal := by
          rw [integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun z => by positivity) hDmeas]
      _ ≤ (∫⁻ u : ℝ, ∫⁻ z : ℝ, P (z, u)).toReal := by
          refine ENNReal.toReal_mono hRHSfin ?_
          rw [← hswap]
          exact lintegral_mono_ae hptae
      _ = (∫⁻ u : ℝ, ENNReal.ofReal (‖K u‖ * ω (u / c))).toReal := by
          rw [lintegral_congr hinner]
      _ = ∫ u : ℝ, ‖K u‖ * ω (u / c) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hKωint c)
            (Filter.Eventually.of_forall fun u => mul_nonneg (norm_nonneg _) (hω0 _)),
            ENNReal.toReal_ofReal (integral_nonneg fun u =>
              mul_nonneg (norm_nonneg _) (hω0 _))]
  -- squeeze
  refine squeeze_zero_norm' ?_ hE
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => by positivity)]
  exact hDE hc

end MeasureTheory
