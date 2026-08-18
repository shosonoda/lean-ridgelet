/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusInverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The invariant measure of hyperbolic space is Möbius invariant

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

The measure `dμ(x) = (2/(1-‖x‖²))^m dx` on the unit ball is the invariant measure of `ℍ^m`, and
this file proves the invariance: the isometries `φ_a` of the ball preserve it.

The point of the proof is that *the derivative of `φ_a` is never computed*. Differentiating a
rational map of a vector and then evaluating a determinant would be a long calculation; instead the
conformal distortion identity of
`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.Mobius` already contains the answer. Since

`‖φ_a(x) - φ_a(y)‖² = λ(x)λ(y)‖x - y‖²`,   `λ(x) = (1-‖a‖²)/[x,a]²`,

the slope of `φ_a` along a line through `x` has squared norm `λ(x)λ(x+tv)‖v‖²` for every small
`t ≠ 0`, and letting `t → 0` gives `‖Dφ_a(x)v‖ = λ(x)‖v‖` — whatever the derivative is. By
polarization it then scales inner products by `λ(x)²`, so it is *conformal*, so it is `λ(x)` times a
linear isometry, so `|det| = λ(x)^m`. Only differentiability is taken from calculus; the value of
the derivative never appears.

With the Jacobian in hand the invariance is the change of variables of
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, whose three hypotheses are exactly
what the preceding files supply: differentiability here, injectivity and the image from
`Hyperbolic.MobiusInverse`. The density then cancels the Jacobian pointwise,

`λ(x)^m · (2/(1-‖φ_a(x)‖²))^m = (2/(1-‖x‖²))^m`,

because `1 - ‖φ_a(x)‖² = (1-‖a‖²)(1-‖x‖²)/[x,a]²` — the same identity that made `φ_a` preserve the
ball in the first place. So the invariance of the measure and the preservation of the ball are two
readings of one computation.

## Main definitions

* `HyperbolicSpace.mobiusFactor`: the conformal factor `λ(x) = (1-‖a‖²)/[x,a]²`.

## Main results

* `HyperbolicSpace.differentiableAt_mobius`: `φ_a` is differentiable on the closed ball.
* `HyperbolicSpace.norm_fderiv_mobius_apply`: `‖Dφ_a(x)v‖ = λ(x)‖v‖`, from a slope limit.
* `HyperbolicSpace.isConformalMap_fderiv_mobius`: the derivative is a conformal linear map.
* `HyperbolicSpace.abs_det_fderiv_mobius`: `|det Dφ_a(x)| = λ(x)^m`.
* `HyperbolicSpace.lintegral_invariantMeasure_comp_mobius`: **the invariance**,
  `∫⁻ g(φ_a x) dμ = ∫⁻ g dμ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HyperbolicSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Differentiability -/

theorem differentiable_mobiusBracketSq (a : E) :
    Differentiable ℝ (fun x : E => mobiusBracketSq x a) := by
  have heq : (fun x : E => (inner ℝ x a : ℝ)) = fun x : E => (inner ℝ a x : ℝ) := by
    funext x
    exact real_inner_comm a x
  have hinner : Differentiable ℝ (fun x : E => (inner ℝ x a : ℝ)) := by
    rw [heq]
    exact (innerSL ℝ a).differentiable
  have hnsq : Differentiable ℝ (fun x : E => ‖x‖ ^ 2) := by
    have h : ContDiff ℝ 1 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact h.differentiable one_ne_zero
  unfold mobiusBracketSq
  exact ((differentiable_const (1 : ℝ)).sub
    ((differentiable_const (2 : ℝ)).mul hinner)).add (hnsq.mul (differentiable_const _))

theorem differentiable_mobiusNum (a : E) : Differentiable ℝ (mobiusNum a) := by
  have hsub : Differentiable ℝ (fun x : E => x - a) :=
    differentiable_id.sub (differentiable_const a)
  have hnsq : Differentiable ℝ (fun x : E => ‖x - a‖ ^ 2) := by
    have h : ContDiff ℝ 1 (fun y : E => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
    exact (h.differentiable one_ne_zero).comp hsub
  unfold mobiusNum
  exact ((differentiable_const _).smul hsub).sub (hnsq.smul (differentiable_const a))

theorem differentiableAt_mobius {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) :
    DifferentiableAt ℝ (mobius a) x := by
  have hB : mobiusBracketSq x a ≠ 0 := mobiusBracketSq_ne_zero hx ha
  unfold mobius
  exact (((differentiable_mobiusBracketSq a).differentiableAt).inv hB).smul
    ((differentiable_mobiusNum a).differentiableAt)

/-! ## The conformal factor -/

/-- The conformal factor of the Möbius transformation, `λ(x) = (1-‖a‖²)/[x,a]²`: the factor by
which `φ_a` scales lengths at `x`. -/
def mobiusFactor (a x : E) : ℝ := (1 - ‖a‖ ^ 2) / mobiusBracketSq x a

theorem mobiusFactor_pos {x a : E} (hx : ‖x‖ ≤ 1) (ha : ‖a‖ < 1) : 0 < mobiusFactor a x :=
  div_pos (one_sub_norm_sq_pos ha) (mobiusBracketSq_pos hx ha)

/-- The conformal distortion identity written with the factor: the squared distance between images
is `λ(x)λ(y)` times the squared distance between the points. -/
theorem norm_sq_mobius_sub_eq_mul {x y a : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (ha : ‖a‖ < 1) :
    ‖mobius a x - mobius a y‖ ^ 2 = mobiusFactor a x * mobiusFactor a y * ‖x - y‖ ^ 2 := by
  have hBx : mobiusBracketSq x a ≠ 0 := mobiusBracketSq_ne_zero hx ha
  have hBy : mobiusBracketSq y a ≠ 0 := mobiusBracketSq_ne_zero hy ha
  rw [norm_sq_mobius_sub hx hy ha, mobiusFactor, mobiusFactor]
  field_simp

/-! ## The derivative scales norms -/

/-- **`‖Dφ_a(x)v‖ = λ(x)‖v‖`.** The derivative is not computed: the slope of `φ_a` along the line
through `x` in direction `v` has squared norm `λ(x)λ(x+tv)‖v‖²` for every small `t ≠ 0`, by the
conformal distortion identity, and both sides converge as `t → 0`. -/
theorem norm_fderiv_mobius_apply {x a : E} (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) (v : E) :
    ‖fderiv ℝ (mobius a) x v‖ = mobiusFactor a x * ‖v‖ := by
  have hx' : ‖x‖ ≤ 1 := le_of_lt hx
  have hBne : mobiusBracketSq x a ≠ 0 := mobiusBracketSq_ne_zero hx' ha
  have hdiff : HasFDerivAt (mobius a) (fderiv ℝ (mobius a) x) x :=
    (differentiableAt_mobius hx' ha).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using h.const_add x
  have hcurve : HasDerivAt (fun t : ℝ => mobius a (x + t • v))
      (fderiv ℝ (mobius a) x v) 0 := by
    have h : HasDerivAt (mobius a ∘ fun t : ℝ => x + t • v) (fderiv ℝ (mobius a) x v) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (hl := hdiff) (hf := hline) (hy := by simp)
    simpa [Function.comp_def] using h
  have hslope := hasDerivAt_iff_tendsto_slope.1 hcurve
  have hsq : Tendsto (fun t : ℝ => ‖slope (fun s : ℝ => mobius a (x + s • v)) 0 t‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖fderiv ℝ (mobius a) x v‖ ^ 2)) := hslope.norm.pow 2
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖x + t • v‖ ≤ 1 := by
    have hcont : ContinuousAt (fun t : ℝ => ‖x + t • v‖) 0 := by fun_prop
    have h := hcont.eventually_lt continuousAt_const (by simpa using hx)
    exact h.mono fun t ht => le_of_lt ht
  have hEq : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ‖slope (fun s : ℝ => mobius a (x + s • v)) 0 t‖ ^ 2
        = mobiusFactor a x * mobiusFactor a (x + t • v) * ‖v‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with t ht hle
    have ht0 : t ≠ 0 := by simpa using ht
    have hslope_eq : slope (fun s : ℝ => mobius a (x + s • v)) 0 t
        = t⁻¹ • (mobius a (x + t • v) - mobius a x) := by
      simp [slope, vsub_eq_sub]
    have hv : ‖x + t • v - x‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hslope_eq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      norm_sq_mobius_sub_eq_mul hle hx' ha, hv]
    field_simp
  have hfacCont : Tendsto (fun t : ℝ => mobiusFactor a x * mobiusFactor a (x + t • v) * ‖v‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (mobiusFactor a x * mobiusFactor a x * ‖v‖ ^ 2)) := by
    have hB : ContinuousAt (fun t : ℝ => mobiusBracketSq (x + t • v) a) 0 := by
      unfold mobiusBracketSq; fun_prop
    have hfac : ContinuousAt (fun t : ℝ => mobiusFactor a (x + t • v)) 0 := by
      unfold mobiusFactor
      exact continuousAt_const.div hB (by simpa using hBne)
    have h0 : ContinuousAt
        (fun t : ℝ => mobiusFactor a x * mobiusFactor a (x + t • v) * ‖v‖ ^ 2) 0 :=
      (continuousAt_const.mul hfac).mul continuousAt_const
    have h1 := h0.continuousWithinAt (s := {(0 : ℝ)}ᶜ)
    simpa [ContinuousWithinAt] using h1
  have hlim : ‖fderiv ℝ (mobius a) x v‖ ^ 2 = (mobiusFactor a x * ‖v‖) ^ 2 := by
    have := tendsto_nhds_unique (hsq.congr' hEq) hfacCont
    rw [this]; ring
  have hnn : 0 ≤ mobiusFactor a x * ‖v‖ := by
    have := mobiusFactor_pos hx' ha
    positivity
  nlinarith [norm_nonneg (fderiv ℝ (mobius a) x v), hnn, hlim]

/-! ## Conformality and the Jacobian -/

/-- The derivative of `φ_a` is a conformal linear map: it scales inner products by `λ(x)²`, which
follows from the norms by polarization. -/
theorem isConformalMap_fderiv_mobius {x a : E} (hx : ‖x‖ < 1) (ha : ‖a‖ < 1) :
    IsConformalMap (fderiv ℝ (mobius a) x) := by
  have hfac : 0 < mobiusFactor a x := mobiusFactor_pos (le_of_lt hx) ha
  refine (isConformalMap_iff _).2 ⟨mobiusFactor a x ^ 2, by positivity, fun u w => ?_⟩
  have hnorm : ∀ z : E, ‖fderiv ℝ (mobius a) x z‖ ^ 2 = mobiusFactor a x ^ 2 * ‖z‖ ^ 2 := by
    intro z
    rw [norm_fderiv_mobius_apply hx ha z]
    ring
  have hadd : fderiv ℝ (mobius a) x u + fderiv ℝ (mobius a) x w
      = fderiv ℝ (mobius a) x (u + w) := (map_add _ _ _).symm
  have hpolar : ∀ p q : E, (inner ℝ p q : ℝ) = (‖p + q‖ ^ 2 - ‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 := by
    intro p q
    rw [norm_add_sq_real]
    ring
  rw [hpolar (fderiv ℝ (mobius a) x u) (fderiv ℝ (mobius a) x w), hpolar u w, hadd,
    hnorm (u + w), hnorm u, hnorm w]
  ring

/-- **The Jacobian of the Möbius transformation**, `|det Dφ_a(x)| = λ(x)^m`.

The derivative is `λ(x)` times a linear isometry; a linear isometry has `normDet` one, and scaling
multiplies `normDet` by the `m`-th power of the modulus of the scalar. -/
theorem abs_det_fderiv_mobius [FiniteDimensional ℝ E] [Nontrivial E] {x a : E} (hx : ‖x‖ < 1)
    (ha : ‖a‖ < 1) :
    |(fderiv ℝ (mobius a) x).det| = mobiusFactor a x ^ Module.finrank ℝ E := by
  obtain ⟨c, hc, li, hli⟩ := isConformalMap_fderiv_mobius hx ha
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hcv : |c| = mobiusFactor a x := by
    have h1 : ‖fderiv ℝ (mobius a) x v‖ = |c| * ‖v‖ := by
      rw [hli]
      simp [norm_smul, Real.norm_eq_abs]
    have h2 := norm_fderiv_mobius_apply hx ha v
    exact mul_right_cancel₀ (ne_of_gt hvpos) (h1.symm.trans h2)
  have hdet : ((fderiv ℝ (mobius a) x : E →ₗ[ℝ] E)) = c • li.toLinearMap := by
    rw [hli]; rfl
  rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det, hdet,
    LinearMap.normDet_smul, li.normDet_eq_one, mul_one, Real.norm_eq_abs, hcv]

/-! ## Invariance of the measure -/

/-- The density of the invariant measure cancels the Jacobian:
`λ(x)^m (2/(1-‖φ_a(x)‖²))^m = (2/(1-‖x‖²))^m`. -/
theorem mobiusFactor_pow_mul_volumeDensity_mobius [FiniteDimensional ℝ E] {x a : E} (hx : ‖x‖ < 1)
    (ha : ‖a‖ < 1) :
    mobiusFactor a x ^ Module.finrank ℝ E * volumeDensity (mobius a x) = volumeDensity x := by
  have hx' : ‖x‖ ≤ 1 := le_of_lt hx
  have hB : mobiusBracketSq x a ≠ 0 := mobiusBracketSq_ne_zero hx' ha
  have hsx : (0 : ℝ) < 1 - ‖x‖ ^ 2 := one_sub_norm_sq_pos hx
  have hA : (0 : ℝ) < 1 - ‖a‖ ^ 2 := one_sub_norm_sq_pos ha
  have hphi : 1 - ‖mobius a x‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) / mobiusBracketSq x a :=
    one_sub_norm_sq_mobius hx' ha
  unfold volumeDensity
  rw [← mul_pow]
  congr 1
  rw [mobiusFactor, hphi]
  field_simp

theorem measurable_ofReal_volumeDensity [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] :
    Measurable (fun x : E => ENNReal.ofReal (volumeDensity x)) := by
  unfold volumeDensity
  fun_prop

theorem measurable_mobius [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (a : E) :
    Measurable (mobius a) := by
  unfold mobius
  exact ((differentiable_mobiusBracketSq a).continuous.measurable.inv).smul
    (differentiable_mobiusNum a).continuous.measurable

/-- **The invariant measure of `ℍ^m` is Möbius invariant.**

The change of variables along `φ_a` needs three inputs and no more: differentiability, injectivity
on the ball, and that the image of the ball is the ball. The density then cancels the Jacobian
pointwise, and what is left is the same integral. -/
theorem lintegral_invariantMeasure_comp_mobius [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] {a : E} (ha : ‖a‖ < 1) {g : E → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g (mobius a x) ∂(invariantMeasure E) = ∫⁻ x, g x ∂(invariantMeasure E) := by
  have hs : MeasurableSet (ball (0 : E) 1) := measurableSet_ball
  have hf' : ∀ x ∈ ball (0 : E) 1,
      HasFDerivWithinAt (mobius a) (fderiv ℝ (mobius a) x) (ball (0 : E) 1) x := fun x hx =>
    ((differentiableAt_mobius (le_of_lt (mem_ball_zero_iff.1 hx)) ha).hasFDerivAt).hasFDerivWithinAt
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure E)) hs
    hf' (injOn_mobius ha) (fun y => ENNReal.ofReal (volumeDensity y) * g y)
  rw [image_mobius ha] at hchange
  have hdens : ∀ h : E → ℝ≥0∞, Measurable h → ∫⁻ x, h x ∂(invariantMeasure E)
      = ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (volumeDensity x) * h x ∂(volume : Measure E) := by
    intro h hh
    rw [invariantMeasure, poincareBall,
      lintegral_withDensity_eq_lintegral_mul _ measurable_ofReal_volumeDensity hh]
    rfl
  rw [hdens g hg, hdens (fun x => g (mobius a x)) (hg.comp (measurable_mobius a)), hchange]
  refine setLIntegral_congr_fun hs fun x hx => ?_
  have hx' : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
  have hlam : (0 : ℝ) ≤ mobiusFactor a x ^ Module.finrank ℝ E :=
    le_of_lt (pow_pos (mobiusFactor_pos (le_of_lt hx') ha) _)
  rw [abs_det_fderiv_mobius hx' ha, ← mul_assoc, ← ENNReal.ofReal_mul hlam,
    mobiusFactor_pow_mul_volumeDensity_mobius hx' ha]

end HyperbolicSpace

end

end
