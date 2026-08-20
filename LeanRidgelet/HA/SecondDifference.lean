/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Algebra.Support
public import LeanRidgelet.Activation.ReLU

/-!
# The second difference, and what it does to the rectified linear unit

An activation of polynomial growth is in no `L^p`, and the rectified linear unit's Fourier transform
has a second-order pole at the origin.  Both obstructions are removed at once by a **second
difference**, and this file computes what it does.

Compare the two natural ways to kill a second-order pole, in the convention
`ĝ(ζ) = ∫ g(z) exp (-i z ζ) dz`:

* `∂_z²` multiplies the transform by `-ζ²`.  That vanishes to second order at the origin, but it
  **grows** at infinity -- and `∂_z²` of the rectified linear unit is the Dirac measure, not a
  function at all.
* `Δ_h²` multiplies it by `-4 sin²(hζ/2)`.  That vanishes to second order at the origin *and* stays
  bounded, by `4`.

So a second difference is the bounded multiplier with a double zero, which is exactly what the pole
needs.  Applied to the rectified linear unit it gives the hat function of width `2h` and height `h`:
bounded, compactly supported, continuous, and of positive integral -- the integral being `h²`, the
double zero cancelling the double pole and leaving a nonzero constant behind.

A second difference is a finite combination of translations, which is the practical point.  Moving
it
across an integral needs only linearity and translation invariance of the measure, never an
integration by parts and never a distributional pairing.

## Main results

* `LeanRidgelet.secondDifference`: the operator `g ↦ g(· + h) - 2 g + g(· - h)`.
* `LeanRidgelet.secondDifference_relu`: it turns the rectified linear unit into the hat function
  `max 0 (h - |z|)`.
* `LeanRidgelet.hatFunction`: that function, with `LeanRidgelet.hatFunction_nonneg`,
  `LeanRidgelet.hatFunction_le`, `LeanRidgelet.hatFunction_eq_zero_of_le`,
  `LeanRidgelet.continuous_hatFunction`, `LeanRidgelet.hasCompactSupport_hatFunction`,
  `LeanRidgelet.integrable_hatFunction` and `LeanRidgelet.integral_hatFunction_pos`.

## What is assumed

Nothing.  Every statement here is an identity or an elementary estimate about explicit functions of
one real variable.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-! ### The operator -/

/-- **The second difference at step `h`.**  A finite combination of three translations, so it moves
across an integral by translation invariance alone. -/
def secondDifference (h : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun z ↦ g (z + h) - 2 * g z + g (z - h)

@[simp]
theorem secondDifference_apply (h : ℝ) (g : ℝ → ℂ) (z : ℝ) :
    secondDifference h g z = g (z + h) - 2 * g z + g (z - h) := rfl

/-- The second difference is symmetric in the step. -/
theorem secondDifference_neg (h : ℝ) (g : ℝ → ℂ) :
    secondDifference (-h) g = secondDifference h g := by
  funext z
  simp only [secondDifference_apply, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-! ### The hat function -/

/-- The hat function of width `2h` and height `h`: the second difference of the rectified linear
unit. -/
def hatFunction (h : ℝ) : ℝ → ℝ :=
  fun z ↦ max 0 (h - |z|)

theorem hatFunction_nonneg (h z : ℝ) : 0 ≤ hatFunction h z := le_max_left _ _

theorem hatFunction_le (h z : ℝ) : hatFunction h z ≤ max 0 h :=
  max_le_max le_rfl (sub_le_self h (abs_nonneg z))

theorem hatFunction_eq_zero_of_le {h z : ℝ} (hz : h ≤ |z|) : hatFunction h z = 0 :=
  max_eq_left (by linarith)

@[simp]
theorem hatFunction_zero (h : ℝ) : hatFunction h 0 = max 0 h := by
  simp only [hatFunction, abs_zero, sub_zero]

theorem continuous_hatFunction (h : ℝ) : Continuous (hatFunction h) :=
  continuous_const.max (continuous_const.sub continuous_abs)

theorem hasCompactSupport_hatFunction (h : ℝ) : HasCompactSupport (hatFunction h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -|h|) (b := |h|)) fun z hz ↦ ?_
  refine hatFunction_eq_zero_of_le ((le_abs_self h).trans ?_)
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  rcases hz with hz | hz
  · have hzneg : z < 0 := lt_of_lt_of_le hz (neg_nonpos.2 (abs_nonneg h))
    rw [abs_of_neg hzneg]
    linarith
  · rw [abs_of_pos (lt_of_le_of_lt (abs_nonneg h) hz)]
    exact hz.le

theorem integrable_hatFunction (h : ℝ) : Integrable (hatFunction h) volume :=
  (continuous_hatFunction h).integrable_of_hasCompactSupport (hasCompactSupport_hatFunction h)

/-! ### The computation -/

/-- **The second difference of the rectified linear unit is the hat function.**  The unit is linear
on each side of the origin, so the difference vanishes outside `[-h, h]`; inside, the three pieces
combine to `h - |z|`. -/
theorem secondDifference_relu (h : ℝ) (hh : 0 ≤ h) (z : ℝ) :
    secondDifference h (fun t : ℝ ↦ ((relu t : ℝ) : ℂ)) z = ((hatFunction h z : ℝ) : ℂ) := by
  have hrelu : ∀ t : ℝ, relu t = max t 0 := fun _ ↦ rfl
  simp only [secondDifference_apply, hrelu, hatFunction]
  rcases le_or_gt z (-h) with h1 | h1
  · have e1 : max (z + h) 0 = 0 := max_eq_right (by linarith)
    have e2 : max z 0 = 0 := max_eq_right (by linarith)
    have e3 : max (z - h) 0 = 0 := max_eq_right (by linarith)
    have e4 : max 0 (h - |z|) = 0 := by
      refine max_eq_left ?_
      have : |z| = -z := abs_of_nonpos (by linarith)
      rw [this]; linarith
    rw [e1, e2, e3, e4]
    norm_num
  · rcases le_or_gt z 0 with h2 | h2
    · have e1 : max (z + h) 0 = z + h := max_eq_left (by linarith)
      have e2 : max z 0 = 0 := max_eq_right h2
      have e3 : max (z - h) 0 = 0 := max_eq_right (by linarith)
      have e4 : max 0 (h - |z|) = z + h := by
        have hzabs : |z| = -z := abs_of_nonpos h2
        rw [hzabs]
        exact (max_eq_right (by linarith)).trans (by ring)
      rw [e1, e2, e3, e4]
      push_cast
      ring
    · rcases le_or_gt z h with h3 | h3
      · have e1 : max (z + h) 0 = z + h := max_eq_left (by linarith)
        have e2 : max z 0 = z := max_eq_left h2.le
        have e3 : max (z - h) 0 = 0 := max_eq_right (by linarith)
        have e4 : max 0 (h - |z|) = h - z := by
          have hzabs : |z| = z := abs_of_nonneg h2.le
          rw [hzabs]
          exact max_eq_right (by linarith)
        rw [e1, e2, e3, e4]
        push_cast
        ring
      · have e1 : max (z + h) 0 = z + h := max_eq_left (by linarith)
        have e2 : max z 0 = z := max_eq_left h2.le
        have e3 : max (z - h) 0 = z - h := max_eq_left (by linarith)
        have e4 : max 0 (h - |z|) = 0 := by
          have hzabs : |z| = z := abs_of_nonneg h2.le
          rw [hzabs]
          exact max_eq_left (by linarith)
        rw [e1, e2, e3, e4]
        push_cast
        ring

/-- **The hat function has positive integral.**  It is continuous, nonnegative, and positive at the
origin, so its support has positive measure.  The value is `h²`; only positivity is needed below,
and it is what makes the reduced activation's admissibility constant nonzero. -/
theorem integral_hatFunction_pos {h : ℝ} (hh : 0 < h) :
    0 < ∫ z, hatFunction h z := by
  refine (integral_pos_iff_support_of_nonneg (fun z ↦ hatFunction_nonneg h z)
    (integrable_hatFunction h)).2 ?_
  have hsub : Set.Ioo (-(h / 2)) (h / 2) ⊆ Function.support (hatFunction h) := by
    intro z hz
    have habs : |z| < h := by
      rw [abs_lt]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    refine ne_of_gt ?_
    simp only [hatFunction]
    exact lt_max_of_lt_right (by linarith : (0 : ℝ) < h - |z|)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [ENNReal.ofReal_pos]
  linarith

/-! ### Complex-valued forms -/

/-- The rectified linear unit as a complex-valued activation. -/
def reluComplex : ℝ → ℂ := fun z ↦ ((relu z : ℝ) : ℂ)

/-- The hat function as a complex-valued activation. -/
def hatComplex (h : ℝ) : ℝ → ℂ := fun z ↦ ((hatFunction h z : ℝ) : ℂ)

/-- The complex hat function is continuous. -/
theorem continuous_hatComplex (h : ℝ) : Continuous (hatComplex h) :=
  Complex.continuous_ofReal.comp (continuous_hatFunction h)

/-- The complex hat function is bounded by the height of the hat. -/
theorem norm_hatComplex_le (h z : ℝ) : ‖hatComplex h z‖ ≤ max 0 h := by
  rw [hatComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hatFunction_nonneg h z)]
  exact hatFunction_le h z

/-- **The second difference of the rectified linear unit is the hat function**, as complex-valued
activations. -/
theorem secondDifference_reluComplex {h : ℝ} (hh : 0 ≤ h) :
    secondDifference h reluComplex = hatComplex h :=
  funext fun z ↦ secondDifference_relu h hh z

end LeanRidgelet
