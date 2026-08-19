/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A bounded operator on `L²` from a pointwise formula

An integral transform is given by a formula on functions, and turning it into a bounded operator on
`L²` is always the same four steps: the value of the formula is square integrable, the formula is
additive and homogeneous almost everywhere, and its `L²` norm is bounded by a constant times the
input's.  This file does those steps once.

`MeasureTheory.lpOperatorOfPointwise` takes exactly those four inputs and returns the operator, with
`MeasureTheory.coeFn_lpOperatorOfPointwise` identifying its values with the formula and
`MeasureTheory.norm_lpOperatorOfPointwise_le` giving the operator norm bound.  The almost-everywhere
additivity and homogeneity are hypotheses rather than consequences because they are where the
integrability of the defining integral enters: a formula that is linear on functions need not be
linear on almost-everywhere classes unless its integrals converge.

This file is a Mathlib upstream candidate and has no dependencies on the rest of the `LeanRidgelet`
project.

## Main results

* `MeasureTheory.lpOperatorOfPointwise`: the bounded operator.
* `MeasureTheory.coeFn_lpOperatorOfPointwise`: its values are represented by the formula.
* `MeasureTheory.norm_lpOperatorOfPointwise_le`: the operator norm is at most the constant.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

section Linear

variable {T : (α → ℂ) → β → ℂ} (hmem : ∀ f : Lp ℂ 2 μ, MemLp (T (f : α → ℂ)) 2 ν)

/-- The linear map underlying `MeasureTheory.lpOperatorOfPointwise`.  Additivity and homogeneity are
the hypotheses, taken almost everywhere, since that is the level at which an `L²` class determines
its representative. -/
def lpLinearMapOfPointwise
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ)) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν where
  toFun f := (hmem f).toLp _
  map_add' f g := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (f + g)),
      Lp.coeFn_add ((hmem f).toLp (T (f : α → ℂ))) ((hmem g).toLp (T (g : α → ℂ))),
      MemLp.coeFn_toLp (hmem f), MemLp.coeFn_toLp (hmem g), hadd f g] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (c • f)),
      Lp.coeFn_smul c ((hmem f).toLp (T (f : α → ℂ))),
      MemLp.coeFn_toLp (hmem f), hsmul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply]

theorem coeFn_lpLinearMapOfPointwise
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ)) (f : Lp ℂ 2 μ) :
    (lpLinearMapOfPointwise hmem hadd hsmul f : β → ℂ) =ᵐ[ν] T (f : α → ℂ) :=
  MemLp.coeFn_toLp (hmem f)

end Linear

/-- **A bounded operator on `L²` from a pointwise formula.**  Given that the formula's value is
square integrable, that it is additive and homogeneous almost everywhere, and that its `L²` norm is
at most a constant times the input's, the formula defines a bounded linear operator between the `L²`
spaces.

The four hypotheses are what an integral transform supplies: square integrability and the norm
bound come from an estimate on the transform, and additivity and homogeneity come from integrability
of the defining integral, which is what lets it be split. -/
def lpOperatorOfPointwise {T : (α → ℂ) → β → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (T (f : α → ℂ)) 2 ν)
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ))
    (hbound : ∀ f : Lp ℂ 2 μ, (eLpNorm (T (f : α → ℂ)) 2 ν).toReal ≤ C * ‖f‖) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous (lpLinearMapOfPointwise hmem hadd hsmul) C fun f ↦ by
    have h : ‖lpLinearMapOfPointwise hmem hadd hsmul f‖ = (eLpNorm (T (f : α → ℂ)) 2 ν).toReal :=
      Lp.norm_toLp _ (hmem f)
    rw [h]
    exact hbound f

@[simp]
theorem lpOperatorOfPointwise_apply {T : (α → ℂ) → β → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (T (f : α → ℂ)) 2 ν)
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ))
    (hbound : ∀ f : Lp ℂ 2 μ, (eLpNorm (T (f : α → ℂ)) 2 ν).toReal ≤ C * ‖f‖) (f : Lp ℂ 2 μ) :
    lpOperatorOfPointwise hC hmem hadd hsmul hbound f =
      lpLinearMapOfPointwise hmem hadd hsmul f := rfl

/-- The operator's values are represented by the formula. -/
theorem coeFn_lpOperatorOfPointwise {T : (α → ℂ) → β → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (T (f : α → ℂ)) 2 ν)
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ))
    (hbound : ∀ f : Lp ℂ 2 μ, (eLpNorm (T (f : α → ℂ)) 2 ν).toReal ≤ C * ‖f‖) (f : Lp ℂ 2 μ) :
    (lpOperatorOfPointwise hC hmem hadd hsmul hbound f : β → ℂ) =ᵐ[ν] T (f : α → ℂ) :=
  coeFn_lpLinearMapOfPointwise hmem hadd hsmul f

/-- The operator norm is at most the constant of the bound. -/
theorem norm_lpOperatorOfPointwise_le {T : (α → ℂ) → β → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (T (f : α → ℂ)) 2 ν)
    (hadd : ∀ f g : Lp ℂ 2 μ, T ((f + g : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      T (f : α → ℂ) + T (g : α → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ), T ((c • f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[ν]
      c • T (f : α → ℂ))
    (hbound : ∀ f : Lp ℂ 2 μ, (eLpNorm (T (f : α → ℂ)) 2 ν).toReal ≤ C * ‖f‖) :
    ‖lpOperatorOfPointwise hC hmem hadd hsmul hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end MeasureTheory
