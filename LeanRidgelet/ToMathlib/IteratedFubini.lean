/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for triple iterated integrals

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib's `MeasureTheory.integral_integral_swap` exchanges the two integrals of a doubly iterated
Bochner integral. Nothing there covers the triply iterated case, which is what one needs whenever
a kernel is written as an iterated integral over three parameters and the outer one has to be
brought inside — as in the passage from a network written as an integral over weights, directions
and biases to its Fourier expression, where the bias frequency has to end up outermost.

## Main results

* `MeasureTheory.integral_integral_integral_swap_left`: moving the outermost integral of a triple
  iterated integral to the innermost position.
* `MeasureTheory.integral_integral_integral_swap_right`: the reverse direction.

Both take the integrability of the whole integrand against the triple product measure, which is
the hypothesis Fubini needs and the one a statement of this kind has to carry.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Moving the outermost integral of a triple iterated integral to the innermost position.**
Mathlib's `MeasureTheory.integral_integral_swap` does this for two variables; here the outer
variable passes both inner ones at once. -/
theorem integral_integral_integral_swap_left (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] (f : α → β → γ → E)
    (hf : Integrable (fun p : α × β × γ => f p.1 p.2.1 p.2.2) (μ.prod (ν.prod ρ))) :
    ∫ a, (∫ b, (∫ c, f a b c ∂ρ) ∂ν) ∂μ = ∫ b, (∫ c, (∫ a, f a b c ∂μ) ∂ρ) ∂ν := by
  have hswap : (∫ a, (∫ q : β × γ, f a q.1 q.2 ∂(ν.prod ρ)) ∂μ)
      = ∫ q : β × γ, (∫ a, f a q.1 q.2 ∂μ) ∂(ν.prod ρ) :=
    integral_integral_swap (f := fun a (q : β × γ) => f a q.1 q.2) hf
  have hleft : (∫ a, (∫ q : β × γ, f a q.1 q.2 ∂(ν.prod ρ)) ∂μ)
      = ∫ a, (∫ b, (∫ c, f a b c ∂ρ) ∂ν) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.prod_right_ae] with a ha
    exact integral_prod _ ha
  have hright : (∫ q : β × γ, (∫ a, f a q.1 q.2 ∂μ) ∂(ν.prod ρ))
      = ∫ b, (∫ c, (∫ a, f a b c ∂μ) ∂ρ) ∂ν :=
    integral_prod _ hf.swap.integral_prod_left
  rw [← hleft, hswap, hright]

/-- **Moving the innermost integral of a triple iterated integral to the outermost position**, the
reverse of `MeasureTheory.integral_integral_integral_swap_left`. -/
theorem integral_integral_integral_swap_right (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] (f : α → β → γ → E)
    (hf : Integrable (fun p : α × β × γ => f p.1 p.2.1 p.2.2) (μ.prod (ν.prod ρ))) :
    ∫ b, (∫ c, (∫ a, f a b c ∂μ) ∂ρ) ∂ν = ∫ a, (∫ b, (∫ c, f a b c ∂ρ) ∂ν) ∂μ :=
  (integral_integral_integral_swap_left μ ν ρ f hf).symm

end MeasureTheory
