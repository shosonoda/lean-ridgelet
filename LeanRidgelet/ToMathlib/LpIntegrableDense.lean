/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Density of the integrable elements in `Lp`

For `p ≠ ∞`, the elements of `Lp E p μ` whose representative is integrable form a dense subset.
Mathlib (as of the pinned version) provides the density of `Lp` simple functions
(`MeasureTheory.Lp.simpleFunc.dense`) and the integrability of `Lp` simple functions
(`MeasureTheory.SimpleFunc.memLp_iff_integrable`), but not this direct combination, which is the
standard entry point for extending an operator defined by an absolutely convergent integral on
`L¹ ∩ L^p` to all of `L^p`. Candidate for upstreaming to Mathlib.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

namespace Lp

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `p ≠ ∞`, the classes in `Lp E p μ` with an integrable representative are dense; this is
the density of `L¹ ∩ L^p` in `L^p`. -/
theorem dense_setOf_integrable (hp_ne_top : p ≠ ∞) :
    Dense {f : Lp E p μ | Integrable f μ} := by
  have hp_pos : p ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  refine (Lp.simpleFunc.dense hp_ne_top).mono fun f hf => ?_
  have hmem : MemLp (Lp.simpleFunc.toSimpleFunc (⟨f, hf⟩ : Lp.simpleFunc E p μ)) p μ :=
    Lp.simpleFunc.memLp _
  have hint : Integrable (Lp.simpleFunc.toSimpleFunc (⟨f, hf⟩ : Lp.simpleFunc E p μ)) μ :=
    (SimpleFunc.memLp_iff_integrable hp_pos hp_ne_top).mp hmem
  exact hint.congr (Lp.simpleFunc.toSimpleFunc_eq_toFun (⟨f, hf⟩ : Lp.simpleFunc E p μ))

end Lp

end MeasureTheory
