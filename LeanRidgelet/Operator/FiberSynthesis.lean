/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Abstract fiber synthesis

This is the operator-theoretic core of Chapters 3--4 of the L2 manuscript. A bounded functional
`L : H →L[ℂ] ℂ` is applied pointwise to a Bochner `L²` function. The construction is independent of
the later weighted-Sobolev realization of the fiber Hilbert space.
-/

@[expose] public section

noncomputable section

open scoped InnerProduct ComplexConjugate
open MeasureTheory InnerProductSpace

namespace LeanRidgelet

variable {α H : Type*} [MeasurableSpace α] (μ : Measure α)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Apply a bounded fiber functional pointwise on Bochner `L²`. -/
def fiberSynthesis (L : H →L[ℂ] ℂ) : BochnerL2 α H μ →L[ℂ] L2 α μ :=
  L.compLpL 2 μ

theorem fiberSynthesis_apply_ae (L : H →L[ℂ] ℂ) (γ : BochnerL2 α H μ) :
    fiberSynthesis μ L γ =ᵐ[μ] fun x => L (γ x) :=
  L.coeFn_compLpL γ

/-- The simple-tensor/ridgelet map `f ↦ f ⊗ q`. -/
def fiberRidgelet (q : H) : L2 α μ →L[ℂ] BochnerL2 α H μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ q).compLpL 2 μ

theorem fiberRidgelet_apply_ae (q : H) (f : L2 α μ) :
    fiberRidgelet μ q f =ᵐ[μ] fun x => f x • q := by
  simpa [fiberRidgelet] using
    (ContinuousLinearMap.toSpanSingleton ℂ q).coeFn_compLpL f

variable [CompleteSpace H]

/-- The Riesz representer `q_L`, characterized by `L q = ⟪q_L, q⟫`. -/
def rieszRepresenter (L : H →L[ℂ] ℂ) : H :=
  (toDual ℂ H).symm L

@[simp]
theorem inner_rieszRepresenter (L : H →L[ℂ] ℂ) (q : H) :
    ⟪rieszRepresenter L, q⟫_ℂ = L q := by
  exact toDual_symm_apply

theorem rieszRepresenter_eq_zero_iff (L : H →L[ℂ] ℂ) :
    rieszRepresenter L = 0 ↔ L = 0 := by
  constructor
  · intro h
    ext q
    rw [← inner_rieszRepresenter L q, h]
    simp
  · intro h
    simp [rieszRepresenter, h]

/-- The positive normalization constant `c_L = ‖q_L‖²`. -/
def fiberNormalization (L : H →L[ℂ] ℂ) : ℝ :=
  ‖rieszRepresenter L‖ ^ 2

theorem fiberNormalization_pos {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    0 < fiberNormalization L := by
  rw [fiberNormalization, sq_pos_iff]
  simpa [rieszRepresenter_eq_zero_iff] using hL

/-- The fiber functional applied to its Riesz representer. -/
theorem apply_rieszRepresenter (L : H →L[ℂ] ℂ) :
    L (rieszRepresenter L) = (fiberNormalization L : ℂ) := by
  rw [← inner_rieszRepresenter]
  simp [fiberNormalization]

omit [CompleteSpace H] in
/-- Reconstruction by a simple tensor: `S_L (R_q f) = L(q) f`. -/
theorem fiberSynthesis_comp_fiberRidgelet (L : H →L[ℂ] ℂ) (q : H) :
    fiberSynthesis μ L ∘L fiberRidgelet μ q =
      L q • ContinuousLinearMap.id ℂ (L2 α μ) := by
  ext f
  filter_upwards [fiberSynthesis_apply_ae μ L (fiberRidgelet μ q f),
    fiberRidgelet_apply_ae μ q f, Lp.coeFn_smul (L q) f] with x hS hR hsmul
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [hS, hR, hsmul]
  simp [mul_comm]

/-- The adjoint of pointwise synthesis is the ridgelet map associated with the Riesz representer. -/
theorem adjoint_fiberSynthesis (L : H →L[ℂ] ℂ) :
    (fiberSynthesis μ L)† = fiberRidgelet μ (rieszRepresenter L) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f γ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fiberRidgelet_apply_ae μ (rieszRepresenter L) f,
    fiberSynthesis_apply_ae μ L γ] with x hR hS
  rw [hR, hS, inner_smul_left, inner_rieszRepresenter]
  simp [mul_comm]

end LeanRidgelet
