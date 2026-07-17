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
# Pointwise synthesis and simple tensors

This is the coordinate-side operator-theoretic core of the L2 manuscript. A bounded functional
`L : H →L[ℂ] ℂ` is applied pointwise to a Bochner `L²` function. In the manuscript this map is
`\widetilde L`; it becomes a synthesis operator only after composition with a unitary coordinate
transform `T`. The construction is independent of the later weighted-Sobolev realization of the
coefficient Hilbert space.
-/

@[expose] public section

noncomputable section

open scoped InnerProduct ComplexConjugate
open MeasureTheory InnerProductSpace

namespace LeanRidgelet

variable {α H : Type*} [MeasurableSpace α] (μ : Measure α)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The pointwise lift `\widetilde L` of a bounded coefficient functional to Bochner `L²`.

The historical name `fiberSynthesis` is retained for API compatibility. -/
def fiberSynthesis (L : H →L[ℂ] ℂ) : BochnerL2 α H μ →L[ℂ] L2 α μ :=
  L.compLpL 2 μ

theorem fiberSynthesis_apply_ae (L : H →L[ℂ] ℂ) (γ : BochnerL2 α H μ) :
    fiberSynthesis μ L γ =ᵐ[μ] fun x => L (γ x) :=
  L.coeFn_compLpL γ

/-- The simple-tensor embedding `J_h : f ↦ f ⊗ h` on unitary coordinates.

It is not by itself the parameter-space map `R_h = T* J_h`; the historical name
`fiberRidgelet` is retained for API compatibility. -/
def fiberRidgelet (h : H) : L2 α μ →L[ℂ] BochnerL2 α H μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ h).compLpL 2 μ

theorem fiberRidgelet_apply_ae (h : H) (f : L2 α μ) :
    fiberRidgelet μ h f =ᵐ[μ] fun x => f x • h := by
  simpa [fiberRidgelet] using
    (ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLpL f

variable [CompleteSpace H]

/-- The Riesz representer `h_L`, characterized in Mathlib's convention by
`⟪h_L, h⟫ = L h`. This is the manuscript identity `L[h] = ⟨h, h_L⟩`, because the
manuscript inner product is linear in the first argument whereas Mathlib's is linear in the
second. -/
def rieszRepresenter (L : H →L[ℂ] ℂ) : H :=
  (toDual ℂ H).symm L

@[simp]
theorem inner_rieszRepresenter (L : H →L[ℂ] ℂ) (h : H) :
    ⟪rieszRepresenter L, h⟫_ℂ = L h := by
  exact toDual_symm_apply

theorem rieszRepresenter_eq_zero_iff (L : H →L[ℂ] ℂ) :
    rieszRepresenter L = 0 ↔ L = 0 := by
  constructor
  · intro hzero
    ext h
    rw [← inner_rieszRepresenter L h, hzero]
    simp
  · intro hzero
    simp [rieszRepresenter, hzero]

/-- The nonnegative normalization constant `c_L = ‖h_L‖²`. -/
def fiberNormalization (L : H →L[ℂ] ℂ) : ℝ :=
  ‖rieszRepresenter L‖ ^ 2

theorem fiberNormalization_pos {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    0 < fiberNormalization L := by
  rw [fiberNormalization, sq_pos_iff]
  simpa [rieszRepresenter_eq_zero_iff] using hL

/-- The coefficient functional applied to its Riesz representer. -/
theorem apply_rieszRepresenter (L : H →L[ℂ] ℂ) :
    L (rieszRepresenter L) = (fiberNormalization L : ℂ) := by
  rw [← inner_rieszRepresenter]
  simp [fiberNormalization]

omit [CompleteSpace H] in
/-- Reconstruction in coordinates: `\widetilde L (J_h f) = L[h] f`. -/
theorem fiberSynthesis_comp_fiberRidgelet (L : H →L[ℂ] ℂ) (h : H) :
    fiberSynthesis μ L ∘L fiberRidgelet μ h =
      L h • ContinuousLinearMap.id ℂ (L2 α μ) := by
  ext f
  filter_upwards [fiberSynthesis_apply_ae μ L (fiberRidgelet μ h f),
    fiberRidgelet_apply_ae μ h f, Lp.coeFn_smul (L h) f] with x hS hR hsmul
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [hS, hR, hsmul]
  simp [mul_comm]

/-- The adjoint of the pointwise lift is `J_{h_L}`. -/
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
