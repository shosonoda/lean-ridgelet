/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# A section cocycle for a homogeneous space

For a subgroup `H` of a group `G`, the quotient map `G → G/H` has the noncomputable
set-theoretic section supplied by `Quotient.out`.  Comparing this section before and after left
translation gives an `H`-valued reentry cocycle

`s(q)⁻¹ g s(g⁻¹ q)`.

This file records the purely algebraic part of the section model for induced representations.
No measurability of the chosen section is asserted.  In applications, measurability should be
proved for the resulting multiplier, or the multiplier should be identified with an independently
constructed measurable function.
-/

@[expose] public section

noncomputable section

namespace QuotientGroup

variable {G M : Type*} [Group G] [Monoid M]

/-- The choice-based section of the left-coset quotient map. -/
def leftCosetSection (H : Subgroup G) : G ⧸ H → G :=
  Quotient.out

/-- The chosen representative belongs to the coset it represents. -/
@[simp]
theorem mk_leftCosetSection (H : Subgroup G) (q : G ⧸ H) :
    QuotientGroup.mk (leftCosetSection H q) = q :=
  Quotient.out_eq' q

/-- The `H`-valued reentry cocycle associated with the chosen left-coset section. -/
def leftCosetSectionCocycleOf (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (g : G) (q : G ⧸ H) : H :=
  ⟨(sec q)⁻¹ * g * sec (g⁻¹ • q), by
    rw [mul_assoc, ← QuotientGroup.leftRel_apply]
    apply Quotient.exact'
    calc
      QuotientGroup.mk (sec q) = q := hsec q
      _ = g • (g⁻¹ • q) := by simp
      _ = g • QuotientGroup.mk (sec (g⁻¹ • q)) :=
        congrArg (g • ·) (hsec (g⁻¹ • q)).symm
      _ = QuotientGroup.mk (g * sec (g⁻¹ • q)) := rfl⟩

/-- The reentry cocycle for Mathlib's choice-based quotient section. -/
def leftCosetSectionCocycle (H : Subgroup G) (g : G) (q : G ⧸ H) : H :=
  leftCosetSectionCocycleOf H (leftCosetSection H) (mk_leftCosetSection H) g q

/-- The section cocycle is trivial at the identity. -/
@[simp]
theorem leftCosetSectionCocycle_one (H : Subgroup G) (q : G ⧸ H) :
    leftCosetSectionCocycle H 1 q = 1 := by
  apply Subtype.ext
  simp [leftCosetSectionCocycle, leftCosetSectionCocycleOf]

/-- The reentry factors multiply according to the inverse-left-translation cocycle law. -/
theorem leftCosetSectionCocycle_mul (H : Subgroup G) (g h : G) (q : G ⧸ H) :
    leftCosetSectionCocycle H (g * h) q =
      leftCosetSectionCocycle H g q * leftCosetSectionCocycle H h (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [leftCosetSectionCocycle, leftCosetSectionCocycleOf, Subgroup.coe_mul]
  simp only [mul_inv_rev, mul_smul]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- The reentry cocycle of any right inverse to the quotient map is trivial at the identity. -/
@[simp]
theorem leftCosetSectionCocycleOf_one (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (q : G ⧸ H) :
    leftCosetSectionCocycleOf H sec hsec 1 q = 1 := by
  apply Subtype.ext
  simp [leftCosetSectionCocycleOf]

/-- Every choice of section gives the same formal cocycle law. -/
theorem leftCosetSectionCocycleOf_mul (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (g h : G) (q : G ⧸ H) :
    leftCosetSectionCocycleOf H sec hsec (g * h) q =
      leftCosetSectionCocycleOf H sec hsec g q *
        leftCosetSectionCocycleOf H sec hsec h (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [leftCosetSectionCocycleOf, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- A subgroup character applied to the section cocycle gives the multiplier used by the
section realization of an induced representation. -/
def leftCosetSectionMultiplierOf (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (χ : H →* M)
    (g : G) (q : G ⧸ H) : M :=
  χ (leftCosetSectionCocycleOf H sec hsec g q)

/-- The multiplier associated with Mathlib's choice-based quotient section. -/
def leftCosetSectionMultiplier (H : Subgroup G) (χ : H →* M) (g : G) (q : G ⧸ H) : M :=
  χ (leftCosetSectionCocycle H g q)

/-- The section multiplier is one at the identity. -/
@[simp]
theorem leftCosetSectionMultiplier_one (H : Subgroup G) (χ : H →* M) (q : G ⧸ H) :
    leftCosetSectionMultiplier H χ 1 q = 1 := by
  simp [leftCosetSectionMultiplier]

/-- A character of the reentry cocycle is a multiplier cocycle. -/
theorem leftCosetSectionMultiplier_mul (H : Subgroup G) (χ : H →* M)
    (g h : G) (q : G ⧸ H) :
    leftCosetSectionMultiplier H χ (g * h) q =
      leftCosetSectionMultiplier H χ g q *
        leftCosetSectionMultiplier H χ h (g⁻¹ • q) := by
  simp only [leftCosetSectionMultiplier, leftCosetSectionCocycle_mul, map_mul]

/-- The multiplier of an arbitrary section is one at the identity. -/
@[simp]
theorem leftCosetSectionMultiplierOf_one (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (χ : H →* M)
    (q : G ⧸ H) :
    leftCosetSectionMultiplierOf H sec hsec χ 1 q = 1 := by
  simp [leftCosetSectionMultiplierOf]

/-- A character of an arbitrary section's reentry cocycle is a multiplier cocycle. -/
theorem leftCosetSectionMultiplierOf_mul (H : Subgroup G) (sec : G ⧸ H → G)
    (hsec : Function.RightInverse sec QuotientGroup.mk) (χ : H →* M)
    (g h : G) (q : G ⧸ H) :
    leftCosetSectionMultiplierOf H sec hsec χ (g * h) q =
      leftCosetSectionMultiplierOf H sec hsec χ g q *
        leftCosetSectionMultiplierOf H sec hsec χ h (g⁻¹ • q) := by
  simp only [leftCosetSectionMultiplierOf, leftCosetSectionCocycleOf_mul, map_mul]

end QuotientGroup
