/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Schur
public import Mathlib.Analysis.Complex.Isometry

/-!
# Circle characters as one-dimensional unitary representations

A multiplicative character with values in the complex unit circle acts on `ℂ` by scalar
multiplication. This file bundles that elementary construction as a unitary representation and
records its strong continuity and irreducibility. It is independent of ridgelet transforms and is
intended as a Mathlib upstream candidate.
-/

@[expose] public section

noncomputable section

/-- Complex multiplication by a unit-circle element, as a complex-linear isometric equivalence. -/
def circleComplexLinearIsometryEquiv : Circle →* (ℂ ≃ₗᵢ[ℂ] ℂ) where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℂ ℂ a with
      norm_map' z := show ‖a * z‖ = ‖z‖ by
        rw [norm_mul, Circle.norm_coe, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| by simp
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b

@[simp]
theorem circleComplexLinearIsometryEquiv_apply (a : Circle) (z : ℂ) :
    circleComplexLinearIsometryEquiv a z = a * z := rfl

namespace UnitaryRepresentation

variable {G : Type*} [Group G]

/-- A circle-valued multiplicative character acts unitarily on the complex line. -/
def ofCircleCharacter (χ : G →* Circle) : UnitaryRepresentation G ℂ :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (circleComplexLinearIsometryEquiv.comp χ)

@[simp]
theorem ofCircleCharacter_apply (χ : G →* Circle) (g : G) (z : ℂ) :
    ((ofCircleCharacter χ g : ℂ →L[ℂ] ℂ) z) = (χ g : ℂ) * z := by
  rfl

/-- A continuous circle character gives a strongly continuous one-dimensional unitary
representation. -/
theorem ofCircleCharacter_isStronglyContinuous [TopologicalSpace G] (χ : G →* Circle)
    (hχ : Continuous χ) : (ofCircleCharacter χ).IsStronglyContinuous := by
  intro z
  change Continuous fun g : G ↦ (χ g).val * z
  exact (continuous_id.mul_const z).comp (continuous_subtype_val.comp hχ)

/-- A circle character acts irreducibly on the complex line. -/
theorem ofCircleCharacter_isTopologicallyIrreducible (χ : G →* Circle) :
    (ofCircleCharacter χ).IsTopologicallyIrreducible :=
  complex_isTopologicallyIrreducible _

end UnitaryRepresentation
