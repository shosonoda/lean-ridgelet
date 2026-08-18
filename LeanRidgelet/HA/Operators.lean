/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Operator-level joint-equivariant machines and ridgelet transforms

At the bounded-operator level, a joint-equivariant machine and its ridgelet transform are exactly
continuous intertwining maps in opposite directions. This file packages the terminology of
Lemmas 3.7 and 3.9 and proves the commutation identity used in Theorem 3.10.

The later integral modules construct these operators from feature maps. Keeping this layer
abstract separates the Schur argument from Bochner measurability and integrability.
-/

@[expose] public section

open scoped ContRepresentation

namespace LeanRidgelet

variable {G H K : Type*} [Monoid G] [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A bounded joint-equivariant machine from parameter space to data space. -/
abbrev JointEquivariantMachine (πParameter : ContRepresentation ℂ G K)
    (πData : ContRepresentation ℂ G H) :=
  πParameter →ⁱL πData

/-- A bounded joint-equivariant ridgelet transform from data space to parameter space. -/
abbrev JointEquivariantRidgelet (πData : ContRepresentation ℂ G H)
    (πParameter : ContRepresentation ℂ G K) :=
  πData →ⁱL πParameter

/-- The reconstruction operator `M_φ R_ψ`. -/
def jointReconstructionOperator {πData : ContRepresentation ℂ G H}
    {πParameter : ContRepresentation ℂ G K}
    (M : JointEquivariantMachine πParameter πData)
    (R : JointEquivariantRidgelet πData πParameter) : H →L[ℂ] H :=
  (M.comp R).toContinuousLinearMap

@[simp]
theorem jointReconstructionOperator_apply {πData : ContRepresentation ℂ G H}
    {πParameter : ContRepresentation ℂ G K}
    (M : JointEquivariantMachine πParameter πData)
    (R : JointEquivariantRidgelet πData πParameter) (f : H) :
    jointReconstructionOperator M R f = M (R f) := rfl

/-- Lemmas 3.7 and 3.9 imply that `M_φ R_ψ` commutes with the data representation. -/
theorem jointReconstructionOperator_commutes {πData : ContRepresentation ℂ G H}
    {πParameter : ContRepresentation ℂ G K}
    (M : JointEquivariantMachine πParameter πData)
    (R : JointEquivariantRidgelet πData πParameter) (g : G) :
    (jointReconstructionOperator M R).comp (πData g) =
      (πData g).comp (jointReconstructionOperator M R) := by
  ext f
  exact (M.comp R).isIntertwining g f

end LeanRidgelet
