/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Operators
public import LeanRidgelet.ToMathlib.LieGroup.Schur

/-!
# Reconstruction from Schur's lemma

This is the operator-theoretic core of Theorem 3.10 in arXiv:2405.13682. The first theorem accepts
the Schur property as an explicit hypothesis, while the paper-level endpoint derives it from the
fully proved infinite-dimensional unitary Schur lemma.

## Deviations from the article

The article calls the scalar `c_{φ,ψ}` bilinear in the two complex feature maps. With the displayed
pairing `∫ f overline(ψ)`, it is linear in `φ` and conjugate-linear in `ψ`; the later integral API
will state this as sesquilinearity. The operator theorem here only asserts existence of the scalar.
-/

@[expose] public section

noncomputable section

open scoped ContRepresentation

namespace LeanRidgelet

variable {G H K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A bounded endomorphism already bundled as an intertwiner is scalar under the Schur property.
This form is used when only the composite pointwise synthesis/ridgelet formula has a bounded
extension, without assuming boundedness of the two integral operators separately. -/
theorem ha_reconstruction_of_hasSchurProperty_of_intertwiner
    (πData : UnitaryRepresentation G H) (hschur : πData.HasSchurProperty)
    (T : JointEquivariantMachine πData.toContRepresentation πData.toContRepresentation) :
    ∃ c : ℂ, T.toContinuousLinearMap = c • ContinuousLinearMap.id ℂ H := by
  apply hschur
  intro g
  ext f
  exact T.isIntertwining g f

/-- Topological irreducibility makes every bounded intertwining endomorphism scalar. -/
theorem ha_reconstruction_of_intertwiner (πData : UnitaryRepresentation G H)
    (hirr : πData.IsTopologicallyIrreducible)
    (T : JointEquivariantMachine πData.toContRepresentation πData.toContRepresentation) :
    ∃ c : ℂ, T.toContinuousLinearMap = c • ContinuousLinearMap.id ℂ H := by
  exact ha_reconstruction_of_hasSchurProperty_of_intertwiner πData
    (πData.hasSchurProperty_of_isTopologicallyIrreducible hirr) T

/-- Theorem 3.10 conditional on precisely the Schur property it uses. This version has no hidden
analytic assumption and no dependency on a placeholder. -/
theorem ha_reconstruction_of_hasSchurProperty (πData : UnitaryRepresentation G H)
    (hschur : πData.HasSchurProperty) (πParameter : ContRepresentation ℂ G K)
    (M : JointEquivariantMachine πParameter πData.toContRepresentation)
    (R : JointEquivariantRidgelet πData.toContRepresentation πParameter) :
    ∃ c : ℂ, jointReconstructionOperator M R = c • ContinuousLinearMap.id ℂ H := by
  apply hschur
  exact jointReconstructionOperator_commutes M R

/-- The paper-level reconstruction formula, stated from topological irreducibility. -/
theorem ha_reconstruction_formula (πData : UnitaryRepresentation G H)
    (hirr : πData.IsTopologicallyIrreducible) (πParameter : ContRepresentation ℂ G K)
    (M : JointEquivariantMachine πParameter πData.toContRepresentation)
    (R : JointEquivariantRidgelet πData.toContRepresentation πParameter) :
    ∃ c : ℂ, jointReconstructionOperator M R = c • ContinuousLinearMap.id ℂ H := by
  exact ha_reconstruction_of_hasSchurProperty πData
    (πData.hasSchurProperty_of_isTopologicallyIrreducible hirr) πParameter M R

omit [CompleteSpace H] in
/-- A nonzero reconstruction scalar makes the normalized ridgelet transform a right inverse of
the machine. This is the constructive universality conclusion following Theorem 3.10. -/
theorem ha_normalizedRidgelet_rightInverse {πData : ContRepresentation ℂ G H}
    {πParameter : ContRepresentation ℂ G K}
    (M : JointEquivariantMachine πParameter πData)
    (R : JointEquivariantRidgelet πData πParameter) {c : ℂ}
    (hrec : jointReconstructionOperator M R = c • ContinuousLinearMap.id ℂ H) (hc : c ≠ 0) :
    Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) := by
  intro f
  have hf : M (R f) = c • f := by
    simpa using congr($(hrec) f)
  change M (c⁻¹ • R f) = f
  rw [map_smul, hf]
  simp [hc]

end LeanRidgelet
