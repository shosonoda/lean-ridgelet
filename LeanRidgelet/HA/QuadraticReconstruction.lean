/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.AffineMackey
public import LeanRidgelet.HA.QuadraticRelativeMeasure
public import LeanRidgelet.HA.Reconstruction

/-!
# Universality of the quadratic-form network

This file states the endpoint of Section 7 of arXiv:2405.13682.  A bounded machine and a bounded
ridgelet transform that intertwine the quadratic parameter representation with the affine data
representation compose to a scalar multiple of the identity, and when that scalar is nonzero the
normalized ridgelet transform is a right inverse of the machine.  That is the article's universality
claim for the quadratic-form network.

The scalarity is Schur's lemma applied to the data representation, whose topological irreducibility
is `LeanRidgelet.affineDataLpUnitaryRepresentation_isTopologicallyIrreducible` — proved in this
development, not assumed.  The parameter side is the relatively invariant model of
`LeanRidgelet.HA.QuadraticRelativeMeasure`, which exists precisely so that the two representations
are balanced; with the additive Haar parameter measure of `LeanRidgelet.HA.QuadraticMeasure` they
are not, and no such pair of intertwiners can be built.

## Main results

* `LeanRidgelet.quadraticReconstructionOperator_eq_smul_id`: the reconstruction operator of the
  quadratic-form network is a scalar.
* `LeanRidgelet.quadraticNormalizedRidgelet_rightInverse`: a nonzero scalar makes the normalized
  quadratic ridgelet transform a right inverse of the quadratic machine.
* `LeanRidgelet.quadratic_reconstruction`: the two statements combined, in the shape the article
  uses.

## What is assumed

Boundedness.  The two operators enter as bundled bounded intertwiners rather than being built from
the pointwise Bochner formulas of `LeanRidgelet.HA.QuadraticRelativeMeasure`.  This is the standing
convention of this development for the analytic input of the article's boundedness appendix, and it
is the same convention `LeanRidgelet.HA.L2Bridge` follows for the depth-two example: the pointwise
equivariance identities are proved there, while a bounded realization of the two integrals on `L²`
is an input.  Nothing else is assumed; in particular the Schur step carries no placeholder.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- The reconstruction operator of the quadratic-form network is a scalar multiple of the identity.
This is Schur's lemma applied to the affine data representation, whose topological irreducibility is
proved in `LeanRidgelet.HA.AffineMackey`. -/
theorem quadraticReconstructionOperator_eq_smul_id
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : JointEquivariantMachine
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation)
    (R : JointEquivariantRidgelet
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation) :
    ∃ c : ℂ, jointReconstructionOperator M R =
      c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
  ha_reconstruction_formula (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible
    (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation M R

omit [Nontrivial E] in
/-- A nonzero reconstruction scalar makes the normalized quadratic ridgelet transform a right
inverse of the quadratic machine. -/
theorem quadraticNormalizedRidgelet_rightInverse
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : JointEquivariantMachine
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation)
    (R : JointEquivariantRidgelet
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation)
    {c : ℂ}
    (hrec : jointReconstructionOperator M R =
      c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)))
    (hc : c ≠ 0) :
    Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) :=
  ha_normalizedRidgelet_rightInverse M R hrec hc

/-- Section 7 of the article: the quadratic-form network reconstructs the data space.  The
reconstruction operator is a scalar, and a nonzero scalar turns the normalized quadratic ridgelet
transform into a right inverse of the quadratic machine. -/
theorem quadratic_reconstruction
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : JointEquivariantMachine
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation)
    (R : JointEquivariantRidgelet
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation) :
    ∃ c : ℂ, jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      (c ≠ 0 → Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M)) := by
  obtain ⟨c, hc⟩ := quadraticReconstructionOperator_eq_smul_id lam M R
  exact ⟨c, hc, fun hc0 ↦ quadraticNormalizedRidgelet_rightInverse lam M R hc hc0⟩

end LeanRidgelet
