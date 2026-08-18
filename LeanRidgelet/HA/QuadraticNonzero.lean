/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticReconstruction
public import LeanRidgelet.HA.QuadraticSobolevSpace

/-!
# A nonzero reconstruction constant for the quadratic-form network

`LeanRidgelet.quadratic_reconstruction` gives the Section 7 endpoint with the reconstruction scalar
left unnamed and its nonvanishing left as a hypothesis of the right-inverse branch, and
`LeanRidgelet.HA.QuadraticComposite` records why that branch is unreachable through the
square-integrability route: a square-integrable kernel makes the operator compact, and a scalar
operator on an infinite-dimensional space is compact only for the zero scalar.  This file assembles
the statement the article actually claims -- a reconstruction formula whose constant is **nonzero**,
so that the normalized ridgelet transform really is a right inverse -- through the intermediate
coefficient space of `LeanRidgelet.HA.QuadraticSobolevSpace`, where neither operator is
Hilbert--Schmidt.

The assembly separates cleanly into a part that is proved here and two analytic inputs that are not.

## What is proved

* `LeanRidgelet.quadraticReconstructionScalar`: the Schur scalar of the pair, named, with
  `LeanRidgelet.quadraticReconstructionOperator_eq_scalar_smul_id` and
  `LeanRidgelet.quadraticReconstruction_apply`.
* `LeanRidgelet.quadraticReconstructionScalar_ne_zero`: one datum with nonzero image forces the
  scalar to be nonzero -- the whole nonvanishing question is the existence of a single probe.
* `LeanRidgelet.inner_quadraticReconstruction`: the scalar is computed by every probe, so it is the
  admissibility constant of the pair rather than an abstract choice.
* `LeanRidgelet.quadratic_reconstruction_nonzero_of_apply_ne_zero`: the endpoint with a nonzero
  constant, from a probe.  No placeholder in its proof.

## What remains, and where it is recorded

Two named theorems carry a `sorry`, and they are the two halves of the article's boundedness
appendix in the shape the intermediate space needs.

* `LeanRidgelet.exists_quadraticIntertwiners_of_bounds`: the two bounds through `Γ^k` --
  `LeanRidgelet.QuadraticAnalysisBound` and `LeanRidgelet.QuadraticSynthesisBound`, stated exactly
  as
  `LeanRidgelet.HA.QuadraticSobolevSpace` leaves them -- produce a bounded intertwining pair whose
  composite is the pointwise Bochner composite.  What is missing is the packaging: a carrier for
  `Γ^k`, its completeness, and the promotion of the seminorm identities to a bounded action, none of
  which that file does.
* `LeanRidgelet.exists_quadraticAdmissiblePair`: an admissible pair exists -- some synthesis
feature,
  analysis feature and order satisfy both bounds and leave the pointwise composite nonvanishing on
  some datum.  This is the admissibility constant of the article being nonzero.

The nonvanishing is stated as an existence over pairs on purpose.  For a *fixed* pair it is false:
the zero synthesis feature satisfies both bounds and annihilates everything, so any statement
quantified over all pairs satisfying the bounds would be a false statement behind a placeholder.
The article fixes the activation to be the rectified linear unit, and specializing the existence to
a
fixed activation is the natural follow-up: it needs the nonvanishing of the activation on the
Fourier
side, which is where the negative-order condition on the synthesis feature -- the growth index of
the
L2 activation spaces -- enters.  Nothing here assumes it.

## What is deliberately not assumed

No boundedness of a machine or a ridgelet transform is taken as a hypothesis, and no nonvanishing
constant is taken as a hypothesis: both are conclusions, resting on the two placeholders above.  The
Schur step itself carries nothing, the irreducibility of the data representation being proved in
`LeanRidgelet.HA.AffineMackey`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-! ### The two operator types -/

/-- A bounded machine for the quadratic-form network: an intertwiner from the relatively invariant
parameter representation to the affine data representation. -/
abbrev QuadraticMachine (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] :=
  JointEquivariantMachine
    (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation

/-- A bounded ridgelet transform for the quadratic-form network: an intertwiner the other way. -/
abbrev QuadraticRidgelet (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] :=
  JointEquivariantRidgelet
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
    (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation

/-! ### The reconstruction scalar, named -/

/-- **The reconstruction scalar of a pair.**  Schur's lemma makes the reconstruction operator a
scalar multiple of the identity; this is that scalar.  It is the admissibility constant of the pair:
`LeanRidgelet.quadraticReconstructionScalar_eq_inner_div` computes it from any nonzero datum, so
nothing about the choice is arbitrary. -/
def quadraticReconstructionScalar (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : QuadraticMachine lam) (R : QuadraticRidgelet lam) : ℂ :=
  (quadraticReconstructionOperator_eq_smul_id lam M R).choose

/-- The reconstruction operator is its scalar times the identity. -/
theorem quadraticReconstructionOperator_eq_scalar_smul_id
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : QuadraticMachine lam) (R : QuadraticRidgelet lam) :
    jointReconstructionOperator M R =
      quadraticReconstructionScalar lam M R •
        ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
  (quadraticReconstructionOperator_eq_smul_id lam M R).choose_spec

/-- The pointwise form: the machine applied to the transform of a datum is the scalar times the
datum. -/
theorem quadraticReconstruction_apply (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (M : QuadraticMachine lam) (R : QuadraticRidgelet lam)
    (f : Lp ℂ 2 (volume : Measure E)) :
    M (R f) = quadraticReconstructionScalar lam M R • f := by
  simpa using congr($(quadraticReconstructionOperator_eq_scalar_smul_id lam M R) f)

/-- **One probe decides the nonvanishing.**  If some datum has nonzero image under the composite
then
the reconstruction scalar is nonzero.  This is why the whole question reduces to exhibiting a single
datum, and why the admissibility statement below is an existence. -/
theorem quadraticReconstructionScalar_ne_zero (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (M : QuadraticMachine lam) (R : QuadraticRidgelet lam)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : M (R f) ≠ 0) :
    quadraticReconstructionScalar lam M R ≠ 0 := by
  intro h
  rw [quadraticReconstruction_apply lam M R f, h, zero_smul] at hf
  exact hf rfl

/-- **The scalar is the admissibility constant.**  Every datum computes it: the pairing of the datum
with its reconstruction is the scalar times the datum's squared norm.  So the scalar is determined
by
the pair of features and by no choice made in its definition, and for a nonzero datum it is the
Rayleigh quotient of the reconstruction operator. -/
theorem inner_quadraticReconstruction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (M : QuadraticMachine lam) (R : QuadraticRidgelet lam)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ⟪f, M (R f)⟫_ℂ = quadraticReconstructionScalar lam M R * ⟪f, f⟫_ℂ := by
  rw [quadraticReconstruction_apply lam M R f, inner_smul_right]

/-! ### The endpoint with a nonzero constant -/

/-- **Section 7 with a nonzero reconstruction constant, from a probe.**  A pair of bounded
intertwiners and one datum whose reconstruction is nonzero give a reconstruction formula whose
constant is nonzero, so the normalized ridgelet transform is a genuine right inverse of the machine.
Nothing is assumed beyond the probe, and the proof carries no placeholder. -/
theorem quadratic_reconstruction_nonzero_of_apply_ne_zero
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (M : QuadraticMachine lam) (R : QuadraticRidgelet lam)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : M (R f) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) :=
  ⟨quadraticReconstructionScalar lam M R, quadraticReconstructionScalar_ne_zero lam M R f hf,
    quadraticReconstructionOperator_eq_scalar_smul_id lam M R,
    quadraticNormalizedRidgelet_rightInverse lam M R
      (quadraticReconstructionOperator_eq_scalar_smul_id lam M R)
      (quadraticReconstructionScalar_ne_zero lam M R f hf)⟩

/-! ### The two bounds through the intermediate space -/

/-- **The analysis bound through `Γ^k`.**  The order-`k` Sobolev seminorm in the constant
coefficient
of the analysis transform of a datum is at most a finite constant times the datum's `L²` norm.  This
is the bound `LeanRidgelet.quadraticSobolevSeminorm_bochnerRidgelet` reduces to an estimate on the
derivative features, and it is where smoothness of the analysis feature is spent. -/
def QuadraticAnalysisBound (lam : Measure (QuadraticParameter E)) (ψ : ℝ → ℂ) (k : ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ 2 (volume : Measure E),
    quadraticSobolevSeminorm lam k
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) ≤
      C * eLpNorm (f : E → ℂ) 2 (volume : Measure E)

/-- **The synthesis bound out of `Γ^k`.**  The `L²` norm of the synthesis integral of a coefficient
function in the space is at most a finite constant times its order-`k` seminorm.  This is the bound
`LeanRidgelet.enorm_bochnerSynthesis_le_quadraticSobolevSeminorm_mul` gives pointwise in the data
variable; integrating it in that variable is what a proof has to supply. -/
def QuadraticSynthesisBound (lam : Measure (QuadraticParameter E)) (σ : ℝ → ℂ) (k : ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ γ : QuadraticParameter E → ℂ, MemQuadraticSobolev lam k γ →
    eLpNorm (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ) γ) 2
        (volume : Measure E) ≤
      C * quadraticSobolevSeminorm lam k γ

/-! ### The two analytic inputs that remain -/

/-- **Remaining: the bounded intertwining pair through `Γ^k`.**  Given the two bounds, the machine
and the ridgelet transform exist as bounded intertwiners and their composite is the pointwise
Bochner
composite of the two features.

Not proved here.  What is missing is not the two estimates -- those are the hypotheses -- but the
packaging `LeanRidgelet.HA.QuadraticSobolevSpace` deliberately leaves out: a carrier for `Γ^k`, its
completeness, the promotion of `LeanRidgelet.quadraticSobolevSeminorm_comp_smul` to a bounded action
on that carrier, and the factorization of each Bochner integral through it.  The equivariance of the
two integrals is already available pointwise from
`LeanRidgelet.HA.QuadraticRelativeMeasure`. -/
theorem exists_quadraticIntertwiners_of_bounds (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ} {k : ℕ}
    (hψ : QuadraticAnalysisBound lam ψ k) (hσ : QuadraticSynthesisBound lam σ k) :
    ∃ (M : QuadraticMachine lam) (R : QuadraticRidgelet lam),
      ∀ f : Lp ℂ 2 (volume : Measure E),
        (M (R f) : E → ℂ) =ᵐ[(volume : Measure E)]
          bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) := by
  sorry

/-- **Remaining: an admissible pair exists.**  Some synthesis feature, analysis feature and order
satisfy both bounds and leave the pointwise composite nonvanishing on some datum.  This is the
article's admissibility constant being nonzero.

Not proved here, and stated as an existence over pairs on purpose: for a fixed pair the conclusion
is
false, the zero synthesis feature satisfying both bounds and annihilating every datum.  The article
fixes the activation to be the rectified linear unit; specializing this existence to a fixed
activation needs its nonvanishing on the Fourier side together with the negative-order condition
that
controls its growth, and neither is assumed anywhere in this development. -/
theorem exists_quadraticAdmissiblePair (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] :
    ∃ (σ ψ : ℝ → ℂ) (k : ℕ), QuadraticAnalysisBound lam ψ k ∧ QuadraticSynthesisBound lam σ k ∧
      ∃ f : Lp ℂ 2 (volume : Measure E),
        ¬ bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
              (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
            =ᵐ[(volume : Measure E)] 0 := by
  sorry

/-! ### The nonzero-constant reconstruction formula -/

/-- **Section 7 of the article, with a nonzero reconstruction constant.**  There are a synthesis
feature, an analysis feature, an order, and a bounded intertwining pair realizing the two Bochner
integrals through the intermediate coefficient space, whose reconstruction operator is a **nonzero**
scalar multiple of the identity; the normalized ridgelet transform is then a right inverse of the
machine.  This is the universality claim for the quadratic-form network in the form the article
states it.

The Schur step and the reduction of nonvanishing to a single probe carry nothing.  What this rests
on
is exactly the two placeholders above, `LeanRidgelet.exists_quadraticIntertwiners_of_bounds` and
`LeanRidgelet.exists_quadraticAdmissiblePair`. -/
theorem quadratic_reconstruction_nonzero (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] :
    ∃ (σ ψ : ℝ → ℂ) (k : ℕ) (M : QuadraticMachine lam) (R : QuadraticRidgelet lam) (c : ℂ),
      c ≠ 0 ∧
      jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) ∧
      QuadraticAnalysisBound lam ψ k ∧ QuadraticSynthesisBound lam σ k ∧
      ∀ f : Lp ℂ 2 (volume : Measure E),
        (M (R f) : E → ℂ) =ᵐ[(volume : Measure E)]
          bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) := by
  obtain ⟨σ, ψ, k, hψ, hσ, f, hf⟩ := exists_quadraticAdmissiblePair (E := E) lam
  obtain ⟨M, R, hMR⟩ := exists_quadraticIntertwiners_of_bounds lam hψ hσ
  have hne : M (R f) ≠ 0 := by
    intro h
    refine hf ((hMR f).symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure E)
  obtain ⟨c, hc, hrec, hright⟩ :=
    quadratic_reconstruction_nonzero_of_apply_ne_zero lam M R f hne
  exact ⟨σ, ψ, k, M, R, c, hc, hrec, hright, hψ, hσ, hMR⟩

end LeanRidgelet
