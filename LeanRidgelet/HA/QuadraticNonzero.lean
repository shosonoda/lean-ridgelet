/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.AdjointReconstruction
public import LeanRidgelet.HA.BochnerAdjoint
public import LeanRidgelet.ToMathlib.LpOperatorOfPointwise
public import LeanRidgelet.HA.QuadraticSobolevCarrier
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
* `LeanRidgelet.quadratic_reconstruction_nonzero_of_apply_ne_zero` and
  `LeanRidgelet.exists_ne_zero_of_quadraticCompositeEndomorphism`: the endpoint with a nonzero
  constant from a probe, for a pair and for an endomorphism.  No placeholder in either proof.
* `LeanRidgelet.eLpNorm_bochnerSynthesis_bochnerRidgelet_le`: **the composite is bounded** by the
  product of the two constants -- and the estimate does *not* say either factor is bounded on
  parameter `L²`, which is exactly why it escapes the Hilbert--Schmidt obstruction.

## What remains, and where it is recorded

**One** named theorem carries a `sorry`, and it is the article's admissibility condition.  The
packaging half is proved: `LeanRidgelet.exists_quadraticCompositeIntertwiner_of_bounds` builds the
bounded intertwining **endomorphism** of data `L²` from the two bounds through `Γ^k` together with
the integrability that makes the two integrals additive on almost-everywhere classes, using the
estimate `LeanRidgelet.eLpNorm_bochnerSynthesis_bochnerRidgelet_le`, the packaging tool
`MeasureTheory.lpOperatorOfPointwise`, and the equivariance
`LeanRidgelet.quadraticComposite_intertwines_of_coeFn` -- which uses nothing about how the operator
was built.
* `LeanRidgelet.exists_quadraticAdmissiblePair`: an admissible pair exists -- some synthesis
  feature, analysis feature and order satisfy both bounds and leave the pointwise composite
  nonvanishing on
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

/-- A bounded intertwining **endomorphism** of data `L²`: the shape the article's weaker boundedness
hypothesis takes, and -- as `LeanRidgelet.eLpNorm_bochnerSynthesis_bochnerRidgelet_le` shows -- the
shape the intermediate-space route actually produces.  The two bounds control the composite, not the
two factors separately: the synthesis is bounded on `Γ^k`, which is smaller than parameter `L²`, so
nothing in them says the machine is bounded there. -/
abbrev QuadraticCompositeEndomorphism :=
  JointEquivariantMachine
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation

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
function in the space is at most a finite constant times its order-`k` seminorm.

A warning about how *not* to prove it.  The theorem
`LeanRidgelet.enorm_bochnerSynthesis_le_quadraticSobolevSeminorm_mul` gives this pointwise in the
data variable, by Cauchy--Schwarz in the parameter -- but integrating that estimate in the data
variable asks exactly for the square integrability of the feature over the product, which is
condition T2, which
`LeanRidgelet.HA.QuadraticComposite` shows forces the reconstruction constant to vanish.  The
pointwise estimate uses only the order-`0` term of the seminorm, and that is why: a bound that does
not see the derivatives cannot escape Hilbert--Schmidt.  A proof has to use the higher-order terms,
pairing the derivatives of the coefficient function against a negative-order object built from the
synthesis feature.  For an activation of polynomial growth that also needs a polynomial weight in
the constant coefficient -- the growth index `t` of the L2 activation spaces -- which `Γ^k` as
defined does not carry. -/
def QuadraticSynthesisBound (lam : Measure (QuadraticParameter E)) (σ : ℝ → ℂ) (k : ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ γ : QuadraticParameter E → ℂ, MemQuadraticSobolev lam k γ →
    eLpNorm (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ) γ) 2
        (volume : Measure E) ≤
      C * quadraticSobolevSeminorm lam k γ

/-! ### The composite estimate -/

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The composite is bounded, and neither factor need be.**  The two bounds compose: the analysis
transform of a datum has order-`k` seminorm at most a constant times the datum's `L²` norm, and the
synthesis integral of a member of the space has `L²` norm at most a constant times its seminorm, so
the composite of the two Bochner integrals is bounded on data `L²` with the product of the two
constants.

This is the estimate the whole route exists to produce, and the point is what it does *not* say.  It
does not say the synthesis integral is bounded on parameter `L²`: it is bounded on `Γ^k`, which is
smaller, and the seminorm dominates the `L²` norm rather than the other way round.  So the composite
is bounded without either factor being Hilbert--Schmidt, which is exactly the shape
`LeanRidgelet.HA.QuadraticComposite` shows is needed -- and the shape the article's boundedness
hypothesis takes when read as a hypothesis on the composite alone. -/
theorem eLpNorm_bochnerSynthesis_bochnerRidgelet_le (lam : Measure (QuadraticParameter E))
    {σ ψ : ℝ → ℂ} {k : ℕ} (hψ : QuadraticAnalysisBound lam ψ k)
    (hσ : QuadraticSynthesisBound lam σ k) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ 2 (volume : Measure E),
      MemQuadraticSobolev lam k
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) →
        eLpNorm (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))) 2
            (volume : Measure E) ≤
          C * eLpNorm (f : E → ℂ) 2 (volume : Measure E) := by
  obtain ⟨Cψ, hCψ, hψ'⟩ := hψ
  obtain ⟨Cσ, hCσ, hσ'⟩ := hσ
  refine ⟨Cσ * Cψ, ENNReal.mul_ne_top hCσ hCψ, fun f hf ↦ ?_⟩
  calc eLpNorm (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))) 2
          (volume : Measure E)
      ≤ Cσ * quadraticSobolevSeminorm lam k
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) :=
        hσ' _ hf
    _ ≤ Cσ * (Cψ * eLpNorm (f : E → ℂ) 2 (volume : Measure E)) := by
        gcongr
        exact hψ' f
    _ = Cσ * Cψ * eLpNorm (f : E → ℂ) 2 (volume : Measure E) := by rw [mul_assoc]

/-! ### A nonzero constant from a bounded intertwining endomorphism -/

omit [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)] in
/-- **The endomorphism form of the endpoint, with no placeholder.**  A bounded intertwining
endomorphism of data `L²` that does not annihilate some datum is a **nonzero** scalar multiple of
the identity.  Schur gives the scalar and the probe gives its nonvanishing; this is the same
two-line reduction as for a pair of intertwiners, in the shape the intermediate-space route
produces. -/
theorem exists_ne_zero_of_quadraticCompositeEndomorphism
    (T : QuadraticCompositeEndomorphism (E := E)) (f : Lp ℂ 2 (volume : Measure E)) (hf : T f ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ T.toContinuousLinearMap =
      c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) := by
  obtain ⟨c, hc⟩ := ha_reconstruction_of_intertwiner
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible T
  refine ⟨c, ?_, hc⟩
  intro hc0
  refine hf ?_
  have h1 : T.toContinuousLinearMap f = c • f := by simpa using congr($(hc) f)
  rw [hc0, zero_smul] at h1
  exact h1

/-! ### Equivariance of any operator realizing the composite -/

omit [Nontrivial E] in
/-- **Any operator that realizes the composite pointwise intertwines the data representation.**  The
equivariance argument uses nothing about how the operator was built: only the two pointwise Bochner
intertwining identities of `LeanRidgelet.HA.QuadraticRelativeMeasure` and the almost-everywhere
formula for the data representation.  `LeanRidgelet.HA.QuadraticComposite` runs it for the operator
as a hypothesis, so it applies to an operator built any other way. -/
theorem quadraticComposite_intertwines_of_coeFn (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ}
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ f : Lp ℂ 2 (volume : Measure E), (T f : E → ℂ) =ᵐ[(volume : Measure E)]
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)))
    (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 (volume : Measure E)) :
    T ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
        Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f) =
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (T f) := by
  refine Lp.ext_iff.2 ?_
  have hπD := affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g f
  have hpull : bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
      (fun x ↦ ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
        Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f : E → ℂ) x) =
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          fun x ↦ (f : E → ℂ) x) := by
    have hstep := bochnerRidgelet_quadraticVectorFeature_congr_ae (E := E) ψ
      (hπD.trans (Filter.EventuallyEq.of_eq
        (quasiUnitaryPullbackAction_one_eq affineDataJacobian g fun x ↦ (f : E → ℂ) x).symm))
    rw [hstep]
    funext ξ
    exact quadraticRelativeBochnerRidgelet_intertwines (volume : Measure E) ψ g
      (fun x ↦ (f : E → ℂ) x) ξ
  refine (hT _).trans ?_
  rw [hpull]
  have hsyn : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
      (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          fun x ↦ (f : E → ℂ) x)) =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g
        (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
            fun x ↦ (f : E → ℂ) x)) := by
    funext x
    exact quadraticRelativeBochnerSynthesis_intertwines lam σ g _ x
  rw [hsyn]
  refine Filter.EventuallyEq.symm ?_
  refine (affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g _).trans ?_
  rw [← quasiUnitaryPullbackAction_one_eq affineDataJacobian g]
  exact affineData_quasiUnitaryPullbackAction_congr_ae g (hT f)

/-! ### From the bounds to an operator, and the one analytic input that remains -/

omit [Nontrivial E] in
/-- **The composite is a bounded intertwining endomorphism.**  Given the two bounds through `Γ^k`,
the integrability that makes the two Bochner integrals additive and homogeneous on almost-everywhere
classes, and measurability of the composite, the composite is realized by a bounded intertwining
endomorphism of data `L²`.

Every hypothesis beyond the two bounds is one that packaging a pointwise formula as an operator
requires and that no estimate can supply.  A formula linear on functions need not be linear on
almost-everywhere classes: splitting the defining integral over a sum needs each piece integrable,
so `hadd` and `hsmul` are where the convergence of the two integrals enters.  Membership of the
analysis transform in the space is what the synthesis bound is stated against, and measurability is
what turns a finite norm into membership of `L²`.

The estimate is `LeanRidgelet.eLpNorm_bochnerSynthesis_bochnerRidgelet_le`, the packaging is
`MeasureTheory.lpOperatorOfPointwise`, and the equivariance is
`LeanRidgelet.quadraticComposite_intertwines_of_coeFn` -- which uses nothing about how the operator
was built. -/
theorem exists_quadraticCompositeIntertwiner_of_bounds (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ} {k : ℕ}
    (hψ : QuadraticAnalysisBound lam ψ k) (hσ : QuadraticSynthesisBound lam σ k)
    (hmemΓ : ∀ f : Lp ℂ 2 (volume : Measure E), MemQuadraticSobolev lam k
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)))
    (hmeas : ∀ f : Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable
      (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)))
      (volume : Measure E))
    (hadd : ∀ f h : Lp ℂ 2 (volume : Measure E),
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
            ((f + h : Lp ℂ 2 (volume : Measure E)) : E → ℂ))
        =ᵐ[(volume : Measure E)]
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) +
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (h : E → ℂ)))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)),
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
            ((c • f : Lp ℂ 2 (volume : Measure E)) : E → ℂ))
        =ᵐ[(volume : Measure E)]
      c • bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))) :
    ∃ T : QuadraticCompositeEndomorphism (E := E),
      ∀ f : Lp ℂ 2 (volume : Measure E),
        (T f : E → ℂ) =ᵐ[(volume : Measure E)]
          bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) := by
  obtain ⟨C, hCtop, hC⟩ := eLpNorm_bochnerSynthesis_bochnerRidgelet_le lam hψ hσ
  set Φ : (E → ℂ) → E → ℂ := fun u ↦
    bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) u) with hΦ
  have hmem : ∀ f : Lp ℂ 2 (volume : Measure E), MemLp (Φ (f : E → ℂ)) 2 (volume : Measure E) :=
    fun f ↦ ⟨hmeas f, lt_of_le_of_lt (hC f (hmemΓ f))
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCtop) (Lp.eLpNorm_lt_top f))⟩
  have hbound : ∀ f : Lp ℂ 2 (volume : Measure E),
      (eLpNorm (Φ (f : E → ℂ)) 2 (volume : Measure E)).toReal ≤ C.toReal * ‖f‖ := by
    intro f
    have h := hC f (hmemΓ f)
    have hne : C * eLpNorm (f : E → ℂ) 2 (volume : Measure E) ≠ ∞ :=
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCtop) (Lp.eLpNorm_lt_top f)).ne
    calc (eLpNorm (Φ (f : E → ℂ)) 2 (volume : Measure E)).toReal
        ≤ (C * eLpNorm (f : E → ℂ) 2 (volume : Measure E)).toReal :=
          ENNReal.toReal_le_toReal (hmem f).2.ne hne |>.2 h
      _ = C.toReal * ‖f‖ := by rw [ENNReal.toReal_mul, ← Lp.norm_def]
  have hcoe := fun f ↦ MeasureTheory.coeFn_lpOperatorOfPointwise
    (ENNReal.toReal_nonneg (a := C)) hmem hadd hsmul hbound f
  exact ⟨⟨MeasureTheory.lpOperatorOfPointwise (ENNReal.toReal_nonneg (a := C)) hmem hadd hsmul
      hbound,
    fun g ↦ ContinuousLinearMap.ext fun f ↦
      quadraticComposite_intertwines_of_coeFn lam _ hcoe g f⟩, hcoe⟩

/-- **Remaining: an admissible pair exists.**  Some synthesis feature, analysis feature and order
satisfy both bounds and leave the pointwise composite nonvanishing on some datum.  This is the
article's admissibility constant being nonzero.

Not proved here, and stated as an existence over pairs on purpose: for a fixed pair the conclusion
is false, the zero synthesis feature satisfying both bounds and annihilating every datum.  The
article fixes the activation to be the rectified linear unit; specializing this existence to a fixed
activation needs its nonvanishing on the Fourier side together with the negative-order condition
that controls its growth, and neither is assumed anywhere in this development. -/
theorem exists_quadraticAdmissiblePair (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] :
    ∃ (σ ψ : ℝ → ℂ) (k : ℕ), QuadraticAnalysisBound lam ψ k ∧ QuadraticSynthesisBound lam σ k ∧
      (∀ f : Lp ℂ 2 (volume : Measure E), MemQuadraticSobolev lam k
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))) ∧
      (∀ f : Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable
        (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)))
        (volume : Measure E)) ∧
      (∀ f h : Lp ℂ 2 (volume : Measure E),
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
              ((f + h : Lp ℂ 2 (volume : Measure E)) : E → ℂ))
          =ᵐ[(volume : Measure E)]
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) +
          bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (h : E → ℂ))) ∧
      (∀ (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)),
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
              ((c • f : Lp ℂ 2 (volume : Measure E)) : E → ℂ))
          =ᵐ[(volume : Measure E)]
        c • bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))) ∧
      ∃ f : Lp ℂ 2 (volume : Measure E),
        ¬ bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
              (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
            =ᵐ[(volume : Measure E)] 0 := by
  sorry

/-! ### The nonzero-constant reconstruction formula -/

/-- **Section 7 of the article, with a nonzero reconstruction constant.**  There are a synthesis
feature, an analysis feature, an order satisfying both bounds through the intermediate coefficient
space, and a **nonzero** constant such that the composite of the two Bochner integrals returns every
datum multiplied by that constant.  Equivalently: the network whose coefficient function is the
normalized analysis transform of a datum outputs that datum.  This is the universality claim for the
quadratic-form network, stated on the network's own integrals rather than on an abstract pair of
operators.

The Schur step and the reduction of nonvanishing to a single probe carry nothing, and the composite
estimate is proved.  What this rests on is exactly the two placeholders above,
`LeanRidgelet.exists_quadraticCompositeIntertwiner_of_bounds` and
`LeanRidgelet.exists_quadraticAdmissiblePair`. -/
theorem quadratic_reconstruction_nonzero (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] :
    ∃ (σ ψ : ℝ → ℂ) (k : ℕ) (c : ℂ), c ≠ 0 ∧
      QuadraticAnalysisBound lam ψ k ∧ QuadraticSynthesisBound lam σ k ∧
      ∀ f : Lp ℂ 2 (volume : Measure E),
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
            (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
          =ᵐ[(volume : Measure E)] fun x ↦ c • (f : E → ℂ) x := by
  obtain ⟨σ, ψ, k, hψ, hσ, hmemΓ, hmeas, hadd, hsmul, f, hf⟩ :=
    exists_quadraticAdmissiblePair (E := E) lam
  obtain ⟨T, hT⟩ :=
    exists_quadraticCompositeIntertwiner_of_bounds lam hψ hσ hmemΓ hmeas hadd hsmul
  have hne : T f ≠ 0 := by
    intro h
    refine hf ((hT f).symm.trans ?_)
    rw [h]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure E)
  obtain ⟨c, hc, hrec⟩ := exists_ne_zero_of_quadraticCompositeEndomorphism T f hne
  refine ⟨σ, ψ, k, c, hc, hψ, hσ, fun h ↦ ?_⟩
  refine (hT h).symm.trans ?_
  have hTh : T.toContinuousLinearMap h = c • h := by simpa using congr($(hrec) h)
  rw [show T h = c • h from hTh]
  exact Lp.coeFn_smul c h

/-! ### The coorbit route: a nonzero constant with no placeholder -/

/-- **Section 7 with a nonzero reconstruction constant, unconditionally.**  Take the machine to be
the adjoint of the ridgelet transform.  Then a single datum with nonzero transform gives a
**nonzero** reconstruction constant, the reconstruction operator is that constant times the
identity, and the normalized ridgelet transform is a right inverse of the machine -- the article's
endpoint, with nothing left assumed but the boundedness of the ridgelet transform itself.

This is the argument of coorbit theory and of the theory of generalized wavelet transforms; see
`LeanRidgelet.HA.AdjointReconstruction` for the general statement and for the reference.  The
constant is `‖R f‖² / ‖f‖²`, which the orthogonality relation below exhibits, so it is real and
positive rather than merely nonzero, and the compactness obstruction of
`LeanRidgelet.HA.QuadraticComposite` cannot arise: no kernel is assumed square integrable, and the
composite is a multiple of an isometry, which in infinite dimensions is not compact.

What it costs is that the machine is the adjoint rather than an independently chosen synthesis
integral.  At the level of the Bochner formulas that is the common-feature case -- the adjoint of
the ridgelet transform against a feature is the synthesis integral against the same feature -- so
this reconstructs with the network whose activation is the analysis feature.  Identifying the
adjoint with the pointwise synthesis integral is a Fubini computation and is not done here; fixing
the activation in advance is the harder problem the two placeholders above are about. -/
theorem quadratic_reconstruction_adjoint (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (R : QuadraticRidgelet lam) (f₀ : Lp ℂ 2 (volume : Measure E))
    (hf₀ : R f₀ ≠ 0) :
    ∃ (M : QuadraticMachine lam) (c : ℂ), c ≠ 0 ∧
      jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) ∧
      ∀ f : Lp ℂ 2 (volume : Measure E), ⟪R f, R f⟫_ℂ = c * ⟪f, f⟫_ℂ := by
  obtain ⟨c, hc, hscalar, horth, _⟩ := ha_adjoint_reconstruction_of_ne_zero
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible R f₀ hf₀
  exact ⟨adjointIntertwiner R, c, hc, hscalar,
    quadraticNormalizedRidgelet_rightInverse lam (adjointIntertwiner R) R hscalar hc, horth⟩

/-- **The quadratic-form network reconstructs, on its own integrals.**  Take the synthesis feature
to be the analysis feature.  Then the synthesis integral is the adjoint of the ridgelet transform,
so one datum with nonzero transform gives a **nonzero** constant for which the composite of the
network's two Bochner integrals returns every datum multiplied by that constant.

This is the Section 7 endpoint stated on the integrals the article writes down rather than on
abstract operators, and it carries no placeholder.  What is assumed is what the development assumes
everywhere for analytic input -- that the two integrals are realized by bounded intertwiners --
together with one Fubini hypothesis and the nonvanishing probe.  The constant is `‖R f‖² / ‖f‖²`, so
it is positive.

The synthesis feature being the analysis feature is what makes the two integrals adjoint, and it is
the whole cost of the route: this reconstructs with the network whose activation is the analysis
feature.  An activation fixed in advance is the harder problem of the two placeholders above. -/
theorem quadratic_bochner_reconstruction_adjoint (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {ψ : ℝ → ℂ} (R : QuadraticRidgelet lam) (M : QuadraticMachine lam)
    (hR : ∀ f : Lp ℂ 2 (volume : Measure E), (R f : QuadraticParameter E → ℂ)
      =ᵐ[quadraticRelativeMeasure lam]
        bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
    (hM : ∀ γ : Lp ℂ 2 (quadraticRelativeMeasure lam), (M γ : E → ℂ) =ᵐ[(volume : Measure E)]
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature ψ)
          (γ : QuadraticParameter E → ℂ))
    (hfub : ∀ (γ : Lp ℂ 2 (quadraticRelativeMeasure lam)) (f : Lp ℂ 2 (volume : Measure E)),
      Integrable (Function.uncurry fun (x : E) (ξ : QuadraticParameter E) ↦
        conj ((γ : QuadraticParameter E → ℂ) ξ) *
          (conj (quadraticVectorFeature ψ x ξ) * (f : E → ℂ) x))
        ((volume : Measure E).prod (quadraticRelativeMeasure lam)))
    (f₀ : Lp ℂ 2 (volume : Measure E)) (hf₀ : R f₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : Lp ℂ 2 (volume : Measure E),
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature ψ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
        =ᵐ[(volume : Measure E)] fun x ↦ c • (f : E → ℂ) x := by
  have hadj : M.toContinuousLinearMap =
      ContinuousLinearMap.adjoint R.toContinuousLinearMap :=
    bochnerSynthesis_eq_adjoint_bochnerRidgelet (volume : Measure E)
      (quadraticRelativeMeasure lam) (quadraticVectorFeature ψ) M.toContinuousLinearMap
      R.toContinuousLinearMap hM hR hfub
  obtain ⟨c, hc, _, _, hrec⟩ := ha_adjoint_reconstruction_of_ne_zero
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible R f₀ hf₀
  refine ⟨c, hc, fun f ↦ ?_⟩
  have hMf : M (R f) = c • f := by
    have h := hrec f
    rw [← hadj, ContIntertwiningMap.toContinuousLinearMap_apply] at h
    calc M (R f) = (c * c⁻¹) • M (R f) := by rw [mul_inv_cancel₀ hc, one_smul]
      _ = c • (c⁻¹ • M (R f)) := by rw [smul_smul]
      _ = c • f := by rw [h]
  have hsyn : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature ψ)
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ))
      =ᵐ[(volume : Measure E)]
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature ψ)
          ((R f : QuadraticParameter E → ℂ)) :=
    Filter.Eventually.of_forall fun x ↦
      integral_congr_ae ((hR f).mono fun ξ hξ ↦ by simp only [hξ])
  refine hsyn.trans (((hM (R f)).symm.trans ?_))
  rw [hMf]
  exact Lp.coeFn_smul c f

/-! ### The endpoint through the intermediate space -/

/-- A machine out of the intermediate coefficient space: an intertwiner from the representation on
`Γ^k` to the affine data representation.  This is the shape the two bounds through `Γ^k` control --
the synthesis is bounded on `Γ^k`, not on parameter `L²` -- so it is the shape in which a pair of
intertwiners is available at all. -/
abbrev QuadraticGammaMachine (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (k : ℕ) :=
  JointEquivariantMachine (quadraticSobolevContRepresentation lam k)
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation

/-- A ridgelet transform into the intermediate coefficient space. -/
abbrev QuadraticGammaRidgelet (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (k : ℕ) :=
  JointEquivariantRidgelet
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
    (quadraticSobolevContRepresentation lam k)

/-- **Section 7 through the intermediate space.**  A machine out of `Γ^k` and a ridgelet transform
into it compose to a scalar multiple of the identity, and a nonzero scalar makes the normalized
transform a right inverse of the machine.  This is the article's endpoint with the parameter space
taken to be the intermediate coefficient space rather than parameter `L²`, which is the pair shape
the two bounds of this file can produce.

Nothing is assumed: the Schur step uses the irreducibility of the affine data representation, proved
in `LeanRidgelet.HA.AffineMackey`, and the representation on `Γ^k` is
`LeanRidgelet.quadraticSobolevContRepresentation`.  What remains for a concrete pair is to factor
the two Bochner integrals through the space, which is what
`LeanRidgelet.exists_quadraticCompositeIntertwiner_of_bounds` is about. -/
theorem quadratic_gamma_reconstruction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (M : QuadraticGammaMachine lam k)
    (R : QuadraticGammaRidgelet lam k) :
    ∃ c : ℂ, jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      (c ≠ 0 → Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M)) := by
  obtain ⟨c, hc⟩ := ha_reconstruction_formula
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible
    (quadraticSobolevContRepresentation lam k) M R
  exact ⟨c, hc, fun hc0 ↦ ha_normalizedRidgelet_rightInverse M R hc hc0⟩

/-- **A nonzero constant through the intermediate space, from a probe.**  One datum whose image
under the composite is nonzero makes the constant nonzero, so the normalized transform inverts the
machine outright.  The reduction is the same as for the other shapes; only the parameter space
differs. -/
theorem quadratic_gamma_reconstruction_of_ne_zero (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (M : QuadraticGammaMachine lam k)
    (R : QuadraticGammaRidgelet lam k) (f : Lp ℂ 2 (volume : Measure E)) (hf : M (R f) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      jointReconstructionOperator M R =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) := by
  obtain ⟨c, hc, hright⟩ := quadratic_gamma_reconstruction lam k M R
  have hcne : c ≠ 0 := by
    intro hc0
    refine hf ?_
    have h : jointReconstructionOperator M R f = c • f := by simpa using congr($(hc) f)
    rw [hc0, zero_smul] at h
    exact h
  exact ⟨c, hcne, hc, hright hcne⟩

end LeanRidgelet
