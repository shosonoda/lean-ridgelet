/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticSobolevSpace

/-!
# A carrier for the intermediate coefficient space

`LeanRidgelet.HA.QuadraticSobolevSpace` defines the order-`k` Sobolev seminorm in the constant
coefficient of the parameter and the predicate that it is finite, and says explicitly that it stops
there: no carrier, no completeness, no action on a carrier.  This file supplies those, and the
construction is shorter than the informal description suggests, for one reason.

*The carrier is `k + 1` copies of parameter `L²`.*  The seminorm is a sum of `L²` norms of the
derivatives, so the tuple of those derivatives lives in a finite product of copies of parameter
`L²`, and in the `ℓ¹` norm on that product the norm of the tuple is **literally** the seminorm --
no equivalence of norms and no constants.  The product is complete because each factor is, and the
space is a closed subspace of it, so completeness costs nothing.

*The action is the diagonal of an action already built.*  The parameter representation of
`LeanRidgelet.HA.QuadraticRelativeMeasure` multiplies by a Radon--Nikodym weight and pulls back;
its weight is a **constant** in the parameter, the reciprocal square root of the determinant of the
linear part, and pulling back commutes with differentiation in the constant coefficient because the
action is a shear there.  So the tuple map intertwines the parameter representation with its own
diagonal, and the diagonal of a unitary is an isometry of the `ℓ¹` product.  No new representation
is constructed and no new estimate is needed.

The space is defined as the closure of the span of the tuples of *smooth* coefficient functions of
finite seminorm.  That is the standard definition of a Sobolev space as a completion, and it is what
makes the space a legitimate carrier without a theory of weak derivatives: the derivative of an
almost-everywhere equivalence class is not defined, so a Sobolev space cannot be a subspace of `L²`
cut out by a pointwise condition, and taking the closure of the nice elements is the way around
that.  It also makes the space automatically closed under the action, since the action preserves
smoothness.

## Main results

* `LeanRidgelet.QuadraticSobolevCarrier`: the carrier, with
  `LeanRidgelet.norm_quadraticSobolevCarrier` giving its norm as a plain sum.
* `LeanRidgelet.quadraticSobolevJet`: the tuple of `L²` classes of the derivatives, with
  `LeanRidgelet.norm_quadraticSobolevJet`: its norm **is** the order-`k` Sobolev seminorm.
* `LeanRidgelet.quadraticSobolevSpace`: the space `Γ^k`, a closed submodule of the carrier, with
  `LeanRidgelet.isClosed_quadraticSobolevSpace` and the resulting `CompleteSpace` instance.
* `LeanRidgelet.quadraticSobolevCarrierAction`: the diagonal action, an isometric equivalence of the
  carrier, with `LeanRidgelet.quadraticSobolevCarrierAction_one` and
  `LeanRidgelet.quadraticSobolevCarrierAction_mul` making it a representation of the affine group.
* `LeanRidgelet.quadraticConstIteratedDeriv_quasiRegularAction`: the derivative in the constant
  coefficient commutes with the parameter representation's pointwise action, for a smooth
  coefficient function.  This is what makes the tuple map equivariant.
* `LeanRidgelet.quadraticSobolevSeminorm_quasiRegularAction`: the action preserves the seminorm
  **exactly**, the Radon--Nikodym weight cancelling the factor the plain pull-back picks up in
  `LeanRidgelet.quadraticSobolevSeminorm_comp_smul`; hence
  `LeanRidgelet.memQuadraticSobolev_quasiRegularAction`.
* `LeanRidgelet.quadraticSobolevCarrierAction_quadraticSobolevJet`: the tuple map is equivariant,
  and `LeanRidgelet.quadraticSobolevCarrierAction_mem_quadraticSobolevSpace`: **the space is
  invariant**, so the representation restricts to it.

## What is not done

The two Bochner integrals are not factored through the space: that the analysis transform lands in
it and that the synthesis integral is bounded on it are the two estimates
`LeanRidgelet.QuadraticAnalysisBound` and `LeanRidgelet.QuadraticSynthesisBound` of
`LeanRidgelet.HA.QuadraticNonzero`, and promoting them to operators on this carrier is what the
placeholder there still needs.  The restricted action *is* bundled, as
`LeanRidgelet.quadraticSobolevContRepresentation`, so the reconstruction argument can be run through
this space; what is missing is only the factorization of the two integrals through it.

## What is assumed

Nothing beyond what `LeanRidgelet.HA.QuadraticSobolevSpace` and
`LeanRidgelet.HA.QuadraticRelativeMeasure` already prove.  The parameter measure is an additive Haar
measure where the representation is used, as everywhere else in the track.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-! ### The carrier -/

/-- **The carrier of `Γ^k`.**  Order `k` means `k + 1` derivatives, so the carrier is `k + 1` copies
of parameter `L²`, taken in the `ℓ¹` norm.  The choice of `ℓ¹` is what makes
`LeanRidgelet.norm_quadraticSobolevJet` an equality rather than a two-sided estimate: the order-`k`
Sobolev seminorm is a plain sum of `L²` norms, and the `ℓ¹` norm of a tuple is a plain sum too. -/
abbrev QuadraticSobolevCarrier (lam : Measure (QuadraticParameter E)) (k : ℕ) : Type _ :=
  PiLp 1 fun _ : Fin (k + 1) => Lp ℂ 2 (quadraticRelativeMeasure lam)

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The norm on the carrier is the sum of the norms of the components. -/
theorem norm_quadraticSobolevCarrier (lam : Measure (QuadraticParameter E)) (k : ℕ)
    (x : QuadraticSobolevCarrier lam k) :
    ‖x‖ = ∑ j, ‖WithLp.ofLp x j‖ := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  simp

/-! ### The tuple of derivatives -/

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- Every derivative up to order `k` of a member of the space is an `L²` function for the parameter
measure: it is measurable by the membership predicate, and its `L²` norm is one term of a finite
sum. -/
theorem MemQuadraticSobolev.memLp_quadraticConstIteratedDeriv
    {lam : Measure (QuadraticParameter E)} {k j : ℕ} {T : QuadraticParameter E → ℂ}
    (h : MemQuadraticSobolev lam k T) (hj : j ≤ k) :
    MemLp (quadraticConstIteratedDeriv j T) 2 (quadraticRelativeMeasure lam) :=
  ⟨(h.measurable j hj).aestronglyMeasurable,
    lt_of_le_of_lt
      (eLpNorm_quadraticConstIteratedDeriv_le_quadraticSobolevSeminorm lam hj T)
      h.seminorm_lt_top⟩

/-- **The tuple of derivatives.**  A member of the space is sent to the tuple of the `L²` classes of
its derivatives in the constant coefficient, up to order `k`.  This is the map whose image spans the
space. -/
def quadraticSobolevJet (lam : Measure (QuadraticParameter E)) (k : ℕ)
    {T : QuadraticParameter E → ℂ} (h : MemQuadraticSobolev lam k T) :
    QuadraticSobolevCarrier lam k :=
  WithLp.toLp 1 fun j : Fin (k + 1) ↦
    (h.memLp_quadraticConstIteratedDeriv (Nat.lt_succ_iff.1 j.isLt)).toLp _

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The components of the tuple are the `L²` classes of the derivatives. -/
theorem quadraticSobolevJet_component (lam : Measure (QuadraticParameter E)) (k : ℕ)
    {T : QuadraticParameter E → ℂ} (h : MemQuadraticSobolev lam k T) (j : Fin (k + 1)) :
    WithLp.ofLp (quadraticSobolevJet lam k h) j =
      (h.memLp_quadraticConstIteratedDeriv (Nat.lt_succ_iff.1 j.isLt)).toLp _ := rfl

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The norm of the tuple is the seminorm.**  Not up to a constant and not up to equivalence of
norms: the `ℓ¹` norm of the tuple of derivatives is the order-`k` Sobolev seminorm of the
coefficient function.  This is the whole reason the carrier is taken in the `ℓ¹` norm. -/
theorem norm_quadraticSobolevJet (lam : Measure (QuadraticParameter E)) (k : ℕ)
    {T : QuadraticParameter E → ℂ} (h : MemQuadraticSobolev lam k T) :
    ‖quadraticSobolevJet lam k h‖ = (quadraticSobolevSeminorm lam k T).toReal := by
  rw [norm_quadraticSobolevCarrier, quadraticSobolevSeminorm,
    ENNReal.toReal_sum fun j hj ↦
      ((h.memLp_quadraticConstIteratedDeriv (Finset.mem_range_succ_iff.1 hj)).2).ne,
    ← Fin.sum_univ_eq_sum_range fun j ↦
      (eLpNorm (quadraticConstIteratedDeriv j T) 2 (quadraticRelativeMeasure lam)).toReal]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quadraticSobolevJet_component, Lp.norm_toLp]

/-! ### The space -/

/-- The tuples of the smooth members of the space.  Smoothness is what makes the derivative of a
sum the sum of the derivatives, so it is what makes the span below meaningful; and it is preserved
by the action, so the space is invariant. -/
def quadraticSobolevJets (lam : Measure (QuadraticParameter E)) (k : ℕ) :
    Set (QuadraticSobolevCarrier lam k) :=
  {x | ∃ T : QuadraticParameter E → ℂ, ∃ h : MemQuadraticSobolev lam k T,
    ContDiff ℝ k T ∧ quadraticSobolevJet lam k h = x}

/-- **The intermediate coefficient space `Γ^k`.**  The closure of the span of the tuples of the
smooth coefficient functions of finite order-`k` seminorm.  This is the standard construction of a
Sobolev space as a completion, and it is the construction the carrier forces: the derivative of an
almost-everywhere equivalence class is not defined, so `Γ^k` cannot be cut out of `L²` by a
pointwise condition. -/
def quadraticSobolevSpace (lam : Measure (QuadraticParameter E)) (k : ℕ) :
    Submodule ℂ (QuadraticSobolevCarrier lam k) :=
  (Submodule.span ℂ (quadraticSobolevJets lam k)).topologicalClosure

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The space is closed in the carrier. -/
theorem isClosed_quadraticSobolevSpace (lam : Measure (QuadraticParameter E)) (k : ℕ) :
    IsClosed (quadraticSobolevSpace lam k : Set (QuadraticSobolevCarrier lam k)) :=
  Submodule.isClosed_topologicalClosure _

/-- **The space is complete.**  A closed subspace of a finite product of `L²` spaces. -/
instance instCompleteSpaceQuadraticSobolevSpace (lam : Measure (QuadraticParameter E)) (k : ℕ) :
    CompleteSpace (quadraticSobolevSpace lam k) :=
  haveI : IsClosed (quadraticSobolevSpace lam k : Set (QuadraticSobolevCarrier lam k)) :=
    isClosed_quadraticSobolevSpace lam k
  IsClosed.completeSpace_coe

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The tuple of a smooth member lies in the space. -/
theorem quadraticSobolevJet_mem_quadraticSobolevSpace (lam : Measure (QuadraticParameter E))
    (k : ℕ) {T : QuadraticParameter E → ℂ} (h : MemQuadraticSobolev lam k T)
    (hT : ContDiff ℝ k T) :
    quadraticSobolevJet lam k h ∈ quadraticSobolevSpace lam k :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨T, h, hT, rfl⟩)

/-! ### Smoothness under the action and under a constant multiple -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The parameter action is a linear automorphism of a finite-dimensional space, hence smooth, so a
smooth coefficient function stays smooth when pulled back along it. -/
theorem contDiff_comp_quadraticParameterSMul {m : WithTop ℕ∞} {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ m T) (g : E ≃ᵃ[ℝ] E) :
    ContDiff ℝ m fun η : QuadraticParameter E ↦ T (g • η) := by
  have h : ContDiff ℝ m fun η : QuadraticParameter E ↦ g • η := by
    have he : (fun η : QuadraticParameter E ↦ g • η)
        = ((quadraticParameterLinearEquiv g).toLinearMap.toContinuousLinearMap :
            QuadraticParameter E → QuadraticParameter E) := rfl
    rw [he]
    exact ContinuousLinearMap.contDiff _
  exact hT.comp h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- A slice of a smooth coefficient function in the constant coefficient is smooth: the slice is the
composition with an affine map of the line. -/
theorem contDiff_quadraticConstSlice {m : WithTop ℕ∞} {T : QuadraticParameter E → ℂ}
    (hT : ContDiff ℝ m T) (p : QuadraticSymmetric E × E) :
    ContDiff ℝ m (quadraticConstSlice T p) :=
  hT.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The derivative in the constant coefficient commutes with a constant multiple.  Constants are the
only multipliers this is needed for, and it is where smoothness of the coefficient function is
spent. -/
theorem quadraticConstIteratedDeriv_const_smul {j k : ℕ} (hjk : j ≤ k)
    {T : QuadraticParameter E → ℂ} (hT : ContDiff ℝ k T) (c : ℂ) :
    quadraticConstIteratedDeriv j (fun η ↦ c • T η) =
      fun ξ ↦ c • quadraticConstIteratedDeriv j T ξ := by
  funext ξ
  have hslice : quadraticConstSlice (fun η ↦ c • T η) (ξ.1, ξ.2.1)
      = c • quadraticConstSlice T (ξ.1, ξ.2.1) := rfl
  have hcd : ContDiffAt ℝ (j : WithTop ℕ∞) (quadraticConstSlice T (ξ.1, ξ.2.1)) ξ.2.2 :=
    (contDiff_quadraticConstSlice (hT.of_le (by exact_mod_cast hjk)) (ξ.1, ξ.2.1)).contDiffAt
  change iteratedDeriv j (quadraticConstSlice (fun η ↦ c • T η) (ξ.1, ξ.2.1)) ξ.2.2 = _
  rw [hslice, iteratedDeriv_const_smul hcd c]
  rfl

/-! ### The derivative commutes with the parameter representation -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The Radon--Nikodym weight of the relatively invariant parameter measure does not depend on the
parameter: it is the reciprocal square root of the determinant of the linear part.  This is what
lets the weight pass through a derivative in the constant coefficient. -/
theorem radonNikodymWeight_quadraticRelativeParameterJacobian_const (g : E ≃ᵃ[ℝ] E)
    (ξ η : QuadraticParameter E) :
    radonNikodymWeight (quadraticRelativeParameterJacobian (E := E)) g ξ =
      radonNikodymWeight (quadraticRelativeParameterJacobian (E := E)) g η := rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- **The derivative in the constant coefficient commutes with the parameter representation.**  For
a smooth coefficient function, differentiating the corrected pullback in the constant coefficient is
the corrected pullback of the derivative.  Two facts combine: the correction is a constant in the
parameter, and the action is a shear in the constant coefficient, so the pullback commutes with the
derivative on the nose.  This is what makes the tuple map of this file equivariant. -/
theorem quadraticConstIteratedDeriv_quasiRegularAction {j k : ℕ} (hjk : j ≤ k)
    {T : QuadraticParameter E → ℂ} (hT : ContDiff ℝ k T) (g : E ≃ᵃ[ℝ] E) :
    quadraticConstIteratedDeriv j
        (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T) =
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (quadraticConstIteratedDeriv j T) := by
  set c : ℂ := radonNikodymWeight (quadraticRelativeParameterJacobian (E := E)) g 0 with hc
  have hshape : quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T
      = fun η : QuadraticParameter E ↦ c • T (g⁻¹ • η) := by
    funext η
    rw [quasiRegularAction_apply, hc,
      radonNikodymWeight_quadraticRelativeParameterJacobian_const g η 0]
  have hpull : ContDiff ℝ k fun η : QuadraticParameter E ↦ T (g⁻¹ • η) :=
    contDiff_comp_quadraticParameterSMul hT g⁻¹
  rw [hshape, quadraticConstIteratedDeriv_const_smul hjk hpull c]
  funext ξ
  rw [quasiRegularAction_apply, hc,
    radonNikodymWeight_quadraticRelativeParameterJacobian_const g ξ 0,
    quadraticConstIteratedDeriv_comp_smul j T g⁻¹]

/-! ### The action on the carrier -/

/-- The parameter representation at one group element, as an isometric equivalence of parameter
`L²`.  Only the unitarity of the representation is used. -/
def quadraticRelativeParameterLpIsometry (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    Lp ℂ 2 (quadraticRelativeMeasure lam) ≃ₗᵢ[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam) :=
  Unitary.linearIsometryEquiv (quadraticRelativeParameterLpUnitaryRepresentation lam g)

/-- The isometric equivalence is the representation's operator. -/
@[simp]
theorem quadraticRelativeParameterLpIsometry_apply (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 (quadraticRelativeMeasure lam)) :
    quadraticRelativeParameterLpIsometry lam g f =
      (quadraticRelativeParameterLpUnitaryRepresentation lam g :
        Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ]
          Lp ℂ 2 (quadraticRelativeMeasure lam)) f := rfl

/-- **The action on the carrier.**  The diagonal of the parameter representation: it acts on each
component of the tuple by the same operator.  Being the diagonal of a unitary, it is an isometric
equivalence of the `ℓ¹` product. -/
def quadraticSobolevCarrierAction (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (k : ℕ) (g : E ≃ᵃ[ℝ] E) :
    QuadraticSobolevCarrier lam k ≃ₗᵢ[ℂ] QuadraticSobolevCarrier lam k :=
  LinearIsometryEquiv.piLpCongrRight 1 fun _ ↦ quadraticRelativeParameterLpIsometry lam g

/-- The action acts componentwise. -/
@[simp]
theorem quadraticSobolevCarrierAction_component (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E) (x : QuadraticSobolevCarrier lam k)
    (j : Fin (k + 1)) :
    WithLp.ofLp (quadraticSobolevCarrierAction lam k g x) j =
      quadraticRelativeParameterLpIsometry lam g (WithLp.ofLp x j) := by
  simp [quadraticSobolevCarrierAction]

/-- The action is isometric, so it is bounded with norm one on the carrier. -/
theorem norm_quadraticSobolevCarrierAction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E) (x : QuadraticSobolevCarrier lam k) :
    ‖quadraticSobolevCarrierAction lam k g x‖ = ‖x‖ :=
  (quadraticSobolevCarrierAction lam k g).norm_map x

/-- The identity acts trivially. -/
theorem quadraticSobolevCarrierAction_one (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (x : QuadraticSobolevCarrier lam k) :
    quadraticSobolevCarrierAction lam k (1 : E ≃ᵃ[ℝ] E) x = x := by
  refine WithLp.ofLp_injective 1 (funext fun j ↦ ?_)
  rw [quadraticSobolevCarrierAction_component, quadraticRelativeParameterLpIsometry_apply,
    map_one]
  simp

/-- The action is multiplicative, so it is a representation of the affine group on the carrier. -/
theorem quadraticSobolevCarrierAction_mul (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g h : E ≃ᵃ[ℝ] E) (x : QuadraticSobolevCarrier lam k) :
    quadraticSobolevCarrierAction lam k (g * h) x =
      quadraticSobolevCarrierAction lam k g (quadraticSobolevCarrierAction lam k h x) := by
  refine WithLp.ofLp_injective 1 (funext fun j ↦ ?_)
  rw [quadraticSobolevCarrierAction_component, quadraticSobolevCarrierAction_component,
    quadraticSobolevCarrierAction_component, quadraticRelativeParameterLpIsometry_apply,
    quadraticRelativeParameterLpIsometry_apply, quadraticRelativeParameterLpIsometry_apply,
    map_mul]
  rfl

/-! ### The action preserves the space -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The corrected pullback of a smooth coefficient function is smooth. -/
theorem contDiff_quasiRegularAction {k : ℕ} {T : QuadraticParameter E → ℂ} (hT : ContDiff ℝ k T)
    (g : E ≃ᵃ[ℝ] E) :
    ContDiff ℝ k
      (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T) := by
  have hshape : quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T
      = fun η : QuadraticParameter E ↦
        radonNikodymWeight (quadraticRelativeParameterJacobian (E := E)) g 0 * T (g⁻¹ • η) := by
    funext η
    rw [quasiRegularAction_apply,
      radonNikodymWeight_quadraticRelativeParameterJacobian_const g η 0, smul_eq_mul]
  rw [hshape]
  exact contDiff_const.mul (contDiff_comp_quadraticParameterSMul hT g⁻¹)

/-- The image of an `L²` class under the parameter representation is represented by the corrected
pullback of any representative.  This is the bridge between the pointwise identity
`LeanRidgelet.quadraticConstIteratedDeriv_quasiRegularAction` and the `L²` classes the carrier is
built from; the transport of an almost-everywhere equality along the action is what
`LeanRidgelet.quadraticRelative_quasiRegularAction_congr_ae` supplies. -/
theorem coeFn_quadraticRelativeParameterLpIsometry_toLp
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E)
    {u : QuadraticParameter E → ℂ} (hu : MemLp u 2 (quadraticRelativeMeasure lam)) :
    (quadraticRelativeParameterLpIsometry lam g (hu.toLp u) : QuadraticParameter E → ℂ)
      =ᵐ[quadraticRelativeMeasure lam]
        quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g u :=
  (quasiInvariantLpUnitaryRepresentation_apply_ae quadraticRelativeParameterJacobian
    quadraticParameter_measurable (quadraticRelativeParameter_group_map_eq_withDensity lam)
    quadraticRelativeParameterJacobian_measurable quadraticRelativeParameterJacobian_ne_zero
    quadraticRelativeParameterJacobian_one quadraticRelativeParameterJacobian_cocycle g
    (hu.toLp u)).trans
      (quadraticRelative_quasiRegularAction_congr_ae lam g hu.coeFn_toLp)

/-- **The action is isometric on the seminorm.**  The corrected pullback of a smooth coefficient
function has the *same* order-`k` Sobolev seminorm.  Contrast
`LeanRidgelet.quadraticSobolevSeminorm_comp_smul`, where the plain pull-back scales the seminorm by
the square root of the determinant of the linear part: the Radon--Nikodym weight of the
representation is exactly that factor, and it cancels. -/
theorem quadraticSobolevSeminorm_quasiRegularAction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {k : ℕ} {T : QuadraticParameter E → ℂ}
    (h : MemQuadraticSobolev lam k T) (hT : ContDiff ℝ k T) (g : E ≃ᵃ[ℝ] E) :
    quadraticSobolevSeminorm lam k
        (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T) =
      quadraticSobolevSeminorm lam k T := by
  simp only [quadraticSobolevSeminorm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≤ k := Finset.mem_range_succ_iff.1 hj
  have hj' := h.memLp_quadraticConstIteratedDeriv hjk
  calc eLpNorm (quadraticConstIteratedDeriv j
        (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T)) 2
          (quadraticRelativeMeasure lam)
      = eLpNorm (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
          (quadraticConstIteratedDeriv j T)) 2 (quadraticRelativeMeasure lam) := by
        rw [quadraticConstIteratedDeriv_quasiRegularAction hjk hT g]
    _ = eLpNorm ((quadraticRelativeParameterLpIsometry lam g
          (hj'.toLp _) : QuadraticParameter E → ℂ)) 2 (quadraticRelativeMeasure lam) :=
        (eLpNorm_congr_ae (coeFn_quadraticRelativeParameterLpIsometry_toLp lam g hj')).symm
    _ = ‖quadraticRelativeParameterLpIsometry lam g (hj'.toLp _)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hj'.toLp (quadraticConstIteratedDeriv j T)‖ₑ :=
        (quadraticRelativeParameterLpIsometry lam g).enorm_map _
    _ = eLpNorm (quadraticConstIteratedDeriv j T) 2 (quadraticRelativeMeasure lam) :=
        Lp.enorm_toLp hj'

/-- **The action carries the space.**  The corrected pullback of a smooth member is a member. -/
theorem memQuadraticSobolev_quasiRegularAction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {k : ℕ} {T : QuadraticParameter E → ℂ}
    (h : MemQuadraticSobolev lam k T) (hT : ContDiff ℝ k T) (g : E ≃ᵃ[ℝ] E) :
    MemQuadraticSobolev lam k
      (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g T) :=
  memQuadraticSobolev_of_contDiff (contDiff_quasiRegularAction hT g)
    (by rw [quadraticSobolevSeminorm_quasiRegularAction lam h hT g]; exact h.seminorm_lt_top)

/-- **The tuple map is equivariant.**  The action on the carrier applied to the tuple of a smooth
member is the tuple of the corrected pullback of that member.  This is what makes the space
invariant. -/
theorem quadraticSobolevCarrierAction_quadraticSobolevJet (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {k : ℕ} {T : QuadraticParameter E → ℂ}
    (h : MemQuadraticSobolev lam k T) (hT : ContDiff ℝ k T) (g : E ≃ᵃ[ℝ] E) :
    quadraticSobolevCarrierAction lam k g (quadraticSobolevJet lam k h) =
      quadraticSobolevJet lam k (memQuadraticSobolev_quasiRegularAction lam h hT g) := by
  refine WithLp.ofLp_injective 1 (funext fun j ↦ ?_)
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.isLt
  rw [quadraticSobolevCarrierAction_component, quadraticSobolevJet_component,
    quadraticSobolevJet_component]
  refine Lp.ext ?_
  refine ((coeFn_quadraticRelativeParameterLpIsometry_toLp lam g
    (h.memLp_quadraticConstIteratedDeriv hjk)).trans ?_).trans (MemLp.coeFn_toLp _).symm
  rw [quadraticConstIteratedDeriv_quasiRegularAction hjk hT g]

/-- **The space is invariant.**  The action of the affine group on the carrier maps `Γ^k` into
itself, so the representation restricts to it.  The tuples of smooth members are carried among
themselves by the previous theorem, and a continuous linear map that carries a spanning set into a
closed subspace carries the closure of its span into it. -/
theorem quadraticSobolevCarrierAction_mem_quadraticSobolevSpace
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E)
    {x : QuadraticSobolevCarrier lam k} (hx : x ∈ quadraticSobolevSpace lam k) :
    quadraticSobolevCarrierAction lam k g x ∈ quadraticSobolevSpace lam k := by
  set L : QuadraticSobolevCarrier lam k →L[ℂ] QuadraticSobolevCarrier lam k :=
    (quadraticSobolevCarrierAction lam k g).toLinearIsometry.toContinuousLinearMap with hL
  have hclosed : IsClosed
      ((Submodule.comap (L : QuadraticSobolevCarrier lam k →ₗ[ℂ] QuadraticSobolevCarrier lam k)
        (quadraticSobolevSpace lam k) : Set (QuadraticSobolevCarrier lam k))) :=
    (isClosed_quadraticSobolevSpace lam k).preimage L.continuous
  have hsub : Submodule.span ℂ (quadraticSobolevJets lam k) ≤
      Submodule.comap (L : QuadraticSobolevCarrier lam k →ₗ[ℂ] QuadraticSobolevCarrier lam k)
        (quadraticSobolevSpace lam k) := by
    refine Submodule.span_le.2 fun y hy ↦ ?_
    obtain ⟨T, h, hT, rfl⟩ := hy
    change L (quadraticSobolevJet lam k h) ∈ quadraticSobolevSpace lam k
    have : L (quadraticSobolevJet lam k h)
        = quadraticSobolevCarrierAction lam k g (quadraticSobolevJet lam k h) := rfl
    rw [this, quadraticSobolevCarrierAction_quadraticSobolevJet lam h hT g]
    exact quadraticSobolevJet_mem_quadraticSobolevSpace lam k _
      (contDiff_quasiRegularAction hT g)
  exact Submodule.topologicalClosure_minimal _ hsub hclosed hx

/-! ### The representation on the space -/

/-- The action restricted to the space, as a bounded operator on it.  The restriction is legitimate
because the space is invariant. -/
def quadraticSobolevSpaceAction (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (k : ℕ) (g : E ≃ᵃ[ℝ] E) :
    quadraticSobolevSpace lam k →L[ℂ] quadraticSobolevSpace lam k :=
  (((quadraticSobolevCarrierAction lam k g).toLinearIsometry.toContinuousLinearMap).comp
      (quadraticSobolevSpace lam k).subtypeL).codRestrict (quadraticSobolevSpace lam k)
    fun x ↦ quadraticSobolevCarrierAction_mem_quadraticSobolevSpace lam k g x.2

@[simp]
theorem quadraticSobolevSpaceAction_coe (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E) (x : quadraticSobolevSpace lam k) :
    ((quadraticSobolevSpaceAction lam k g x : QuadraticSobolevCarrier lam k)) =
      quadraticSobolevCarrierAction lam k g (x : QuadraticSobolevCarrier lam k) := rfl

/-- The restricted action is isometric, being the restriction of an isometry. -/
theorem norm_quadraticSobolevSpaceAction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E) (x : quadraticSobolevSpace lam k) :
    ‖quadraticSobolevSpaceAction lam k g x‖ = ‖x‖ :=
  norm_quadraticSobolevCarrierAction lam k g (x : QuadraticSobolevCarrier lam k)

/-- The restricted action is multiplicative and unital, as a monoid homomorphism into the bounded
operators on the space. -/
def quadraticSobolevSpaceActionMonoidHom (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) :
    (E ≃ᵃ[ℝ] E) →* (quadraticSobolevSpace lam k →L[ℂ] quadraticSobolevSpace lam k) where
  toFun := quadraticSobolevSpaceAction lam k
  map_one' := ContinuousLinearMap.ext fun x ↦ Subtype.ext
    (quadraticSobolevCarrierAction_one lam k (x : QuadraticSobolevCarrier lam k))
  map_mul' g h := ContinuousLinearMap.ext fun x ↦ Subtype.ext
    (quadraticSobolevCarrierAction_mul lam k g h (x : QuadraticSobolevCarrier lam k))

/-- **The parameter representation on the intermediate coefficient space.**  The affine group acts
on `Γ^k` by the restriction of the diagonal of the parameter representation, isometrically.  This is
the packaging the boundedness route needs: with it, a machine out of `Γ^k` and a ridgelet transform
into it are intertwiners of representations, so the reconstruction argument applies through the
intermediate space rather than through parameter `L²`. -/
def quadraticSobolevContRepresentation (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) :
    ContRepresentation ℂ (E ≃ᵃ[ℝ] E) (quadraticSobolevSpace lam k) :=
  .ofMonoidHom (quadraticSobolevSpaceActionMonoidHom lam k)

@[simp]
theorem quadraticSobolevContRepresentation_apply (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (k : ℕ) (g : E ≃ᵃ[ℝ] E) :
    quadraticSobolevContRepresentation lam k g = quadraticSobolevSpaceAction lam k g := rfl

end LeanRidgelet
