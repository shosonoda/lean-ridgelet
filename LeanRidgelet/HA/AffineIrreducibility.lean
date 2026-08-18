/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Affine
public import LeanRidgelet.ToMathlib.LieGroup.AffineSemidirect
public import LeanRidgelet.ToMathlib.LieGroup.GeneralLinearOrbit
public import LeanRidgelet.ToMathlib.LieGroup.StronglyContinuousConstDensity
public import LeanRidgelet.ToMathlib.LieGroup.UnitaryCharacter
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# Irreducibility of the affine data representation

This file develops Theorem 2.5 of arXiv:2405.13682 by the Mackey-machine route. The translation
subgroup is abelian. After Fourier transform, its characters are parametrized by the data space,
and the linear subgroup acts by the contragredient maps `L⁻ᵀ`. The nonzero characters form one
orbit and the omitted zero character is a null set. Thus the affine quasi-regular representation
is the representation induced from the character at any nonzero base point, with the trivial
representation of its little group; Mackey's irreducibility theorem then gives the result.

The orbit, conullness, inducing-subgroup, and character inputs are proved below.  Their
measure-theoretic connection with the explicit Fourier representation, together with the final
named theorem, is kept in `HA.AffineMackey` so this input module remains independent of the later
Fourier construction.  No missing analytic result is stored in a structure or typeclass.

For the one-dimensional subgroup with only positive dilations, the nonzero dual is instead the
disjoint union of the positive and negative orbits, so its natural `L²` representation splits into
two irreducibles. The full affine group used in the article includes all invertible linear maps;
in dimension one this includes negative dilations and joins those two half-line orbits.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The translation subgroup embedded in the full affine group. -/
def affineTranslation (b : E) : E ≃ᵃ[ℝ] E := AffineEquiv.constVAdd ℝ E b

/-- The general linear subgroup embedded in the full affine group. -/
def affineLinear (L : E ≃ₗ[ℝ] E) : E ≃ᵃ[ℝ] E := L.toAffineEquiv

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineTranslation_apply (b x : E) : affineTranslation b x = b + x := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineLinear_apply (L : E ≃ₗ[ℝ] E) (x : E) : affineLinear L x = L x := rfl

omit [FiniteDimensional ℝ E] in
/-- Every affine equivalence is a translation followed by its linear part. This is the concrete
semidirect-product decomposition used by the Mackey analysis. -/
theorem affine_eq_translation_mul_linear (g : E ≃ᵃ[ℝ] E) :
    g = affineTranslation (g 0) * affineLinear g.linear := by
  simpa only [affineTranslation, affineLinear] using
    (AffineEquiv.translation_mul_linear ℝ E g)

/-- The unique nonzero orbit for the dual action of the full affine linear subgroup. -/
def affineDualOrbit : Set E := {xi | xi ≠ 0}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem mem_affineDualOrbit {xi : E} : xi ∈ affineDualOrbit ↔ xi ≠ 0 := Iff.rfl

/-- The contragredient `GL(E)` action is transitive on the affine dual orbit. -/
theorem affineDualOrbit_transitive {xi eta : E} (hxi : xi ∈ affineDualOrbit)
    (heta : eta ∈ affineDualOrbit) :
    ∃ L : E ≃ₗ[ℝ] E, L.symm.adjoint xi = eta :=
  LinearEquiv.exists_symm_adjoint_apply_eq_of_ne_zero hxi heta

/-- The Mackey little group of a dual base point for the contragredient `GL(E)` action. -/
def affineDualLittleGroup (xi : E) : Subgroup (E ≃ₗ[ℝ] E) :=
  (MulAction.stabilizer (E ≃ₗ[ℝ] E) xi).comap LinearEquiv.contragredientHom

@[simp]
theorem mem_affineDualLittleGroup_iff {xi : E} {L : E ≃ₗ[ℝ] E} :
    L ∈ affineDualLittleGroup xi ↔ L.symm.adjoint xi = xi := Iff.rfl

/-- The translation character at a frequency `xi`, with the sign dictated by Mathlib's Fourier
transform convention. -/
def affineTranslationCharacter (xi : E) : AddChar E Circle where
  toFun b := Real.fourierChar (-⟪b, xi⟫_ℝ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' b c := by
    rw [inner_add_left, neg_add_rev, Real.fourierChar.map_add_eq_mul, mul_comm]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineTranslationCharacter_apply (xi b : E) :
    affineTranslationCharacter xi b = Real.fourierChar (-⟪b, xi⟫_ℝ) := rfl

omit [FiniteDimensional ℝ E] in
/-- The translation character is continuous. -/
theorem continuous_affineTranslationCharacter (xi : E) :
    Continuous (affineTranslationCharacter xi) := by
  exact Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg

/-- A member of the little group fixes the translation character under inverse linear
pullback. -/
theorem affineTranslationCharacter_linear_symm_apply {xi : E} {L : E ≃ₗ[ℝ] E}
    (hL : L ∈ affineDualLittleGroup xi) (b : E) :
    affineTranslationCharacter xi (L.symm b) = affineTranslationCharacter xi b := by
  simp only [affineTranslationCharacter_apply]
  congr 2
  change ⟪(L.symm : E →ₗ[ℝ] E) b, xi⟫_ℝ = ⟪b, xi⟫_ℝ
  change L.symm.adjoint xi = xi at hL
  rw [← LinearMap.adjoint_inner_right]
  change ⟪b, (L.symm.adjoint : E →ₗ[ℝ] E) xi⟫_ℝ = ⟪b, xi⟫_ℝ
  exact congrArg (fun eta ↦ ⟪b, eta⟫_ℝ) hL

/-- A member of the little group also fixes the translation character under forward linear
pullback. This is the form needed by the semidirect-product multiplication law. -/
theorem affineTranslationCharacter_linear_apply {xi : E} {L : E ≃ₗ[ℝ] E}
    (hL : L ∈ affineDualLittleGroup xi) (b : E) :
    affineTranslationCharacter xi (L b) = affineTranslationCharacter xi b := by
  have hInv : L⁻¹ ∈ affineDualLittleGroup xi := (affineDualLittleGroup xi).inv_mem hL
  have h := affineTranslationCharacter_linear_symm_apply hInv b
  change affineTranslationCharacter xi (L.symm.symm b) =
    affineTranslationCharacter xi b at h
  exact h

/-- The contragredient action of the topological general linear group on frequency space. -/
def affineTopologicalDualAction (L : (E →L[ℝ] E)ˣ) (xi : E) : E :=
  (↑(L⁻¹) : E →L[ℝ] E).adjoint xi

/-- The topological contragredient action as a homomorphism into the general linear group. -/
def affineTopologicalDualActionHom : (E →L[ℝ] E)ˣ →* (E ≃ₗ[ℝ] E) :=
  LinearEquiv.contragredientHom.comp
    (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E).toMonoidHom

@[simp]
theorem affineTopologicalDualActionHom_apply (L : (E →L[ℝ] E)ˣ) (xi : E) :
    affineTopologicalDualActionHom L xi = affineTopologicalDualAction L xi := rfl

@[simp]
theorem affineTopologicalDualAction_one (xi : E) :
    affineTopologicalDualAction (1 : (E →L[ℝ] E)ˣ) xi = xi := by
  change affineTopologicalDualActionHom 1 xi = xi
  rw [map_one]
  rfl

@[simp]
theorem affineTopologicalDualAction_mul (L M : (E →L[ℝ] E)ˣ) (xi : E) :
    affineTopologicalDualAction (L * M) xi =
      affineTopologicalDualAction L (affineTopologicalDualAction M xi) := by
  change affineTopologicalDualActionHom (L * M) xi =
    affineTopologicalDualActionHom L (affineTopologicalDualActionHom M xi)
  rw [map_mul]
  rfl

@[simp]
theorem affineTopologicalDualAction_eq_linearEquiv (L : (E →L[ℝ] E)ˣ) (xi : E) :
    affineTopologicalDualAction L xi =
      (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E L).symm.adjoint xi := rfl

/-- The topological contragredient action is jointly continuous. -/
theorem continuous_affineTopologicalDualAction :
    Continuous fun p : (E →L[ℝ] E)ˣ × E ↦ affineTopologicalDualAction p.1 p.2 := by
  have hinv : Continuous fun L : (E →L[ℝ] E)ˣ ↦ L⁻¹ := continuous_inv
  have hop : Continuous fun L : (E →L[ℝ] E)ˣ ↦ (↑(L⁻¹) : E →L[ℝ] E).adjoint :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).isometry.continuous.comp
      (Units.continuous_val.comp hinv)
  exact isBoundedBilinearMap_apply.continuous.comp
    ((hop.comp continuous_fst).prodMk continuous_snd)

/-- The orbit map of a fixed frequency under the topological general linear group is
continuous. -/
theorem continuous_affineTopologicalDualAction_orbit (xi : E) :
    Continuous fun L : (E →L[ℝ] E)ˣ ↦ affineTopologicalDualAction L xi :=
  continuous_affineTopologicalDualAction.comp (continuous_id.prodMk continuous_const)

/-- The Mackey little group as a closed subgroup of the topological general linear group. -/
def affineTopologicalDualLittleGroup (xi : E) : ClosedSubgroup (E →L[ℝ] E)ˣ where
  toSubgroup := (affineDualLittleGroup xi).comap
    (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E).toMonoidHom
  isClosed' := by
    change IsClosed {L : (E →L[ℝ] E)ˣ | affineTopologicalDualAction L xi = xi}
    exact isClosed_eq (continuous_affineTopologicalDualAction_orbit xi) continuous_const

@[simp]
theorem mem_affineTopologicalDualLittleGroup_iff {xi : E} {L : (E →L[ℝ] E)ˣ} :
    L ∈ affineTopologicalDualLittleGroup xi ↔ affineTopologicalDualAction L xi = xi := Iff.rfl

/-- The topological little group is locally compact because it is a closed subgroup of the
finite-dimensional general linear group. -/
noncomputable instance instLocallyCompactSpaceAffineTopologicalDualLittleGroup (xi : E) :
    LocallyCompactSpace (affineTopologicalDualLittleGroup xi) :=
  (affineTopologicalDualLittleGroup xi).isClosed'.locallyCompactSpace

/-- The topological general linear group acts transitively on nonzero frequencies. -/
theorem affineTopologicalDualOrbit_transitive {xi eta : E} (hxi : xi ∈ affineDualOrbit)
    (heta : eta ∈ affineDualOrbit) :
    ∃ L : (E →L[ℝ] E)ˣ, affineTopologicalDualAction L xi = eta := by
  obtain ⟨L, hL⟩ := affineDualOrbit_transitive hxi heta
  refine ⟨(AffineEquiv.continuousLinearUnitsEquivLinearEquiv E).symm L, ?_⟩
  simpa only [affineTopologicalDualAction_eq_linearEquiv,
    MulEquiv.apply_symm_apply] using hL

/-- A topological little-group element fixes the translation character under its forward action. -/
theorem affineTranslationCharacter_topological_linear_apply {xi : E}
    {L : (E →L[ℝ] E)ˣ} (hL : L ∈ affineTopologicalDualLittleGroup xi) (b : E) :
    affineTranslationCharacter xi ((L : E →L[ℝ] E) b) =
      affineTranslationCharacter xi b := by
  exact affineTranslationCharacter_linear_apply hL b

/-- The Mackey inducing subgroup `E ⋊ G_xi` inside the topological affine group. It contains all
translations and restricts the linear factor to the stabilizer of the frequency `xi`. -/
def affineTopologicalMackeySubgroup (xi : E) :
    ClosedSubgroup (AffineEquiv.TopologicalSemidirectProduct E) where
  toSubgroup := (affineTopologicalDualLittleGroup xi).comap SemidirectProduct.rightHom
  isClosed' := (affineTopologicalDualLittleGroup xi).isClosed'.preimage
    (SemidirectProduct.continuous_right
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E))

/-- The underlying subgroup of the closed Mackey inducing subgroup is closed.  This instance lets
Mathlib equip its homogeneous coset space with the separated quotient topology. -/
instance instIsClosedAffineTopologicalMackeySubgroup (xi : E) :
    IsClosed ((affineTopologicalMackeySubgroup xi).toSubgroup :
      Set (AffineEquiv.TopologicalSemidirectProduct E)) :=
  (affineTopologicalMackeySubgroup xi).isClosed'

/-- The homogeneous coset space of the affine group is second countable.  Recording the direct
quotient instance avoids making downstream Borel-space synthesis rediscover second countability of
the general linear factor. -/
noncomputable instance instSecondCountableTopologyAffineTopologicalMackeyQuotient (xi : E) :
    SecondCountableTopology
      (AffineEquiv.TopologicalSemidirectProduct E ⧸
        (affineTopologicalMackeySubgroup xi).toSubgroup) := by
  letI : SecondCountableTopology (E →L[ℝ] E)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  exact QuotientGroup.instSecondCountableTopology
    (affineTopologicalMackeySubgroup xi).toSubgroup

@[simp]
theorem mem_affineTopologicalMackeySubgroup_iff {xi : E}
    {p : AffineEquiv.TopologicalSemidirectProduct E} :
    p ∈ affineTopologicalMackeySubgroup xi ↔
      affineTopologicalDualAction p.right xi = xi := Iff.rfl

/-- The inducing subgroup is locally compact because it is closed in the locally compact affine
semidirect product. -/
noncomputable instance instLocallyCompactSpaceAffineTopologicalMackeySubgroup (xi : E) :
    LocallyCompactSpace (affineTopologicalMackeySubgroup xi) :=
  (affineTopologicalMackeySubgroup xi).isClosed'.locallyCompactSpace

/-- The homogeneous-space orbit map from the affine group to frequency space. Its translation
coordinate is ignored, as expected in Mackey theory. -/
def affineTopologicalMackeyOrbitMap (xi : E)
    (p : AffineEquiv.TopologicalSemidirectProduct E) : E :=
  affineTopologicalDualAction p.right xi

/-- The affine Mackey orbit map is continuous. -/
theorem continuous_affineTopologicalMackeyOrbitMap (xi : E) :
    Continuous (affineTopologicalMackeyOrbitMap xi) :=
  (continuous_affineTopologicalDualAction_orbit xi).comp
    (SemidirectProduct.continuous_right
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E))

/-- A nonzero base frequency stays nonzero along the affine dual orbit. -/
theorem affineTopologicalMackeyOrbitMap_ne_zero {xi : E} (hxi : xi ≠ 0)
    (p : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalMackeyOrbitMap xi p ≠ 0 := by
  intro h
  apply hxi
  apply (affineTopologicalDualActionHom p.right).injective
  simpa [affineTopologicalMackeyOrbitMap] using h

/-- The affine topological group action restricted to the nonzero dual orbit.  It is named rather
than installed globally so that it does not compete with other actions on the same subtype. -/
@[reducible] def affineTopologicalDualOrbitMulAction :
    MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) where
  smul p eta := ⟨affineTopologicalMackeyOrbitMap eta.1 p,
    affineTopologicalMackeyOrbitMap_ne_zero eta.2 p⟩
  one_smul eta := by
    apply Subtype.ext
    exact affineTopologicalDualAction_one eta.1
  mul_smul p q eta := by
    apply Subtype.ext
    exact affineTopologicalDualAction_mul p.right q.right eta.1

@[simp]
theorem affineTopologicalDualOrbitMulAction_smul
    (p : AffineEquiv.TopologicalSemidirectProduct E) (eta : affineDualOrbit (E := E)) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
      affineTopologicalDualOrbitMulAction
    p • eta = ⟨affineTopologicalMackeyOrbitMap eta.1 p,
      affineTopologicalMackeyOrbitMap_ne_zero eta.2 p⟩ := rfl

/-- The restricted affine dual action is jointly continuous. -/
theorem affineTopologicalDualOrbit_continuousSMul :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
      affineTopologicalDualOrbitMulAction
    ContinuousSMul (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
    affineTopologicalDualOrbitMulAction
  constructor
  exact (continuous_affineTopologicalDualAction.comp
    (((SemidirectProduct.continuous_right
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)).comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The full affine topological group acts transitively on the nonzero dual orbit. -/
theorem affineTopologicalDualOrbit_isPretransitive :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
      affineTopologicalDualOrbitMulAction
    MulAction.IsPretransitive (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
    affineTopologicalDualOrbitMulAction
  constructor
  intro eta zeta
  obtain ⟨L, hL⟩ := affineTopologicalDualOrbit_transitive eta.2 zeta.2
  refine ⟨SemidirectProduct.inr L, ?_⟩
  apply Subtype.ext
  exact hL

/-- The affine orbit map into the nonzero-frequency subtype is open.  This is the locally compact
open-mapping theorem for a continuous transitive action of a sigma-compact group. -/
theorem isOpenMap_affineTopologicalMackeyOrbitMap {xi : E} (hxi : xi ≠ 0) :
    IsOpenMap fun p : AffineEquiv.TopologicalSemidirectProduct E ↦
      (⟨affineTopologicalMackeyOrbitMap xi p,
        affineTopologicalMackeyOrbitMap_ne_zero hxi p⟩ : affineDualOrbit (E := E)) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E) (affineDualOrbit (E := E)) :=
    affineTopologicalDualOrbitMulAction
  letI : ContinuousSMul (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbit_continuousSMul
  letI : MulAction.IsPretransitive (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbit_isPretransitive
  letI : SecondCountableTopology (E →L[ℝ] E)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SigmaCompactSpace (AffineEquiv.TopologicalSemidirectProduct E) := inferInstance
  letI : BaireSpace (affineDualOrbit (E := E)) :=
    (isClosed_singleton : IsClosed ({0} : Set E)).isOpen_compl.baireSpace
  exact isOpenMap_smul_of_sigmaCompact (⟨xi, hxi⟩ : affineDualOrbit (E := E))

/-- For a nonzero base frequency, the affine orbit map is onto the full nonzero dual orbit. -/
theorem affineTopologicalMackeyOrbitMap_surjective {xi : E} (hxi : xi ≠ 0) :
    Function.Surjective fun p : AffineEquiv.TopologicalSemidirectProduct E ↦
      (⟨affineTopologicalMackeyOrbitMap xi p,
        affineTopologicalMackeyOrbitMap_ne_zero hxi p⟩ : affineDualOrbit) := by
  rintro ⟨eta, heta⟩
  obtain ⟨L, hL⟩ := affineTopologicalDualOrbit_transitive hxi heta
  refine ⟨SemidirectProduct.inr L, ?_⟩
  apply Subtype.ext
  exact hL

/-- Two affine elements have the same image under the orbit map exactly when they represent the
same left coset of the Mackey inducing subgroup. -/
theorem affineTopologicalMackeyOrbitMap_eq_iff_inv_mul_mem (xi : E)
    (p q : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalMackeyOrbitMap xi p = affineTopologicalMackeyOrbitMap xi q ↔
      p⁻¹ * q ∈ affineTopologicalMackeySubgroup xi := by
  change affineTopologicalDualActionHom p.right xi =
      affineTopologicalDualActionHom q.right xi ↔
    affineTopologicalDualActionHom (p.right⁻¹ * q.right) xi = xi
  rw [map_mul, map_inv]
  constructor
  · intro h
    rw [LinearEquiv.mul_apply, ← h]
    exact (affineTopologicalDualActionHom p.right).symm_apply_apply _
  · intro h
    have h' := congrArg (affineTopologicalDualActionHom p.right) h
    simpa [LinearEquiv.mul_apply] using h'.symm

/-- The orbit map descended to left cosets of the inducing subgroup. -/
def affineTopologicalMackeyQuotientOrbitMap {xi : E} (hxi : xi ≠ 0) :
    (AffineEquiv.TopologicalSemidirectProduct E ⧸
        (affineTopologicalMackeySubgroup xi).toSubgroup) →
      affineDualOrbit (E := E) :=
  Quotient.lift
    (fun p ↦ (⟨affineTopologicalMackeyOrbitMap xi p,
      affineTopologicalMackeyOrbitMap_ne_zero hxi p⟩ : affineDualOrbit (E := E))) <| by
      intro p q hpq
      apply Subtype.ext
      exact (affineTopologicalMackeyOrbitMap_eq_iff_inv_mul_mem xi p q).mpr
        (QuotientGroup.leftRel_apply.mp hpq)

@[simp]
theorem affineTopologicalMackeyQuotientOrbitMap_mk {xi : E} (hxi : xi ≠ 0)
    (p : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalMackeyQuotientOrbitMap hxi (QuotientGroup.mk p) =
      (⟨affineTopologicalMackeyOrbitMap xi p,
        affineTopologicalMackeyOrbitMap_ne_zero hxi p⟩ : affineDualOrbit (E := E)) := rfl

/-- The orbit map remains continuous after descending to the homogeneous left-coset space. -/
theorem continuous_affineTopologicalMackeyQuotientOrbitMap {xi : E} (hxi : xi ≠ 0) :
    Continuous (affineTopologicalMackeyQuotientOrbitMap hxi) := by
  exact ((continuous_affineTopologicalMackeyOrbitMap xi).subtype_mk
    (fun p ↦ affineTopologicalMackeyOrbitMap_ne_zero hxi p)).quotient_lift _

/-- The descended orbit map is open for the quotient topology on the homogeneous space. -/
theorem isOpenMap_affineTopologicalMackeyQuotientOrbitMap {xi : E} (hxi : xi ≠ 0) :
    IsOpenMap (affineTopologicalMackeyQuotientOrbitMap hxi) := by
  rw [QuotientGroup.isOpenQuotientMap_mk.isOpenMap_iff]
  exact isOpenMap_affineTopologicalMackeyOrbitMap hxi

/-- Algebraically, the homogeneous space of left cosets of the inducing subgroup is exactly the
nonzero dual orbit. This is the quotient identification used by the affine induced model. -/
noncomputable def affineTopologicalMackeyQuotientEquivDualOrbit {xi : E} (hxi : xi ≠ 0) :
    (AffineEquiv.TopologicalSemidirectProduct E ⧸
        (affineTopologicalMackeySubgroup xi).toSubgroup) ≃
      affineDualOrbit (E := E) :=
  Equiv.ofBijective (affineTopologicalMackeyQuotientOrbitMap hxi) <| by
    constructor
    · intro a b hab
      revert hab
      refine Quotient.inductionOn₂' a b ?_
      intro p q hpq
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      exact (affineTopologicalMackeyOrbitMap_eq_iff_inv_mul_mem xi p q).mp
        (congrArg Subtype.val hpq)
    · intro eta
      obtain ⟨p, hp⟩ := affineTopologicalMackeyOrbitMap_surjective hxi eta
      exact ⟨QuotientGroup.mk p, hp⟩

/-- The forward direction of the algebraic quotient-orbit equivalence is continuous. Together
with the openness theorem above, this bundles into the homeomorphism below. -/
theorem continuous_affineTopologicalMackeyQuotientEquivDualOrbit {xi : E} (hxi : xi ≠ 0) :
    Continuous (affineTopologicalMackeyQuotientEquivDualOrbit hxi) :=
  continuous_affineTopologicalMackeyQuotientOrbitMap hxi

/-- The homogeneous left-coset space is homeomorphic to the nonzero dual orbit. -/
noncomputable def affineTopologicalMackeyQuotientHomeomorphDualOrbit {xi : E} (hxi : xi ≠ 0) :
    (AffineEquiv.TopologicalSemidirectProduct E ⧸
        (affineTopologicalMackeySubgroup xi).toSubgroup) ≃ₜ
      affineDualOrbit (E := E) :=
  (affineTopologicalMackeyQuotientEquivDualOrbit hxi).toHomeomorphOfContinuousOpen
    (continuous_affineTopologicalMackeyQuotientEquivDualOrbit hxi)
    (isOpenMap_affineTopologicalMackeyQuotientOrbitMap hxi)

/-- The quotient-orbit homeomorphism intertwines left translation on the homogeneous space with
the affine dual action on the nonzero orbit. -/
theorem affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineEquiv.TopologicalSemidirectProduct E ⧸
      (affineTopologicalMackeySubgroup xi).toSubgroup) :
    letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
        (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
    affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi (g • q) =
      g • affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  refine Quotient.inductionOn' q ?_
  intro p
  apply Subtype.ext
  exact affineTopologicalDualAction_mul g.right p.right xi

/-- Include the full translation subgroup in the Mackey inducing subgroup. -/
def affineTopologicalMackeyTranslationHom (xi : E) :
    Multiplicative E →* affineTopologicalMackeySubgroup xi where
  toFun b := ⟨SemidirectProduct.inl b, by
    change (1 : (E →L[ℝ] E)ˣ) ∈ affineTopologicalDualLittleGroup xi
    exact (affineTopologicalDualLittleGroup xi).one_mem⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' b c := by
    apply Subtype.ext
    simp

/-- Include the little group as the linear factor of the Mackey inducing subgroup. -/
def affineTopologicalMackeyLittleGroupHom (xi : E) :
    affineTopologicalDualLittleGroup xi →*
      affineTopologicalMackeySubgroup xi where
  toFun L := ⟨SemidirectProduct.inr L.1, L.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' L M := by
    apply Subtype.ext
    simp

/-- The character of the inducing subgroup: it is the frequency character on translations and
is trivial on the little group. -/
def affineTopologicalMackeyCharacter (xi : E) :
    affineTopologicalMackeySubgroup xi →* Circle where
  toFun p := affineTranslationCharacter xi p.1.left.toAdd
  map_one' := by simp
  map_mul' p q := by
    change affineTranslationCharacter xi
        (p.1.left.toAdd + (p.1.right : E →L[ℝ] E) q.1.left.toAdd) =
      affineTranslationCharacter xi p.1.left.toAdd *
        affineTranslationCharacter xi q.1.left.toAdd
    rw [(affineTranslationCharacter xi).map_add_eq_mul]
    congr 1
    exact affineTranslationCharacter_topological_linear_apply p.property q.1.left.toAdd

@[simp]
theorem affineTopologicalMackeyCharacter_apply (xi : E)
    (p : affineTopologicalMackeySubgroup xi) :
    affineTopologicalMackeyCharacter xi p =
      affineTranslationCharacter xi p.1.left.toAdd := rfl

/-- On the translation subgroup, the inducing character is exactly the frequency character. -/
theorem affineTopologicalMackeyCharacter_comp_translation (xi : E) :
    (affineTopologicalMackeyCharacter xi).comp
        (affineTopologicalMackeyTranslationHom xi) =
      (affineTranslationCharacter xi).toMonoidHom := by
  ext b
  rfl

/-- On the little group, the inducing character is trivial. -/
theorem affineTopologicalMackeyCharacter_comp_littleGroup (xi : E) :
    (affineTopologicalMackeyCharacter xi).comp
        (affineTopologicalMackeyLittleGroupHom xi) = 1 := by
  ext L
  simp [affineTopologicalMackeyCharacter, affineTopologicalMackeyLittleGroupHom]

/-- The inducing character is continuous. -/
theorem continuous_affineTopologicalMackeyCharacter (xi : E) :
    Continuous (affineTopologicalMackeyCharacter xi) := by
  exact (continuous_affineTranslationCharacter xi).comp
    ((SemidirectProduct.continuous_left
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)).comp continuous_subtype_val)

/-- The one-dimensional unitary representation of the Mackey inducing subgroup. -/
def affineTopologicalMackeyUnitaryRepresentation (xi : E) :
    UnitaryRepresentation (affineTopologicalMackeySubgroup xi) ℂ :=
  UnitaryRepresentation.ofCircleCharacter (affineTopologicalMackeyCharacter xi)

/-- The Mackey inducing representation is strongly continuous. -/
theorem affineTopologicalMackeyUnitaryRepresentation_isStronglyContinuous (xi : E) :
    (affineTopologicalMackeyUnitaryRepresentation xi).IsStronglyContinuous :=
  UnitaryRepresentation.ofCircleCharacter_isStronglyContinuous _
    (continuous_affineTopologicalMackeyCharacter xi)

/-- The Mackey inducing representation is irreducible because its Hilbert space is the complex
line. -/
theorem affineTopologicalMackeyUnitaryRepresentation_isTopologicallyIrreducible (xi : E) :
    (affineTopologicalMackeyUnitaryRepresentation xi).IsTopologicallyIrreducible :=
  UnitaryRepresentation.ofCircleCharacter_isTopologicallyIrreducible _

@[simp]
theorem affineTopologicalMackeyUnitaryRepresentation_translation_apply (xi : E)
    (b : Multiplicative E) (z : ℂ) :
    ((affineTopologicalMackeyUnitaryRepresentation xi
        (affineTopologicalMackeyTranslationHom xi b) : ℂ →L[ℂ] ℂ) z) =
      (affineTranslationCharacter xi b.toAdd : ℂ) * z := by
  rfl

@[simp]
theorem affineTopologicalMackeyUnitaryRepresentation_littleGroup_apply (xi : E)
    (L : affineTopologicalDualLittleGroup xi) (z : ℂ) :
    ((affineTopologicalMackeyUnitaryRepresentation xi
        (affineTopologicalMackeyLittleGroupHom xi L) : ℂ →L[ℂ] ℂ) z) = z := by
  simp [affineTopologicalMackeyUnitaryRepresentation, affineTopologicalMackeyCharacter,
    affineTopologicalMackeyLittleGroupHom]

section Measure

variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
/-- The corrected affine `L²` action has the expected determinant-weighted pullback as an a.e.
representative. -/
theorem affineDataLpUnitaryRepresentation_apply_ae (mu : Measure E) [mu.IsAddHaarMeasure]
    [SigmaFinite mu] (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 mu) :
    ((↑(affineDataLpUnitaryRepresentation (Y := ℂ) mu g) :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) f) =ᵐ[mu]
      fun x ↦ ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) • f (g.symm x) := by
  have h := quasiInvariantLpUnitaryRepresentation_apply_ae (E := ℂ) affineDataJacobian
    affineData_measurable (affineData_group_map_eq_withDensity mu)
    affineDataJacobian_measurable affineDataJacobian_ne_zero affineDataJacobian_one
    affineDataJacobian_cocycle g f
  filter_upwards [h] with x hx
  exact hx

omit [Nontrivial E] in
/-- On the translation subgroup the Jacobian disappears, leaving ordinary translation of the
argument. -/
theorem affineDataLpUnitaryRepresentation_translation_apply_ae
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu] (b : E) (f : Lp ℂ 2 mu) :
    ((↑(affineDataLpUnitaryRepresentation (Y := ℂ) mu (affineTranslation b)) :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) f) =ᵐ[mu]
      fun x ↦ f (x - b) := by
  simpa [affineTranslation, affineDataJacobian, sub_eq_add_neg, add_comm] using
    (affineDataLpUnitaryRepresentation_apply_ae mu (affineTranslation b) f)

omit [Nontrivial E] in
/-- On the linear subgroup the action is the determinant-weighted pullback by `L⁻¹`. -/
theorem affineDataLpUnitaryRepresentation_linear_apply_ae
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu]
    (L : E ≃ₗ[ℝ] E) (f : Lp ℂ 2 mu) :
    ((↑(affineDataLpUnitaryRepresentation (Y := ℂ) mu (affineLinear L)) :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) f) =ᵐ[mu]
      fun x ↦ ((‖LinearMap.det (L : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) • f (L.symm x) := by
  have h := affineDataLpUnitaryRepresentation_apply_ae mu (affineLinear L) f
  filter_upwards [h] with x hx
  exact hx

/-- The affine data representation, reindexed by the locally compact semidirect-product model of
the affine group.  This is the group model to which locally compact Mackey theory applies. -/
noncomputable def affineTopologicalLpUnitaryRepresentation
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu] :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E) (Lp ℂ 2 mu) :=
  (affineDataLpUnitaryRepresentation (Y := ℂ) mu).restrict
    (AffineEquiv.topologicalSemidirectProductEquiv E).toMonoidHom

omit [Nontrivial E] in
@[simp]
theorem affineTopologicalLpUnitaryRepresentation_apply
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu]
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalLpUnitaryRepresentation mu g =
      affineDataLpUnitaryRepresentation (Y := ℂ) mu
        (AffineEquiv.topologicalSemidirectProductEquiv E g) := rfl

/-- The finite measure-density multiplier of the inverse affine map in topological semidirect-
product coordinates. -/
def affineTopologicalJacobian (g : AffineEquiv.TopologicalSemidirectProduct E) : ℝ≥0 :=
  ‖LinearMap.det ((g.right : E →L[ℝ] E) : E →ₗ[ℝ] E)‖₊

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The affine determinant multiplier is continuous in the locally compact semidirect-product
topology. -/
theorem continuous_affineTopologicalJacobian :
    Continuous (affineTopologicalJacobian (E := E)) := by
  exact (ContinuousLinearMap.continuous_det.comp <|
    Units.continuous_val.comp <|
      SemidirectProduct.continuous_right
        (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)).nnnorm

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The affine determinant multiplier is everywhere positive. -/
theorem affineTopologicalJacobian_ne_zero
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalJacobian g ≠ 0 := by
  simp only [affineTopologicalJacobian, ne_eq, nnnorm_eq_zero]
  exact (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E g.right).isUnit_det'.ne_zero

omit [Nontrivial E] in
/-- The inverse affine map rescales additive Haar measure by the topological affine Jacobian. -/
theorem affineTopologicalInverse_map_eq_smul (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    mu.map (AffineEquiv.topologicalSemidirectProductInverseContinuousMap E g) =
      (affineTopologicalJacobian g : ℝ≥0∞) • mu := by
  rw [show (AffineEquiv.topologicalSemidirectProductInverseContinuousMap E g : E → E) =
      (AffineEquiv.topologicalSemidirectProductEquiv E g).symm by
    funext x
    exact AffineEquiv.topologicalSemidirectProductInverseContinuousMap_apply E g x]
  rw [Measure.map_affineEquiv_symm_addHaar_eq_withDensity, withDensity_const]
  rfl

omit [Nontrivial E] in
/-- The topologically reindexed affine representation has the constant-density corrected
pullback formula required by the general strong-continuity theorem. -/
theorem affineTopologicalLpUnitaryRepresentation_apply_ae
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu]
    (g : AffineEquiv.TopologicalSemidirectProduct E) (f : Lp ℂ 2 mu) :
    ((affineTopologicalLpUnitaryRepresentation mu g :
        Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) f) =ᵐ[mu]
      fun x ↦ (((affineTopologicalJacobian g).sqrt : ℂ)⁻¹) •
        f (AffineEquiv.topologicalSemidirectProductInverseContinuousMap E g x) := by
  simpa only [affineTopologicalLpUnitaryRepresentation_apply,
    affineTopologicalJacobian, AffineEquiv.det_topologicalSemidirectProductEquiv_linear,
    AffineEquiv.topologicalSemidirectProductInverseContinuousMap_apply] using
      affineDataLpUnitaryRepresentation_apply_ae mu
        (AffineEquiv.topologicalSemidirectProductEquiv E g) f

omit [Nontrivial E] in
/-- The determinant-corrected affine `L²` representation is strongly continuous on the locally
compact semidirect-product model of the affine group. -/
theorem affineTopologicalLpUnitaryRepresentation_isStronglyContinuous
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu]
    [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] :
    (affineTopologicalLpUnitaryRepresentation mu).IsStronglyContinuous := by
  exact UnitaryRepresentation.isStronglyContinuous_of_const_density
    (affineTopologicalLpUnitaryRepresentation mu)
    (AffineEquiv.topologicalSemidirectProductInverseContinuousMap E)
    affineTopologicalJacobian
    (AffineEquiv.continuous_topologicalSemidirectProductInverseContinuousMap E)
    continuous_affineTopologicalJacobian affineTopologicalJacobian_ne_zero
    (affineTopologicalInverse_map_eq_smul mu)
    (affineTopologicalLpUnitaryRepresentation_apply_ae mu)

omit [Nontrivial E] in
/-- Reindexing the affine group by its locally compact semidirect-product model preserves and
reflects topological irreducibility. -/
theorem affineTopologicalLpUnitaryRepresentation_isTopologicallyIrreducible_iff
    (mu : Measure E) [mu.IsAddHaarMeasure] [SigmaFinite mu] :
    UnitaryRepresentation.IsTopologicallyIrreducible
        (affineTopologicalLpUnitaryRepresentation mu) ↔
      UnitaryRepresentation.IsTopologicallyIrreducible
        (affineDataLpUnitaryRepresentation (Y := ℂ) mu) :=
  UnitaryRepresentation.restrict_isTopologicallyIrreducible_iff_of_surjective
    (affineDataLpUnitaryRepresentation (Y := ℂ) mu)
    (AffineEquiv.topologicalSemidirectProductEquiv E).toMonoidHom
    (AffineEquiv.topologicalSemidirectProductEquiv E).surjective

/-- The affine dual orbit is conull for every additive Haar measure. -/
theorem affineDualOrbit_ae_eq_univ (mu : Measure E) [mu.IsAddHaarMeasure] :
    affineDualOrbit (E := E) =ᵐ[mu] Set.univ := by
  exact MeasureTheory.setOf_ne_zero_ae_eq_univ mu

end Measure

end LeanRidgelet
