/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The orthogonal group of a finite-dimensional inner product space, and its Haar measure

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib has the orthogonal group only as linear algebra: `Matrix.orthogonalGroup` is a submonoid of
matrices, with no topology, no compactness and no measure. What it does have is the unitary group of
a C\*-algebra, `unitary (E →L[𝕜] E)`, as a topological group whenever the star operation is
continuous, together with `unitary.linearIsometryEquiv`, the identification of its elements with the
linear isometry equivalences of `E`. That is the orthogonal group in the coordinate-free form this
project uses, and this file supplies what is missing from it: continuity of the adjoint, so that it
is a topological group at all; compactness in finite dimensions; and hence a Haar measure, which is
a probability measure because the group is compact.

The motivation is the invariant measure on the Stiefel manifold of orthonormal `k`-frames, which
the `d`-plane reconstruction formulas of the Fourier slice method need in codimension `k > 1`. A
frame is a linear isometry `ℝ^k →ₗᵢ E`, the orthogonal group acts on frames by post-composition,
and the invariant measure is the pushforward of the Haar measure along that action — so invariance
is true by construction rather than by a uniqueness argument.

## Main results

* `ContinuousLinearMap.instContinuousStar`: the adjoint is continuous, since it is an isometry. This
  is what turns Mathlib's `IsTopologicalGroup (unitary R)` into a statement about `E →L[𝕜] E`.
* `ContinuousLinearMap.norm_le_one_of_mem_unitary`: a unitary has operator norm at most one, so the
  unitary group is bounded.
* `ContinuousLinearMap.isCompact_unitary`: **the unitary group of a finite-dimensional inner
  product space is compact**, by Heine--Borel: it is closed by `isClosed_unitary` and bounded by the
  previous result, and the operator space is finite-dimensional hence proper.
* `ContinuousLinearMap.orthogonalHaar`: **the Haar probability measure on the orthogonal group.**
* A topology, a Borel structure, and the action of the orthogonal group on the space of linear
  isometries `F →ₗᵢ[ℝ] E`, which Mathlib leaves without any of the three.
* `ContinuousLinearMap.stiefelMeasure`: **the invariant measure on the Stiefel manifold**, the
  pushforward of `orthogonalHaar` along the action on a fixed frame, and
  `ContinuousLinearMap.map_stiefelAct_stiefelMeasure`: it is invariant, by construction.

* `ContinuousLinearMap.exists_stiefelAct_eq`: **the action is transitive on frames**, so
  `ContinuousLinearMap.stiefelMeasure_eq`: the measure does not depend on the frame it is built
  from; and `ContinuousLinearMap.map_comp_right_stiefelMeasure`: it is invariant under the right
  action `L ↦ L ∘ V` of the isometries of `F`, which is only a change of that frame.
* `ContinuousLinearMap.instIsMulRightInvariantOrthogonalHaar`: **the group is unimodular.** Mathlib
  derives right invariance from left invariance only for abelian groups; here it comes from
  compactness, and frame independence is what needs it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric

namespace ContinuousLinearMap

/-! ## Continuity of the adjoint -/

section Star

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The adjoint is continuous: it is an isometric equivalence of the operator space with itself.
Together with Mathlib's `IsTopologicalGroup (unitary R)` for a topological star monoid `R`, this is
what makes the unitary group of `E →L[𝕜] E` a topological group. -/
instance instContinuousStar : ContinuousStar (E →L[𝕜] E) where
  continuous_star := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E) (F := E)).isometry.continuous

end Star

/-! ## Compactness of the unitary group -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A unitary operator has operator norm at most one — exactly one unless the space is trivial, but
the inequality is what boundedness of the unitary group needs. -/
theorem norm_le_one_of_mem_unitary {u : E →L[ℝ] E} (hu : u ∈ unitary (E →L[ℝ] E)) : ‖u‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, u.norm_map_of_mem_unitary hu]

/-- **The orthogonal group of a finite-dimensional real inner product space is compact.** It is
closed because the defining equations are closed conditions and the star operation is continuous,
and bounded because a unitary has operator norm at most one; in finite dimensions the operator space
is proper, so Heine--Borel applies. -/
theorem isCompact_unitary : IsCompact (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)) :=
  isCompact_of_isClosed_isBounded isClosed_unitary
    (isBounded_iff_forall_norm_le.2 ⟨1, fun _ hu => norm_le_one_of_mem_unitary hu⟩)

instance instCompactSpaceUnitary : CompactSpace (unitary (E →L[ℝ] E)) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

/-! ## The Haar probability measure -/

/-- **The Haar probability measure on the orthogonal group.** The group is compact, so the Haar
measure normalized on the whole group is a probability measure, and that is the normalization an
invariant measure on a Stiefel manifold is built from. -/
def orthogonalHaar : Measure (unitary (E →L[ℝ] E)) := Measure.haarMeasure ⊤

instance instIsHaarMeasureOrthogonalHaar : (orthogonalHaar (E := E)).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance instIsProbabilityMeasureOrthogonalHaar :
    IsProbabilityMeasure (orthogonalHaar (E := E)) :=
  ⟨by
    rw [show (orthogonalHaar (E := E)) = Measure.haarMeasure ⊤ from rfl,
      ← TopologicalSpace.PositiveCompacts.coe_top (α := unitary (E →L[ℝ] E)),
      Measure.haarMeasure_self]⟩

/-- **The orthogonal group is unimodular**: its Haar measure is right invariant as well as left
invariant. Mathlib derives right invariance from left invariance only for abelian groups; here it
comes from compactness. Right translation of a left invariant measure is again left invariant, so by
uniqueness it is a scalar multiple of the Haar measure, and the scalar is the total mass, which is
`1` on both sides because the group is compact. -/
instance instIsMulRightInvariantOrthogonalHaar :
    (orthogonalHaar (E := E)).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : IsProbabilityMeasure (Measure.map (· * g) (orthogonalHaar (E := E))) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  have h := Measure.haarMeasure_unique (Measure.map (· * g) (orthogonalHaar (E := E))) ⊤
  rwa [TopologicalSpace.PositiveCompacts.coe_top, measure_univ, one_smul] at h

/-- A linear isometry of a finite-dimensional space into itself is an isometric equivalence, since
an injective endomorphism of a finite-dimensional space is surjective. -/
def isometryEquivOfIsometry (T : E →ₗᵢ[ℝ] E) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective T
    ((LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp T.injective)

@[simp] theorem isometryEquivOfIsometry_apply (T : E →ₗᵢ[ℝ] E) (x : E) :
    isometryEquivOfIsometry T x = T x := rfl

/-- An isometric equivalence of `E`, read as an element of the orthogonal group. -/
def unitaryOfIsometryEquiv (e : E ≃ₗᵢ[ℝ] E) : unitary (E →L[ℝ] E) :=
  Unitary.linearIsometryEquiv.symm e

@[simp] theorem coe_unitaryOfIsometryEquiv (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    (unitaryOfIsometryEquiv e : E →L[ℝ] E) x = e x := rfl

end Compact

/-! ## The Stiefel manifold and its invariant measure -/

section Stiefel

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The operator-norm topology on the space of linear isometries, induced from the continuous linear
maps. Mathlib gives `LinearIsometry` no topology, and the Stiefel manifold of orthonormal `k`-frames
in `E` is exactly `ℝ^k →ₗᵢ[ℝ] E`. -/
instance instTopologicalSpaceLinearIsometry : TopologicalSpace (F →ₗᵢ[ℝ] E) :=
  TopologicalSpace.induced LinearIsometry.toContinuousLinearMap inferInstance

instance instMeasurableSpaceLinearIsometry : MeasurableSpace (F →ₗᵢ[ℝ] E) := borel _

instance instBorelSpaceLinearIsometry : BorelSpace (F →ₗᵢ[ℝ] E) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_toContinuousLinearMap :
    Continuous (LinearIsometry.toContinuousLinearMap : (F →ₗᵢ[ℝ] E) → (F →L[ℝ] E)) :=
  continuous_induced_dom

/-- A unitary operator read as a linear isometry of `E`. -/
def unitaryIsometry (Q : unitary (E →L[ℝ] E)) : E →ₗᵢ[ℝ] E where
  toLinearMap := (Q : E →L[ℝ] E).toLinearMap
  norm_map' x := (Q : E →L[ℝ] E).norm_map_of_mem_unitary Q.property x

@[simp] theorem coe_unitaryIsometry (Q : unitary (E →L[ℝ] E)) (x : E) :
    unitaryIsometry Q x = (Q : E →L[ℝ] E) x := rfl

/-- The action of the orthogonal group of `E` on the Stiefel manifold of frames `F →ₗᵢ[ℝ] E`, by
post-composition. It is transitive on frames of a fixed dimension, which is why the pushforward of
the Haar measure along it does not depend on the frame chosen — a fact this file does not need and
does not prove. -/
def stiefelAct (Q : unitary (E →L[ℝ] E)) (L : F →ₗᵢ[ℝ] E) : F →ₗᵢ[ℝ] E :=
  (unitaryIsometry Q).comp L

@[simp] theorem stiefelAct_apply (Q : unitary (E →L[ℝ] E)) (L : F →ₗᵢ[ℝ] E) (x : F) :
    stiefelAct Q L x = (Q : E →L[ℝ] E) (L x) := rfl

theorem stiefelAct_one (L : F →ₗᵢ[ℝ] E) : stiefelAct 1 L = L := by
  ext x
  simp

theorem stiefelAct_mul (Q Q' : unitary (E →L[ℝ] E)) (L : F →ₗᵢ[ℝ] E) :
    stiefelAct (Q * Q') L = stiefelAct Q (stiefelAct Q' L) := by
  ext x
  simp [Submonoid.coe_mul]

theorem continuous_stiefelAct_right (Q : unitary (E →L[ℝ] E)) :
    Continuous (stiefelAct Q : (F →ₗᵢ[ℝ] E) → (F →ₗᵢ[ℝ] E)) := by
  refine continuous_induced_rng.2 ?_
  exact (ContinuousLinearMap.compL ℝ F E E (Q : E →L[ℝ] E)).continuous.comp
    continuous_toContinuousLinearMap

theorem continuous_stiefelAct_left (L : F →ₗᵢ[ℝ] E) :
    Continuous fun Q : unitary (E →L[ℝ] E) => stiefelAct Q L := by
  refine continuous_induced_rng.2 ?_
  exact ((ContinuousLinearMap.compL ℝ F E E).flip L.toContinuousLinearMap).continuous.comp
    continuous_induced_dom

/-- **The invariant measure on the Stiefel manifold of orthonormal frames**, the pushforward of the
Haar probability measure of the orthogonal group along its action on a fixed frame.

Building it this way makes invariance true by construction — see
`ContinuousLinearMap.map_stiefelAct_stiefelMeasure` — rather than something to be recovered from a
uniqueness theorem, which is what a construction by iterated sphere measures would need. -/
def stiefelMeasure (L : F →ₗᵢ[ℝ] E) : Measure (F →ₗᵢ[ℝ] E) :=
  Measure.map (fun Q => stiefelAct Q L) orthogonalHaar

instance instIsProbabilityMeasureStiefelMeasure (L : F →ₗᵢ[ℝ] E) :
    IsProbabilityMeasure (stiefelMeasure L) :=
  Measure.isProbabilityMeasure_map (continuous_stiefelAct_left L).measurable.aemeasurable

/-- **The Stiefel measure is invariant under the orthogonal group.** This is the property the
construction was chosen for, and the proof is left invariance of the Haar measure: acting by `Q` on
the pushforward along `Q' ↦ Q' L` is the pushforward along `Q' ↦ (Q Q') L`. -/
theorem map_stiefelAct_stiefelMeasure (Q : unitary (E →L[ℝ] E)) (L : F →ₗᵢ[ℝ] E) :
    Measure.map (stiefelAct Q) (stiefelMeasure L) = stiefelMeasure L := by
  rw [stiefelMeasure, Measure.map_map (continuous_stiefelAct_right Q).measurable
    (continuous_stiefelAct_left L).measurable]
  have hcomp : (stiefelAct Q ∘ fun Q' : unitary (E →L[ℝ] E) => stiefelAct Q' L)
      = (fun R : unitary (E →L[ℝ] E) => stiefelAct R L) ∘ (fun Q' => Q * Q') := by
    funext Q'
    simp only [Function.comp_apply, stiefelAct_mul]
  rw [hcomp, ← Measure.map_map (continuous_stiefelAct_left L).measurable
    (measurable_const_mul Q), map_mul_left_eq_self]

/-! ### Transitivity on frames, and independence of the base frame -/

/-- **The orthogonal group acts transitively on frames.** Two linear isometries of `F` into `E`
differ by an isometry of `E`: the map `L' ∘ L⁻¹`, defined on the range of `L`, extends to all of `E`
by `LinearIsometry.extend`, and in finite dimensions an isometry of `E` into itself is surjective,
hence a unitary. -/
theorem exists_stiefelAct_eq (L L' : F →ₗᵢ[ℝ] E) :
    ∃ Q : unitary (E →L[ℝ] E), stiefelAct Q L = L' := by
  refine ⟨unitaryOfIsometryEquiv (isometryEquivOfIsometry
    (L'.comp L.equivRange.symm.toLinearIsometry).extend), ?_⟩
  ext y
  have hy : (L y : E) = ((L.equivRange y : LinearMap.range L.toLinearMap) : E) := rfl
  rw [stiefelAct_apply, coe_unitaryOfIsometryEquiv, isometryEquivOfIsometry_apply, hy,
    LinearIsometry.extend_apply]
  simp

/-- **The Stiefel measure does not depend on the frame it is built from.** By transitivity the two
pushforwards differ by a right translation of the group, which the Haar measure does not see because
the group is unimodular. -/
theorem stiefelMeasure_eq (L L' : F →ₗᵢ[ℝ] E) : stiefelMeasure L = stiefelMeasure L' := by
  obtain ⟨Q₀, hQ₀⟩ := exists_stiefelAct_eq L L'
  have hcomp : (fun Q : unitary (E →L[ℝ] E) => stiefelAct Q L')
      = (fun R : unitary (E →L[ℝ] E) => stiefelAct R L) ∘ (fun Q => Q * Q₀) := by
    funext Q
    simp only [Function.comp_apply, stiefelAct_mul, ← hQ₀]
  rw [stiefelMeasure, stiefelMeasure, hcomp, ← Measure.map_map
    (continuous_stiefelAct_left L).measurable (measurable_mul_const Q₀), map_mul_right_eq_self]

/-- **The Stiefel measure is invariant under the right action of the isometries of the frame
space**, `L ↦ L ∘ V`. Precomposing by `V` only replaces the frame the measure is built from, and by
`stiefelMeasure_eq` every frame gives the same measure. -/
theorem map_comp_right_stiefelMeasure (V : F ≃ₗᵢ[ℝ] F) (L : F →ₗᵢ[ℝ] E) :
    Measure.map (fun M : F →ₗᵢ[ℝ] E => M.comp V.toLinearIsometry) (stiefelMeasure L)
      = stiefelMeasure L := by
  have hcont : Continuous fun M : F →ₗᵢ[ℝ] E => M.comp V.toLinearIsometry := by
    refine continuous_induced_rng.2 ?_
    exact ((ContinuousLinearMap.compL ℝ F F E).flip
      V.toLinearIsometry.toContinuousLinearMap).continuous.comp continuous_toContinuousLinearMap
  have hcomp : ((fun M : F →ₗᵢ[ℝ] E => M.comp V.toLinearIsometry) ∘
        fun Q : unitary (E →L[ℝ] E) => stiefelAct Q L)
      = fun Q : unitary (E →L[ℝ] E) => stiefelAct Q (L.comp V.toLinearIsometry) := by
    funext Q
    ext y
    simp
  rw [stiefelMeasure, Measure.map_map hcont.measurable (continuous_stiefelAct_left L).measurable,
    hcomp]
  exact stiefelMeasure_eq (L.comp V.toLinearIsometry) L

end Stiefel

end ContinuousLinearMap
