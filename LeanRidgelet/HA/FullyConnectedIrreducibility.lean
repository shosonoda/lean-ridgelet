/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Affine
public import LeanRidgelet.HA.FullyConnected
public import LeanRidgelet.ToMathlib.LieGroup.OrthogonalComplexification
public import LeanRidgelet.ToMathlib.LieGroup.UnitaryLp

/-!
# The product-group representation for fully-connected networks

This file constructs the representation used in Lemma 5.1 of arXiv:2405.13682 directly on the
Bochner space `L²(E;Y)`.  An output representation acts pointwise on `Y`, while the full affine
group acts by the determinant-corrected pullback on `E`.  The two actions commute, hence combine
to a unitary representation of the product group.  Its a.e. formula is

`((q,g) • f)(x) = |det g.linear|⁻¹ᐟ² • υ(q)[f(g⁻¹ x)]`.

Folland Theorem 7.12 proves the corresponding abstract outer-tensor-product statement.  Mathlib
does not currently provide the completed Hilbert tensor product or the canonical unitary
identification `L²(E;Y) ≃ Y ⊗₂ L²(E;ℂ)`.  For the finite-dimensional output spaces of Section 5,
we instead prove the endpoint directly on Bochner `L²`: matrix coefficients of an invariant
orthogonal projection are scalar by Schur for the affine factor; finite coordinate reconstruction
makes the projection pointwise; and Schur for the output factor makes it scalar.  Thus Lemma 5.1
is reduced only to the separately exposed scalar affine irreducibility endpoint.

## Deviations from the article

The article takes the standard representation of `O(m)` on `ℝ^m`.  The Schur development is over
complex Hilbert spaces, so the construction below accepts its complexified output representation
`υ`.  The final section supplies the coordinate realization on `EuclideanSpace ℂ ι`, specializes
the product action to `O(ι) × Aff(ι)`, and records its matrix formula.  Its output irreducibility
is proved in `ToMathlib.LieGroup.OrthogonalComplexification`; no irreducibility claim is stored in
the representation data.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix NNReal

namespace LeanRidgelet

variable {G E Y : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Every bounded value-space map intertwines the determinant-corrected affine pullbacks on the
corresponding Bochner `L²` spaces.  This naturality supplies both the coordinate embeddings and
coordinate projections used in the finite-output Schur argument. -/
theorem compLpL_intertwines_affineData {Z : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (L : Y →L[ℂ] Z) (g : E ≃ᵃ[ℝ] E) :
    (affineDataLpUnitaryRepresentation (Y := Z) (volume : Measure E) g :
        Lp Z 2 (volume : Measure E) →L[ℂ] Lp Z 2 (volume : Measure E)) ∘L
        L.compLpL 2 (volume : Measure E) =
      L.compLpL 2 (volume : Measure E) ∘L
        (affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g :
          Lp Y 2 (volume : Measure E) →L[ℂ] Lp Y 2 (volume : Measure E)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hleft := affineDataLpUnitaryRepresentation_apply_ae_vector
    (Y := Z) (volume : Measure E) g (L.compLpL 2 (volume : Measure E) f)
  have hright := L.coeFn_compLpL
    ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g).1 f)
  have haff := affineDataLpUnitaryRepresentation_apply_ae_vector
    (Y := Y) (volume : Measure E) g f
  have hpull :=
    (quasiMeasurePreserving_of_map_eq_withDensity affineDataJacobian
      affineData_measurable (affineData_group_map_eq_withDensity (volume : Measure E)) g)
      |>.ae_eq (L.coeFn_compLpL f)
  filter_upwards [hleft, hright, haff, hpull] with x hl hr ha hp
  change ((affineDataLpUnitaryRepresentation (Y := Z) (volume : Measure E) g).1
      (L.compLpL 2 (volume : Measure E) f)) x =
    (L.compLpL 2 (volume : Measure E)
      ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g).1 f)) x
  rw [hl, hr, ha]
  simp only [quasiRegularAction, Function.comp_apply] at hp ⊢
  rw [hp, map_smul]

/-- Pointwise output unitaries commute with the determinant-corrected affine pullback on
vector-valued `L²`. -/
theorem lpPointwise_commute_affineData (υ : UnitaryRepresentation G Y) (q : G)
    (g : E ≃ᵃ[ℝ] E) :
    Commute (υ.lpPointwise (μ := (volume : Measure E)) q)
      (affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have houtLeft := υ.lpPointwise_apply_ae q
    ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g).1 f)
  have haffLeft := affineDataLpUnitaryRepresentation_apply_ae_vector
    (Y := Y) (volume : Measure E) g f
  have haffRight := affineDataLpUnitaryRepresentation_apply_ae_vector
    (Y := Y) (volume : Measure E) g
      ((υ.lpPointwise (μ := (volume : Measure E)) q).1 f)
  have hout := υ.lpPointwise_apply_ae (μ := (volume : Measure E)) q f
  have houtPull :=
    (quasiMeasurePreserving_of_map_eq_withDensity affineDataJacobian
      affineData_measurable (affineData_group_map_eq_withDensity (volume : Measure E)) g)
      |>.ae_eq hout
  filter_upwards [houtLeft, haffLeft, haffRight, houtPull] with x hol hal har hop
  simp only [Function.comp_apply] at hop
  change ((υ.lpPointwise (μ := (volume : Measure E)) q).1
      ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g).1 f)) x =
    ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g).1
      ((υ.lpPointwise (μ := (volume : Measure E)) q).1 f)) x
  rw [hol, hal, har]
  simp only [quasiRegularAction]
  rw [hop]
  exact map_smul _ _ _

/-- The Section 5 product-group representation on `L²(E;Y)`: the first factor acts on output
values and the affine factor acts on the input variable. -/
def fullyConnectedLpUnitaryRepresentation (υ : UnitaryRepresentation G Y) :
    UnitaryRepresentation (G × (E ≃ᵃ[ℝ] E)) (Lp Y 2 (volume : Measure E)) :=
  UnitaryRepresentation.prodOfCommute
    (υ.lpPointwise (μ := (volume : Measure E)))
    (affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E))
    (lpPointwise_commute_affineData υ)

/-- The product representation has the determinant-corrected form stated in Section 5, with the
output unitary applied after affine pullback. -/
theorem fullyConnectedLpUnitaryRepresentation_apply_ae
    (υ : UnitaryRepresentation G Y) (g : G × (E ≃ᵃ[ℝ] E))
    (f : Lp Y 2 (volume : Measure E)) :
    (fullyConnectedLpUnitaryRepresentation υ g).1 f =ᵐ[volume]
      fun x ↦ radonNikodymWeight affineDataJacobian g.2 x •
        (υ g.1 : Y →L[ℂ] Y) (f (g.2⁻¹ • x)) := by
  have hout := υ.lpPointwise_apply_ae g.1
    ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g.2).1 f)
  have haff := affineDataLpUnitaryRepresentation_apply_ae_vector
    (Y := Y) (volume : Measure E) g.2 f
  filter_upwards [hout, haff] with x houtx haffx
  change ((υ.lpPointwise (μ := (volume : Measure E)) g.1).1
    ((affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E) g.2).1 f)) x = _
  rw [houtx, haffx]
  simp only [quasiRegularAction]
  rw [map_smul]

/-- The finite-output Bochner-`L²` form of Folland Theorem 7.12 needed in Section 5:
irreducibility of the value representation and of the scalar affine representation implies
irreducibility of their commuting product on `L²(E;Y)`.

The proof uses the finite-coordinate version in `ToMathlib.LieGroup.UnitaryLp`.  Naturality of
the affine pullback with respect to coordinate embeddings and projections replaces the unavailable
completed-Hilbert-tensor identification. -/
theorem fullyConnectedLpUnitaryRepresentation_isTopologicallyIrreducible_of
    [FiniteDimensional ℂ Y] (υ : UnitaryRepresentation G Y)
    (hυ : υ.IsTopologicallyIrreducible)
    (hAffine : (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
      |>.IsTopologicallyIrreducible) :
    (fullyConnectedLpUnitaryRepresentation (E := E) υ).IsTopologicallyIrreducible := by
  apply UnitaryRepresentation.prodOfCommute_isTopologicallyIrreducible_of_finiteDimensional
    υ
    (affineDataLpUnitaryRepresentation (Y := Y) (volume : Measure E))
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
  · intro g v
    simpa [ContinuousLinearMap.lpCoordinateEmbedding] using
      (compLpL_intertwines_affineData (E := E)
        (L := ContinuousLinearMap.toSpanSingleton ℂ v) g)
  · intro g v
    simpa [ContinuousLinearMap.lpCoordinateProjection] using
      (compLpL_intertwines_affineData (E := E) (L := innerSL ℂ v) g).symm
  · exact hυ
  · exact hAffine

section StandardOrthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (EuclideanSpace ℝ ι)] [BorelSpace (EuclideanSpace ℝ ι)]

/-- The concrete Section 5 representation of
`O(ι) × Aff(EuclideanSpace ℝ ι)` on vector-valued `L²`, with the standard orthogonal action on
the complexified output coordinates. -/
def standardOrthogonalAffineLpUnitaryRepresentation :
    UnitaryRepresentation
      (Matrix.orthogonalGroup ι ℝ ×
        (EuclideanSpace ℝ ι ≃ᵃ[ℝ] EuclideanSpace ℝ ι))
      (Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ ι))) :=
  fullyConnectedLpUnitaryRepresentation
    (Matrix.standardComplexOrthogonalRepresentation (ι := ι))

/-- The standard `O(ι) × Aff(ι)` representation acts by the article's determinant-corrected
affine pullback followed by complexified orthogonal matrix multiplication. -/
theorem standardOrthogonalAffineLpUnitaryRepresentation_apply_ae
    (g : Matrix.orthogonalGroup ι ℝ ×
      (EuclideanSpace ℝ ι ≃ᵃ[ℝ] EuclideanSpace ℝ ι))
    (f : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    (standardOrthogonalAffineLpUnitaryRepresentation g).1 f =ᵐ[volume]
      fun x ↦ radonNikodymWeight affineDataJacobian g.2 x •
        WithLp.toLp 2
          ((g.1.1.map (RCLike.ofReal : ℝ → ℂ)) *ᵥ WithLp.ofLp (f (g.2⁻¹ • x))) := by
  have h := fullyConnectedLpUnitaryRepresentation_apply_ae
    (Matrix.standardComplexOrthogonalRepresentation (ι := ι)) g f
  filter_upwards [h] with x hx
  change ((fullyConnectedLpUnitaryRepresentation
    (Matrix.standardComplexOrthogonalRepresentation (ι := ι)) g).1 f) x = _
  rw [hx]
  congr 1

/-- Lemma 5.1 for the standard complexified orthogonal output action, conditional only on scalar
affine irreducibility.  The latter remains the separately named Mackey-imprimitivity endpoint. -/
theorem standardOrthogonalAffineLpUnitaryRepresentation_isTopologicallyIrreducible_of
    [Nonempty ι]
    (hAffine :
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure (EuclideanSpace ℝ ι))).IsTopologicallyIrreducible) :
    standardOrthogonalAffineLpUnitaryRepresentation
      (ι := ι) |>.IsTopologicallyIrreducible := by
  change (fullyConnectedLpUnitaryRepresentation
    (E := EuclideanSpace ℝ ι)
    (Matrix.standardComplexOrthogonalRepresentation (ι := ι))).IsTopologicallyIrreducible
  apply fullyConnectedLpUnitaryRepresentation_isTopologicallyIrreducible_of
  · exact Matrix.standardComplexOrthogonalRepresentation_isTopologicallyIrreducible
  · exact hAffine

end StandardOrthogonal

end LeanRidgelet
