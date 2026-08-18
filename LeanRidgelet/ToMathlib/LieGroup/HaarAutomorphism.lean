/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measure under a topological group automorphism

A continuous group automorphism with continuous inverse pushes Haar measure to a Haar measure, hence
to a positive finite multiple of the original one. Restricting to a set turns this into an exact
identity between the restricted image measure and the restriction to the image set, which is the
form needed when a compactly supported estimate has to be carried through a coordinate change such
as the contragredient map `L ↦ (L†)⁻¹` of a general linear group.

## Main results

* `MeasureTheory.exists_map_continuousMulEquiv_haar_eq_smul_haar`
* `MeasureTheory.exists_map_continuousMulEquiv_haar_restrict_eq_smul_haar_restrict`
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Pushing Haar measure forward along a topological group automorphism gives a positive finite
multiple of Haar measure. -/
theorem exists_map_continuousMulEquiv_haar_eq_smul_haar (σ : G ≃ₜ* G) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map σ (Measure.haar : Measure G) = c • (Measure.haar : Measure G) := by
  haveI : (Measure.map σ (Measure.haar : Measure G)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map (Measure.haar : Measure G) σ
  obtain ⟨k, hkpos, heq⟩ : ∃ k : ℝ≥0, 0 < k ∧
      Measure.map σ (Measure.haar : Measure G) = k • (Measure.haar : Measure G) :=
    ⟨Measure.haarScalarFactor (Measure.map σ (Measure.haar : Measure G))
        (Measure.haar : Measure G),
      Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
      Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨((k : ℝ≥0) : ℝ≥0∞), by simpa using hkpos.ne', ENNReal.coe_ne_top, ?_⟩
  apply Measure.ext
  intro s hs
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

/-- The image of a restricted Haar measure under a topological group automorphism is a positive
finite multiple of Haar measure restricted to the image set. -/
theorem exists_map_continuousMulEquiv_haar_restrict_eq_smul_haar_restrict (σ : G ≃ₜ* G)
    {s : Set G} (hs : MeasurableSet s) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map σ ((Measure.haar : Measure G).restrict s) =
        c • (Measure.haar : Measure G).restrict (σ '' s) := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_map_continuousMulEquiv_haar_eq_smul_haar (G := G) σ
  refine ⟨c, hc0, hctop, ?_⟩
  have hembedding : MeasurableEmbedding (σ : G → G) := σ.toHomeomorph.measurableEmbedding
  have himage : MeasurableSet ((σ : G → G) '' s) := hembedding.measurableSet_image' hs
  have hpreimage : (σ : G → G) ⁻¹' ((σ : G → G) '' s) = s :=
    Set.preimage_image_eq s σ.injective
  calc
    Measure.map σ ((Measure.haar : Measure G).restrict s) =
        Measure.map σ ((Measure.haar : Measure G).restrict
          ((σ : G → G) ⁻¹' ((σ : G → G) '' s))) := by rw [hpreimage]
    _ = (Measure.map σ (Measure.haar : Measure G)).restrict ((σ : G → G) '' s) :=
      (Measure.restrict_map hembedding.measurable himage).symm
    _ = (c • (Measure.haar : Measure G)).restrict ((σ : G → G) '' s) := by rw [hc]
    _ = c • (Measure.haar : Measure G).restrict ((σ : G → G) '' s) := Measure.restrict_smul c _ _

end MeasureTheory
