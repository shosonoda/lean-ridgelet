/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.CodimOne
public import LeanRidgelet.FS.DPlane.Stiefel
public import LeanRidgelet.ToMathlib.LieGroup.StiefelCodimOne

/-!
# Fourier slice method, Case IV: the two developments agree at codimension one

`stiefelSynthesis` over the Stiefel manifold and `sphereSynthesis` over the sphere are two
presentations of the same layer. This file makes that a theorem rather than a resemblance, which is
the same status the transform itself has through `MeasureTheory.dPlaneTransform_codimOne`.

Three identifications go into it, all of them in `ToMathlib`: of the two parameter spaces, by
`MeasureTheory.stiefelHomeomorphSphere`; of the bias space `ℝ^1` with `ℝ`, by
`MeasureTheory.integral_euclideanSpace_fin_one`; and of the frame coordinate with the inner product
against the unit vector, which is `inner_dPlaneCoord` at `k = 1`.

## Main results

* `fs_stiefelSynthesis_codimOne`: at `k = 1` the general-codimension layer is the codimension-one
  layer, up to the total mass of the surface measure — the invariant measure on the Stiefel manifold
  being normalized to a probability measure and `Measure.toSphere` not.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The two developments agree at codimension one

`stiefelSynthesis` over the Stiefel manifold and `sphereSynthesis` over the sphere are the same
layer: at `k = 1` the parameter spaces are identified by `stiefelHomeomorphSphere`, the bias space
`ℝ^1` is identified with `ℝ`, and the two measures differ only by the normalization. So the general
codimension specializes to codimension one as a theorem, not as a resemblance.
-/

section CodimOneConsistency

open Metric

variable {m : ℕ}

/-- **The general-codimension layer is the codimension-one layer at `k = 1`.** The frame is its unit
vector, the bias `b : ℝ^1` is the scalar `b 0`, and the frame coordinate is the inner product with
the unit vector, by `inner_dPlaneCoord`. The scalar is the total mass of the surface measure because
`stiefelMeasure` is normalized to a probability measure and `Measure.toSphere` is not. -/
theorem fs_stiefelSynthesis_codimOne [Nontrivial (InputSpace m)]
    (L₀ : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] InputSpace m) (σ : ℝ → ℂ)
    (γ : sphere (0 : InputSpace m) 1 → ℝ → ℂ) (x : InputSpace m) :
    stiefelSynthesis (ContinuousLinearMap.stiefelMeasure L₀) (fun b => σ (b 0))
        (fun L b => γ (MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne) (b 0)) x
      = (((volume : Measure (InputSpace m)).toSphere.real Set.univ : ℝ)⁻¹ : ℝ) •
          sphereSynthesis σ γ x := by
  have hbias : ∀ L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] InputSpace m,
      (∫ b : EuclideanSpace ℝ (Fin 1),
        γ (MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne) (b 0) *
          σ ((dPlaneCoord L x - b) 0))
        = ∫ t : ℝ, γ (MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne) t *
            σ (inner ℝ ((MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne :
              InputSpace m)) x - t) := by
    intro L
    have hcoord : (dPlaneCoord L x) 0
        = inner ℝ ((MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne :
            InputSpace m)) x := by
      have h := inner_dPlaneCoord L x
        (MeasureTheory.unitVectorFinOne : EuclideanSpace ℝ (Fin 1))
      rw [MeasureTheory.coe_unitVectorFinOne] at h
      simpa [PiLp.inner_apply, RCLike.inner_apply] using h
    have hsub : ∀ b : EuclideanSpace ℝ (Fin 1),
        (dPlaneCoord L x - b) 0 = (dPlaneCoord L x) 0 - b 0 := fun b => rfl
    simp only [hsub, hcoord]
    exact MeasureTheory.integral_euclideanSpace_fin_one
      (fun t => γ (MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne) t *
        σ (inner ℝ ((MeasureTheory.frameDirection L MeasureTheory.unitVectorFinOne :
          InputSpace m)) x - t))
  rw [stiefelSynthesis, integral_congr_ae (Filter.Eventually.of_forall hbias),
    MeasureTheory.integral_stiefelMeasure_codimOne L₀
      (fun u : sphere (0 : InputSpace m) 1 =>
        ∫ t : ℝ, γ u t * σ (inner ℝ (u : InputSpace m) x - t)),
    sphereSynthesis]

end CodimOneConsistency
end LeanRidgelet
