/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.DPlaneTransform
public import LeanRidgelet.ToMathlib.LieGroup.SphereInvariantMeasure

/-!
# The Stiefel manifold at codimension one is the unit sphere

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

An orthonormal `1`-frame is a unit vector, so the Stiefel manifold `V_{m,1}` is the sphere
`𝕊^{m-1}`. `ToMathlib.DPlaneTransform` has the algebra of that identification —
`MeasureTheory.frameVectorCodimOne` and `MeasureTheory.frameOfUnitVector` are mutually inverse — and
`ToMathlib.LieGroup.SphereInvariantMeasure` has the measure theory of both sides. This file joins
them: the identification is a homeomorphism, and it carries the invariant measure of the Stiefel
manifold to the *normalized* surface measure, the normalization being the only difference between
the two sides (`MeasureTheory.ContinuousLinearMap.stiefelMeasure` is a probability measure, whereas
`MeasureTheory.Measure.toSphere` has total mass `|𝕊^{m-1}|`).

The point of having this as a theorem rather than a remark is that a development in general
codimension over the Stiefel manifold and a development at codimension one over the sphere are then
provably the same construction, not two constructions that resemble each other.

## Main results

* `MeasureTheory.stiefelHomeomorphSphere`: the identification `V_{m,1} ≃ₜ 𝕊^{m-1}`, given by
  `L ↦ L e₀` with inverse `u ↦ (b ↦ b 0 • u)`.
* `MeasureTheory.measurePreserving_stiefelHomeomorphSphere`: it carries the invariant measure to the
  normalized surface measure. This is `MeasureTheory.map_frameDirection_stiefelMeasure` read through
  the identification.
* `MeasureTheory.integral_stiefelMeasure_codimOne`: the resulting change of variables for integrals,
  `∫ L, g(L e₀) dL = |𝕊^{m-1}|⁻¹ ∫_{𝕊^{m-1}} g(u) du`, with no measurability hypothesis on `g`
  because the change of variables is along an equivalence.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Building a codimension-one frame out of a unit vector is continuous: as a continuous linear map
the frame is `MeasureTheory.EuclideanSpace.proj 0` tensored with the vector, and that is bilinear
and bounded. -/
theorem continuous_frameOfUnitVector :
    Continuous (frameOfUnitVector :
      sphere (0 : E) 1 → (EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E)) := by
  refine continuous_induced_rng.2 ?_
  have hclm : (LinearIsometry.toContinuousLinearMap ∘
      (frameOfUnitVector : sphere (0 : E) 1 → (EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E)))
      = fun u : sphere (0 : E) 1 =>
        (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin 1)) E
          (EuclideanSpace.proj (0 : Fin 1))) (u : E) := by
    funext u
    ext b
    simp [EuclideanSpace.proj]
  rw [hclm]
  exact ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin 1)) E
    (EuclideanSpace.proj (0 : Fin 1))).continuous).comp continuous_subtype_val

/-- **The Stiefel manifold at codimension one is the unit sphere.** A frame is its unit vector and a
unit vector is the frame that scales it. -/
def stiefelHomeomorphSphere : (EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) ≃ₜ sphere (0 : E) 1 where
  toFun L := frameDirection L unitVectorFinOne
  invFun u := frameOfUnitVector u
  left_inv L := by
    ext b
    exact (apply_eq_smul_frameVectorCodimOne L b).symm
  right_inv u := by
    ext
    simp
  continuous_toFun := continuous_frameDirection _
  continuous_invFun := continuous_frameOfUnitVector

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem stiefelHomeomorphSphere_apply (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) :
    (stiefelHomeomorphSphere L : E) = frameVectorCodimOne L := rfl

/-- **The invariant measure of `V_{m,1}` is the normalized surface measure of `𝕊^{m-1}`.** This is
`MeasureTheory.map_frameDirection_stiefelMeasure` read through the identification of the two spaces;
the inverse of the total mass is there because
`MeasureTheory.ContinuousLinearMap.stiefelMeasure` is a probability measure. -/
theorem measurePreserving_stiefelHomeomorphSphere [Nontrivial E]
    (L₀ : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) :
    MeasurePreserving (stiefelHomeomorphSphere : (EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) → _)
      (ContinuousLinearMap.stiefelMeasure L₀)
      (((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere) :=
  ⟨stiefelHomeomorphSphere.continuous.measurable,
    map_frameDirection_stiefelMeasure L₀ unitVectorFinOne⟩

/-- **Integration over `V_{m,1}` is normalized integration over `𝕊^{m-1}`.** No measurability
hypothesis on the integrand is needed: the change of variables is along an equivalence. -/
theorem integral_stiefelMeasure_codimOne [Nontrivial E]
    (L₀ : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : sphere (0 : E) 1 → G) :
    ∫ L, g (frameDirection L unitVectorFinOne) ∂(ContinuousLinearMap.stiefelMeasure L₀)
      = (((volume : Measure E).toSphere.real univ)⁻¹ : ℝ) •
        ∫ u : sphere (0 : E) 1, g u ∂(volume : Measure E).toSphere := by
  calc ∫ L, g (frameDirection L unitVectorFinOne) ∂(ContinuousLinearMap.stiefelMeasure L₀)
      = ∫ u : sphere (0 : E) 1, g u
          ∂(((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere) :=
        (measurePreserving_stiefelHomeomorphSphere L₀).integral_comp'
          (f := stiefelHomeomorphSphere.toMeasurableEquiv) g
    _ = (((volume : Measure E).toSphere.real univ)⁻¹ : ℝ) •
          ∫ u : sphere (0 : E) 1, g u ∂(volume : Measure E).toSphere := by
        rw [integral_smul_measure, ENNReal.toReal_inv, measureReal_def]

end MeasureTheory
