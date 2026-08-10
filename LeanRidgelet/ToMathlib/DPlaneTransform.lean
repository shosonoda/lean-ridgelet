/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.RadonTransform

/-!
# The `d`-plane transform and its Fourier slice theorem

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project beyond the Radon transform file it generalizes.

The `d`-plane transform integrates a function over a `d`-dimensional affine subspace of an
`m`-dimensional space. It is parametrized by an orthonormal `k`-frame, `k = m - d`, presented here
as a linear isometry `L : ℝ^k →ₗᵢ E`: the `d`-plane is `L b + (range L)ᗮ`, and the transform is
$$`P_d[f](L,\boldsymbol b)=\int_{(\operatorname{range}L)^\perp}f(L\boldsymbol b+y)\,\mathrm dy.`
For `k = 1` it is the Radon transform of `ToMathlib.RadonTransform`; for `k = m - 1` it is the
X-ray transform.

Mathlib has neither the transform nor its Fourier slice theorem. Both are proved here, in the same
way as the `k = 1` case: the parametrization `(b, y) ↦ L b + y` of `E` by the range of `L` and its
orthogonal complement is a linear isometry equivalence, hence measure preserving, and everything
else is Fubini.

## Main definitions and results

* `MeasureTheory.planeOrthogonalSplit`: the measure-preserving parametrization
  `(b, y) ↦ L b + y` of `E`.
* `MeasureTheory.dPlaneTransform`: the transform `P_d[f](L, b)`.
* `MeasureTheory.integrable_dPlaneTransform`, `MeasureTheory.integral_dPlaneTransform`: its `L¹`
  theory, `‖P_d[f](L,·)‖₁ ≤ ‖f‖₁` and `∫ P_d[f](L,b) db = ∫ f`.
* `MeasureTheory.fourier_slice_dPlaneTransform`: **the Fourier slice theorem**
  `𝓕 f (L ω) = 𝓕(P_d[f](L,·))(ω)`, in the Mathlib `2π` convention.
* `MeasureTheory.dPlaneTransform_codimOne`: **at `k = 1` the transform is the Radon transform.** A
  codimension-one frame is a unit vector `u = L e₀`, its range is the line `ℝ u`, and
  `P_d[f](L, b) = R[f](u, b 0)`.
* `MeasureTheory.frameOfUnitVector`, `MeasureTheory.frameOfUnitVector_frameVectorCodimOne`: the
  inverse of that identification, `u ↦ (b ↦ b 0 • u)`. So a codimension-one frame *is* a unit
  vector: the Stiefel manifold `V_{m,1}` is the sphere `𝕊^{m-1}`, as sets here and as measure
  spaces in `ToMathlib.LieGroup.StiefelCodimOne`.
* `MeasureTheory.integral_euclideanSpace_fin_one`: integration over the bias space `ℝ^1` is
  integration over `ℝ`, the only coordinate being a measure-preserving equivalence.

The slice theorem needs no measure on the space of frames: it is a statement at a fixed `L`, as in
the `k = 1` case. A measure on the Stiefel manifold is needed only for the inversion formula,
which is not here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace MeasureTheory

/-! ## The measure-preserving plane–complement splitting -/

/-- The parametrization `(b, y) ↦ L b + y` of `E` by the range of the frame `L` and its orthogonal
complement, as a measurable equivalence. For `k = 1` this is
`MeasureTheory.lineOrthogonalSplit`. -/
def planeOrthogonalSplit (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    (EuclideanSpace ℝ (Fin k) ×
      ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E)) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (EuclideanSpace ℝ (Fin k) ×
      ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E))).trans
    (((LinearIsometryEquiv.withLpProdCongr 2 L.equivRange
        (LinearIsometryEquiv.refl ℝ ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E))).trans
      (LinearMap.range L.toLinearMap).orthogonalDecomposition.symm).toMeasurableEquiv)

theorem planeOrthogonalSplit_apply (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
    (by_ : EuclideanSpace ℝ (Fin k) ×
      ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E)) :
    planeOrthogonalSplit L by_ = L by_.1 + (by_.2 : E) := by
  have hstep : planeOrthogonalSplit L by_ =
      ((LinearIsometryEquiv.withLpProdCongr 2 L.equivRange
          (LinearIsometryEquiv.refl ℝ ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E))).trans
        (LinearMap.range L.toLinearMap).orthogonalDecomposition.symm) (WithLp.toLp 2 by_) := rfl
  rw [hstep]
  simp [LinearIsometryEquiv.withLpProdCongr]

/-- The plane–complement parametrization preserves Lebesgue measure. -/
theorem measurePreserving_planeOrthogonalSplit (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    MeasurePreserving (planeOrthogonalSplit L)
      (volume : Measure (EuclideanSpace ℝ (Fin k) ×
        ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E)))
      (volume : Measure E) :=
  ((((LinearIsometryEquiv.withLpProdCongr 2 L.equivRange
      (LinearIsometryEquiv.refl ℝ ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E))).trans
    (LinearMap.range L.toLinearMap).orthogonalDecomposition.symm)).measurePreserving).comp
    (WithLp.volume_preserving_toLp (EuclideanSpace ℝ (Fin k))
      ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Under the splitting, pairing against a vector of the range of `L` only sees the coordinate
along the frame: `⟪L b + y, L ω⟫ = ⟪b, ω⟫`. -/
theorem inner_planeOrthogonalSplit (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
    (b ω : EuclideanSpace ℝ (Fin k))
    (y : ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E)) :
    ⟪(L b + (y : E) : E), L ω⟫ = ⟪b, ω⟫ := by
  have hy : ⟪(y : E), L ω⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal (LinearMap.range L.toLinearMap) (y : E)).mp y.2 (L ω)
      ⟨ω, rfl⟩
  rw [inner_add_left, hy, add_zero, L.inner_map_map]

/-! ## The `d`-plane transform -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `d`-plane transform `P_d[f](L, b) = ∫_{(range L)ᗮ} f (L b + y) dy`, the integral of `f`
over the `d`-plane through `L b` parallel to the orthogonal complement of the frame. -/
def dPlaneTransform (f : E → F) (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
    (b : EuclideanSpace ℝ (Fin k)) : F :=
  ∫ y : ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E), f (L b + (y : E))

omit [NormedSpace ℝ F] in
/-- Transport of integrability through the plane–complement parametrization. -/
theorem integrable_comp_planeOrthogonalSplit {f : E → F} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    Integrable (fun by_ : EuclideanSpace ℝ (Fin k) ×
      ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E) => f (L by_.1 + (by_.2 : E)))
      volume := by
  have h := ((measurePreserving_planeOrthogonalSplit L).integrable_comp_emb
    (planeOrthogonalSplit L).measurableEmbedding).mpr hf
  refine h.congr (Filter.Eventually.of_forall fun by_ => ?_)
  simp only [Function.comp_apply, planeOrthogonalSplit_apply]

omit [NormedSpace ℝ F] in
/-- For integrable `f`, almost every `d`-plane section is integrable, so the transform is an
absolutely convergent integral at almost every offset. -/
theorem ae_integrable_dPlaneTransform_section {f : E → F} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    ∀ᵐ b : EuclideanSpace ℝ (Fin k),
      Integrable (fun y : ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E) =>
        f (L b + (y : E))) volume := by
  have h := integrable_comp_planeOrthogonalSplit hf L
  rw [Measure.volume_eq_prod] at h
  exact h.prod_right_ae

/-- The `d`-plane transform of an integrable function is integrable in the offset. -/
theorem integrable_dPlaneTransform {f : E → F} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    Integrable (dPlaneTransform f L) volume := by
  have h := integrable_comp_planeOrthogonalSplit hf L
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- The Fubini corollary `∫ b, P_d[f](L, b) db = ∫ x, f x dx`. -/
theorem integral_dPlaneTransform {f : E → F} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) :
    ∫ b, dPlaneTransform f L b = ∫ x, f x := by
  have h := integrable_comp_planeOrthogonalSplit hf L
  have hcomp : ∫ x, f x
      = ∫ by_ : EuclideanSpace ℝ (Fin k) ×
          ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E), f (L by_.1 + (by_.2 : E)) := by
    rw [← (measurePreserving_planeOrthogonalSplit L).integral_comp
      (planeOrthogonalSplit L).measurableEmbedding f]
    exact integral_congr_ae (Filter.Eventually.of_forall fun by_ => by
      simp only [planeOrthogonalSplit_apply])
  rw [hcomp, Measure.volume_eq_prod] at *
  rw [MeasureTheory.integral_prod _ h]
  rfl

/-! ## Codimension one: the Radon transform -/

/-- The unit vector that a codimension-one frame is: an orthonormal `1`-frame in `E` is a unit
vector, namely the image of the standard basis vector of `ℝ^1`. -/
def frameVectorCodimOne (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) : E :=
  L (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_frameVectorCodimOne (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) :
    ‖frameVectorCodimOne L‖ = 1 := by
  rw [frameVectorCodimOne, L.norm_map, PiLp.norm_single, norm_one]

/-- A vector of `ℝ^1` is its only coordinate times the standard basis vector. -/
theorem eq_smul_single_fin_one (b : EuclideanSpace ℝ (Fin 1)) :
    b = b 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  ext i
  rw [Subsingleton.elim i (0 : Fin 1)]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A codimension-one frame acts by scaling its unit vector. -/
theorem apply_eq_smul_frameVectorCodimOne (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E)
    (b : EuclideanSpace ℝ (Fin 1)) : L b = b 0 • frameVectorCodimOne L := by
  rw [frameVectorCodimOne, ← L.map_smul, ← eq_smul_single_fin_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `d`-plane of a codimension-one frame is a hyperplane: the range of the frame is the line
through its unit vector. -/
theorem range_eq_span_frameVectorCodimOne (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E) :
    LinearMap.range L.toLinearMap = ℝ ∙ frameVectorCodimOne L := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨b, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨b 0, (apply_eq_smul_frameVectorCodimOne L b).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), rfl⟩

/-- **At codimension one the `d`-plane transform is the Radon transform.** The frame is a unit
vector, its range is the line through it, and the `d`-plane is the hyperplane orthogonal to that
line. So `MeasureTheory.radonTransform` is the `k = 1` case of `MeasureTheory.dPlaneTransform`, as
is the Fourier slice theorem of each. -/
theorem dPlaneTransform_codimOne (f : E → F) (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E)
    (b : EuclideanSpace ℝ (Fin 1)) :
    dPlaneTransform f L b = radonTransform f (frameVectorCodimOne L) (b 0) := by
  have hrange : (LinearMap.range L.toLinearMap)ᗮ = (ℝ ∙ frameVectorCodimOne L)ᗮ := by
    rw [range_eq_span_frameVectorCodimOne]
  set e := LinearIsometryEquiv.ofEq _ _ hrange with he
  rw [dPlaneTransform, radonTransform, apply_eq_smul_frameVectorCodimOne,
    ← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding
      (fun y : ((ℝ ∙ frameVectorCodimOne L)ᗮ : Submodule ℝ E) =>
        f (b 0 • frameVectorCodimOne L + (y : E)))]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The norm of a vector of `ℝ^1` is the absolute value of its only coordinate. -/
theorem norm_eq_abs_apply_fin_one (b : EuclideanSpace ℝ (Fin 1)) : ‖b‖ = |b 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- The codimension-one frame that a unit vector is: the inverse of
`MeasureTheory.frameVectorCodimOne`, sending `u` to the isometry `b ↦ b 0 • u` of `ℝ^1` into `E`. -/
def frameOfUnitVector (u : Metric.sphere (0 : E) 1) : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E where
  toFun b := b 0 • (u : E)
  map_add' b b' := by simp [add_smul]
  map_smul' c b := by simp [mul_smul]
  norm_map' b := by
    simp [norm_smul, mem_sphere_zero_iff_norm.1 u.2, norm_eq_abs_apply_fin_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem frameOfUnitVector_apply (u : Metric.sphere (0 : E) 1)
    (b : EuclideanSpace ℝ (Fin 1)) : frameOfUnitVector u b = b 0 • (u : E) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem frameVectorCodimOne_frameOfUnitVector (u : Metric.sphere (0 : E) 1) :
    frameVectorCodimOne (frameOfUnitVector u) = (u : E) := by
  simp [frameVectorCodimOne]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A codimension-one frame is exactly a unit vector.** Together with
`MeasureTheory.frameVectorCodimOne_frameOfUnitVector` this identifies the Stiefel manifold
`V_{m,1}` with the sphere `𝕊^{m-1}`. -/
theorem frameOfUnitVector_frameVectorCodimOne (L : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] E)
    (hL : ‖frameVectorCodimOne L‖ = 1) :
    frameOfUnitVector ⟨frameVectorCodimOne L, mem_sphere_zero_iff_norm.2 hL⟩ = L := by
  ext b
  exact (apply_eq_smul_frameVectorCodimOne L b).symm

/-- The unit vector of `ℝ^1` that a codimension-one frame is applied to. -/
def unitVectorFinOne : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩

@[simp] theorem coe_unitVectorFinOne :
    (unitVectorFinOne : EuclideanSpace ℝ (Fin 1)) = EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :=
  rfl

/-- **Integration over `ℝ^1` is integration over `ℝ`.** The only coordinate is a
measure-preserving equivalence `ℝ^1 ≃ᵐ ℝ`. -/
theorem integral_euclideanSpace_fin_one {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : ℝ → G) : ∫ b : EuclideanSpace ℝ (Fin 1), g (b 0) = ∫ t : ℝ, g t := by
  have hmp : MeasurePreserving
      (((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
        (MeasurableEquiv.funUnique (Fin 1) ℝ) : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ))
      volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  exact hmp.integral_comp' g

/-! ## The Fourier slice theorem -/

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- **Fourier slice theorem for the `d`-plane transform** (the projection-slice theorem in
codimension `k`): the `k`-dimensional Fourier transform of the transform in the offset is the
`m`-dimensional Fourier transform of `f` restricted to the range of the frame,
`𝓕 f (L ω) = 𝓕(P_d[f](L,·))(ω)`. For `k = 1` this is
`MeasureTheory.fourier_slice_radonTransform`. -/
theorem fourier_slice_dPlaneTransform {f : E → F'} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (ω : EuclideanSpace ℝ (Fin k)) :
    𝓕 f (L ω) = 𝓕 (dPlaneTransform f L) ω := by
  have h := integrable_comp_planeOrthogonalSplit hf L
  have hint : Integrable
      (fun by_ : EuclideanSpace ℝ (Fin k) ×
        ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E) =>
          ((Real.fourierChar (-⟪by_.1, ω⟫) : Circle) : ℂ) • f (L by_.1 + (by_.2 : E)))
      volume := by
    refine Integrable.bdd_smul h 1 ?_ (Filter.Eventually.of_forall fun by_ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp
          ((continuous_fst.inner continuous_const).neg))
    · simp
  calc 𝓕 f (L ω)
      = ∫ by_ : EuclideanSpace ℝ (Fin k) ×
          ((LinearMap.range L.toLinearMap)ᗮ : Submodule ℝ E),
            ((Real.fourierChar (-⟪by_.1, ω⟫) : Circle) : ℂ) • f (L by_.1 + (by_.2 : E)) := by
        rw [Real.fourier_eq,
          ← (measurePreserving_planeOrthogonalSplit L).integral_comp
            (planeOrthogonalSplit L).measurableEmbedding
            fun x => Real.fourierChar (-(inner ℝ x (L ω) : ℝ)) • f x]
        refine integral_congr_ae (Filter.Eventually.of_forall fun by_ => ?_)
        simp only [planeOrthogonalSplit_apply,
          inner_planeOrthogonalSplit L by_.1 ω by_.2, Circle.smul_def]
    _ = ∫ b : EuclideanSpace ℝ (Fin k), ∫ y : ((LinearMap.range L.toLinearMap)ᗮ :
          Submodule ℝ E), ((Real.fourierChar (-⟪b, ω⟫) : Circle) : ℂ) • f (L b + (y : E)) := by
        rw [Measure.volume_eq_prod] at hint ⊢
        exact MeasureTheory.integral_prod _ hint
    _ = ∫ b : EuclideanSpace ℝ (Fin k),
          ((Real.fourierChar (-⟪b, ω⟫) : Circle) : ℂ) • dPlaneTransform f L b := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
        exact integral_smul _ _
    _ = 𝓕 (dPlaneTransform f L) ω := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
        simp only [Circle.smul_def]

end MeasureTheory
