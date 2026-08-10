/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.OrthogonalGroup
public import LeanRidgelet.ToMathlib.PolarCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The rotation-invariant measure on the unit sphere is unique

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib records how `MeasureTheory.Measure.toSphere` is computed but none of its symmetries. This
file supplies the one that matters: **it is invariant under the orthogonal group**, and it is the
only such measure up to a scalar. Concretely, the orbit measure of a unit vector — the pushforward
of the Haar probability measure of the orthogonal group along `Q ↦ Q v` — does not depend on `v`,
and the surface measure is its total mass times that orbit measure.

The two together are what turns an invariance statement into a computation against the surface
measure, which is what the matrix polar integration formula needs: there the direction integral of a
frame is invariant by construction, and it has to be recognized as an integral over the sphere.

## Main results

* `MeasureTheory.sphereAct`: the action of the orthogonal group on the unit sphere.
* `MeasureTheory.map_sphereAct_toSphere`: **the surface measure is rotation invariant.** With
  `Measure.toSphere_apply'`, which computes `μ.toSphere s` as `dim E` times the measure of the open
  cone over `s`, this reduces to invariance of Lebesgue measure, because a rotation carries that
  cone to the cone over the rotated set.
* `MeasureTheory.exists_sphereAct_eq`: the action is transitive, the `k = 1` case of transitivity on
  frames.
* `MeasureTheory.sphereOrbitMeasure_eq`: the orbit measure does not depend on the vector.
* `MeasureTheory.toSphere_eq_smul_sphereOrbitMeasure`, and its inverted form
  `MeasureTheory.sphereOrbitMeasure_eq_smul_toSphere`: **uniqueness.** The Fubini argument: average
  the invariance of the surface measure over the group, exchange the two integrals, and use that the
  inner average is the orbit measure and does not depend on the point it is taken at.
* `MeasureTheory.map_frameDirection_stiefelMeasure`: **the direction of a random frame is uniform on
  the sphere.** The pushforward of the invariant measure on the Stiefel manifold along `L ↦ L ω`,
  for a fixed unit vector `ω` of the frame space, is the normalized surface measure. This is the
  identity the matrix polar integration formula turns on, and both halves of its proof are what the
  two constructions were for: the orbit map of a frame composed with the direction map is the orbit
  map of a vector, and the orbit measure of a vector is the normalized surface measure.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped Pointwise ENNReal

namespace MeasureTheory

section Action

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The action of the orthogonal group on the unit sphere -/

/-- The action of the orthogonal group on the unit sphere. -/
def sphereAct (Q : unitary (E →L[ℝ] E)) (u : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨(Q : E →L[ℝ] E) u, by
    rw [mem_sphere_zero_iff_norm, (Q : E →L[ℝ] E).norm_map_of_mem_unitary Q.property]
    exact mem_sphere_zero_iff_norm.1 u.2⟩

@[simp] theorem coe_sphereAct (Q : unitary (E →L[ℝ] E)) (u : sphere (0 : E) 1) :
    ((sphereAct Q u : sphere (0 : E) 1) : E) = (Q : E →L[ℝ] E) u := rfl

theorem sphereAct_mul (Q Q' : unitary (E →L[ℝ] E)) (u : sphere (0 : E) 1) :
    sphereAct (Q * Q') u = sphereAct Q (sphereAct Q' u) := by
  ext
  simp [Submonoid.coe_mul]

theorem continuous_sphereAct_right (Q : unitary (E →L[ℝ] E)) :
    Continuous (sphereAct Q : sphere (0 : E) 1 → sphere (0 : E) 1) :=
  Continuous.subtype_mk ((Q : E →L[ℝ] E).continuous.comp continuous_subtype_val) _

theorem continuous_sphereAct :
    Continuous fun p : unitary (E →L[ℝ] E) × sphere (0 : E) 1 => sphereAct p.1 p.2 := by
  have h : Continuous fun p : unitary (E →L[ℝ] E) × sphere (0 : E) 1 =>
      ((p.1 : E →L[ℝ] E) (p.2 : E)) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact Continuous.subtype_mk h _

theorem continuous_sphereAct_left (u : sphere (0 : E) 1) :
    Continuous fun Q : unitary (E →L[ℝ] E) => sphereAct Q u :=
  continuous_sphereAct.comp (continuous_id.prodMk continuous_const)

/-! ## Invariance of the surface measure -/

/-- Under the coercion to `E`, the preimage of a set of the sphere along a rotation is the preimage
along that rotation of the coerced set. -/
theorem coe_image_preimage_sphereAct (Q : unitary (E →L[ℝ] E)) (s : Set (sphere (0 : E) 1)) :
    ((Subtype.val '' (sphereAct Q ⁻¹' s) : Set E))
      = (fun x => (Q : E →L[ℝ] E) x) ⁻¹' (Subtype.val '' s) := by
  ext x
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨sphereAct Q u, hu, rfl⟩
  · rintro ⟨v, hv, hxv⟩
    have hx : x ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, ← (Q : E →L[ℝ] E).norm_map_of_mem_unitary Q.property x, ← hxv]
      exact mem_sphere_zero_iff_norm.1 v.2
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have hv' : sphereAct Q ⟨x, hx⟩ = v := Subtype.ext hxv.symm
    rw [hv']
    exact hv

omit [FiniteDimensional ℝ E] in
/-- A linear isometric equivalence commutes with the pointwise action of a set of scalars, on
preimages. -/
theorem smul_set_preimage_isometryEquiv (e : E ≃ₗᵢ[ℝ] E) (S : Set ℝ) (A : Set E) :
    S • (e ⁻¹' A) = e ⁻¹' (S • A) := by
  ext x
  simp only [mem_preimage, Set.mem_smul]
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, hr, e y, hy, by rw [map_smul]⟩
  · rintro ⟨r, hr, z, hz, hx⟩
    refine ⟨r, hr, e.symm z, by simpa using hz, e.injective ?_⟩
    rw [map_smul]
    simpa using hx

end Action

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The surface measure of the unit sphere is invariant under the orthogonal group.** Mathlib
computes `μ.toSphere s` as `dim E` times the measure of the open cone `Ioo 0 1 • s`; a rotation
carries that cone to the cone over the rotated set, and Lebesgue measure does not see it. -/
theorem map_sphereAct_toSphere (Q : unitary (E →L[ℝ] E)) :
    Measure.map (sphereAct Q) (volume : Measure E).toSphere = (volume : Measure E).toSphere := by
  refine Measure.ext fun s hs => ?_
  have hmeas := (continuous_sphereAct_right Q).measurable
  set e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv Q with he
  have hQe : ∀ x : E, (Q : E →L[ℝ] E) x = e x := fun x => rfl
  rw [Measure.map_apply hmeas hs,
    Measure.toSphere_apply' (volume : Measure E) (hmeas hs),
    Measure.toSphere_apply' (volume : Measure E) hs, coe_image_preimage_sphereAct]
  congr 1
  rw [show (fun x : E => (Q : E →L[ℝ] E) x) = (e : E → E) from funext hQe,
    smul_set_preimage_isometryEquiv]
  exact e.measurePreserving.measure_preimage_equiv (f := e.toMeasurableEquiv) _

/-! ## Transitivity -/

/-- A unit vector as a linear isometry of the line: the `k = 1` frame it is. -/
def unitVectorIsometry {u : E} (hu : ‖u‖ = 1) : ℝ →ₗᵢ[ℝ] E where
  toFun t := t • u
  map_add' s t := by simp [add_smul]
  map_smul' c t := by simp [smul_smul]
  norm_map' t := by simp [norm_smul, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem unitVectorIsometry_apply {u : E} (hu : ‖u‖ = 1) (t : ℝ) :
    unitVectorIsometry hu t = t • u := rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The orthogonal group acts transitively on the unit sphere.** This is the `k = 1` case of
transitivity on frames: a unit vector is a linear isometry of the line. -/
theorem exists_sphereAct_eq (u v : sphere (0 : E) 1) :
    ∃ Q : unitary (E →L[ℝ] E), sphereAct Q u = v := by
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.exists_stiefelAct_eq
    (unitVectorIsometry (mem_sphere_zero_iff_norm.1 u.2))
    (unitVectorIsometry (mem_sphere_zero_iff_norm.1 v.2))
  refine ⟨Q, Subtype.ext ?_⟩
  have h := congrArg (fun L : ℝ →ₗᵢ[ℝ] E => L 1) hQ
  simpa using h

/-! ## The orbit measure, and uniqueness -/

/-- The orbit measure of a unit vector: the pushforward of the Haar probability measure of the
orthogonal group along the orbit map `Q ↦ Q v`. -/
def sphereOrbitMeasure (v : sphere (0 : E) 1) : Measure (sphere (0 : E) 1) :=
  Measure.map (fun Q => sphereAct Q v) ContinuousLinearMap.orthogonalHaar

instance instIsProbabilityMeasureSphereOrbitMeasure (v : sphere (0 : E) 1) :
    IsProbabilityMeasure (sphereOrbitMeasure v) :=
  Measure.isProbabilityMeasure_map (continuous_sphereAct_left v).measurable.aemeasurable

theorem sphereOrbitMeasure_apply (v : sphere (0 : E) 1) {s : Set (sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereOrbitMeasure v s
      = ∫⁻ Q, s.indicator 1 (sphereAct Q v) ∂ContinuousLinearMap.orthogonalHaar := by
  rw [sphereOrbitMeasure, Measure.map_apply (continuous_sphereAct_left v).measurable hs,
    ← lintegral_indicator_one ((continuous_sphereAct_left v).measurable hs)]
  exact lintegral_congr fun Q => rfl

/-- **The orbit measure does not depend on the vector it is taken at.** By transitivity the two
pushforwards differ by a right translation of the group, which the Haar measure does not see. -/
theorem sphereOrbitMeasure_eq (u v : sphere (0 : E) 1) :
    sphereOrbitMeasure u = sphereOrbitMeasure v := by
  obtain ⟨Q₀, hQ₀⟩ := exists_sphereAct_eq u v
  have hcomp : (fun Q : unitary (E →L[ℝ] E) => sphereAct Q v)
      = (fun R : unitary (E →L[ℝ] E) => sphereAct R u) ∘ (fun Q => Q * Q₀) := by
    funext Q
    simp only [Function.comp_apply, sphereAct_mul, ← hQ₀]
  rw [sphereOrbitMeasure, sphereOrbitMeasure, hcomp, ← Measure.map_map
    (continuous_sphereAct_left u).measurable (measurable_mul_const Q₀), map_mul_right_eq_self]

/-- **Uniqueness of the rotation-invariant measure on the unit sphere.** The surface measure is its
total mass times the orbit measure of any unit vector.

The proof is the standard averaging argument. Averaging the invariance of the surface measure over
the group and exchanging the two integrals turns the measure of a set into the integral over the
sphere of the orbit measure of that set, read at each point; that reading does not depend on the
point, so the integral is the total mass times a single value. -/
theorem toSphere_eq_smul_sphereOrbitMeasure (v : sphere (0 : E) 1) :
    (volume : Measure E).toSphere
      = (volume : Measure E).toSphere univ • sphereOrbitMeasure v := by
  refine Measure.ext fun s hs => ?_
  have hind : Measurable (s.indicator (1 : sphere (0 : E) 1 → ℝ≥0∞)) :=
    (measurable_one.indicator hs)
  calc (volume : Measure E).toSphere s
      = ∫⁻ _ : unitary (E →L[ℝ] E), (volume : Measure E).toSphere s
          ∂ContinuousLinearMap.orthogonalHaar := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ Q : unitary (E →L[ℝ] E), ∫⁻ u, s.indicator 1 (sphereAct Q u)
          ∂(volume : Measure E).toSphere ∂ContinuousLinearMap.orthogonalHaar := by
        refine lintegral_congr fun Q => ?_
        have hpre : ∀ u, s.indicator (1 : sphere (0 : E) 1 → ℝ≥0∞) (sphereAct Q u)
            = (sphereAct Q ⁻¹' s).indicator 1 u := fun _ => rfl
        rw [lintegral_congr hpre,
          lintegral_indicator_one ((continuous_sphereAct_right Q).measurable hs),
          ← Measure.map_apply (continuous_sphereAct_right Q).measurable hs,
          map_sphereAct_toSphere]
    _ = ∫⁻ u, ∫⁻ Q : unitary (E →L[ℝ] E), s.indicator 1 (sphereAct Q u)
          ∂ContinuousLinearMap.orthogonalHaar ∂(volume : Measure E).toSphere :=
        lintegral_lintegral_swap
          (hind.comp continuous_sphereAct.measurable).aemeasurable
    _ = ∫⁻ _ : sphere (0 : E) 1, sphereOrbitMeasure v s ∂(volume : Measure E).toSphere := by
        refine lintegral_congr fun u => ?_
        rw [← sphereOrbitMeasure_apply u hs, sphereOrbitMeasure_eq u v]
    _ = (volume : Measure E).toSphere univ • sphereOrbitMeasure v s := by
        rw [lintegral_const, smul_eq_mul, mul_comm]

/-- Uniqueness, solved for the orbit measure: it is the normalized surface measure. -/
theorem sphereOrbitMeasure_eq_smul_toSphere [Nontrivial E] (v : sphere (0 : E) 1) :
    sphereOrbitMeasure v
      = ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere := by
  have hne : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have htop : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  have h := toSphere_eq_smul_sphereOrbitMeasure (E := E) v
  calc sphereOrbitMeasure v
      = (((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure E).toSphere univ)
          • sphereOrbitMeasure v := by
        rw [ENNReal.inv_mul_cancel hne htop, one_smul]
    _ = ((volume : Measure E).toSphere univ)⁻¹ • ((volume : Measure E).toSphere univ
          • sphereOrbitMeasure v) := by rw [smul_smul]
    _ = ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere := by rw [← h]

/-! ## The direction of a random frame -/

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- The direction a frame sends a unit vector of the frame space to, as a point of the unit sphere
of `E`. -/
def frameDirection (L : F' →ₗᵢ[ℝ] E) (ω : sphere (0 : F') 1) : sphere (0 : E) 1 :=
  ⟨L ω, by
    rw [mem_sphere_zero_iff_norm, L.norm_map]
    exact mem_sphere_zero_iff_norm.1 ω.2⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem coe_frameDirection (L : F' →ₗᵢ[ℝ] E) (ω : sphere (0 : F') 1) :
    ((frameDirection L ω : sphere (0 : E) 1) : E) = L ω := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_frameDirection (ω : sphere (0 : F') 1) :
    Continuous fun L : F' →ₗᵢ[ℝ] E => frameDirection L ω := by
  have h : Continuous fun L : F' →ₗᵢ[ℝ] E => (L (ω : F') : E) :=
    (ContinuousLinearMap.apply ℝ E (ω : F')).continuous.comp
      ContinuousLinearMap.continuous_toContinuousLinearMap
  exact Continuous.subtype_mk h _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The direction map is *jointly* continuous in the frame and the unit vector. -/
theorem continuous_frameDirection_prod :
    Continuous fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 => frameDirection p.1 p.2 := by
  have h : Continuous fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 => (p.1 (p.2 : F') : E) :=
    isBoundedBilinearMap_apply.continuous.comp
      ((ContinuousLinearMap.continuous_toContinuousLinearMap.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact Continuous.subtype_mk h _

/-- **The direction of a random frame is uniform on the sphere.** For a fixed unit vector of the
frame space, the pushforward of the invariant measure on the Stiefel manifold along `L ↦ L ω` is the
normalized surface measure — whichever unit vector is chosen, and whichever frame the Stiefel
measure was built from.

This is the identity the matrix polar integration formula turns on: it is what lets a direction
integral over frames be read as an integral over the sphere. Both halves of its proof are the point
of the two constructions: the pushforward along the orbit map of the *frame* composes with the
direction map to the orbit map of the *vector*, and the orbit measure of a vector is the normalized
surface measure by uniqueness. -/
theorem map_frameDirection_stiefelMeasure [Nontrivial E] (L₀ : F' →ₗᵢ[ℝ] E)
    (ω : sphere (0 : F') 1) [FiniteDimensional ℝ F'] :
    Measure.map (fun L : F' →ₗᵢ[ℝ] E => frameDirection L ω)
        (ContinuousLinearMap.stiefelMeasure L₀)
      = ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere := by
  have hcomp : ((fun L : F' →ₗᵢ[ℝ] E => frameDirection L ω) ∘
        fun Q : unitary (E →L[ℝ] E) => ContinuousLinearMap.stiefelAct Q L₀)
      = fun Q : unitary (E →L[ℝ] E) => sphereAct Q (frameDirection L₀ ω) := by
    funext Q
    ext
    simp
  rw [ContinuousLinearMap.stiefelMeasure, Measure.map_map (continuous_frameDirection ω).measurable
    (ContinuousLinearMap.continuous_stiefelAct_left L₀).measurable, hcomp,
    ← sphereOrbitMeasure, sphereOrbitMeasure_eq_smul_toSphere]

end Measure

end MeasureTheory
