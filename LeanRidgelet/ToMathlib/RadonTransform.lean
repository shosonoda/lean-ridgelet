/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import LeanRidgelet.ToMathlib.FourierInversion

/-!
# The Radon transform: definitions, `L¹` theory, and the Fourier slice theorem

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project. Mathlib currently has no Radon transform (the pinned version only
carries Radon--Nikodym derivatives and Radon measures).

Everything is stated on an arbitrary finite-dimensional real inner product space `E` with its
canonical `volume`, for functions with values in a normed space `F`.

## Main definitions

* `MeasureTheory.radonTransform`: `R[f](u, p) = ∫_{(ℝu)^⊥} f (p u + y) dy`, integrating over
  the orthogonal complement of the line `ℝ u` with its canonical Lebesgue measure.
* `MeasureTheory.dualRadonTransform`: `R†[Φ](x) = ∫_{𝕊} Φ (u, ⟪u, x⟫) du` with the surface
  measure `volume.toSphere` on the unit sphere.
* `MeasureTheory.lineOrthogonalSplit`: the parametrization `(p, y) ↦ p • u + y` of `E` by the
  line `ℝ u` and its orthogonal complement, as a measurable equivalence, for a unit vector `u`.

## Main results

* `MeasureTheory.measurePreserving_lineOrthogonalSplit`: the parametrization preserves the
  Lebesgue measure.
* `MeasureTheory.integrable_radonTransform`: for integrable `f` and every unit direction `u`,
  the Radon transform `R[f](u, ·)` is integrable on `ℝ`.
* `MeasureTheory.integral_radonTransform`: `∫ p, R[f](u, p) dp = ∫ x, f x dx`, the corollary
  of Fubini's theorem quoted in the tomography literature; here it holds for every unit `u`
  rather than almost every `u`.
* `MeasureTheory.integral_norm_radonTransform_le`: `‖R[f](u, ·)‖_{L¹(ℝ)} ≤ ‖f‖_{L¹(E)}`.
* `MeasureTheory.fourier_slice_radonTransform`: the Fourier slice theorem (also known as the
  projection-slice or central-slice theorem) `𝓕 f (ω • u) = 𝓕 (R[f](u, ·)) ω`, where the
  left-hand side is the Fourier transform on `E` and the right-hand side the one-dimensional
  Fourier transform.
* `MeasureTheory.continuous_radonTransform_schwartz`: the Radon section of a Schwartz function is
  continuous (dominated convergence with the Japanese-bracket dominator, using that a point of
  the line `ℝ u` and a point of `(ℝ u)^⊥` are orthogonal, so `‖p u + y‖ ≥ ‖y‖`).
* `MeasureTheory.radonSchwartzSection` and
  `MeasureTheory.radonTransform_eq_radonSchwartzSection`: **the Radon section of a Schwartz
  function is a Schwartz function** — it equals the inverse Fourier transform of the Fourier
  slice `ω ↦ 𝓕 f (ω • u)`, which is Schwartz because the ray map `ω ↦ ω • u` is temperate and
  antilipschitz. The identification goes through the Fourier slice theorem and almost-everywhere
  Fourier inversion, upgraded to everywhere equality by continuity. This is what makes
  one-dimensional Schwartz theory (Fourier multipliers, in particular the filter of filtered
  backprojection) available on Radon sections.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Radon transform and dual Radon transform -/

section Definitions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Radon transform `R[f](u, p) = ∫_{(ℝu)^⊥} f (p u + y) dy`, integrating over the
orthogonal complement of the line `ℝu` with its canonical Lebesgue measure. It is customarily
used for unit vectors `u`. -/
def radonTransform (f : E → F) (u : E) (p : ℝ) : F :=
  ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ E), f (p • u + ↑y)

/-- The dual Radon transform (backprojection) `R†[Φ](x) = ∫_{𝕊} Φ (u, ⟪u, x⟫) du`, with the
surface measure `volume.toSphere` on the unit sphere of `E`. -/
def dualRadonTransform (Φ : E → ℝ → F) (x : E) : F :=
  ∫ u : Metric.sphere (0 : E) 1,
    Φ u (inner ℝ (u : E) x) ∂(volume : Measure E).toSphere

end Definitions

/-! ## The measure-preserving line–hyperplane splitting -/

/-- The parametrization `(p, y) ↦ p • u + y` of `E` by the line `ℝ u` and its orthogonal
complement, as a measurable equivalence, for a unit vector `u`. It is assembled from the
`WithLp 2` product coordinates and the orthogonal decomposition `E ≃ₗᵢ ℝu ×₂ (ℝu)^⊥`. -/
def lineOrthogonalSplit (u : E) (hu : ‖u‖ = 1) :
    (ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E)) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E))).trans
    (((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton u hu)
        (LinearIsometryEquiv.refl ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E))).trans
      (ℝ ∙ u).orthogonalDecomposition.symm).toMeasurableEquiv)

theorem lineOrthogonalSplit_apply (u : E) (hu : ‖u‖ = 1)
    (py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E)) :
    lineOrthogonalSplit u hu py = py.1 • u + (py.2 : E) := by
  have hstep : lineOrthogonalSplit u hu py =
      ((LinearIsometryEquiv.withLpProdCongr 2
          (LinearIsometryEquiv.toSpanUnitSingleton u hu)
          (LinearIsometryEquiv.refl ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E))).trans
        (ℝ ∙ u).orthogonalDecomposition.symm) (WithLp.toLp 2 py) := rfl
  rw [hstep]
  simp [LinearIsometryEquiv.withLpProdCongr]

/-- The line–hyperplane parametrization preserves Lebesgue measure. -/
theorem measurePreserving_lineOrthogonalSplit (u : E) (hu : ‖u‖ = 1) :
    MeasurePreserving (lineOrthogonalSplit u hu)
      (volume : Measure (ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E)))
      (volume : Measure E) :=
  ((((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton u hu)
      (LinearIsometryEquiv.refl ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E))).trans
    (ℝ ∙ u).orthogonalDecomposition.symm)).measurePreserving).comp
    (WithLp.volume_preserving_toLp ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Under the line–hyperplane splitting, the inner product with a vector on the ray through
`u` only sees the offset coordinate. -/
theorem inner_lineOrthogonalSplit_smul {u : E} (hu : ‖u‖ = 1) (ω p : ℝ)
    (y : ((ℝ ∙ u)ᗮ : Submodule ℝ E)) :
    inner ℝ ((p • u + (y : E)) : E) (ω • u) = p * ω := by
  have hy : inner ℝ u (y : E) = 0 :=
    ((Submodule.mem_orthogonal (ℝ ∙ u) (y : E)).mp y.2) u
      (Submodule.mem_span_singleton_self u)
  have hyu : inner ℝ (y : E) u = 0 := by
    rw [real_inner_comm]
    exact hy
  rw [inner_add_left, real_inner_smul_right, real_inner_smul_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hu, hyu]
  ring

/-! ## `L¹` theory of the Radon transform -/

section L1Theory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Transport of integrability through the line–hyperplane parametrization. -/
theorem integrable_comp_lineOrthogonalSplit {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) :
    Integrable
      (fun py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E) =>
        f (py.1 • u + (py.2 : E))) volume := by
  have h :=
    ((measurePreserving_lineOrthogonalSplit u hu).integrable_comp_emb
      (lineOrthogonalSplit u hu).measurableEmbedding).mpr hf
  refine h.congr (Filter.Eventually.of_forall fun py => ?_)
  simp only [Function.comp_apply, lineOrthogonalSplit_apply]

omit [NormedSpace ℝ F] in
/-- For integrable `f` and a unit direction `u`, almost every hyperplane section of `f` is
integrable, so the Radon transform is an absolutely convergent integral at almost every
offset `p`. -/
theorem ae_integrable_radonTransform_section {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) :
    ∀ᵐ p : ℝ, Integrable
      (fun y : ((ℝ ∙ u)ᗮ : Submodule ℝ E) => f (p • u + (y : E)))
      volume := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  rw [Measure.volume_eq_prod] at h
  exact h.prod_right_ae

/-- The Radon transform of an integrable function along any unit direction is integrable: the
`L¹` half of the Fubini corollary, `R : L¹(E) → L¹(ℝ)` in the offset variable. -/
theorem integrable_radonTransform {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) :
    Integrable (radonTransform f u) volume := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- The Fubini corollary `∫ p, R[f](u, p) dp = ∫ x, f x dx` for every unit direction `u`. -/
theorem integral_radonTransform {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) :
    ∫ p, radonTransform f u p = ∫ x, f x := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  have hcomp : ∫ x, f x
      = ∫ py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E),
          f (py.1 • u + (py.2 : E)) := by
    rw [← (measurePreserving_lineOrthogonalSplit u hu).integral_comp
      (lineOrthogonalSplit u hu).measurableEmbedding f]
    exact integral_congr_ae (Filter.Eventually.of_forall fun py => by
      simp only [lineOrthogonalSplit_apply])
  rw [hcomp, Measure.volume_eq_prod] at *
  rw [MeasureTheory.integral_prod _ h]
  rfl

/-- The Radon transform contracts the `L¹` norm: `∫ p, ‖R[f](u, p)‖ dp ≤ ∫ x, ‖f x‖ dx`. -/
theorem integral_norm_radonTransform_le {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) :
    ∫ p, ‖radonTransform f u p‖ ≤ ∫ x, ‖f x‖ := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  rw [Measure.volume_eq_prod] at h
  have hmaj : Integrable (fun p : ℝ =>
      ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ E),
        ‖f (p • u + (y : E))‖) volume :=
    h.norm.integral_prod_left
  have hnormcomp : ∫ x, ‖f x‖
      = ∫ py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E),
          ‖f (py.1 • u + (py.2 : E))‖ := by
    rw [← (measurePreserving_lineOrthogonalSplit u hu).integral_comp
      (lineOrthogonalSplit u hu).measurableEmbedding fun x => ‖f x‖]
    exact integral_congr_ae (Filter.Eventually.of_forall fun py => by
      simp only [lineOrthogonalSplit_apply])
  calc ∫ p, ‖radonTransform f u p‖
      ≤ ∫ p, ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ E),
          ‖f (p • u + (y : E))‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hmaj
          (Filter.Eventually.of_forall fun p => norm_integral_le_integral_norm _)
    _ = ∫ x, ‖f x‖ := by
        rw [hnormcomp, Measure.volume_eq_prod, MeasureTheory.integral_prod _ h.norm]

end L1Theory

/-! ## The Fourier slice theorem -/

section FourierSlice

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Fourier slice theorem** (projection-slice theorem): the Fourier transform of an
integrable function on `E`, restricted to the ray through a unit vector `u`, is the
one-dimensional Fourier transform of its Radon transform:
`𝓕 f (ω • u) = 𝓕 (R[f](u, ·)) ω`. -/
theorem fourier_slice_radonTransform {f : E → F}
    (hf : Integrable f volume) (u : E) (hu : ‖u‖ = 1) (ω : ℝ) :
    𝓕 f (ω • u) = 𝓕 (radonTransform f u) ω := by
  have h := integrable_comp_lineOrthogonalSplit hf u hu
  have hint : Integrable
      (fun py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E) =>
        ((𝐞 (-(py.1 * ω)) : Circle) : ℂ) • f (py.1 • u + (py.2 : E))) volume := by
    refine Integrable.bdd_smul h 1 ?_ (Filter.Eventually.of_forall fun py => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_fst.mul continuous_const).neg)
    · simp
  calc 𝓕 f (ω • u)
      = ∫ py : ℝ × ((ℝ ∙ u)ᗮ : Submodule ℝ E),
          ((𝐞 (-(py.1 * ω)) : Circle) : ℂ) • f (py.1 • u + (py.2 : E)) := by
        rw [Real.fourier_eq,
          ← (measurePreserving_lineOrthogonalSplit u hu).integral_comp
            (lineOrthogonalSplit u hu).measurableEmbedding
            fun x => 𝐞 (-(inner ℝ x (ω • u) : ℝ)) • f x]
        refine integral_congr_ae (Filter.Eventually.of_forall fun py => ?_)
        simp only [lineOrthogonalSplit_apply, inner_lineOrthogonalSplit_smul hu,
          Circle.smul_def]
    _ = ∫ p : ℝ, ∫ y : ((ℝ ∙ u)ᗮ : Submodule ℝ E),
          ((𝐞 (-(p * ω)) : Circle) : ℂ) • f (p • u + (y : E)) := by
        rw [Measure.volume_eq_prod] at hint ⊢
        exact MeasureTheory.integral_prod _ hint
    _ = ∫ p : ℝ, ((𝐞 (-(p * ω)) : Circle) : ℂ) • radonTransform f u p := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        exact integral_smul _ _
    _ = 𝓕 (radonTransform f u) ω := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        have hinner : inner ℝ p ω = p * ω := by
          rw [RCLike.inner_apply, conj_trivial]
          ring
        simp only [hinner, Circle.smul_def]

end FourierSlice


/-! ## Radon sections of Schwartz functions -/

section Schwartz

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Schwartz decay in Japanese-bracket form: `‖f x‖ ≤ C (1 + ‖x‖)^{-k}`. -/
theorem schwartz_norm_le_one_add_norm_rpow (f : SchwartzMap E ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℝ)) := by
  refine ⟨2 ^ k * (Finset.Iic ((k, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((k, 0) : ℕ × ℕ))
    (le_refl k) (le_refl 0) f x
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, le_mul_inv_iff₀ hpos, mul_comm]
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a unit vector `u`, a point of the line `ℝ u` and a point of its orthogonal complement
have norm at least that of the second summand. -/
theorem norm_le_norm_smul_add {u : E} (p : ℝ)
    (y : ((ℝ ∙ u)ᗮ : Submodule ℝ E)) : ‖(y : E)‖ ≤ ‖p • u + (y : E)‖ := by
  have hinner : ⟪p • u, (y : E)⟫ = 0 := by
    have hy := y.2
    rw [Submodule.mem_orthogonal] at hy
    exact hy (p • u) (Submodule.smul_mem _ p (Submodule.mem_span_singleton_self u))
  have hsq : ‖p • u + (y : E)‖ ^ 2 = ‖p • u‖ ^ 2 + ‖(y : E)‖ ^ 2 := by
    rw [norm_add_sq_real, hinner]
    ring
  have h2 : ‖(y : E)‖ ^ 2 ≤ ‖p • u + (y : E)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖p • u‖]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The Radon section of a Schwartz function is continuous. -/
theorem continuous_radonTransform_schwartz (f : SchwartzMap E ℂ) (u : E) :
    Continuous (radonTransform (⇑f) u) := by
  classical
  set K : Submodule ℝ E := (ℝ ∙ u)ᗮ with hK_def
  set d : ℕ := Module.finrank ℝ K with hd_def
  obtain ⟨C, hC⟩ := schwartz_norm_le_one_add_norm_rpow f (d + 1)
  have hbound : Integrable (fun y : K => C * (1 + ‖(y : E)‖) ^ (-((d + 1 : ℕ) : ℝ)))
      (volume : Measure K) := by
    have h : Integrable (fun y : K => (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ))) (volume : Measure K) := by
      refine integrable_one_add_norm ?_
      rw [hd_def]
      push_cast
      linarith
    exact h.const_mul C
  refine continuous_of_dominated (F := fun p (y : K) => f (p • u + (y : E)))
    (bound := fun y : K => C * (1 + ‖(y : E)‖) ^ (-((d + 1 : ℕ) : ℝ))) ?_ ?_ hbound ?_
  · intro p
    exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun y => ?_
    refine le_trans (hC (p • u + (y : E))) ?_
    have hle : ‖(y : E)‖ ≤ ‖p • u + (y : E)‖ := norm_le_norm_smul_add p y
    have hmono : (1 + ‖p • u + (y : E)‖) ^ (-((d + 1 : ℕ) : ℝ))
        ≤ (1 + ‖(y : E)‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) ?_
      exact neg_nonpos.mpr (by positivity)
    have hC0 : 0 ≤ C := by
      have h0 := hC 0
      rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h0
      exact le_trans (norm_nonneg _) h0
    exact mul_le_mul_of_nonneg_left hmono hC0
  · refine Filter.Eventually.of_forall fun y => ?_
    exact f.continuous.comp (by fun_prop)


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The ray map `ω ↦ ω • u` has temperate growth. -/
theorem hasTemperateGrowth_smul_right (u : E) :
    Function.HasTemperateGrowth (fun ω : ℝ => ω • u) :=
  (ContinuousLinearMap.toSpanSingleton ℝ u).hasTemperateGrowth

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The ray map through a unit vector is antilipschitz with constant `1`. -/
theorem antilipschitzWith_smul_right {u : E} (hu : ‖u‖ = 1) :
    AntilipschitzWith 1 (fun ω : ℝ => ω • u) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  simp [dist_eq_norm, ← sub_smul, norm_smul, hu]

/-- The Radon section of a Schwartz function, realized as a Schwartz function: the inverse
Fourier transform of the Fourier slice `ω ↦ 𝓕 f (ω • u)`. -/
def radonSchwartzSection (f : SchwartzMap E ℂ) {u : E} (hu : ‖u‖ = 1) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (hasTemperateGrowth_smul_right u)
    (antilipschitzWith_smul_right hu) (𝓕 f))

theorem fourier_radonSchwartzSection (f : SchwartzMap E ℂ) {u : E} (hu : ‖u‖ = 1) :
    𝓕 (⇑(radonSchwartzSection f hu)) = fun ω : ℝ => 𝓕 (⇑f) (ω • u) := by
  set ψ : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ)
    (hasTemperateGrowth_smul_right u) (antilipschitzWith_smul_right hu) (𝓕 f) with hψ_def
  have hψ : ⇑ψ = fun ω : ℝ => 𝓕 (⇑f) (ω • u) := by
    rw [hψ_def]
    funext ω
    rw [SchwartzMap.compCLMOfAntilipschitz_apply]
    simp only [Function.comp_apply]
    rw [SchwartzMap.fourier_coe]
  have hFψ : Integrable (𝓕 (⇑ψ)) volume := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  have h : 𝓕 (𝓕⁻ (⇑ψ)) = ⇑ψ :=
    ψ.continuous.fourier_fourierInv_eq (SchwartzMap.integrable _) hFψ
  rw [radonSchwartzSection, ← hψ_def, SchwartzMap.fourierInv_coe, h, hψ]

/-- **The Radon section of a Schwartz function is a Schwartz function**: for every unit
direction, `R[f](u, ·)` coincides with the Schwartz function `radonSchwartzSection f hu`. The
proof identifies their Fourier transforms by the Fourier slice theorem, concludes almost
everywhere equality by Fourier inversion, and upgrades it to everywhere equality by
continuity. -/
theorem radonTransform_eq_radonSchwartzSection (f : SchwartzMap E ℂ) {u : E} (hu : ‖u‖ = 1) :
    radonTransform (⇑f) u = ⇑(radonSchwartzSection f hu) := by
  have hcont1 : Continuous (radonTransform (⇑f) u) := continuous_radonTransform_schwartz f u
  have hcont2 : Continuous (⇑(radonSchwartzSection f hu)) := (radonSchwartzSection f hu).continuous
  have hF1 : 𝓕 (radonTransform (⇑f) u) = fun ω : ℝ => 𝓕 (⇑f) (ω • u) := by
    funext ω
    exact (fourier_slice_radonTransform (SchwartzMap.integrable f) u hu ω).symm
  have hF2 := fourier_radonSchwartzSection f hu
  have hFint : Integrable (fun ω : ℝ => 𝓕 (⇑f) (ω • u)) volume := by
    rw [← hF2, ← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  have hint1 : Integrable (radonTransform (⇑f) u) volume :=
    integrable_radonTransform (SchwartzMap.integrable f) u hu
  have hint2 : Integrable (⇑(radonSchwartzSection f hu)) volume := SchwartzMap.integrable _
  have hae1 := hint1.fourierInv_fourier_ae_eq (by rw [hF1]; exact hFint)
  have hae2 := hint2.fourierInv_fourier_ae_eq (by rw [hF2]; exact hFint)
  have heq : 𝓕⁻ (𝓕 (radonTransform (⇑f) u)) = 𝓕⁻ (𝓕 (⇑(radonSchwartzSection f hu))) := by
    rw [hF1, hF2]
  have hae : radonTransform (⇑f) u =ᵐ[volume] ⇑(radonSchwartzSection f hu) := by
    filter_upwards [hae1, hae2] with p h1 h2
    rw [← h1, ← h2, heq]
  exact (hcont1.ae_eq_iff_eq volume hcont2).mp hae

end Schwartz

end MeasureTheory
