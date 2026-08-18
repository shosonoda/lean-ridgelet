/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Indicator projections on Bochner `Lp`

Multiplication by the indicator of a measurable set is a contractive idempotent bounded linear
operator on every Bochner `Lp` space.  On scalar `L²` these are the canonical multiplication
projections in a system of imprimitivity; their self-adjointness and orthogonal star-projection
property are proved from the integral inner product.  This file develops the operator independently
of any group action so that quasi-regular and induced representations can reuse it.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {X E 𝕜 : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} {μ : Measure X}

/-- The `MemLp` witness for restricting an `Lp` class to a measurable set. -/
theorem indicatorMemLp (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    MemLp (s.indicator fun x ↦ f x) p μ :=
  (Lp.memLp f).indicator hs

/-- The linear map on `Lp` represented by multiplication by the indicator of a measurable set. -/
noncomputable def indicatorLpLinearMap (s : Set X) (hs : MeasurableSet s) :
    Lp E p μ →ₗ[𝕜] Lp E p μ where
  toFun f := (indicatorMemLp s hs f).toLp (s.indicator fun x ↦ f x)
  map_add' f g := by
    let hsum := (Lp.memLp (f + g)).indicator hs
    let hf := (Lp.memLp f).indicator hs
    let hg := (Lp.memLp g).indicator hs
    change hsum.toLp _ = hf.toLp _ + hg.toLp _
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add f g] with x hx
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, Pi.add_apply, hx]
    · simp only [Set.indicator_of_notMem hxs, Pi.add_apply, add_zero]
  map_smul' c f := by
    let hcf := (Lp.memLp (c • f)).indicator hs
    let hf := (Lp.memLp f).indicator hs
    change hcf.toLp _ = c • hf.toLp _
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul c f] with x hx
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, Pi.smul_apply, hx]
    · simp only [Set.indicator_of_notMem hxs, Pi.smul_apply, smul_zero]

/-- The underlying indicator linear map has the expected pointwise representative. -/
theorem indicatorLpLinearMap_apply_ae (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    indicatorLpLinearMap (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f =ᵐ[μ]
      s.indicator fun x ↦ f x := by
  change
    ((indicatorMemLp s hs f).toLp (s.indicator fun x ↦ f x) : Lp E p μ) =ᵐ[μ]
      s.indicator fun x ↦ f x
  exact MemLp.coeFn_toLp (indicatorMemLp s hs f)

variable [Fact (1 ≤ p)]

/-- Multiplication by a measurable indicator as a contractive bounded linear operator on `Lp`. -/
noncomputable def indicatorLp (s : Set X) (hs : MeasurableSet s) :
    Lp E p μ →L[𝕜] Lp E p μ :=
  (indicatorLpLinearMap (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs).mkContinuous 1 fun f ↦ by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have hout := indicatorLpLinearMap_apply_ae
      (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f
    filter_upwards [hout] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, one_mul]
      exact le_rfl
    · simp only [Set.indicator_of_notMem hxs, norm_zero, one_mul, norm_nonneg]

/-- The indicator operator has the expected pointwise representative. -/
theorem indicatorLp_apply_ae (s : Set X) (hs : MeasurableSet s) (f : Lp E p μ) :
    indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f =ᵐ[μ]
      s.indicator fun x ↦ f x := by
  exact indicatorLpLinearMap_apply_ae (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f

/-- Indicator multiplication is idempotent. -/
theorem indicatorLp_comp_self (s : Set X) (hs : MeasurableSet s) :
    indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs ∘L
        indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs =
      indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have houter := indicatorLp_apply_ae (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs
    (indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f)
  have hinner := indicatorLp_apply_ae (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f
  filter_upwards [houter, hinner] with x houterx hinnerx
  change
    (indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs
      (indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f)) x =
        (indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) s hs f) x
  rw [houterx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs]
    simpa only [Set.indicator_of_notMem hxs] using hinnerx.symm

/-- The indicator of the whole space is the identity operator on `Lp`. -/
@[simp]
theorem indicatorLp_univ :
    indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) Set.univ MeasurableSet.univ =
      ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have h := indicatorLp_apply_ae (p := p) (μ := μ) (E := E) (𝕜 := 𝕜)
    Set.univ MeasurableSet.univ f
  filter_upwards [h] with x hx
  simpa using hx

/-- The indicator of the empty set is the zero operator on `Lp`. -/
@[simp]
theorem indicatorLp_empty :
    indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜) ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have h := indicatorLp_apply_ae (p := p) (μ := μ) (E := E) (𝕜 := 𝕜)
    ∅ MeasurableSet.empty f
  filter_upwards [h, Lp.coeFn_zero E p μ] with x hx hzero
  have hx0 : (indicatorLp (p := p) (μ := μ) (E := E) (𝕜 := 𝕜)
      ∅ MeasurableSet.empty f) x = 0 := by
    simpa only [Set.indicator_empty', Pi.zero_apply] using hx
  exact hx0.trans hzero.symm

end MeasureTheory

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- On scalar complex `L²`, multiplication by a measurable indicator is self-adjoint. -/
theorem indicatorLp_isSelfAdjoint (s : Set X) (hs : MeasurableSet s) :
    IsSelfAdjoint (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hf := indicatorLp_apply_ae (p := (2 : ℝ≥0∞))
    (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f
  have hg := indicatorLp_apply_ae (p := (2 : ℝ≥0∞))
    (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs g
  filter_upwards [hf, hg] with x hfx hgx
  change
    inner ℂ ((indicatorLp (p := (2 : ℝ≥0∞))
      (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f) x) (g x) =
      inner ℂ (f x) ((indicatorLp (p := (2 : ℝ≥0∞))
        (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs g) x)
  rw [hfx, hgx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- On scalar complex `L²`, multiplication by a measurable indicator is an orthogonal
projection. -/
theorem indicatorLp_isStarProjection (s : Set X) (hs : MeasurableSet s) :
    IsStarProjection (indicatorLp (p := (2 : ℝ≥0∞))
      (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs) := by
  constructor
  · change
      indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs ∘L
          indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs =
        indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs
    exact indicatorLp_comp_self s hs
  · exact indicatorLp_isSelfAdjoint s hs

/-- If the orthogonal projection onto a closed subspace commutes with a measurable-set
projection, then that closed subspace is stable under the corresponding indicator
multiplication. -/
theorem indicatorLp_mem_of_starProjection_commute
    (K : ClosedSubmodule ℂ (Lp ℂ 2 μ))
    (s : Set X) (hs : MeasurableSet s)
    (hcommute :
      K.toSubmodule.starProjection.comp
          (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs) =
        (indicatorLp (p := (2 : ℝ≥0∞))
          (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs).comp K.toSubmodule.starProjection)
    {f : Lp ℂ 2 μ} (hf : f ∈ K) :
    indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f ∈ K := by
  apply K.toSubmodule.starProjection_eq_self_iff.mp
  have h := DFunLike.congr_fun hcommute f
  simpa only [ContinuousLinearMap.comp_apply,
    K.toSubmodule.starProjection_eq_self_iff.mpr hf] using h

/-- If every measurable indicator restriction of `f` belongs to a submodule of scalar `L²`, then
every vector orthogonal to that submodule vanishes almost everywhere on the set where `f` does not
vanish.

Testing orthogonality against the indicator restrictions of `f` says exactly that the integrable
pointwise inner product `⟪f, v⟫` has vanishing integral over every measurable set, hence vanishes
almost everywhere.  This is the elementary mechanism behind the fact that a closed subspace stable
under all multiplication projections is the set of vectors supported in a fixed measurable set. -/
theorem ae_eq_zero_of_mem_orthogonal_of_indicatorLp_mem
    {K : Submodule ℂ (Lp ℂ 2 μ)} {f v : Lp ℂ 2 μ}
    (hf : ∀ (s : Set X) (hs : MeasurableSet s),
      indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f ∈ K)
    (hv : v ∈ Kᗮ) :
    ∀ᵐ x ∂μ, f x ≠ 0 → v x = 0 := by
  have hint : Integrable (fun x ↦ (inner ℂ (f x) (v x) : ℂ)) μ := L2.integrable_inner f v
  have hzero : ∀ s : Set X, MeasurableSet s → μ s < ⊤ →
      ∫ x in s, (inner ℂ (f x) (v x) : ℂ) ∂μ = 0 := by
    intro s hs _
    have hinner : (inner ℂ (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f)
        v : ℂ) = 0 := (Submodule.mem_orthogonal K v).mp hv _ (hf s hs)
    rw [L2.inner_def] at hinner
    have hcongr : ∀ᵐ x ∂μ,
        (inner ℂ ((indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) s hs f) x)
          (v x) : ℂ) = s.indicator (fun y ↦ (inner ℂ (f y) (v y) : ℂ)) x := by
      filter_upwards [indicatorLp_apply_ae (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
        s hs f] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [← integral_indicator hs, ← integral_congr_ae hcongr]
    exact hinner
  have hae := hint.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun s _ _ ↦ hint.integrableOn) hzero
  filter_upwards [hae] with x hx hfx
  have hx' : v x * (starRingEnd ℂ) (f x) = 0 := by
    simpa only [RCLike.inner_apply, Pi.zero_apply] using hx
  rcases mul_eq_zero.mp hx' with h | h
  · exact h
  · exact absurd (by simpa using congrArg (starRingEnd ℂ) h) hfx

end MeasureTheory
