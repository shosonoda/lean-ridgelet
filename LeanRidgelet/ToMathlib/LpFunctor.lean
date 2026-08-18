/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Functoriality of pointwise bounded maps on Bochner `Lp`

Mathlib's `ContinuousLinearMap.compLpL` applies a bounded linear map to a Bochner `Lp` class.
This file records the elementary functor laws which are useful when finite-dimensional value
spaces are decomposed into coordinates: the lift preserves zero, identity, composition, and
finite sums.  In particular, a finite orthonormal resolution of the identity on the value space
lifts to a resolution of the identity on Bochner `Lp`.  A small nontriviality criterion records
that a measurable set of positive finite measure supplies a nonzero indicator class; this is the
standard input needed when a faithful `Lp` functor is used abstractly.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [Nontrivial E]
  {p : ℝ≥0∞} {μ : Measure X}

/-- A measurable set of positive finite measure gives a nontrivial Bochner `Lp` space for every
nonzero finite exponent.  The witness is the indicator of the set with any nonzero constant
value. -/
theorem nontrivial_Lp_of_exists_measurableSet (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (s : Set X) (hs : MeasurableSet s) (hs_zero : μ s ≠ 0) (hs_top : μ s ≠ ∞) :
    Nontrivial (Lp E p μ) := by
  obtain ⟨c, hc⟩ : ∃ c : E, c ≠ 0 := exists_ne 0
  apply nontrivial_of_ne (indicatorConstLp p hs hs_top c) 0
  intro hzero
  have hnorm : ‖c‖ * μ.real s ^ (1 / p.toReal) = 0 := by
    simpa only [norm_indicatorConstLp hp_zero hp_top, Lp.norm_zero] using
      congrArg (fun f : Lp E p μ ↦ ‖f‖) hzero
  have hmeasureReal_ne : μ.real s ≠ 0 :=
    (measureReal_ne_zero_iff hs_top).mpr hs_zero
  have hmeasureReal_pos : 0 < μ.real s :=
    lt_of_le_of_ne measureReal_nonneg hmeasureReal_ne.symm
  have hnorm_pos : 0 < ‖c‖ * μ.real s ^ (1 / p.toReal) :=
    mul_pos (norm_pos_iff.mpr hc) (Real.rpow_pos_of_pos hmeasureReal_pos _)
  exact (ne_of_gt hnorm_pos) hnorm

end MeasureTheory

namespace ContinuousLinearMap

variable {X 𝕜 E F G ι : Type*} [MeasurableSpace X]
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ℝ≥0∞} {μ : Measure X} [Fact (1 ≤ p)]

/-- Pointwise `Lp` lifting sends the zero bounded map to zero. -/
@[simp]
theorem zero_compLpL : (0 : E →L[𝕜] F).compLpL p μ = 0 := by
  ext f
  filter_upwards [(0 : E →L[𝕜] F).coeFn_compLpL f,
    Lp.coeFn_zero F p μ] with x hzero hout
  simpa using hzero.trans hout.symm

/-- Pointwise `Lp` lifting sends the identity bounded map to the identity. -/
@[simp]
theorem id_compLpL : (ContinuousLinearMap.id 𝕜 E).compLpL p μ =
    ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext f
  filter_upwards [(ContinuousLinearMap.id 𝕜 E).coeFn_compLpL f] with x hx
  exact hx

/-- Pointwise `Lp` lifting preserves composition. -/
theorem comp_compLpL (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A.comp B).compLpL p μ = A.compLpL p μ ∘L B.compLpL p μ := by
  ext f
  filter_upwards [(A.comp B).coeFn_compLpL f,
    A.coeFn_compLpL (B.compLpL p μ f), B.coeFn_compLpL f] with x hab ha hb
  simpa only [comp_apply] using hab.trans ((congrArg A hb.symm).trans ha.symm)

/-- Pointwise `Lp` lifting preserves subtraction. -/
theorem sub_compLpL (A B : E →L[𝕜] F) :
    (A - B).compLpL p μ = A.compLpL p μ - B.compLpL p μ := by
  ext f
  filter_upwards [(A - B).coeFn_compLpL f, A.coeFn_compLpL f, B.coeFn_compLpL f,
    Lp.coeFn_sub (A.compLpL p μ f) (B.compLpL p μ f)] with x hab ha hb hout
  simpa only [sub_apply] using
    hab.trans ((congrArg₂ (· - ·) ha hb).symm.trans hout.symm)

/-- Pointwise `Lp` lifting commutes with a finite sum of bounded maps. -/
theorem finsetSum_compLpL (s : Finset ι) (A : ι → E →L[𝕜] F) :
    (∑ i ∈ s, A i).compLpL p μ = ∑ i ∈ s, (A i).compLpL p μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, add_compLpL]

section Faithful

variable {X' K V W : Type*} [MeasurableSpace X'] [RCLike K]
  [NormedAddCommGroup V] [NormedSpace K V]
  [NormedAddCommGroup W] [InnerProductSpace K W]
  {q : ℝ≥0∞} {ν : Measure X'} [Fact (1 ≤ q)]

/-- If scalar `Lp` is nontrivial, pointwise `Lp` lifting is faithful on bounded maps whose
codomain is an inner product space.  This is the analytic replacement for faithfulness of tensoring
with a nonzero Hilbert space in finite-output arguments. -/
theorem compLpL_injective [Nontrivial (Lp K q ν)] :
    Function.Injective (fun A : V →L[K] W ↦ A.compLpL q ν) := by
  intro A B hAB
  obtain ⟨f : Lp K q ν, hf⟩ := exists_ne (0 : Lp K q ν)
  ext x
  by_contra hx
  let z : W := A x - B x
  have hz : z ≠ 0 := sub_ne_zero.mpr hx
  let J : K →L[K] V := ContinuousLinearMap.toSpanSingleton K x
  let Q : W →L[K] K := innerSL K z
  change A.compLpL q ν = B.compLpL q ν at hAB
  have hzero : ((A - B).comp J).compLpL q ν f = 0 := by
    rw [comp_compLpL]
    change (A - B).compLpL q ν (J.compLpL q ν f) = 0
    rw [sub_compLpL, hAB, sub_self, zero_apply]
  have hspan : (A - B).comp J = ContinuousLinearMap.toSpanSingleton K z := by
    apply ContinuousLinearMap.ext
    intro c
    simpa [J, z, sub_apply] using (smul_sub c (A x) (B x)).symm
  have hQ : (Q.comp (ContinuousLinearMap.toSpanSingleton K z)).compLpL q ν f = 0 := by
    rw [comp_compLpL, ContinuousLinearMap.comp_apply, ← hspan, hzero, map_zero]
  have hscalar : Q.comp (ContinuousLinearMap.toSpanSingleton K z) =
      inner K z z • ContinuousLinearMap.id K K := by
    apply ContinuousLinearMap.ext
    intro c
    simp [Q, mul_comm]
  rw [hscalar, smul_compLpL, id_compLpL] at hQ
  have : inner K z z = 0 ∨ f = 0 := smul_eq_zero.mp hQ
  exact this.elim (fun hzinner ↦ hz (inner_self_eq_zero.mp hzinner)) hf

end Faithful

section Coordinates

variable {X' K V ι' : Type*} [MeasurableSpace X'] [RCLike K]
  [NormedAddCommGroup V] [InnerProductSpace K V]
  {q : ℝ≥0∞} {ν : Measure X'} [Fact (1 ≤ q)]

/-- Embed scalar `Lp` into vector-valued `Lp` along a fixed value vector. -/
def lpCoordinateEmbedding (v : V) : Lp K q ν →L[K] Lp V q ν :=
  (ContinuousLinearMap.toSpanSingleton K v).compLpL q ν

/-- Extract the coefficient along a fixed value vector pointwise on `Lp`. -/
def lpCoordinateProjection (v : V) : Lp V q ν →L[K] Lp K q ν :=
  (innerSL K v).compLpL q ν

theorem lpCoordinateEmbedding_apply_ae (v : V) (f : Lp K q ν) :
    lpCoordinateEmbedding (q := q) (ν := ν) v f =ᵐ[ν] fun x ↦ f x • v := by
  simpa [lpCoordinateEmbedding] using
    (ContinuousLinearMap.toSpanSingleton K v).coeFn_compLpL f

theorem lpCoordinateProjection_apply_ae (v : V) (f : Lp V q ν) :
    lpCoordinateProjection (q := q) (ν := ν) v f =ᵐ[ν] fun x ↦ inner K v (f x) := by
  simpa [lpCoordinateProjection] using (innerSL K v).coeFn_compLpL f

/-- The pointwise rank-one operator is coordinate embedding after coordinate projection. -/
theorem rankOne_compLpL_eq_coordinate_comp (v w : V) :
    (InnerProductSpace.rankOne K v w).compLpL q ν =
      lpCoordinateEmbedding (q := q) (ν := ν) v ∘L
        lpCoordinateProjection (q := q) (ν := ν) w := by
  rw [InnerProductSpace.rankOne_def', comp_compLpL]
  rfl

/-- A finite orthonormal basis gives a coordinate resolution of the identity on Bochner `Lp`. -/
theorem sum_lpCoordinateEmbedding_comp_projection_eq_id [Fintype ι']
    (b : OrthonormalBasis ι' K V) :
    ∑ i, lpCoordinateEmbedding (q := q) (ν := ν) (b i) ∘L
        lpCoordinateProjection (q := q) (ν := ν) (b i) =
      ContinuousLinearMap.id K (Lp V q ν) := by
  simp_rw [← rankOne_compLpL_eq_coordinate_comp]
  rw [← finsetSum_compLpL, b.sum_rankOne_eq_id, id_compLpL]

/-- A bounded operator on vector-valued `Lp` whose matrix coefficients are scalar operators on
scalar `Lp` is the pointwise lift of one bounded value-space operator.  This finite-dimensional
reconstruction is the coordinate form of the elementary finite-factor tensor-product argument. -/
theorem exists_eq_compLpL_of_matrixCoefficient_scalar [Fintype ι']
    (b : OrthonormalBasis ι' K V) (P : Lp V q ν →L[K] Lp V q ν)
    (hP : ∀ i j, ∃ c : K,
      lpCoordinateProjection (q := q) (ν := ν) (b i) ∘L P ∘L
          lpCoordinateEmbedding (q := q) (ν := ν) (b j) =
        c • ContinuousLinearMap.id K (Lp K q ν)) :
    ∃ C : V →L[K] V, P = C.compLpL q ν := by
  classical
  choose c hc using hP
  let J : ι' → Lp K q ν →L[K] Lp V q ν := fun i ↦
    lpCoordinateEmbedding (q := q) (ν := ν) (b i)
  let Q : ι' → Lp V q ν →L[K] Lp K q ν := fun i ↦
    lpCoordinateProjection (q := q) (ν := ν) (b i)
  let C : V →L[K] V :=
    ∑ i, ∑ j, c i j • InnerProductSpace.rankOne K (b i) (b j)
  refine ⟨C, ?_⟩
  have hI : ∑ i, J i ∘L Q i = ContinuousLinearMap.id K (Lp V q ν) := by
    exact sum_lpCoordinateEmbedding_comp_projection_eq_id b
  have hC : C.compLpL q ν = ∑ i, ∑ j, c i j • (J i ∘L Q j) := by
    dsimp only [C, J, Q]
    simp_rw [finsetSum_compLpL, smul_compLpL,
      rankOne_compLpL_eq_coordinate_comp]
  apply ContinuousLinearMap.ext
  intro f
  calc
    P f = (∑ i, J i ∘L Q i) (P ((∑ j, J j ∘L Q j) f)) := by rw [hI]; rfl
    _ = ∑ i, ∑ j, J i ((Q i ∘L P ∘L J j) (Q j f)) := by
      simp_rw [sum_apply, comp_apply, map_sum]
    _ = ∑ i, ∑ j, J i
        ((c i j • ContinuousLinearMap.id K (Lp K q ν)) (Q j f)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc i j]
    _ = (∑ i, ∑ j, c i j • (J i ∘L Q j)) f := by
      simp_rw [sum_apply, smul_apply, comp_apply, id_apply, map_smul]
    _ = C.compLpL q ν f := DFunLike.congr_fun hC.symm f

end Coordinates

end ContinuousLinearMap

namespace OrthonormalBasis

variable {X 𝕜 E ι : Type*} [MeasurableSpace X] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {p : ℝ≥0∞} {μ : Measure X} [Fact (1 ≤ p)]

/-- A finite orthonormal resolution of the identity remains a resolution of the identity after
applying its rank-one operators pointwise on Bochner `Lp`. -/
theorem sum_rankOne_compLpL_eq_id (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, (InnerProductSpace.rankOne 𝕜 (b i) (b i)).compLpL p μ =
      ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  rw [← ContinuousLinearMap.finsetSum_compLpL]
  rw [b.sum_rankOne_eq_id, ContinuousLinearMap.id_compLpL]

end OrthonormalBasis
