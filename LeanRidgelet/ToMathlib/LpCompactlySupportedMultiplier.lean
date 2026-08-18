/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma
public import LeanRidgelet.ToMathlib.LpIndicator

/-!
# Compactly supported scalar multipliers on `Lp`

This file promotes stability under measurable indicator projections to stability under
compactly supported continuous scalar multipliers.  The proof uniformly approximates a compactly
supported continuous scalar function by measurable simple functions, writes a simple multiplier as
a finite linear combination of indicator projections, and then passes to the limit in `Lp`.
-/

@[expose] public section

noncomputable section

open scoped CompactlySupported ENNReal

open Set

namespace HasCompactSupport

variable {X F : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [PseudoMetricSpace F] [Zero F]

/-- A compactly supported continuous function on one measurable space can be uniformly
approximated by measurable simple functions.  Mathlib provides the product-space version; the
one-space statement follows by adjoining a `PUnit` factor. -/
theorem exists_simpleFunc_approx {f : X → F} (hf : Continuous f) (h'f : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : MeasureTheory.SimpleFunc X F, ∀ x, dist (f x) (g x) < ε := by
  let F' : X × PUnit → F := fun x ↦ f x.1
  have hF' : Continuous F' := hf.comp continuous_fst
  have hF'compact : HasCompactSupport F' := by
    apply HasCompactSupport.intro (h'f.prod isCompact_univ)
    intro x hx
    have hx1 : x.1 ∉ tsupport f := fun hx1 ↦ hx ⟨hx1, Set.mem_univ x.2⟩
    change f x.1 = 0
    exact image_eq_zero_of_notMem_tsupport hx1
  obtain ⟨g, hg⟩ := hF'compact.exists_simpleFunc_approx_of_prod hF' hε
  let e : X → X × PUnit := fun x ↦ (x, PUnit.unit)
  have he : Measurable e := measurable_id.prodMk measurable_const
  refine ⟨g.comp e he, fun x ↦ ?_⟩
  simpa only [F', MeasureTheory.SimpleFunc.coe_comp, Function.comp_apply, e] using
    hg (x, PUnit.unit)

end HasCompactSupport

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem Lp.coeFn_finset_sum {ι : Type*}
    (s : Finset ι) (u : ι → Lp ℂ 2 μ) :
    ((∑ i ∈ s, u i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x ↦ ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
      simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert a s ha ih =>
      have hadd := Lp.coeFn_add (u a) (∑ i ∈ s, u i)
      filter_upwards [hadd, ih] with x hxadd hxsum
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [hxadd, Pi.add_apply, hxsum]

/-- The `Lp` multiplier associated with a measurable complex simple function, expressed as a
finite linear combination of measurable indicator projections. -/
noncomputable def simpleFuncMultiplierLp (s : SimpleFunc X ℂ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ∑ c ∈ s.range, c • indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
    (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f

/-- A simple-function multiplier has its expected pointwise representative. -/
theorem simpleFuncMultiplierLp_apply_ae (s : SimpleFunc X ℂ) (f : Lp ℂ 2 μ) :
    simpleFuncMultiplierLp s f =ᵐ[μ] fun x ↦ s x * f x := by
  classical
  unfold simpleFuncMultiplierLp
  have hsum := Lp.coeFn_finset_sum s.range fun c ↦
    c • indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
      (s ⁻¹' {c}) (s.measurableSet_fiber c) f
  have hterms : ∀ c ∈ s.range,
      (c • indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
        (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f : Lp ℂ 2 μ) =ᵐ[μ]
        fun x ↦ c * (⇑s ⁻¹' {c}).indicator (fun y ↦ f y) x := by
    intro c hc
    have hsmul := Lp.coeFn_smul c
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
        (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f)
    have hindicator := indicatorLp_apply_ae (p := (2 : ℝ≥0∞))
      (μ := μ) (E := ℂ) (𝕜 := ℂ) (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f
    filter_upwards [hsmul, hindicator] with x hxsmul hxindicator
    rw [hxsmul]
    change c *
      (indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
        (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f) x = _
    rw [hxindicator]
  filter_upwards [hsum, s.range.eventually_all.mpr hterms] with x hxsum hxterms
  rw [hxsum]
  calc
    (∑ c ∈ s.range,
          (c • indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ)
          (⇑s ⁻¹' {c}) (s.measurableSet_fiber c) f : Lp ℂ 2 μ) x) =
        ∑ c ∈ s.range, c * (⇑s ⁻¹' {c}).indicator (fun y ↦ f y) x := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hxterms c hc
    _ = s x * f x := by
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
      simp only [mul_ite, mul_zero, eq_comm, Finset.sum_ite_eq',
        SimpleFunc.mem_range_self, if_true]

/-- Stability under all measurable indicator projections implies stability under a measurable
simple scalar multiplier. -/
theorem simpleFuncMultiplierLp_mem_of_indicatorLp_mem
    (K : ClosedSubmodule ℂ (Lp ℂ 2 μ)) (s : SimpleFunc X ℂ)
    {f : Lp ℂ 2 μ}
    (hindicator : ∀ (t : Set X) (ht : MeasurableSet t),
      indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) t ht f ∈ K) :
    simpleFuncMultiplierLp s f ∈ K := by
  classical
  apply Submodule.sum_mem
  intro c hc
  exact K.smul_mem c (hindicator (⇑s ⁻¹' {c}) (s.measurableSet_fiber c))

variable [TopologicalSpace X] [R1Space X] [BorelSpace X]

omit [R1Space X] in
/-- A compactly supported continuous scalar function belongs to every finite-exponent `Lp` space
for a measure finite on compact sets. -/
theorem compactlySupportedContinuous_memLp [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, ℂ)) : MemLp f 2 μ :=
  f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

/-- The linear map sending a compactly supported continuous scalar function to its `L²` class. -/
noncomputable def compactlySupportedContinuousToLp [IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℂ) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (compactlySupportedContinuous_memLp f).toLp f
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ by simp
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x ↦ by simp

/-- Multiplication of an `Lp` class by a compactly supported continuous scalar function. -/
noncomputable def compactlySupportedContinuousMultiplierLp
    (φ : C_c(X, ℂ)) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ := by
  let C : ℝ := ‖φ.toBoundedContinuousFunction‖
  have hmem : MemLp (fun x ↦ φ x * f x) 2 μ := by
    apply MemLp.of_le_mul (c := C) (Lp.memLp f)
      (φ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards with x
    change ‖φ x * f x‖ ≤ C * ‖f x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (φ.toBoundedContinuousFunction.norm_coe_le_norm x) (norm_nonneg _)
  exact hmem.toLp fun x ↦ φ x * f x

omit [R1Space X] in
/-- The compactly supported continuous multiplier has its expected pointwise representative. -/
theorem compactlySupportedContinuousMultiplierLp_apply_ae
    (φ : C_c(X, ℂ)) (f : Lp ℂ 2 μ) :
    compactlySupportedContinuousMultiplierLp φ f =ᵐ[μ] fun x ↦ φ x * f x := by
  unfold compactlySupportedContinuousMultiplierLp
  exact MemLp.coeFn_toLp _

/-- A closed subspace stable under every measurable indicator projection is stable under every
compactly supported continuous scalar multiplier. -/
theorem compactlySupportedContinuousMultiplierLp_mem_of_indicatorLp_mem
    (K : ClosedSubmodule ℂ (Lp ℂ 2 μ)) (φ : C_c(X, ℂ))
    {f : Lp ℂ 2 μ}
    (hindicator : ∀ (t : Set X) (ht : MeasurableSet t),
      indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) t ht f ∈ K) :
    compactlySupportedContinuousMultiplierLp φ f ∈ K := by
  choose s hs using fun n : ℕ ↦ φ.hasCompactSupport.exists_simpleFunc_approx φ.continuous
    (show 0 < (1 : ℝ) / (n + 1) by positivity)
  have hsK : ∀ n, simpleFuncMultiplierLp (s n) f ∈ K := fun n ↦
    simpleFuncMultiplierLp_mem_of_indicatorLp_mem K (s n) hindicator
  apply K.isClosed.mem_of_tendsto (b := Filter.atTop)
    (f := fun n ↦ simpleFuncMultiplierLp (s n) f)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n ↦ norm_nonneg _)
        (fun n ↦ ?_)
        (show Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1) * ‖f‖)
            Filter.atTop (nhds 0) by
          simpa using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖f‖)
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have hsimple := simpleFuncMultiplierLp_apply_ae (s n) f
    have hcontinuous := compactlySupportedContinuousMultiplierLp_apply_ae φ f
    have hsub := Lp.coeFn_sub (simpleFuncMultiplierLp (s n) f)
      (compactlySupportedContinuousMultiplierLp φ f)
    filter_upwards [hsimple, hcontinuous, hsub] with x hsimplex hcontinuousx hsubx
    rw [hsubx, Pi.sub_apply, hsimplex, hcontinuousx, ← sub_mul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply le_of_lt
    rw [← dist_eq_norm, dist_comm]
    exact hs n x
  · exact Filter.Eventually.of_forall hsK

/-- If a continuous representative belongs to a closed subspace stable under measurable
indicators, then it can be approximated by compactly supported continuous representatives in the
same subspace. -/
theorem exists_compactlySupportedContinuousToLp_mem_dist_lt
    [LocallyCompactSpace X] [NormalSpace X] [μ.Regular]
    (K : ClosedSubmodule ℂ (Lp ℂ 2 μ))
    {g : X → ℂ} (hgcontinuous : Continuous g) (hgmem : MemLp g 2 μ)
    (hindicator : ∀ (t : Set X) (ht : MeasurableSet t),
      indicatorLp (p := (2 : ℝ≥0∞)) (μ := μ) (E := ℂ) (𝕜 := ℂ) t ht
        (hgmem.toLp g) ∈ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : C_c(X, ℂ), compactlySupportedContinuousToLp r ∈ K ∧
      dist (compactlySupportedContinuousToLp r) (hgmem.toLp g) < ε := by
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  obtain ⟨h, hhcompact, hhclose, hhcontinuous, hhmem⟩ :=
    hgmem.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.coe_ne_top hδ
  obtain ⟨k, hkcompact, hhk⟩ := exists_compact_superset hhcompact
  obtain ⟨φ, hφone, hφcompact, _hφsupport, hφrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hhcompact isOpen_interior hhk
  let φc : C_c(X, ℂ) :=
    { toFun := fun x ↦ φ x
      continuous_toFun := Complex.continuous_ofReal.comp φ.continuous
      hasCompactSupport' := by
        change HasCompactSupport (Complex.ofReal ∘ (φ : X → ℝ))
        exact (show HasCompactSupport (φ : X → ℝ) from hφcompact).comp_left
          Complex.ofReal_zero }
  let r : C_c(X, ℂ) :=
    { toFun := fun x ↦ φc x * g x
      continuous_toFun := φc.continuous.mul hgcontinuous
      hasCompactSupport' := φc.hasCompactSupport.mul_right }
  have hφh : ∀ x, φc x * h x = h x := by
    intro x
    by_cases hx : x ∈ tsupport h
    · change (φ x : ℂ) * h x = h x
      rw [hφone hx]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hφnorm : ∀ x, ‖(1 : ℂ) - φc x‖ ≤ 1 := by
    intro x
    change ‖(1 : ℂ) - (φ x : ℂ)‖ ≤ 1
    have hreal : 0 ≤ 1 - φ x := by linarith [(hφrange x).2]
    calc
      ‖(1 : ℂ) - (φ x : ℂ)‖ = |1 - φ x| := by norm_cast
      _ = 1 - φ x := abs_of_nonneg hreal
      _ ≤ 1 := by linarith [(hφrange x).1]
  have hreqlp : compactlySupportedContinuousToLp r =
      compactlySupportedContinuousMultiplierLp φc (hgmem.toLp g) := by
    change (compactlySupportedContinuous_memLp (μ := μ) r).toLp r = _
    apply Lp.ext
    have hr := (compactlySupportedContinuous_memLp (μ := μ) r).coeFn_toLp
    have hmult := compactlySupportedContinuousMultiplierLp_apply_ae φc (hgmem.toLp g)
    have hg := hgmem.coeFn_toLp
    filter_upwards [hr, hmult, hg] with x hrx hmultx hgx
    rw [hrx, hmultx, hgx]
    rfl
  refine ⟨r, ?_, ?_⟩
  · rw [hreqlp]
    exact compactlySupportedContinuousMultiplierLp_mem_of_indicatorLp_mem K φc hindicator
  · rw [Lp.dist_edist]
    have hmono : eLpNorm ((fun x ↦ r x) - g) 2 μ ≤ eLpNorm (g - h) 2 μ := by
      apply eLpNorm_mono
      intro x
      change ‖φc x * g x - g x‖ ≤ ‖g x - h x‖
      rw [norm_sub_rev]
      calc
        ‖g x - φc x * g x‖ = ‖((1 : ℂ) - φc x) * (g x - h x)‖ := by
          congr 1
          rw [sub_mul, one_mul, mul_sub, hφh]
          ring
        _ = ‖(1 : ℂ) - φc x‖ * ‖g x - h x‖ := norm_mul _ _
        _ ≤ 1 * ‖g x - h x‖ :=
          mul_le_mul_of_nonneg_right (hφnorm x) (norm_nonneg _)
        _ = ‖g x - h x‖ := one_mul _
    have hed : edist (compactlySupportedContinuousToLp r) (hgmem.toLp g) ≤
        ENNReal.ofReal (ε / 2) := by
      rw [hreqlp]
      calc
        edist (compactlySupportedContinuousMultiplierLp φc (hgmem.toLp g))
            (hgmem.toLp g) = eLpNorm ((fun x ↦ r x) - g) 2 μ := by
              rw [← hreqlp]
              change edist ((compactlySupportedContinuous_memLp (μ := μ) r).toLp r)
                (hgmem.toLp g) = _
              rw [Lp.edist_toLp_toLp]
        _ ≤ eLpNorm (g - h) 2 μ := hmono
        _ ≤ ENNReal.ofReal (ε / 2) := hhclose
    calc
      (edist (compactlySupportedContinuousToLp r) (hgmem.toLp g)).toReal ≤ ε / 2 := by
        rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 2)]
        exact ENNReal.toReal_mono (by finiteness) hed
      _ < ε := by linarith

end MeasureTheory
