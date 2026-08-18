/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Defs

/-!
# Haar measure on the unit group of a finite-dimensional real algebra

The group of units of a finite-dimensional real normed algebra `A` is an open subset of `A`, and its
Haar measure is an explicit weighted additive Haar measure: the weight is the reciprocal absolute
algebra norm `|Algebra.norm ℝ a|⁻¹`, that is, the reciprocal absolute determinant of left
multiplication by `a`. Multiplicativity of the algebra norm is exactly what makes the weighted
measure invariant under left multiplication by units, so no determinant power has to be computed.

## Main results

* `MeasureTheory.Measure.unitsHaar`: the weighted additive Haar measure of `A`, transported to `Aˣ`
  along the open embedding `Units.val`.
* `MeasureTheory.Measure.isHaarMeasure_unitsHaar`: it is a Haar measure of the unit group.
* `MeasureTheory.Measure.exists_haar_eq_smul_unitsHaar`: consequently the canonical Haar measure of
  the unit group is a positive multiple of it.
* `MeasureTheory.Measure.exists_map_units_val_haar_restrict_le`: on a compact subset of the unit
  group, the image of Haar measure under `Units.val` is dominated by additive Haar measure. This is
  the comparison used to prove local integrability of functions pulled back from `A`.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Left multiplication as a linear map is the algebra multiplication map used by the algebra
norm. -/
theorem lmul_eq_mulLeft (a : A) :
    (Algebra.lmul ℝ A a : A →ₗ[ℝ] A) = LinearMap.mulLeft ℝ a :=
  LinearMap.ext fun _ ↦ rfl

/-- The algebra norm of a finite-dimensional real normed algebra is continuous: it is the
determinant of left multiplication, which depends continuously on the multiplier. -/
theorem continuous_algebraNorm : Continuous (Algebra.norm ℝ : A → ℝ) := by
  have hlinear : ∀ a : A,
      (Algebra.lmul ℝ A a : A →ₗ[ℝ] A) =
        ((ContinuousLinearMap.mul ℝ A a : A →L[ℝ] A) : A →ₗ[ℝ] A) := by
    intro a
    exact LinearMap.ext fun b ↦ rfl
  have hfun : (Algebra.norm ℝ : A → ℝ) =
      fun a ↦ LinearMap.det ((ContinuousLinearMap.mul ℝ A a : A →L[ℝ] A) : A →ₗ[ℝ] A) := by
    funext a
    rw [Algebra.norm_apply, hlinear a]
  rw [hfun]
  exact ContinuousLinearMap.continuous_det.comp (ContinuousLinearMap.mul ℝ A).continuous

/-- The algebra norm of a unit is nonzero. -/
theorem algebraNorm_units_ne_zero (u : Aˣ) : Algebra.norm ℝ (u : A) ≠ 0 :=
  isUnit_iff_ne_zero.mp (u.isUnit.map (Algebra.norm ℝ))

/-- The density turning the additive Haar measure of a finite-dimensional real algebra into the
multiplicative Haar measure of its unit group: the reciprocal absolute algebra norm.

Multiplicativity of the algebra norm makes this density a multiplicative cocycle, which is the only
property used in the invariance proof; in particular no determinant power in the dimension of `A`
has to be evaluated. -/
def unitsHaarDensity (a : A) : ℝ≥0∞ := ENNReal.ofReal |Algebra.norm ℝ a|⁻¹

theorem unitsHaarDensity_apply (a : A) :
    unitsHaarDensity a = ENNReal.ofReal |Algebra.norm ℝ a|⁻¹ := rfl

theorem continuous_unitsHaarDensity_comp_units_val :
    Continuous fun u : Aˣ ↦ |Algebra.norm ℝ (u : A)|⁻¹ :=
  ((continuous_algebraNorm.comp Units.continuous_val).abs).inv₀ fun u ↦
    abs_ne_zero.mpr (algebraNorm_units_ne_zero u)

/-- The density is multiplicative, because the algebra norm is. -/
theorem unitsHaarDensity_mul (a b : A) :
    unitsHaarDensity (a * b) = unitsHaarDensity a * unitsHaarDensity b := by
  rw [unitsHaarDensity_apply, unitsHaarDensity_apply, unitsHaarDensity_apply, map_mul, abs_mul,
    mul_inv, ← ENNReal.ofReal_mul (by positivity)]

@[simp]
theorem unitsHaarDensity_one : unitsHaarDensity (1 : A) = 1 := by
  rw [unitsHaarDensity_apply, map_one, abs_one, inv_one, ENNReal.ofReal_one]

theorem unitsHaarDensity_units_ne_zero (u : Aˣ) : unitsHaarDensity (u : A) ≠ 0 := by
  rw [unitsHaarDensity_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact inv_pos.mpr (abs_pos.mpr (algebraNorm_units_ne_zero u))

theorem unitsHaarDensity_units_ne_top (u : Aˣ) : unitsHaarDensity (u : A) ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem unitsHaarDensity_units_inv_mul_units (u : Aˣ) :
    unitsHaarDensity ((u⁻¹ : Aˣ) : A) * unitsHaarDensity (u : A) = 1 := by
  rw [← unitsHaarDensity_mul]
  simp

/-- On a compact subset of the unit group the density is bounded. -/
theorem exists_unitsHaarDensity_le_of_isCompact {S : Set Aˣ} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a ∈ Units.val '' S, unitsHaarDensity a ≤ C := by
  obtain ⟨M, hM⟩ := hS.bddAbove_image
    (continuous_unitsHaarDensity_comp_units_val (A := A)).continuousOn
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, ?_⟩
  rintro a ⟨u, hu, rfl⟩
  exact ENNReal.ofReal_le_ofReal (hM ⟨u, hu, rfl⟩)

variable [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]

omit [FiniteDimensional ℝ A] in
theorem measurable_unitsHaarDensity : Measurable (unitsHaarDensity : A → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp continuous_algebraNorm.abs.measurable.inv

variable (μ : Measure A)

/-- The additive Haar measure of a finite-dimensional real algebra, weighted by the reciprocal
absolute algebra norm, is invariant under left multiplication by a unit: the determinant factor
produced by the change of variables cancels against the multiplicative weight. -/
theorem map_mul_left_withDensity_unitsHaarDensity [μ.IsAddHaarMeasure] (u : Aˣ) :
    Measure.map (fun b : A ↦ (u : A) * b) (μ.withDensity unitsHaarDensity) =
      μ.withDensity unitsHaarDensity := by
  have hlinear : (fun b : A ↦ (u : A) * b) = (LinearMap.mulLeft ℝ (u : A) : A → A) := rfl
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (u : A)) ≠ 0 := by
    have hnorm := algebraNorm_units_ne_zero (A := A) u
    rw [Algebra.norm_apply] at hnorm
    exact hnorm
  have hmeasurable : Measurable (fun b : A ↦ (u : A) * b) := measurable_const_mul _
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hmeasurable hs,
    withDensity_apply _ (hmeasurable hs), withDensity_apply _ hs]
  have hshift : ∀ b : A,
      unitsHaarDensity b =
        unitsHaarDensity ((u⁻¹ : Aˣ) : A) * unitsHaarDensity ((u : A) * b) := by
    intro b
    rw [← unitsHaarDensity_mul]
    congr 1
    simp [← mul_assoc]
  calc
    ∫⁻ b in (fun b : A ↦ (u : A) * b) ⁻¹' s, unitsHaarDensity b ∂μ =
        ∫⁻ b in (fun b : A ↦ (u : A) * b) ⁻¹' s,
          unitsHaarDensity ((u⁻¹ : Aˣ) : A) * unitsHaarDensity ((u : A) * b) ∂μ := by
      exact lintegral_congr fun b ↦ hshift b
    _ = unitsHaarDensity ((u⁻¹ : Aˣ) : A) *
        ∫⁻ b in (fun b : A ↦ (u : A) * b) ⁻¹' s, unitsHaarDensity ((u : A) * b) ∂μ :=
      lintegral_const_mul _ (measurable_unitsHaarDensity.comp hmeasurable)
    _ = unitsHaarDensity ((u⁻¹ : Aˣ) : A) *
        ∫⁻ a in s, unitsHaarDensity a ∂(Measure.map (fun b : A ↦ (u : A) * b) μ) := by
      congr 1
      exact (setLIntegral_map hs measurable_unitsHaarDensity hmeasurable).symm
    _ = unitsHaarDensity ((u⁻¹ : Aˣ) : A) *
        (unitsHaarDensity (u : A) * ∫⁻ a in s, unitsHaarDensity a ∂μ) := by
      rw [hlinear, Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
        Measure.restrict_smul, lintegral_smul_measure]
      congr 2
      rw [unitsHaarDensity_apply, Algebra.norm_apply, lmul_eq_mulLeft, abs_inv]
    _ = ∫⁻ a in s, unitsHaarDensity a ∂μ := by
      rw [← mul_assoc, unitsHaarDensity_units_inv_mul_units u, one_mul]

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- Haar measure of the unit group of a finite-dimensional real normed algebra, realized as the
reciprocal-algebra-norm-weighted additive Haar measure of the algebra, restricted to the open set of
units. -/
def Measure.unitsHaar : Measure Aˣ :=
  Measure.comap Units.val (μ.withDensity unitsHaarDensity)

theorem Measure.unitsHaar_apply (s : Set Aˣ) :
    Measure.unitsHaar μ s = μ.withDensity unitsHaarDensity (Units.val '' s) :=
  (Units.isOpenEmbedding_val.measurableEmbedding).comap_apply _ s

theorem Measure.unitsHaar_apply_of_measurableSet {s : Set Aˣ} (hs : MeasurableSet s) :
    Measure.unitsHaar μ s = ∫⁻ a in Units.val '' s, unitsHaarDensity a ∂μ := by
  rw [Measure.unitsHaar_apply, withDensity_apply _
    (Units.isOpenEmbedding_val.measurableEmbedding.measurableSet_image' hs)]

omit [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- Left translation by a unit matches, through `Units.val`, left multiplication in the algebra. -/
theorem units_val_image_preimage_mul_left (u : Aˣ) (s : Set Aˣ) :
    Units.val '' ((fun x : Aˣ ↦ u * x) ⁻¹' s) =
      (fun b : A ↦ (u : A) * b) ⁻¹' (Units.val '' s) := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨u * x, hx, rfl⟩
  · rintro ⟨y, hy, hby⟩
    refine ⟨u⁻¹ * y, ?_, ?_⟩
    · simpa using hy
    · have hcast : ((u⁻¹ * y : Aˣ) : A) = ((u⁻¹ : Aˣ) : A) * (y : A) := by push_cast; rfl
      rw [hcast, hby]
      simp

theorem Measure.isMulLeftInvariant_unitsHaar [μ.IsAddHaarMeasure] :
    (Measure.unitsHaar μ).IsMulLeftInvariant := by
  constructor
  intro u
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_const_mul u) hs, Measure.unitsHaar_apply,
    Measure.unitsHaar_apply, units_val_image_preimage_mul_left u s]
  have himage : MeasurableSet (Units.val '' s) :=
    Units.isOpenEmbedding_val.measurableEmbedding.measurableSet_image' hs
  have h := map_mul_left_withDensity_unitsHaarDensity μ u
  rw [← Measure.map_apply (measurable_const_mul (u : A)) himage, h]

theorem Measure.isFiniteMeasureOnCompacts_unitsHaar [μ.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (Measure.unitsHaar μ) := by
  constructor
  intro S hS
  obtain ⟨C, hCtop, hC⟩ := exists_unitsHaarDensity_le_of_isCompact (A := A) hS
  have himage : IsCompact (Units.val '' S) := hS.image Units.continuous_val
  rw [Measure.unitsHaar_apply_of_measurableSet μ hS.measurableSet]
  calc
    ∫⁻ a in Units.val '' S, unitsHaarDensity a ∂μ ≤ ∫⁻ _ in Units.val '' S, C ∂μ :=
      setLIntegral_mono' himage.measurableSet hC
    _ = C * μ (Units.val '' S) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top hCtop.lt_top himage.measure_lt_top

theorem Measure.isOpenPosMeasure_unitsHaar [μ.IsAddHaarMeasure] :
    (Measure.unitsHaar μ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [Measure.unitsHaar_apply, ne_eq,
    withDensity_apply_eq_zero measurable_unitsHaarDensity]
  have hsubset : Units.val '' U ⊆ {a : A | unitsHaarDensity a ≠ 0} := by
    rintro a ⟨u, _, rfl⟩
    exact unitsHaarDensity_units_ne_zero u
  rw [Set.inter_eq_self_of_subset_right hsubset]
  exact (Units.isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero μ (hUne.image Units.val)

theorem Measure.isHaarMeasure_unitsHaar [μ.IsAddHaarMeasure] :
    (Measure.unitsHaar μ).IsHaarMeasure where
  lt_top_of_isCompact := (Measure.isFiniteMeasureOnCompacts_unitsHaar μ).lt_top_of_isCompact
  map_mul_left_eq_self := (Measure.isMulLeftInvariant_unitsHaar μ).map_mul_left_eq_self
  open_pos := (Measure.isOpenPosMeasure_unitsHaar μ).open_pos

/-- The unit group of a finite-dimensional real normed algebra is locally compact, being an open
subset of the algebra. -/
instance instLocallyCompactSpaceUnits : LocallyCompactSpace Aˣ :=
  Units.isOpenEmbedding_val.locallyCompactSpace

/-- The unit group of a finite-dimensional real normed algebra is second countable, being embedded
in the algebra. -/
instance instSecondCountableTopologyUnits : SecondCountableTopology Aˣ :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

/-- Uniqueness of Haar measure identifies the canonical Haar measure of the unit group with the
explicit weighted additive Haar measure, up to a positive finite factor. -/
theorem Measure.exists_haar_eq_smul_unitsHaar [μ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ s : Set Aˣ, (Measure.haar : Measure Aˣ) s = c * Measure.unitsHaar μ s := by
  haveI : IsFiniteMeasureOnCompacts (Measure.unitsHaar μ) :=
    Measure.isFiniteMeasureOnCompacts_unitsHaar μ
  haveI : (Measure.unitsHaar μ).IsMulLeftInvariant := Measure.isMulLeftInvariant_unitsHaar μ
  haveI : (Measure.unitsHaar μ).IsHaarMeasure := Measure.isHaarMeasure_unitsHaar μ
  obtain ⟨k, hkpos, heq⟩ : ∃ k : ℝ≥0, 0 < k ∧
      Measure.unitsHaar μ = k • (Measure.haar : Measure Aˣ) :=
    ⟨Measure.haarScalarFactor (Measure.unitsHaar μ) (Measure.haar : Measure Aˣ),
      Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
      Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hne : ((k : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hkpos.ne'
  refine ⟨((k : ℝ≥0) : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.mpr hne, fun s ↦ ?_⟩
  have hval : Measure.unitsHaar μ s = ((k : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure Aˣ) s := by
    rw [heq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hval, ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]

/-- On a compact subset of the unit group, the image of Haar measure under `Units.val` is dominated
by additive Haar measure of the algebra, restricted to the compact image.  This is the comparison
used to deduce local integrability on the unit group from integrability on the algebra; keeping the
restriction is what makes the bound usable for functions that are only locally integrable. -/
theorem Measure.exists_map_units_val_haar_restrict_le [μ.IsAddHaarMeasure]
    {S : Set Aˣ} (hS : IsCompact S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map Units.val ((Measure.haar : Measure Aˣ).restrict S) ≤
        C • μ.restrict (Units.val '' S) := by
  obtain ⟨c, _, hctop, hcs⟩ := Measure.exists_haar_eq_smul_unitsHaar μ
  obtain ⟨C₁, hC₁top, hC₁⟩ := exists_unitsHaarDensity_le_of_isCompact (A := A) hS
  have himage : IsCompact (Units.val '' S) := hS.image Units.continuous_val
  refine ⟨c * C₁, ENNReal.mul_ne_top hctop hC₁top, ?_⟩
  rw [Measure.le_iff]
  intro t ht
  have hpre : MeasurableSet (Units.val ⁻¹' t) := ht.preimage Units.continuous_val.measurable
  have hsubset : Units.val '' (Units.val ⁻¹' t ∩ S) ⊆ t ∩ Units.val '' S := by
    rintro a ⟨x, ⟨hxt, hxS⟩, rfl⟩
    exact ⟨hxt, ⟨x, hxS, rfl⟩⟩
  calc
    Measure.map Units.val ((Measure.haar : Measure Aˣ).restrict S) t =
        (Measure.haar : Measure Aˣ) (Units.val ⁻¹' t ∩ S) := by
      rw [Measure.map_apply Units.continuous_val.measurable ht, Measure.restrict_apply hpre]
    _ = c * Measure.unitsHaar μ (Units.val ⁻¹' t ∩ S) := hcs _
    _ = c * (μ.withDensity unitsHaarDensity) (Units.val '' (Units.val ⁻¹' t ∩ S)) := by
      rw [Measure.unitsHaar_apply]
    _ ≤ c * (μ.withDensity unitsHaarDensity) (t ∩ Units.val '' S) :=
      mul_le_mul_right (measure_mono hsubset) c
    _ = c * ∫⁻ a in t ∩ Units.val '' S, unitsHaarDensity a ∂μ := by
      rw [withDensity_apply _ (ht.inter himage.measurableSet)]
    _ ≤ c * ∫⁻ _ in t ∩ Units.val '' S, C₁ ∂μ :=
      mul_le_mul_right (setLIntegral_mono' (ht.inter himage.measurableSet)
        fun a ha ↦ hC₁ a ha.2) c
    _ = c * (C₁ * μ (t ∩ Units.val '' S)) := by rw [setLIntegral_const]
    _ = (c * C₁) * (μ.restrict (Units.val '' S)) t := by
      rw [Measure.restrict_apply ht, mul_assoc]
    _ = ((c * C₁) • μ.restrict (Units.val '' S)) t := by
      rw [Measure.smul_apply, smul_eq_mul]

end MeasureTheory
