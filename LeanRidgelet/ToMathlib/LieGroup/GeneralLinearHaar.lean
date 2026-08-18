/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanRidgelet.ToMathlib.LinearSurjectionHaar
public import LeanRidgelet.ToMathlib.LieGroup.HaarAutomorphism
public import LeanRidgelet.ToMathlib.LieGroup.UnitsHaar

/-!
# Contragredient orbits of the general linear group and Haar measure

The contragredient map `L ↦ (L⁻¹)†` is an automorphism of the group of invertible continuous linear
operators on a finite-dimensional real inner-product space: it is the composition of the two
anti-automorphisms `L ↦ L⁻¹` and `L ↦ L†`. Composing the resulting Haar transport with the
comparison between Haar measure of a unit group and additive Haar measure of the ambient algebra,
and with the pushforward bound along the evaluation map `A ↦ A ξ`, bounds the image of a compactly
restricted Haar measure under a contragredient orbit map by Lebesgue measure.

## Main results

* `ContinuousLinearMap.contragredientUnits`: the contragredient automorphism of the unit group.
* `ContinuousLinearMap.exists_map_contragredientOrbit_haar_restrict_le`: on a compact set, the image
  of Haar measure of the unit group under `L ↦ (L⁻¹)† ξ` is dominated by additive Haar measure of
  the vector space, restricted to the compact image.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The adjoint of the inverse of an invertible operator, as an invertible operator. -/
def contragredientUnit (L : (E →L[ℝ] E)ˣ) : (E →L[ℝ] E)ˣ where
  val := (↑L⁻¹ : E →L[ℝ] E).adjoint
  inv := (↑L : E →L[ℝ] E).adjoint
  val_inv := by
    change ((↑L⁻¹ : E →L[ℝ] E).adjoint) ∘L ((↑L : E →L[ℝ] E).adjoint) = 1
    rw [← ContinuousLinearMap.adjoint_comp]
    change ((↑L : E →L[ℝ] E) * (↑L⁻¹ : E →L[ℝ] E)).adjoint = 1
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  inv_val := by
    change ((↑L : E →L[ℝ] E).adjoint) ∘L ((↑L⁻¹ : E →L[ℝ] E).adjoint) = 1
    rw [← ContinuousLinearMap.adjoint_comp]
    change ((↑L⁻¹ : E →L[ℝ] E) * (↑L : E →L[ℝ] E)).adjoint = 1
    rw [← Units.val_mul, inv_mul_cancel]
    simp

@[simp]
theorem contragredientUnit_val (L : (E →L[ℝ] E)ˣ) :
    (contragredientUnit L : E →L[ℝ] E) = (↑L⁻¹ : E →L[ℝ] E).adjoint := rfl

@[simp]
theorem contragredientUnit_inv_val (L : (E →L[ℝ] E)ˣ) :
    (↑((contragredientUnit L)⁻¹) : E →L[ℝ] E) = (↑L : E →L[ℝ] E).adjoint := rfl

theorem contragredientUnit_mul (L M : (E →L[ℝ] E)ˣ) :
    contragredientUnit (L * M) = contragredientUnit L * contragredientUnit M := by
  apply Units.ext
  change ((↑(L * M)⁻¹ : E →L[ℝ] E)).adjoint =
    ((↑L⁻¹ : E →L[ℝ] E).adjoint) ∘L ((↑M⁻¹ : E →L[ℝ] E).adjoint)
  rw [← ContinuousLinearMap.adjoint_comp]
  congr 1

theorem contragredientUnit_one :
    contragredientUnit (1 : (E →L[ℝ] E)ˣ) = 1 := by
  apply Units.ext
  rw [contragredientUnit_val]
  simp

theorem contragredientUnit_involutive :
    Function.Involutive (contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) := by
  intro L
  apply Units.ext
  rw [contragredientUnit_val, contragredientUnit_inv_val,
    ContinuousLinearMap.adjoint_adjoint]

theorem continuous_contragredientUnit_val :
    Continuous fun L : (E →L[ℝ] E)ˣ ↦ ((contragredientUnit L : E →L[ℝ] E)) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).isometry.continuous.comp
    (Units.continuous_val.comp continuous_inv)

theorem continuous_contragredientUnit :
    Continuous (contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_contragredientUnit_val, ?_⟩
  have hfun : (fun L : (E →L[ℝ] E)ˣ ↦ (↑((contragredientUnit L)⁻¹) : E →L[ℝ] E)) =
      fun L : (E →L[ℝ] E)ˣ ↦ ((contragredientUnit L⁻¹ : E →L[ℝ] E)) := by
    funext L
    rw [contragredientUnit_inv_val, contragredientUnit_val, inv_inv]
  rw [hfun]
  exact continuous_contragredientUnit_val.comp continuous_inv

/-- The contragredient map `L ↦ (L⁻¹)†` as a topological automorphism of the group of invertible
operators.  It is an involution, so it is its own inverse. -/
def contragredientUnits : (E →L[ℝ] E)ˣ ≃ₜ* (E →L[ℝ] E)ˣ where
  toFun := contragredientUnit
  invFun := contragredientUnit
  left_inv := contragredientUnit_involutive
  right_inv := contragredientUnit_involutive
  map_mul' := contragredientUnit_mul
  continuous_toFun := continuous_contragredientUnit
  continuous_invFun := continuous_contragredientUnit

@[simp]
theorem contragredientUnits_apply (L : (E →L[ℝ] E)ˣ) :
    contragredientUnits L = contragredientUnit L := rfl

variable (E) in
/-- Evaluation of a continuous linear operator at a fixed vector, as a linear map. -/
def evalLinearMap (xi : E) : (E →L[ℝ] E) →ₗ[ℝ] E where
  toFun A := A xi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem evalLinearMap_apply (xi : E) (A : E →L[ℝ] E) : evalLinearMap E xi A = A xi := rfl

omit [FiniteDimensional ℝ E] in
/-- Evaluation at a nonzero vector is onto: a rank-one operator sends it to any prescribed
vector. -/
theorem evalLinearMap_surjective {xi : E} (hxi : xi ≠ 0) :
    Function.Surjective (evalLinearMap E xi) := by
  intro v
  refine ⟨(‖xi‖ ^ 2)⁻¹ • ((innerSL ℝ xi).smulRight v), ?_⟩
  have hnorm : ‖xi‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hxi)
  have hinner : (innerSL ℝ xi) xi = ‖xi‖ ^ 2 := real_inner_self_eq_norm_sq xi
  simp only [evalLinearMap_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hinner, smul_smul]
  rw [inv_mul_cancel₀ hnorm, one_smul]

variable (E) in
/-- Evaluation of the adjoint of an operator at a fixed vector, as a linear map.  Unlike the
contragredient map, this one is linear on the whole operator algebra, because it does not invert. -/
def adjointEvalLinearMap (xi : E) : (E →L[ℝ] E) →ₗ[ℝ] E where
  toFun A := A.adjoint xi
  map_add' A B := by
    have hadd : (A + B).adjoint = A.adjoint + B.adjoint :=
      map_add ContinuousLinearMap.adjoint A B
    simp [hadd]
  map_smul' c A := by
    have hsmul : (c • A).adjoint = c • A.adjoint := by
      simp [map_smulₛₗ ContinuousLinearMap.adjoint c A]
    simp [hsmul]

@[simp]
theorem adjointEvalLinearMap_apply (xi : E) (A : E →L[ℝ] E) :
    adjointEvalLinearMap E xi A = A.adjoint xi := rfl

/-- Evaluating the adjoint at a nonzero vector is onto, because taking adjoints is involutive. -/
theorem adjointEvalLinearMap_surjective {xi : E} (hxi : xi ≠ 0) :
    Function.Surjective (adjointEvalLinearMap E xi) := by
  intro v
  obtain ⟨A, hA⟩ := evalLinearMap_surjective hxi v
  refine ⟨A.adjoint, ?_⟩
  rw [adjointEvalLinearMap_apply, ContinuousLinearMap.adjoint_adjoint]
  exact hA

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]
  [MeasurableSpace (E →L[ℝ] E)ˣ] [BorelSpace (E →L[ℝ] E)ˣ]

/-- On a compact set of invertible operators, the image of Haar measure under a contragredient orbit
map `L ↦ (L⁻¹)† ξ` is dominated by a finite multiple of additive Haar measure of the vector space,
restricted to the compact image.

The three factors of the estimate are the Haar transport along the contragredient automorphism, the
comparison between Haar measure of the unit group and additive Haar measure of the operator algebra,
and the pushforward bound along the surjective evaluation map. -/
theorem exists_map_contragredientOrbit_haar_restrict_le
    (μ : Measure (E →L[ℝ] E)) [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    {xi : E} (hxi : xi ≠ 0)
    {S : Set (E →L[ℝ] E)ˣ} (hS : IsCompact S) :
    ∃ (C : ℝ≥0∞) (B : Set E), C ≠ ⊤ ∧ IsCompact B ∧
      Measure.map (fun L : (E →L[ℝ] E)ˣ ↦ evalLinearMap E xi (contragredientUnit L))
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S) ≤ C • ν.restrict B := by
  classical
  -- transport along the contragredient automorphism
  obtain ⟨c, hc0, hctop, hc⟩ :=
    MeasureTheory.exists_map_continuousMulEquiv_haar_restrict_eq_smul_haar_restrict
      (contragredientUnits (E := E)) hS.measurableSet
  rw [show (⇑(contragredientUnits (E := E)) : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) =
    contragredientUnit from rfl] at hc
  have himageS : IsCompact ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S) :=
    hS.image continuous_contragredientUnit
  -- compare with additive Haar measure of the operator algebra
  obtain ⟨C₁, hC₁top, hC₁⟩ :=
    MeasureTheory.Measure.exists_map_units_val_haar_restrict_le μ himageS
  -- push forward along the evaluation map
  obtain ⟨C₂, hC₂top, hC₂⟩ :=
    LinearMap.exists_map_restrict_addHaar_le_smul_addHaar μ ν
      (evalLinearMap_surjective hxi)
      (himageS.image Units.continuous_val)
  refine ⟨c * (C₁ * C₂), (evalLinearMap E xi) ''
      (Units.val '' ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S)),
    ENNReal.mul_ne_top hctop (ENNReal.mul_ne_top hC₁top hC₂top),
    ((himageS.image Units.continuous_val).image
      (LinearMap.continuous_of_finiteDimensional (evalLinearMap E xi))), ?_⟩
  have hmeasurableEval : Measurable (evalLinearMap E xi) :=
    (LinearMap.continuous_of_finiteDimensional (evalLinearMap E xi)).measurable
  have hmeasurableVal : Measurable (Units.val : (E →L[ℝ] E)ˣ → E →L[ℝ] E) :=
    Units.continuous_val.measurable
  have hmeasurableContra : Measurable (contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) :=
    continuous_contragredientUnit.measurable
  calc
    Measure.map (fun L : (E →L[ℝ] E)ˣ ↦ evalLinearMap E xi (contragredientUnit L))
        ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S) =
        Measure.map (evalLinearMap E xi) (Measure.map Units.val
          (Measure.map (contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ)
            ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S))) := by
      rw [Measure.map_map hmeasurableVal hmeasurableContra,
        Measure.map_map hmeasurableEval (hmeasurableVal.comp hmeasurableContra)]
      rfl
    _ = Measure.map (evalLinearMap E xi) (Measure.map Units.val
          (c • (Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S))) := by
      rw [hc]
    _ = c • Measure.map (evalLinearMap E xi) (Measure.map Units.val
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S))) := by
      rw [Measure.map_smul, Measure.map_smul]
    _ ≤ c • Measure.map (evalLinearMap E xi)
          (C₁ • μ.restrict (Units.val ''
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S))) := by
      gcongr
    _ = c • (C₁ • Measure.map (evalLinearMap E xi) (μ.restrict (Units.val ''
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S)))) := by
      rw [Measure.map_smul]
    _ ≤ c • (C₁ • (C₂ • ν.restrict ((evalLinearMap E xi) '' (Units.val ''
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S))))) := by
      gcongr
    _ = (c * (C₁ * C₂)) • ν.restrict ((evalLinearMap E xi) '' (Units.val ''
            ((contragredientUnit : (E →L[ℝ] E)ˣ → (E →L[ℝ] E)ˣ) '' S))) := by
      rw [smul_smul, smul_smul, mul_assoc]

/-- On a compact set of invertible operators, the image of Haar measure under an adjoint orbit map
`L ↦ L† ξ` is dominated by a finite multiple of additive Haar measure of the vector space,
restricted to the compact image.

This is the variant needed when the orbit map is composed with inversion, and it is cheaper than the
contragredient one: taking adjoints and evaluating are both linear on the operator algebra, so only
the unit-group comparison and the linear pushforward bound are used, with no Haar transport along a
group automorphism. -/
theorem exists_map_adjointOrbit_haar_restrict_le
    (μ : Measure (E →L[ℝ] E)) [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    {xi : E} (hxi : xi ≠ 0)
    {S : Set (E →L[ℝ] E)ˣ} (hS : IsCompact S) :
    ∃ (C : ℝ≥0∞) (B : Set E), C ≠ ⊤ ∧ IsCompact B ∧
      Measure.map (fun L : (E →L[ℝ] E)ˣ ↦ adjointEvalLinearMap E xi (L : E →L[ℝ] E))
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S) ≤ C • ν.restrict B := by
  classical
  obtain ⟨C₁, hC₁top, hC₁⟩ :=
    MeasureTheory.Measure.exists_map_units_val_haar_restrict_le μ hS
  obtain ⟨C₂, hC₂top, hC₂⟩ :=
    LinearMap.exists_map_restrict_addHaar_le_smul_addHaar μ ν
      (adjointEvalLinearMap_surjective hxi) (hS.image Units.continuous_val)
  have hmeasurableVal : Measurable (Units.val : (E →L[ℝ] E)ˣ → E →L[ℝ] E) :=
    Units.continuous_val.measurable
  have hmeasurableEval : Measurable (adjointEvalLinearMap E xi) :=
    (LinearMap.continuous_of_finiteDimensional (adjointEvalLinearMap E xi)).measurable
  refine ⟨C₁ * C₂, (adjointEvalLinearMap E xi) '' (Units.val '' S),
    ENNReal.mul_ne_top hC₁top hC₂top,
    (hS.image Units.continuous_val).image
      (LinearMap.continuous_of_finiteDimensional (adjointEvalLinearMap E xi)), ?_⟩
  calc
    Measure.map (fun L : (E →L[ℝ] E)ˣ ↦ adjointEvalLinearMap E xi (L : E →L[ℝ] E))
        ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S) =
        Measure.map (adjointEvalLinearMap E xi) (Measure.map Units.val
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict S)) := by
      rw [Measure.map_map hmeasurableEval hmeasurableVal]
      rfl
    _ ≤ Measure.map (adjointEvalLinearMap E xi) (C₁ • μ.restrict (Units.val '' S)) :=
      Measure.map_mono hC₁ hmeasurableEval
    _ = C₁ • Measure.map (adjointEvalLinearMap E xi) (μ.restrict (Units.val '' S)) := by
      rw [Measure.map_smul]
    _ ≤ C₁ • (C₂ • ν.restrict ((adjointEvalLinearMap E xi) '' (Units.val '' S))) := by gcongr
    _ = (C₁ * C₂) • ν.restrict ((adjointEvalLinearMap E xi) '' (Units.val '' S)) := by
      rw [smul_smul]

end ContinuousLinearMap
