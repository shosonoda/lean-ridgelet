/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.AffineIrreducibility
public import LeanRidgelet.ToMathlib.LieGroup.GeneralLinearHaar
public import LeanRidgelet.ToMathlib.LieGroup.SemidirectProductHaar

/-!
# Haar measure of the affine group along the frequency orbit map

The orbit map `x ↦ (x.right⁻¹)† ξ` sends the affine group onto frequency space, and the estimate
proved here bounds the image of a compactly restricted Haar measure under it by Lebesgue measure of
frequency space, restricted to a compact set. This is the quotient-integral input for local
integrability of the lift of a quotient `L²` class: an integral over a compact set of group elements
becomes an integral over a compact set of frequencies.

The proof instantiates the general semidirect-product Haar factorization at the affine group and
composes it with the contragredient-orbit estimate for the general linear group. The translation
factor `Multiplicative E` is the additive group of `E` written multiplicatively, so its Haar measure
is Lebesgue measure verbatim and the linear action rescales it by the reciprocal absolute
determinant. Borel structures on the two factors are introduced inside the proofs rather than as
global instances, since they do not appear in the statements.

## Main results

* `LeanRidgelet.affineLinearDeterminantCharacter`: the reciprocal absolute determinant, as a
  multiplicative character of the linear factor.
* `LeanRidgelet.affine_map_orbitMap_haar_restrict_le`: the pushforward bound.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The reciprocal absolute determinant of the linear factor of the affine group, as a
multiplicative character.  It is the factor by which the linear action rescales Lebesgue measure of
the translation factor, hence the density that turns Haar measure of the linear factor into the
relatively invariant measure of the semidirect-product factorization. -/
def affineLinearDeterminantCharacter : (E →L[ℝ] E)ˣ →* ℝ≥0∞ where
  toFun L := ENNReal.ofReal |LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)|⁻¹
  map_one' := by simp
  map_mul' L M := by
    have hdet : LinearMap.det (((L * M : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E) *
          LinearMap.det ((M : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      change LinearMap.det (((L : E →L[ℝ] E) ∘L (M : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
      exact LinearMap.det_comp _ _
    rw [hdet, abs_mul, mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem affineLinearDeterminantCharacter_apply (L : (E →L[ℝ] E)ˣ) :
    affineLinearDeterminantCharacter L =
      ENNReal.ofReal |LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)|⁻¹ := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem affineLinearDeterminantCharacter_ne_zero (L : (E →L[ℝ] E)ˣ) :
    affineLinearDeterminantCharacter L ≠ 0 := by
  rw [affineLinearDeterminantCharacter_apply, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine inv_pos.mpr (abs_pos.mpr ?_)
  exact (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E L).isUnit_det'.ne_zero

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_affineLinearDeterminantCharacter_real :
    Continuous fun L : (E →L[ℝ] E)ˣ ↦
      |LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)|⁻¹ := by
  refine Continuous.inv₀ ?_ ?_
  · exact (ContinuousLinearMap.continuous_det.comp Units.continuous_val).abs
  · intro L
    refine abs_ne_zero.mpr ?_
    exact (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E L).isUnit_det'.ne_zero

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem measurable_affineLinearDeterminantCharacter
    [MeasurableSpace (E →L[ℝ] E)ˣ] [BorelSpace (E →L[ℝ] E)ˣ] :
    Measurable (affineLinearDeterminantCharacter : (E →L[ℝ] E)ˣ → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp continuous_affineLinearDeterminantCharacter_real.measurable

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- On a compact set of linear factors the character is bounded. -/
theorem exists_affineLinearDeterminantCharacter_le_of_isCompact
    {K : Set (E →L[ℝ] E)ˣ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ L ∈ K, affineLinearDeterminantCharacter L ≤ C := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image
    (continuous_affineLinearDeterminantCharacter_real (E := E)).continuousOn
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, ?_⟩
  intro L hL
  exact ENNReal.ofReal_le_ofReal (hM ⟨L, hL, rfl⟩)

set_option maxHeartbeats 1600000 in
-- The proof instantiates two general theorems whose statements mention several transported
-- measures, so unification unfolds a long chain of semidirect-product coordinates.
omit [Nontrivial E] in
/-- The image of a compactly restricted Haar measure of the affine group under the frequency orbit
map is dominated by a finite multiple of Lebesgue measure of frequency space, restricted to the
compact image.

The translation factor contributes only the finite Haar measure of a compact set, because left
translation acts on the two semidirect-product coordinates separately; the linear factor is handled
by the contragredient-orbit estimate. -/
theorem affine_map_orbitMap_haar_restrict_le {xi : E} (hxi : xi ≠ 0)
    {S : Set (AffineEquiv.TopologicalSemidirectProduct E)} (hS : IsCompact S) :
    ∃ (C : ℝ≥0∞) (B : Set E), C ≠ ⊤ ∧ IsCompact B ∧
      Measure.map (affineTopologicalMackeyOrbitMap xi)
          ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) ≤
        C • (volume : Measure E).restrict B := by
  classical
  letI : MeasurableSpace (Multiplicative E) := ‹MeasurableSpace E›
  haveI : BorelSpace (Multiplicative E) := ⟨‹BorelSpace E›.measurable_eq⟩
  letI : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
  haveI : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
  letI : MeasurableSpace (E →L[ℝ] E)ˣ := borel (E →L[ℝ] E)ˣ
  haveI : BorelSpace (E →L[ℝ] E)ˣ := ⟨rfl⟩
  -- the translation factor carries Lebesgue measure verbatim
  letI nu : Measure (Multiplicative E) := (volume : Measure E)
  haveI : IsFiniteMeasureOnCompacts nu :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure E))
  haveI : nu.IsOpenPosMeasure := inferInstanceAs ((volume : Measure E).IsOpenPosMeasure)
  haveI : SFinite nu := inferInstanceAs (SFinite (volume : Measure E))
  haveI : nu.IsMulLeftInvariant := by
    constructor
    intro a
    exact map_add_left_eq_self (volume : Measure E) a.toAdd
  have hrescale : ∀ L : (E →L[ℝ] E)ˣ,
      Measure.map (AffineEquiv.continuousLinearMultiplicativeActionHom E L) nu =
        affineLinearDeterminantCharacter L • nu := by
    intro L
    have hdet : LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 :=
      (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E L).isUnit_det'.ne_zero
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
      (f := ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)) hdet
    rw [abs_inv] at h
    exact h
  -- the linear factor carries the relatively invariant twisted Haar measure
  letI lam : Measure (E →L[ℝ] E)ˣ :=
    (Measure.haar : Measure (E →L[ℝ] E)ˣ).withDensity affineLinearDeterminantCharacter
  haveI : IsFiniteMeasureOnCompacts lam := by
    constructor
    intro K hK
    obtain ⟨C, hCtop, hC⟩ := exists_affineLinearDeterminantCharacter_le_of_isCompact (E := E) hK
    have hbound : lam K ≤ C * (Measure.haar : Measure (E →L[ℝ] E)ˣ) K := by
      calc
        lam K = ∫⁻ L in K, affineLinearDeterminantCharacter L
            ∂(Measure.haar : Measure (E →L[ℝ] E)ˣ) := withDensity_apply _ hK.measurableSet
        _ ≤ ∫⁻ _ in K, C ∂(Measure.haar : Measure (E →L[ℝ] E)ˣ) :=
          setLIntegral_mono' hK.measurableSet hC
        _ = C * (Measure.haar : Measure (E →L[ℝ] E)ˣ) K := by rw [setLIntegral_const]
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hCtop.lt_top hK.measure_lt_top)
  haveI : lam.IsOpenPosMeasure := by
    constructor
    intro U hU hUne
    rw [ne_eq, withDensity_apply_eq_zero measurable_affineLinearDeterminantCharacter]
    have hsubset : U ⊆ {L : (E →L[ℝ] E)ˣ | affineLinearDeterminantCharacter L ≠ 0} :=
      fun L _ ↦ affineLinearDeterminantCharacter_ne_zero L
    rw [Set.inter_eq_self_of_subset_right hsubset]
    exact hU.measure_ne_zero _ hUne
  haveI : SigmaFinite lam := inferInstance
  haveI : SFinite lam := inferInstance
  have hlam : ∀ L : (E →L[ℝ] E)ˣ,
      Measure.map (fun M ↦ L * M) lam = affineLinearDeterminantCharacter L⁻¹ • lam :=
    fun L ↦ MeasureTheory.map_mul_left_withDensity_monoidHom
      (Measure.haar : Measure (E →L[ℝ] E)ˣ) affineLinearDeterminantCharacter
      measurable_affineLinearDeterminantCharacter L
  -- the semidirect-product factorization bounds the projection to the linear factor
  obtain ⟨C₁, hC₁top, hC₁⟩ :=
    SemidirectProduct.exists_map_right_haar_restrict_le
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)
      (ν := nu) (lam := lam) hrescale hlam
      (fun L ↦ (AffineEquiv.continuous_continuousLinearMultiplicativeAction E).comp
        (continuous_const.prodMk continuous_id)) hS
  -- the character is bounded on the compact projection
  have hprojection : IsCompact (SemidirectProduct.right '' S) :=
    hS.image (SemidirectProduct.continuous_right _)
  obtain ⟨C₂, hC₂top, hC₂⟩ :=
    exists_affineLinearDeterminantCharacter_le_of_isCompact (E := E) hprojection
  have hlamle : lam.restrict (SemidirectProduct.right '' S) ≤
      C₂ • (Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict (SemidirectProduct.right '' S) :=
    MeasureTheory.withDensity_restrict_le_smul_restrict
      (Measure.haar : Measure (E →L[ℝ] E)ˣ) hprojection.measurableSet hC₂
  -- the contragredient orbit estimate finishes on the linear factor
  obtain ⟨C₃, B, hC₃top, hBcompact, hC₃⟩ :=
    ContinuousLinearMap.exists_map_contragredientOrbit_haar_restrict_le
      (Measure.addHaar : Measure (E →L[ℝ] E)) (volume : Measure E) hxi hprojection
  refine ⟨C₁ * (C₂ * C₃), B, ENNReal.mul_ne_top hC₁top (ENNReal.mul_ne_top hC₂top hC₃top),
    hBcompact, ?_⟩
  have hmeasurableRight :
      Measurable (SemidirectProduct.right :
        AffineEquiv.TopologicalSemidirectProduct E → (E →L[ℝ] E)ˣ) :=
    (SemidirectProduct.continuous_right _).measurable
  have hmeasurableOrbit :
      Measurable fun L : (E →L[ℝ] E)ˣ ↦
        ContinuousLinearMap.evalLinearMap E xi (ContinuousLinearMap.contragredientUnit L) :=
    ((LinearMap.continuous_of_finiteDimensional
      (ContinuousLinearMap.evalLinearMap E xi)).comp
      ContinuousLinearMap.continuous_contragredientUnit_val).measurable
  calc
    Measure.map (affineTopologicalMackeyOrbitMap xi)
        ((Measure.haar :
          Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) =
        Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.evalLinearMap E xi (ContinuousLinearMap.contragredientUnit L))
          (Measure.map SemidirectProduct.right
            ((Measure.haar :
              Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S)) := by
      rw [Measure.map_map hmeasurableOrbit hmeasurableRight]
      rfl
    _ ≤ Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.evalLinearMap E xi (ContinuousLinearMap.contragredientUnit L))
          (C₁ • lam.restrict (SemidirectProduct.right '' S)) :=
      Measure.map_mono hC₁ hmeasurableOrbit
    _ ≤ Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.evalLinearMap E xi (ContinuousLinearMap.contragredientUnit L))
          (C₁ • (C₂ • (Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict
            (SemidirectProduct.right '' S))) := by
      refine Measure.map_mono ?_ hmeasurableOrbit
      gcongr
    _ = (C₁ * C₂) • Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.evalLinearMap E xi (ContinuousLinearMap.contragredientUnit L))
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict (SemidirectProduct.right '' S)) := by
      rw [Measure.map_smul, Measure.map_smul, smul_smul]
    _ ≤ (C₁ * C₂) • (C₃ • (volume : Measure E).restrict B) := by gcongr
    _ = (C₁ * (C₂ * C₃)) • (volume : Measure E).restrict B := by
      rw [smul_smul, mul_assoc]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The orbit map evaluated at an inverse is the adjoint orbit map: the linear coordinate of an
inverse is the inverse linear coordinate, and the contragredient of an inverse is the adjoint. -/
theorem affineTopologicalMackeyOrbitMap_inv (xi : E)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalMackeyOrbitMap xi x⁻¹ =
      ContinuousLinearMap.adjointEvalLinearMap E xi ((x.right : E →L[ℝ] E)) := by
  change (↑((x⁻¹).right)⁻¹ : E →L[ℝ] E).adjoint xi = ((x.right : E →L[ℝ] E)).adjoint xi
  rw [SemidirectProduct.inv_right, inv_inv]

set_option maxHeartbeats 1600000 in
-- As above, the composition of two general estimates unfolds the semidirect-product coordinates.
omit [Nontrivial E] in
/-- The same bound for the orbit map composed with inversion, which is the adjoint orbit map
`x ↦ (x.right)† ξ`.  This is the form consumed by the group-convolution continuity theorem, whose
local-integrability hypothesis is stated for the inverse-composed integrand.

Taking adjoints is linear on the operator algebra, so this variant does not use the Haar transport
along the contragredient automorphism. -/
theorem affine_map_adjointOrbitMap_haar_restrict_le {xi : E} (hxi : xi ≠ 0)
    {S : Set (AffineEquiv.TopologicalSemidirectProduct E)} (hS : IsCompact S) :
    ∃ (C : ℝ≥0∞) (B : Set E), C ≠ ⊤ ∧ IsCompact B ∧
      Measure.map (fun x ↦ affineTopologicalMackeyOrbitMap xi x⁻¹)
          ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) ≤
        C • (volume : Measure E).restrict B := by
  classical
  letI : MeasurableSpace (Multiplicative E) := ‹MeasurableSpace E›
  haveI : BorelSpace (Multiplicative E) := ⟨‹BorelSpace E›.measurable_eq⟩
  letI : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
  haveI : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
  letI : MeasurableSpace (E →L[ℝ] E)ˣ := borel (E →L[ℝ] E)ˣ
  haveI : BorelSpace (E →L[ℝ] E)ˣ := ⟨rfl⟩
  letI nu : Measure (Multiplicative E) := (volume : Measure E)
  haveI : IsFiniteMeasureOnCompacts nu :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure E))
  haveI : nu.IsOpenPosMeasure := inferInstanceAs ((volume : Measure E).IsOpenPosMeasure)
  haveI : SFinite nu := inferInstanceAs (SFinite (volume : Measure E))
  haveI : nu.IsMulLeftInvariant := by
    constructor
    intro a
    exact map_add_left_eq_self (volume : Measure E) a.toAdd
  have hrescale : ∀ L : (E →L[ℝ] E)ˣ,
      Measure.map (AffineEquiv.continuousLinearMultiplicativeActionHom E L) nu =
        affineLinearDeterminantCharacter L • nu := by
    intro L
    have hdet : LinearMap.det ((L : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 :=
      (AffineEquiv.continuousLinearUnitsEquivLinearEquiv E L).isUnit_det'.ne_zero
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
      (f := ((L : E →L[ℝ] E) : E →ₗ[ℝ] E)) hdet
    rw [abs_inv] at h
    exact h
  letI lam : Measure (E →L[ℝ] E)ˣ :=
    (Measure.haar : Measure (E →L[ℝ] E)ˣ).withDensity affineLinearDeterminantCharacter
  haveI : IsFiniteMeasureOnCompacts lam := by
    constructor
    intro K hK
    obtain ⟨C, hCtop, hC⟩ := exists_affineLinearDeterminantCharacter_le_of_isCompact (E := E) hK
    have hbound : lam K ≤ C * (Measure.haar : Measure (E →L[ℝ] E)ˣ) K := by
      calc
        lam K = ∫⁻ L in K, affineLinearDeterminantCharacter L
            ∂(Measure.haar : Measure (E →L[ℝ] E)ˣ) := withDensity_apply _ hK.measurableSet
        _ ≤ ∫⁻ _ in K, C ∂(Measure.haar : Measure (E →L[ℝ] E)ˣ) :=
          setLIntegral_mono' hK.measurableSet hC
        _ = C * (Measure.haar : Measure (E →L[ℝ] E)ˣ) K := by rw [setLIntegral_const]
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hCtop.lt_top hK.measure_lt_top)
  haveI : lam.IsOpenPosMeasure := by
    constructor
    intro U hU hUne
    rw [ne_eq, withDensity_apply_eq_zero measurable_affineLinearDeterminantCharacter]
    have hsubset : U ⊆ {L : (E →L[ℝ] E)ˣ | affineLinearDeterminantCharacter L ≠ 0} :=
      fun L _ ↦ affineLinearDeterminantCharacter_ne_zero L
    rw [Set.inter_eq_self_of_subset_right hsubset]
    exact hU.measure_ne_zero _ hUne
  haveI : SigmaFinite lam := inferInstance
  haveI : SFinite lam := inferInstance
  have hlam : ∀ L : (E →L[ℝ] E)ˣ,
      Measure.map (fun M ↦ L * M) lam = affineLinearDeterminantCharacter L⁻¹ • lam :=
    fun L ↦ MeasureTheory.map_mul_left_withDensity_monoidHom
      (Measure.haar : Measure (E →L[ℝ] E)ˣ) affineLinearDeterminantCharacter
      measurable_affineLinearDeterminantCharacter L
  obtain ⟨C₁, hC₁top, hC₁⟩ :=
    SemidirectProduct.exists_map_right_haar_restrict_le
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)
      (ν := nu) (lam := lam) hrescale hlam
      (fun L ↦ (AffineEquiv.continuous_continuousLinearMultiplicativeAction E).comp
        (continuous_const.prodMk continuous_id)) hS
  have hprojection : IsCompact (SemidirectProduct.right '' S) :=
    hS.image (SemidirectProduct.continuous_right _)
  obtain ⟨C₂, hC₂top, hC₂⟩ :=
    exists_affineLinearDeterminantCharacter_le_of_isCompact (E := E) hprojection
  have hlamle : lam.restrict (SemidirectProduct.right '' S) ≤
      C₂ • (Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict (SemidirectProduct.right '' S) :=
    MeasureTheory.withDensity_restrict_le_smul_restrict
      (Measure.haar : Measure (E →L[ℝ] E)ˣ) hprojection.measurableSet hC₂
  obtain ⟨C₃, B, hC₃top, hBcompact, hC₃⟩ :=
    ContinuousLinearMap.exists_map_adjointOrbit_haar_restrict_le
      (Measure.addHaar : Measure (E →L[ℝ] E)) (volume : Measure E) hxi hprojection
  refine ⟨C₁ * (C₂ * C₃), B, ENNReal.mul_ne_top hC₁top (ENNReal.mul_ne_top hC₂top hC₃top),
    hBcompact, ?_⟩
  have hmeasurableRight :
      Measurable (SemidirectProduct.right :
        AffineEquiv.TopologicalSemidirectProduct E → (E →L[ℝ] E)ˣ) :=
    (SemidirectProduct.continuous_right _).measurable
  have hmeasurableOrbit :
      Measurable fun L : (E →L[ℝ] E)ˣ ↦
        ContinuousLinearMap.adjointEvalLinearMap E xi (L : E →L[ℝ] E) :=
    ((LinearMap.continuous_of_finiteDimensional
      (ContinuousLinearMap.adjointEvalLinearMap E xi)).comp Units.continuous_val).measurable
  calc
    Measure.map (fun x ↦ affineTopologicalMackeyOrbitMap xi x⁻¹)
        ((Measure.haar :
          Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) =
        Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.adjointEvalLinearMap E xi (L : E →L[ℝ] E))
          (Measure.map SemidirectProduct.right
            ((Measure.haar :
              Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S)) := by
      rw [Measure.map_map hmeasurableOrbit hmeasurableRight]
      congr 1
    _ ≤ Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.adjointEvalLinearMap E xi (L : E →L[ℝ] E))
          (C₁ • lam.restrict (SemidirectProduct.right '' S)) :=
      Measure.map_mono hC₁ hmeasurableOrbit
    _ ≤ Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.adjointEvalLinearMap E xi (L : E →L[ℝ] E))
          (C₁ • (C₂ • (Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict
            (SemidirectProduct.right '' S))) := by
      refine Measure.map_mono ?_ hmeasurableOrbit
      gcongr
    _ = (C₁ * C₂) • Measure.map (fun L : (E →L[ℝ] E)ˣ ↦
            ContinuousLinearMap.adjointEvalLinearMap E xi (L : E →L[ℝ] E))
          ((Measure.haar : Measure (E →L[ℝ] E)ˣ).restrict (SemidirectProduct.right '' S)) := by
      rw [Measure.map_smul, Measure.map_smul, smul_smul]
    _ ≤ (C₁ * C₂) • (C₃ • (volume : Measure E).restrict B) := by gcongr
    _ = (C₁ * (C₂ * C₃)) • (volume : Measure E).restrict B := by
      rw [smul_smul, mul_assoc]

end LeanRidgelet
