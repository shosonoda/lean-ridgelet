/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.AffineMackeyMeasure
public import LeanRidgelet.ToMathlib.LpIndicator
public import LeanRidgelet.ToMathlib.LieGroup.HomogeneousSection

/-!
# Normalized-section induction for the affine Mackey model

This file constructs the normalized quotient section, its reentry cocycle and character phase,
the untwisted and character-twisted quasi-regular representations, and the canonical indicator
covariance. The induced model is identified with the explicit twisted quotient model.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContRepresentation ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A normalized set-theoretic section of the affine homogeneous quotient.  Starting from
`Quotient.out`, it discards the translation coordinate.  This does not change the coset because
the Mackey subgroup contains every translation, and it is the normalization for which the
section-cocycle character agrees exactly with the Fourier phase. -/
noncomputable def affineTopologicalMackeySection {xi : E}
    (q : AffineTopologicalMackeyQuotient xi) :
    AffineEquiv.TopologicalSemidirectProduct E :=
  SemidirectProduct.inr (Quotient.out q).right

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized affine section is a right inverse of the quotient map. -/
theorem affineTopologicalMackeySection_rightInverse {xi : E} :
  Function.RightInverse (affineTopologicalMackeySection (E := E) (xi := xi))
      QuotientGroup.mk := by
  intro q
  calc
    QuotientGroup.mk (affineTopologicalMackeySection (E := E) q) =
        QuotientGroup.mk (Quotient.out q) := by
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      change affineTopologicalDualAction
        ((affineTopologicalMackeySection (E := E) q)⁻¹ * Quotient.out q).right xi = xi
      simpa [affineTopologicalMackeySection] using
        affineTopologicalDualAction_one (E := E) xi
    _ = q := Quotient.out_eq' q

/-- The Mackey-subgroup-valued reentry cocycle of the normalized affine section. -/
noncomputable def affineTopologicalMackeySectionCocycle {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) : affineTopologicalMackeySubgroup xi :=
  QuotientGroup.leftCosetSectionCocycleOf
    (affineTopologicalMackeySubgroup xi).toSubgroup
    (affineTopologicalMackeySection (E := E))
    affineTopologicalMackeySection_rightInverse g q

/-- Applying the inducing character to the normalized section cocycle gives the section-model
phase. -/
noncomputable def affineTopologicalMackeySectionPhase {xi : E}
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) : ℂ :=
  (affineTopologicalMackeyCharacter xi
    (affineTopologicalMackeySectionCocycle g q) : Circle)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Evaluating the quotient-orbit homeomorphism through `Quotient.out` uses only the linear
coordinate of the representative. -/
theorem affineTopologicalMackeyQuotientHomeomorphDualOrbit_eq_out {xi : E} (hxi : xi ≠ 0)
    (q : AffineTopologicalMackeyQuotient xi) :
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 =
      affineTopologicalDualAction (Quotient.out q).right xi := by
  let p := Quotient.out q
  calc
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 =
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi
          (QuotientGroup.mk p)).1 := by
            exact congrArg
              (fun z ↦ (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi z).1)
              (Quotient.out_eq' q).symm
    _ = affineTopologicalDualAction p.right xi := rfl

/-- The Mackey character phase on the affine homogeneous quotient, obtained from the frequency
attached to a coset by the quotient-orbit homeomorphism. -/
def affineTopologicalMackeyQuotientPhase {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) : ℂ :=
  affineFrequencyPhase (AffineEquiv.topologicalSemidirectProductEquiv E g)
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The phase obtained from the normalized section cocycle is exactly the explicit Fourier phase.
Thus the homogeneous quotient representation already is the equivariant-section realization of
unitary induction from `affineTopologicalMackeyCharacter`; no additional gauge multiplier is
needed. -/
theorem affineTopologicalMackeySectionPhase_eq_quotientPhase {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeySectionPhase g q =
      affineTopologicalMackeyQuotientPhase hxi g q := by
  rw [affineTopologicalMackeySectionPhase,
    affineTopologicalMackeySectionCocycle,
    affineTopologicalMackeyCharacter,
    QuotientGroup.leftCosetSectionCocycleOf]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [affineTopologicalMackeyQuotientPhase, affineFrequencyPhase]
  simp only [affineTopologicalMackeySection, SemidirectProduct.mul_left,
    SemidirectProduct.inv_left, SemidirectProduct.right_inr, map_inv,
    SemidirectProduct.left_inr, inv_one, MulAut.inv_apply, map_one,
    SemidirectProduct.inv_right, one_mul, SemidirectProduct.mul_right, map_mul,
    map_zero, mul_one, affineTranslationCharacter_apply,
    AffineEquiv.topologicalSemidirectProductEquiv_apply, add_zero, SetLike.coe_eq_coe]
  rw [affineTopologicalMackeyQuotientHomeomorphDualOrbit_eq_out hxi]
  change Real.fourierChar
      (-⟪((↑((Quotient.out q).right⁻¹) : E →L[ℝ] E) g.left.toAdd), xi⟫_ℝ) =
    Real.fourierChar
      (-⟪g.left.toAdd,
        ((AffineEquiv.continuousLinearUnitsEquivLinearEquiv E
          (Quotient.out q).right).symm.adjoint xi)⟫_ℝ)
  apply congrArg Real.fourierChar
  apply congrArg Neg.neg
  exact (LinearMap.adjoint_inner_right
    ((↑((Quotient.out q).right⁻¹) : E →L[ℝ] E) : E →ₗ[ℝ] E) g.left.toAdd xi).symm

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The quotient phase is a multiplier cocycle for inverse left translation. -/
theorem affineTopologicalMackeyQuotientPhase_cocycle {xi : E} (hxi : xi ≠ 0)
    (g h : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientPhase hxi (g * h) q =
      affineTopologicalMackeyQuotientPhase hxi g q *
        affineTopologicalMackeyQuotientPhase hxi h (g⁻¹ • q) := by
  letI : MulAction (AffineEquiv.TopologicalSemidirectProduct E)
      (affineDualOrbit (E := E)) := affineTopologicalDualOrbitMulAction
  have he := affineTopologicalMackeyQuotientHomeomorphDualOrbit_smul hxi g⁻¹ q
  have hp := affineFrequencyPhase_cocycle
    (AffineEquiv.topologicalSemidirectProductEquiv E g)
    (AffineEquiv.topologicalSemidirectProductEquiv E h)
    (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1
  rw [affineTopologicalMackeyQuotientPhase,
    affineTopologicalMackeyQuotientPhase,
    affineTopologicalMackeyQuotientPhase]
  rw [map_mul]
  rw [hp]
  congr 2
  exact (congrArg Subtype.val he).symm

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The Mackey character phase is pointwise unimodular. -/
theorem affineTopologicalMackeyQuotientPhase_norm_one {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    ‖affineTopologicalMackeyQuotientPhase hxi g q‖ = 1 := by
  exact Circle.norm_coe _

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The Mackey character phase is continuous in the homogeneous-space variable. -/
theorem continuous_affineTopologicalMackeyQuotientPhase {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    Continuous (affineTopologicalMackeyQuotientPhase hxi g) := by
  unfold affineTopologicalMackeyQuotientPhase affineFrequencyPhase
  fun_prop

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- On translations, the quotient phase is exactly the Mackey translation character at the
frequency represented by the coset. -/
theorem affineTopologicalMackeyQuotientPhase_translation {xi : E} (hxi : xi ≠ 0) (b : E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientPhase hxi
        ((AffineEquiv.topologicalSemidirectProductEquiv E).symm (affineTranslation b)) q =
      (affineTranslationCharacter
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 b : ℂ) := by
  simp [affineTopologicalMackeyQuotientPhase]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The quotient character phase is one at the identity. -/
@[simp]
theorem affineTopologicalMackeyQuotientPhase_one {xi : E} (hxi : xi ≠ 0)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeyQuotientPhase hxi 1 q = 1 := by
  simp [affineTopologicalMackeyQuotientPhase, affineFrequencyPhase]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized section phase is a multiplier cocycle, as follows either from the general
section-cocycle law or from its identification with the Fourier phase. -/
theorem affineTopologicalMackeySectionPhase_cocycle {xi : E} (hxi : xi ≠ 0)
    (g h : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeySectionPhase (g * h) q =
      affineTopologicalMackeySectionPhase g q *
        affineTopologicalMackeySectionPhase h (g⁻¹ • q) := by
  rw [affineTopologicalMackeySectionPhase_eq_quotientPhase hxi,
    affineTopologicalMackeySectionPhase_eq_quotientPhase hxi,
    affineTopologicalMackeySectionPhase_eq_quotientPhase hxi]
  exact affineTopologicalMackeyQuotientPhase_cocycle hxi g h q

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized section phase is one at the identity. -/
@[simp]
theorem affineTopologicalMackeySectionPhase_one {xi : E} (hxi : xi ≠ 0)
    (q : AffineTopologicalMackeyQuotient xi) :
    affineTopologicalMackeySectionPhase
      (1 : AffineEquiv.TopologicalSemidirectProduct E) q = 1 := by
  rw [affineTopologicalMackeySectionPhase_eq_quotientPhase hxi]
  exact affineTopologicalMackeyQuotientPhase_one hxi q

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Although the chosen normalized section itself is only set-theoretic, its character phase is
continuous: the explicit equality with the Fourier phase supplies the regularity. -/
theorem continuous_affineTopologicalMackeySectionPhase {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    Continuous (affineTopologicalMackeySectionPhase (xi := xi) g) := by
  have hfun : affineTopologicalMackeySectionPhase (xi := xi) g =
      affineTopologicalMackeyQuotientPhase hxi g := by
    funext q
    exact affineTopologicalMackeySectionPhase_eq_quotientPhase hxi g q
  rw [hfun]
  exact continuous_affineTopologicalMackeyQuotientPhase hxi g

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized section phase is jointly continuous.  Rewriting it as the explicit Fourier phase
separates the translation coordinate of the group element from the frequency attached to the coset,
and both depend continuously on the pair. -/
theorem continuous_uncurry_affineTopologicalMackeySectionPhase {xi : E} (hxi : xi ≠ 0) :
    Continuous (Function.uncurry (affineTopologicalMackeySectionPhase (xi := xi))) := by
  have hzero : ∀ x : AffineEquiv.TopologicalSemidirectProduct E,
      (AffineEquiv.topologicalSemidirectProductEquiv E x) 0 = x.left.toAdd := by
    intro x
    simp
  have hfun : Function.uncurry (affineTopologicalMackeySectionPhase (xi := xi)) =
      fun p : AffineEquiv.TopologicalSemidirectProduct E ×
          AffineTopologicalMackeyQuotient xi ↦
        ((Real.fourierChar (-⟪p.1.left.toAdd,
          (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi p.2).1⟫_ℝ) : Circle) : ℂ) := by
    funext p
    change affineTopologicalMackeySectionPhase p.1 p.2 = _
    rw [affineTopologicalMackeySectionPhase_eq_quotientPhase hxi,
      affineTopologicalMackeyQuotientPhase, affineFrequencyPhase, hzero]
  rw [hfun]
  have hleft : Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦ p.1.left.toAdd :=
    (SemidirectProduct.continuous_left
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)).comp continuous_fst
  have horbit : Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦
      (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi p.2).1 :=
    (continuous_subtype_val.comp
      (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).continuous).comp continuous_snd
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (hleft.inner horbit).neg)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized section phase is pointwise unimodular. -/
theorem affineTopologicalMackeySectionPhase_norm_one {xi : E} (hxi : xi ≠ 0)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) :
    ‖affineTopologicalMackeySectionPhase g q‖ = 1 := by
  rw [affineTopologicalMackeySectionPhase_eq_quotientPhase hxi]
  exact affineTopologicalMackeyQuotientPhase_norm_one hxi g q

/-- The untwisted quasi-regular unitary representation on the affine homogeneous quotient.  This
is the measure-theoretic base of the Mackey model; the inducing character supplies an additional
unit-modulus phase in the representation transported from the frequency orbit below. -/
noncomputable def affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation {xi : E}
    (hxi : xi ≠ 0) :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :=
  quasiInvariantLpUnitaryRepresentation
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle

/-- The quotient quasi-regular representation has Folland's determinant-corrected pullback as an
almost-everywhere representative. -/
theorem affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation_apply_ae
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation hxi g) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      quasiRegularAction
        (radonNikodymWeight
          (affineTopologicalMackeyQuotientJacobian (xi := xi))) g fun q ↦ f q := by
  exact quasiInvariantLpUnitaryRepresentation_apply_ae
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle g f

/-- Explicitly, the quotient quasi-regular action is pullback by inverse left translation times
the square root of the affine determinant. -/
theorem affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation_apply_ae_explicit
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation hxi g) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ ((affineTopologicalJacobian g).sqrt : ℂ) • f (g⁻¹ • q) := by
  filter_upwards [
    affineTopologicalMackeyQuotientQuasiRegularLpUnitaryRepresentation_apply_ae hxi g f]
      with q hq
  rw [hq]
  exact congrArg (fun z : ℂ ↦ z • f (g⁻¹ • q))
    (affineTopologicalMackeyQuotientRadonNikodymWeight (E := E) g q)

/-- The character-twisted quasi-regular representation on `L²(G/H)`.  Its two factors are
constructed independently: the quotient measure supplies the Radon--Nikodym correction, while
the Mackey translation character supplies the unimodular multiplier cocycle. -/
noncomputable def
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation {xi : E}
    (hxi : xi ≠ 0) :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :=
  twistedQuasiInvariantLpUnitaryRepresentation
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle
    (affineTopologicalMackeyQuotientPhase hxi)
    (fun g ↦ (continuous_affineTopologicalMackeyQuotientPhase hxi g).aestronglyMeasurable)
    (fun g ↦ Filter.Eventually.of_forall
      (affineTopologicalMackeyQuotientPhase_norm_one hxi g))
    (affineTopologicalMackeyQuotientPhase_one hxi)
    (affineTopologicalMackeyQuotientPhase_cocycle hxi)

/-- The normalized-section realization of the unitary representation induced from the Mackey
character.  The reentry factor is literally the inducing character applied to
`s(q)⁻¹ g s(g⁻¹q)`; the quasi-invariant quotient measure supplies the independent
Radon--Nikodym square-root correction. -/
noncomputable def affineTopologicalMackeySectionInducedLpUnitaryRepresentation {xi : E}
    (hxi : xi ≠ 0) :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :=
  twistedQuasiInvariantLpUnitaryRepresentation
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle
    (affineTopologicalMackeySectionPhase (xi := xi))
    (fun g ↦ (continuous_affineTopologicalMackeySectionPhase hxi g).aestronglyMeasurable)
    (fun g ↦ Filter.Eventually.of_forall
      (affineTopologicalMackeySectionPhase_norm_one hxi g))
    (affineTopologicalMackeySectionPhase_one hxi)
    (affineTopologicalMackeySectionPhase_cocycle hxi)

set_option maxHeartbeats 400000 in
-- Elaborating the fully instantiated general twist unfolds a long chain of `Lp` isometries.
/-- The character-twisted quotient representation acts by the Mackey phase times the positive
square root of the affine determinant and inverse left translation. -/
theorem
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_apply_ae_explicit
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation hxi g) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ affineTopologicalMackeyQuotientPhase hxi g q *
        (((affineTopologicalJacobian g).sqrt : ℂ) * f (g⁻¹ • q)) := by
  have h := twistedQuasiInvariantLpUnitaryRepresentation_apply_ae
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle
    (affineTopologicalMackeyQuotientPhase hxi)
    (fun k ↦ (continuous_affineTopologicalMackeyQuotientPhase hxi k).aestronglyMeasurable)
    (fun k ↦ Filter.Eventually.of_forall
      (affineTopologicalMackeyQuotientPhase_norm_one hxi k))
    (affineTopologicalMackeyQuotientPhase_one hxi)
    (affineTopologicalMackeyQuotientPhase_cocycle hxi) g f
  have h' :
      ((↑(affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation hxi g) :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
              affineTopologicalMackeyQuotientMeasure hxi]
        fun q ↦ affineTopologicalMackeyQuotientPhase hxi g q *
          (radonNikodymWeight
            (affineTopologicalMackeyQuotientJacobian (xi := xi)) g q * f (g⁻¹ • q)) := by
    simpa only [affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation] using h
  filter_upwards [h'] with q hq
  rw [hq, affineTopologicalMackeyQuotientRadonNikodymWeight (E := E) g q]

set_option maxHeartbeats 400000 in
-- As above, the concrete section model instantiates the full general twist construction.
/-- The normalized-section induced representation has the same explicit action, with the
character of the reentry cocycle displayed through its equality with the Fourier phase. -/
theorem affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (f : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    ((↑(affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g) :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
            affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ affineTopologicalMackeySectionPhase g q *
        (((affineTopologicalJacobian g).sqrt : ℂ) * f (g⁻¹ • q)) := by
  have h := twistedQuasiInvariantLpUnitaryRepresentation_apply_ae
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi)
    affineTopologicalMackeyQuotientJacobian_measurable
    affineTopologicalMackeyQuotientJacobian_ne_zero
    affineTopologicalMackeyQuotientJacobian_one
    affineTopologicalMackeyQuotientJacobian_cocycle
    (affineTopologicalMackeySectionPhase (xi := xi))
    (fun k ↦ (continuous_affineTopologicalMackeySectionPhase hxi k).aestronglyMeasurable)
    (fun k ↦ Filter.Eventually.of_forall
      (affineTopologicalMackeySectionPhase_norm_one hxi k))
    (affineTopologicalMackeySectionPhase_one hxi)
    (affineTopologicalMackeySectionPhase_cocycle hxi) g f
  have h' :
      ((↑(affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g) :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f) =ᵐ[
              affineTopologicalMackeyQuotientMeasure hxi]
        fun q ↦ affineTopologicalMackeySectionPhase g q *
          (radonNikodymWeight
            (affineTopologicalMackeyQuotientJacobian (xi := xi)) g q * f (g⁻¹ • q)) := by
    simpa only [affineTopologicalMackeySectionInducedLpUnitaryRepresentation] using h
  filter_upwards [h'] with q hq
  rw [hq, affineTopologicalMackeyQuotientRadonNikodymWeight (E := E) g q]

set_option maxHeartbeats 800000 in
-- The fully instantiated section action and its two `Lp` indicator operators elaborate deeply.
/-- The measurable-set multiplication projections on the homogeneous quotient form the canonical
system of imprimitivity for the normalized-section induced representation.  In operator form,
restricting the output to `s` and then acting by `g` is the same as first restricting to the
inverse translate of `s` and then acting by `g`. -/
theorem
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_indicator_covariant
    {xi : E} (hxi : xi ≠ 0) (g : AffineEquiv.TopologicalSemidirectProduct E)
    (s : Set (AffineTopologicalMackeyQuotient xi)) (hs : MeasurableSet s) :
    let t := (fun q : AffineTopologicalMackeyQuotient xi ↦ g • q) ⁻¹' s
    MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs ∘L
        (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) =
      (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
            Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) ∘L
        MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
          (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) t
          (hs.preimage (measurable_affineTopologicalMackeyQuotient_smul g)) := by
  let t := (fun q : AffineTopologicalMackeyQuotient xi ↦ g • q) ⁻¹' s
  have ht : MeasurableSet t :=
    hs.preimage (measurable_affineTopologicalMackeyQuotient_smul g)
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hleft := MeasureTheory.indicatorLp_apply_ae (p := (2 : ℝ≥0∞))
    (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs
    ((affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f)
  have haction :=
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit hxi g f
  have hright :=
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit hxi g
      (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
        (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) t ht f)
  have hind := MeasureTheory.indicatorLp_apply_ae (p := (2 : ℝ≥0∞))
    (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) t ht f
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi) g
  have hind' := hqmp.ae_eq hind
  filter_upwards [hleft, haction, hright, hind'] with q hleftq hactionq hrightq hindq
  change
    (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
      (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) s hs
      ((affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) f)) q =
    ((affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
      Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi))
      (MeasureTheory.indicatorLp (p := (2 : ℝ≥0∞))
        (μ := affineTopologicalMackeyQuotientMeasure hxi) (E := ℂ) (𝕜 := ℂ) t ht f)) q
  rw [hleftq, hrightq]
  simp only [Function.comp_apply] at hindq
  by_cases hqs : q ∈ s
  · have hqt : g⁻¹ • q ∈ t := by
      change g • (g⁻¹ • q) ∈ s
      simpa only [← mul_smul, mul_inv_cancel, one_smul] using hqs
    simp only [Set.indicator_of_mem hqs, Set.indicator_of_mem hqt] at hindq ⊢
    rw [hactionq, hindq]
  · have hqt : g⁻¹ • q ∉ t := by
      change g • (g⁻¹ • q) ∉ s
      simpa only [← mul_smul, mul_inv_cancel, one_smul] using hqs
    simp only [Set.indicator_of_notMem hqs, Set.indicator_of_notMem hqt] at hindq ⊢
    rw [hindq]
    simp

set_option maxHeartbeats 400000 in
-- Comparing the two independently bundled `Lp` actions elaborates both general twist instances.
/-- The normalized-section induced model equals the explicit character-twisted quotient
representation.  This closes the model-identification part of unitary induction; the remaining
Mackey endpoint is the irreducibility/imprimitivity theorem itself. -/
theorem affineTopologicalMackeySectionInducedLpUnitaryRepresentation_eq_quotient
    {xi : E} (hxi : xi ≠ 0) :
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi =
      affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation hxi := by
  ext g f
  have hsection :=
    affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit hxi g f
  have hquotient :=
    affineTopologicalMackeyQuotientCharacterTwistedLpUnitaryRepresentation_apply_ae_explicit
      hxi g f
  filter_upwards [hsection, hquotient] with q hs hq
  rw [hs, hq, affineTopologicalMackeySectionPhase_eq_quotientPhase hxi]

end LeanRidgelet
