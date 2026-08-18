/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.AffineFourier
public import LeanRidgelet.ToMathlib.LpUnimodular

/-!
# Explicit frequency-space affine action

This file separates the two elementary operators in the Fourier-side affine representation:

* the determinant-corrected pullback along the dual action `ξ ↦ Lᵀ ξ`;
* multiplication by the translation character `ξ ↦ exp (-2πi ⟪t, ξ⟫)`.

The dual pullback is obtained from the general quasi-invariant `L²` construction, and the phase
multiplier from the general unimodular `Lp` construction.  This provides an explicit operator on
every `L²` class, rather than only a formula on the Schwartz core.  The subsequent identification
with the Plancherel-conjugated representation is the analytic bridge to the Mackey model.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform InnerProductSpace NNReal RealInnerProductSpace

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The affine group acts on frequency space through the contragredient of its linear part. -/
def affineDualAction (g : E ≃ᵃ[ℝ] E) (xi : E) : E := g.linear.symm.adjoint xi

/-- The contragredient affine action, bundled separately so that it does not replace Mathlib's
ordinary affine action instance on the same types. -/
@[reducible] def affineDualMulAction : MulAction (E ≃ᵃ[ℝ] E) E :=
  MulAction.compHom E (LinearEquiv.contragredientHom.comp AffineEquiv.linearHom)

@[simp]
theorem affineDualMulAction_smul (g : E ≃ᵃ[ℝ] E) (xi : E) :
    letI : MulAction (E ≃ᵃ[ℝ] E) E := affineDualMulAction
    g • xi = affineDualAction g xi := rfl

/-- The inverse dual action is the adjoint of the forward linear part. -/
@[simp]
theorem affineDualAction_inv (g : E ≃ᵃ[ℝ] E) (xi : E) :
    affineDualAction g⁻¹ xi = g.linear.adjoint xi := by
  rfl

/-- The constant density of the inverse dual action. -/
def affineDualJacobian (g : E ≃ᵃ[ℝ] E) : E → ℝ≥0 :=
  fun _ ↦ ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineDualJacobian_one (xi : E) :
    affineDualJacobian (1 : E ≃ᵃ[ℝ] E) xi = 1 := by
  simp only [affineDualJacobian]
  rw [show (1 : E ≃ᵃ[ℝ] E).linear = LinearEquiv.refl ℝ E by rfl]
  simp

/-- The dual density obeys the Radon--Nikodym cocycle law. -/
theorem affineDualJacobian_cocycle (g h : E ≃ᵃ[ℝ] E) (xi : E) :
    affineDualJacobian (g * h) xi =
      affineDualJacobian g (affineDualAction h xi) * affineDualJacobian h xi := by
  change ‖LinearMap.det ((g * h).linear : E →ₗ[ℝ] E)‖₊⁻¹ =
    ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ *
      ‖LinearMap.det (h.linear : E →ₗ[ℝ] E)‖₊⁻¹
  rw [show (g * h).linear = g.linear * h.linear by
    exact (AffineEquiv.linearHom (k := ℝ) (P₁ := E)).map_mul g h]
  change ‖LinearMap.det ((g.linear : E →ₗ[ℝ] E).comp
    (h.linear : E →ₗ[ℝ] E))‖₊⁻¹ = _
  rw [LinearMap.det_comp, nnnorm_mul, mul_inv_rev]
  exact mul_comm _ _

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- The dual action is measurable. -/
theorem affineDualAction_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (affineDualAction g) :=
  (g.linear.symm.adjoint : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The constant dual Jacobian is measurable. -/
theorem affineDualJacobian_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (affineDualJacobian g) := measurable_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The dual Jacobian is everywhere nonzero. -/
theorem affineDualJacobian_ne_zero (g : E ≃ᵃ[ℝ] E) (xi : E) :
    affineDualJacobian g xi ≠ 0 := by
  simp only [affineDualJacobian, ne_eq, inv_eq_zero, nnnorm_eq_zero]
  exact g.linear.isUnit_det'.ne_zero

/-- Pushforward of Lebesgue measure by the inverse dual action. -/
theorem affineDualAction_map_eq_withDensity (g : E ≃ᵃ[ℝ] E) :
    volume.map (affineDualAction g⁻¹) =
      volume.withDensity (fun xi ↦ (affineDualJacobian g xi : ℝ≥0∞)) := by
  have h := Measure.map_affineEquiv_symm_addHaar_eq_withDensity
    (μ := (volume : Measure E)) (g.linear.symm.adjoint.toAffineEquiv)
  have hfun : ⇑g.linear.symm.adjoint.toAffineEquiv.symm = affineDualAction g⁻¹ := by
    funext xi
    rfl
  rw [hfun] at h
  rw [h]
  congr 1
  funext xi
  change (↑‖LinearMap.det (g.linear.symm.adjoint : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) =
    ↑(‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹)
  rw [LinearEquiv.det_adjoint, LinearEquiv.det_coe_symm, star_trivial, nnnorm_inv]

/-- The determinant-corrected pullback representation for the contragredient action on frequency
space. -/
noncomputable def affineDualPullbackLpUnitaryRepresentation :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp ℂ 2 (volume : Measure E)) := by
  letI : MulAction (E ≃ᵃ[ℝ] E) E := affineDualMulAction
  exact quasiInvariantLpUnitaryRepresentation affineDualJacobian
    (fun g ↦ affineDualAction_measurable g)
    (fun g ↦ affineDualAction_map_eq_withDensity g)
    affineDualJacobian_measurable affineDualJacobian_ne_zero
    affineDualJacobian_one (fun g h xi ↦ affineDualJacobian_cocycle g h xi)

/-- The dual pullback representation acts by `|det L|¹ᐟ² f(Lᵀξ)` on every `L²` class. -/
theorem affineDualPullbackLpUnitaryRepresentation_apply_ae
    (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 (volume : Measure E)) :
    ((↑(affineDualPullbackLpUnitaryRepresentation (E := E) g) :
        Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume) f) =ᵐ[volume]
      fun xi ↦ ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) •
        f (g.linear.adjoint xi)) := by
  letI : MulAction (E ≃ᵃ[ℝ] E) E := affineDualMulAction
  have h := quasiInvariantLpUnitaryRepresentation_apply_ae (E := ℂ) affineDualJacobian
    (fun g ↦ affineDualAction_measurable g)
    (fun g ↦ affineDualAction_map_eq_withDensity g)
    affineDualJacobian_measurable affineDualJacobian_ne_zero
    affineDualJacobian_one (fun g h xi ↦ affineDualJacobian_cocycle g h xi) g f
  have h' :
      ((↑(affineDualPullbackLpUnitaryRepresentation (E := E) g) :
          Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume) f) =ᵐ[volume]
        quasiRegularAction (radonNikodymWeight affineDualJacobian) g fun x ↦ f x := by
    simpa only [affineDualPullbackLpUnitaryRepresentation] using h
  filter_upwards [h'] with xi hxi
  rw [hxi]
  simp only [quasiRegularAction, radonNikodymWeight, affineDualJacobian,
    affineDualMulAction_smul, affineDualAction_inv, NNReal.sqrt_inv]
  push_cast
  rw [inv_inv]

/-- The translation character appearing in the Fourier-side affine action. -/
def affineFrequencyPhase (g : E ≃ᵃ[ℝ] E) (xi : E) : ℂ :=
  ((Real.fourierChar (-⟪g 0, xi⟫_ℝ) : Circle) : ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The affine frequency phase is a multiplier cocycle for inverse dual pullback.  This is the
character twist that distinguishes the Mackey representation from the untwisted quasi-regular
action on the homogeneous orbit. -/
theorem affineFrequencyPhase_cocycle (g h : E ≃ᵃ[ℝ] E) (xi : E) :
    affineFrequencyPhase (g * h) xi =
      affineFrequencyPhase g xi * affineFrequencyPhase h (affineDualAction g⁻¹ xi) := by
  have hzero : (g * h) 0 = g (h 0) := rfl
  have hg : g (h 0) = g.linear (h 0) + g 0 := by
    exact congrFun (AffineMap.decomp (g : E →ᵃ[ℝ] E)) (h 0)
  have hinner : ⟪g.linear (h 0), xi⟫_ℝ = ⟪h 0, g.linear.adjoint xi⟫_ℝ := by
    exact (LinearMap.adjoint_inner_right (g.linear : E →ₗ[ℝ] E) (h 0) xi).symm
  simp only [affineFrequencyPhase, affineDualAction_inv]
  rw [hzero, hg, inner_add_left, neg_add_rev, Real.fourierChar.map_add_eq_mul]
  rw [hinner]
  push_cast
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On the translation subgroup, the Fourier-side phase is precisely the Mackey translation
character at the current frequency. -/
@[simp]
theorem affineFrequencyPhase_translation (b xi : E) :
    affineFrequencyPhase (affineTranslation b) xi =
      (affineTranslationCharacter xi b : ℂ) := by
  simp only [affineFrequencyPhase, affineTranslationCharacter_apply,
    affineTranslation_apply, add_zero]

/-- The affine frequency phase is continuous, hence strongly measurable. -/
theorem affineFrequencyPhase_aestronglyMeasurable (g : E ≃ᵃ[ℝ] E) :
    AEStronglyMeasurable (affineFrequencyPhase g) volume := by
  apply Continuous.aestronglyMeasurable
  have hinner : Continuous (fun xi : E ↦ -⟪g 0, xi⟫_ℝ) :=
    (continuous_const.inner continuous_id).neg
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp hinner)

/-- The affine frequency phase has norm one everywhere. -/
theorem affineFrequencyPhase_norm_one (g : E ≃ᵃ[ℝ] E) :
    ∀ᵐ xi ∂(volume : Measure E), ‖affineFrequencyPhase g xi‖ = 1 := by
  filter_upwards with xi
  exact Circle.norm_coe _

/-- Multiplication by the affine frequency phase, bundled as a unitary `Lp` operator. -/
noncomputable def affineFrequencyPhaseMultiplier (g : E ≃ᵃ[ℝ] E) :
    Lp ℂ 2 (volume : Measure E) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  unimodularMultiplierLinearIsometryEquiv (affineFrequencyPhase g)
    (affineFrequencyPhase_aestronglyMeasurable g) (affineFrequencyPhase_norm_one g)

/-- The phase multiplier has its defining pointwise representative. -/
theorem affineFrequencyPhaseMultiplier_apply_ae (g : E ≃ᵃ[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    affineFrequencyPhaseMultiplier g f =ᵐ[volume]
      fun xi ↦ affineFrequencyPhase g xi * f xi :=
  unimodularMultiplierLinearIsometryEquiv_apply_ae (affineFrequencyPhase g)
    (affineFrequencyPhase_aestronglyMeasurable g) (affineFrequencyPhase_norm_one g) f

/-- The explicit Fourier-side affine operator: dual pullback followed by multiplication by the
translation character. -/
noncomputable def affineFrequencyLinearIsometryEquiv (g : E ≃ᵃ[ℝ] E) :
    Lp ℂ 2 (volume : Measure E) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Unitary.linearIsometryEquiv (affineDualPullbackLpUnitaryRepresentation (E := E) g)).trans
    (affineFrequencyPhaseMultiplier g)

/-- The explicit Fourier-side affine operator acts by character multiplication and adjoint
pullback on every `L²` class. -/
theorem affineFrequencyLinearIsometryEquiv_apply_ae (g : E ≃ᵃ[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    affineFrequencyLinearIsometryEquiv g f =ᵐ[volume]
      fun xi ↦ affineFrequencyPhase g xi *
        (((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) *
          f (g.linear.adjoint xi))) := by
  have hpullback := affineDualPullbackLpUnitaryRepresentation_apply_ae g f
  have hphase := affineFrequencyPhaseMultiplier_apply_ae g
    (Unitary.linearIsometryEquiv (affineDualPullbackLpUnitaryRepresentation (E := E) g) f)
  filter_upwards [hpullback, hphase] with xi hpullbackxi hphasexi
  change (Unitary.linearIsometryEquiv
      (affineDualPullbackLpUnitaryRepresentation (E := E) g) f) xi = _ at hpullbackxi
  change (affineFrequencyPhaseMultiplier g
      (Unitary.linearIsometryEquiv (affineDualPullbackLpUnitaryRepresentation (E := E) g) f)) xi = _
  rw [hphasexi, hpullbackxi]
  simp only [smul_eq_mul]

/-- The Plancherel-conjugated representation has the explicit affine frequency formula on the
ordinary Schwartz core (rather than only on Fourier transforms of Schwartz vectors). -/
theorem affineFourierLpUnitaryRepresentation_schwartz_input_ae
    (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) :
    (Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g)
      (f.toLp 2 volume) : Lp ℂ 2 volume) =ᵐ[volume]
      fun xi ↦ Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) •
          f (g.linear.adjoint xi)) := by
  have h := affineFourierLpUnitaryRepresentation_schwartz_ae g (𝓕⁻ f)
  have hinput : 𝓕 ((𝓕⁻ f).toLp 2 volume) = f.toLp 2 volume := by
    rw [← SchwartzMap.toLp_fourierInv_eq]
    exact FourierTransform.fourier_fourierInv_eq _
  rw [hinput] at h
  filter_upwards [h] with xi hxi
  rw [hxi, ← SchwartzMap.fourier_coe]
  exact congrArg (fun z ↦ Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
    ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) • z))
      (congrArg (fun q : SchwartzMap E ℂ ↦ q (g.linear.adjoint xi))
        (FourierTransform.fourier_fourierInv_eq f))

/-- The explicit frequency operator is exactly the Plancherel-conjugated affine action on all of
`L²`.  The proof uses the explicit formulas on the dense Schwartz core and continuity of both
unitary operators. -/
theorem affineFrequencyLinearIsometryEquiv_eq_fourierRepresentation
    (g : E ≃ᵃ[ℝ] E) :
    affineFrequencyLinearIsometryEquiv g =
      Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g) := by
  letI : MulAction (E ≃ᵃ[ℝ] E) E := affineDualMulAction
  apply LinearIsometryEquiv.ext
  intro f
  let P : Lp ℂ 2 (volume : Measure E) → Prop := fun f ↦
    affineFrequencyLinearIsometryEquiv g f =
      Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g) f
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := (volume : Measure E))
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (affineFrequencyLinearIsometryEquiv g).continuous
      (Unitary.linearIsometryEquiv
        (affineFourierLpUnitaryRepresentation (E := E) g)).continuous
  · intro h
    change affineFrequencyLinearIsometryEquiv g (h.toLp 2 volume) =
      Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g)
        (h.toLp 2 volume)
    apply Lp.ext
    have hexplicit := affineFrequencyLinearIsometryEquiv_apply_ae g (h.toLp 2 volume)
    have habstract := affineFourierLpUnitaryRepresentation_schwartz_input_ae g h
    have hcoe := (quasiMeasurePreserving_of_map_eq_withDensity
      affineDualJacobian (fun k ↦ affineDualAction_measurable k)
      (fun k ↦ affineDualAction_map_eq_withDensity k) g).ae_eq (h.coeFn_toLp 2 volume)
    filter_upwards [hexplicit, habstract, hcoe] with xi hexplicitxi habstractxi hcoexi
    simp only [Function.comp_apply, affineDualMulAction_smul, affineDualAction_inv] at hcoexi
    rw [hexplicitxi, habstractxi]
    rw [hcoexi]
    simp only [affineFrequencyPhase, Circle.smul_def, smul_eq_mul]

/-- Consequently, the Plancherel-conjugated affine representation has the character-times-dual-
pullback formula for every `L²` class. -/
theorem affineFourierLpUnitaryRepresentation_apply_ae (g : E ≃ᵃ[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g) f :
      Lp ℂ 2 volume) =ᵐ[volume]
      fun xi ↦ affineFrequencyPhase g xi *
        (((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) *
          f (g.linear.adjoint xi))) := by
  rw [← affineFrequencyLinearIsometryEquiv_eq_fourierRepresentation g]
  exact affineFrequencyLinearIsometryEquiv_apply_ae g f

end Measure

end LeanRidgelet
