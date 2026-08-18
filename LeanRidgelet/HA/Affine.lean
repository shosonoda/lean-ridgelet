/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.BochnerIntertwining
public import LeanRidgelet.ToMathlib.AffineHaar

/-!
# Affine data and parameter actions

This file formalizes the affine actions underlying the fully-connected depth-two example of
arXiv:2405.13682. An affine equivalence `g x = L x + t` acts on data by `x ↦ g x` and on ridge
parameters by

`(a, b) ↦ (L⁻ᵀ a, b + ⟪t, L⁻ᵀ a⟫)`.

The ridge argument `⟪a, x⟫ - b` is invariant under the joint action. The data and parameter Haar
Jacobians are respectively `‖det L‖₊` and `‖det L‖₊⁻¹`; consequently their Radon--Nikodym square
roots satisfy exactly the balance conditions required by the quasi-invariant Bochner synthesis and
ridgelet intertwining theorems. The resulting corrected pullbacks are also bundled as unitary
representations on `L²`.

The construction is coordinate-free on an arbitrary finite-dimensional real inner-product space;
coordinates enter only through the basis-independent determinant.

## Deviations from the article

The article presents the affine example using invariant-measure notation. Lebesgue measure is not
invariant under a general affine linear part. Here both actions use their explicit constant
Radon--Nikodym densities. This correction changes the representation weights but preserves the
jointly invariant feature formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The translation-dependent lower-left block in the affine parameter action. -/
def affineParameterShear (g : E ≃ᵃ[ℝ] E) : E →ₗ[ℝ] ℝ :=
  (innerSL ℝ (g 0)).toLinearMap.comp (g.linear.symm.adjoint : E →ₗ[ℝ] E)

/-- The contragredient affine action on ridge parameters `(a, b)`. If `g x = L x + t`, this sends
`(a, b)` to `(L⁻ᵀ a, b + ⟪t, L⁻ᵀ a⟫)`. -/
def affineParameterLinearEquiv (g : E ≃ᵃ[ℝ] E) : (E × ℝ) ≃ₗ[ℝ] (E × ℝ) :=
  g.linear.symm.adjoint.skewProd (LinearEquiv.refl ℝ ℝ) (affineParameterShear g)

@[simp]
theorem affineParameterLinearEquiv_apply (g : E ≃ᵃ[ℝ] E) (p : E × ℝ) :
    affineParameterLinearEquiv g p =
      (g.linear.symm.adjoint p.1, p.2 + ⟪g 0, g.linear.symm.adjoint p.1⟫_ℝ) := by
  rfl

/-- The scalar affine functional used by a ridge feature. -/
def affineRidgeArgument (x : E) (p : E × ℝ) : ℝ := ⟪p.1, x⟫_ℝ - p.2

omit [FiniteDimensional ℝ E] in
/-- Ridge parameters are determined by their affine functional. -/
theorem affineRidgeArgument_parameter_injective :
    Function.Injective (fun p : E × ℝ ↦ fun x : E ↦ affineRidgeArgument x p) := by
  intro p q hpq
  have hb : p.2 = q.2 := by
    have hzero := congrFun hpq 0
    simpa [affineRidgeArgument] using hzero
  have ha : innerSL ℝ p.1 = innerSL ℝ q.1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrFun hpq x
    simp only [affineRidgeArgument] at hx
    change ⟪p.1, x⟫_ℝ = ⟪q.1, x⟫_ℝ
    linarith
  exact Prod.ext (innerSL_inj.mp ha) hb

/-- The ridge argument is invariant under the joint affine data/parameter action. -/
theorem affineRidgeArgument_invariant (g : E ≃ᵃ[ℝ] E) (x : E) (p : E × ℝ) :
    affineRidgeArgument (g x) (affineParameterLinearEquiv g p) =
      affineRidgeArgument x p := by
  change ⟪g.linear.symm.adjoint p.1, g x⟫_ℝ -
    (p.2 + ⟪g 0, g.linear.symm.adjoint p.1⟫_ℝ) = ⟪p.1, x⟫_ℝ - p.2
  rw [show g x = g.linear x + g 0 by
    exact congrFun g.toAffineMap.decomp x]
  rw [inner_add_right]
  rw [show ⟪g.linear.symm.adjoint p.1, g.linear x⟫_ℝ =
      ⟪p.1, (g.linear.symm : E →ₗ[ℝ] E) (g.linear x)⟫_ℝ by
    exact LinearMap.adjoint_inner_left (g.linear.symm : E →ₗ[ℝ] E) (g.linear x) p.1]
  simp [real_inner_comm]

/-- The contragredient action of the affine group on ridge parameters. -/
instance affineParameterMulAction : MulAction (E ≃ᵃ[ℝ] E) (E × ℝ) where
  smul g p := affineParameterLinearEquiv g p
  one_smul p := by
    apply affineRidgeArgument_parameter_injective
    funext x
    change affineRidgeArgument x (affineParameterLinearEquiv (AffineEquiv.refl ℝ E) p) =
      affineRidgeArgument x p
    simpa using affineRidgeArgument_invariant (AffineEquiv.refl ℝ E) x p
  mul_smul g h p := by
    apply affineRidgeArgument_parameter_injective
    funext x
    have hgh := affineRidgeArgument_invariant (g * h) ((g * h).symm x) p
    have hg := affineRidgeArgument_invariant g (g.symm x)
      (affineParameterLinearEquiv h p)
    have hh := affineRidgeArgument_invariant h (h.symm (g.symm x)) p
    have hgh' : affineRidgeArgument x (affineParameterLinearEquiv (g * h) p) =
        affineRidgeArgument ((g * h).symm x) p := by simpa using hgh
    have hg' : affineRidgeArgument x
          (affineParameterLinearEquiv g (affineParameterLinearEquiv h p)) =
        affineRidgeArgument (g.symm x) (affineParameterLinearEquiv h p) := by
      simpa using hg
    have hh' : affineRidgeArgument (g.symm x) (affineParameterLinearEquiv h p) =
        affineRidgeArgument (h.symm (g.symm x)) p := by simpa using hh
    exact hgh'.trans <| by
      rw [show (g * h).symm x = h.symm (g.symm x) by rfl]
      exact (hg'.trans hh').symm

/-- The inverse affine group element acts by the inverse parameter equivalence. -/
theorem affineParameterLinearEquiv_inv (g : E ≃ᵃ[ℝ] E) :
    affineParameterLinearEquiv g⁻¹ = (affineParameterLinearEquiv g).symm := by
  apply LinearEquiv.ext
  intro p
  apply (affineParameterLinearEquiv g).injective
  rw [(affineParameterLinearEquiv g).apply_symm_apply]
  change g • (g⁻¹ • p) = p
  exact smul_inv_smul g p

/-- The parameter action has determinant `(det L)⁻¹`. -/
theorem det_affineParameterLinearEquiv (g : E ≃ᵃ[ℝ] E) :
    LinearMap.det (affineParameterLinearEquiv g : E × ℝ →ₗ[ℝ] E × ℝ) =
      (LinearMap.det (g.linear : E →ₗ[ℝ] E))⁻¹ := by
  rw [affineParameterLinearEquiv, LinearEquiv.det_skewProd,
    LinearEquiv.det_adjoint]
  simp [LinearEquiv.det_coe_symm]

/-- The constant Radon--Nikodym density for the inverse affine data action. -/
def affineDataJacobian (g : E ≃ᵃ[ℝ] E) : E → ℝ≥0 :=
  fun _ ↦ ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊

/-- The constant Radon--Nikodym density for the inverse contragredient parameter action. -/
def affineParameterJacobian (g : E ≃ᵃ[ℝ] E) : E × ℝ → ℝ≥0 :=
  fun _ ↦ ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineDataJacobian_one (x : E) :
    affineDataJacobian (1 : E ≃ᵃ[ℝ] E) x = 1 := by
  change ‖LinearMap.det (((1 : E ≃ᵃ[ℝ] E).linear : E →ₗ[ℝ] E))‖₊ = 1
  rw [show (1 : E ≃ᵃ[ℝ] E).linear = LinearEquiv.refl ℝ E by rfl]
  simp

omit [FiniteDimensional ℝ E] in
/-- The data Jacobian obeys the Radon--Nikodym cocycle law. -/
theorem affineDataJacobian_cocycle (g h : E ≃ᵃ[ℝ] E) (x : E) :
    affineDataJacobian (g * h) x =
      affineDataJacobian g (h • x) * affineDataJacobian h x := by
  change ‖LinearMap.det ((g * h).linear : E →ₗ[ℝ] E)‖₊ =
    ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ *
      ‖LinearMap.det (h.linear : E →ₗ[ℝ] E)‖₊
  rw [show (g * h).linear = g.linear * h.linear by
    exact (AffineEquiv.linearHom (k := ℝ) (P₁ := E)).map_mul g h]
  change ‖LinearMap.det ((g.linear : E →ₗ[ℝ] E).comp (h.linear : E →ₗ[ℝ] E))‖₊ = _
  rw [LinearMap.det_comp, nnnorm_mul]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineParameterJacobian_one (p : E × ℝ) :
    affineParameterJacobian (1 : E ≃ᵃ[ℝ] E) p = 1 := by
  simp only [affineParameterJacobian]
  rw [show (1 : E ≃ᵃ[ℝ] E).linear = LinearEquiv.refl ℝ E by rfl]
  simp

/-- The parameter Jacobian obeys the Radon--Nikodym cocycle law. -/
theorem affineParameterJacobian_cocycle (g h : E ≃ᵃ[ℝ] E) (p : E × ℝ) :
    affineParameterJacobian (g * h) p =
      affineParameterJacobian g (h • p) * affineParameterJacobian h p := by
  change ‖LinearMap.det ((g * h).linear : E →ₗ[ℝ] E)‖₊⁻¹ =
    ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ *
      ‖LinearMap.det (h.linear : E →ₗ[ℝ] E)‖₊⁻¹
  rw [show (g * h).linear = g.linear * h.linear by
    exact (AffineEquiv.linearHom (k := ℝ) (P₁ := E)).map_mul g h]
  change ‖LinearMap.det ((g.linear : E →ₗ[ℝ] E).comp (h.linear : E →ₗ[ℝ] E))‖₊⁻¹ = _
  rw [LinearMap.det_comp, nnnorm_mul, mul_inv_rev]
  exact mul_comm _ _

omit [FiniteDimensional ℝ E] in
/-- The parameter density square root is the data-side inverse square-root multiplier. -/
theorem affine_synthesis_balance (g : E ≃ᵃ[ℝ] E) (x : E) (p : E × ℝ) :
    ((affineParameterJacobian g p).sqrt : ℂ) =
      ((affineDataJacobian g (g.symm x)).sqrt : ℂ)⁻¹ := by
  simp [affineParameterJacobian, affineDataJacobian, NNReal.sqrt_inv]

/-- The data density square root is the parameter-side inverse square-root multiplier. -/
theorem affine_ridgelet_balance (g : E ≃ᵃ[ℝ] E) (x : E) (p : E × ℝ) :
    ((affineDataJacobian g x).sqrt : ℂ) =
      ((affineParameterJacobian g ((affineParameterLinearEquiv g).symm p)).sqrt : ℂ)⁻¹ := by
  simp [affineParameterJacobian, affineDataJacobian, NNReal.sqrt_inv]

omit [FiniteDimensional ℝ E] in
/-- The synthesis balance in the form expected by the generic quasi-invariant theorem. -/
theorem affine_synthesis_radonNikodym_balance (g : E ≃ᵃ[ℝ] E)
    (x : E) (p : E × ℝ) :
    ((affineParameterJacobian g p).sqrt : ℂ) =
      radonNikodymWeight affineDataJacobian g x := by
  exact affine_synthesis_balance g x p

/-- The ridgelet balance in the form expected by the generic quasi-invariant theorem. -/
theorem affine_ridgelet_radonNikodym_balance (g : E ≃ᵃ[ℝ] E)
    (x : E) (p : E × ℝ) :
    ((affineDataJacobian g x).sqrt : ℂ) =
      radonNikodymWeight affineParameterJacobian g p := by
  exact affine_ridgelet_balance g x p

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- Pushforward of data Haar measure by the inverse affine action. -/
theorem affineData_map_eq_withDensity (μ : Measure E) [μ.IsAddHaarMeasure]
    (g : E ≃ᵃ[ℝ] E) :
    μ.map g.symm = μ.withDensity (fun x ↦ (affineDataJacobian g x : ℝ≥0∞)) := by
  exact Measure.map_affineEquiv_symm_addHaar_eq_withDensity μ g

/-- Pushforward of parameter Haar measure by the inverse contragredient action. -/
theorem affineParameter_map_eq_withDensity (ν : Measure (E × ℝ))
    [ν.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    ν.map (affineParameterLinearEquiv g).symm =
      ν.withDensity (fun p ↦ (affineParameterJacobian g p : ℝ≥0∞)) := by
  have h := Measure.map_affineEquiv_symm_addHaar_eq_withDensity ν
    (affineParameterLinearEquiv g).toAffineEquiv
  have hfun :
      ⇑(affineParameterLinearEquiv g).toAffineEquiv.symm =
        ⇑(affineParameterLinearEquiv g).symm := rfl
  rw [hfun] at h
  simpa [LinearEquiv.toAffineEquiv,
    det_affineParameterLinearEquiv, affineParameterJacobian, nnnorm_inv] using h

/-- The data pushforward formula expressed through the affine-group action instance. -/
theorem affineData_group_map_eq_withDensity (μ : Measure E) [μ.IsAddHaarMeasure]
    (g : E ≃ᵃ[ℝ] E) :
    μ.map (fun x ↦ g⁻¹ • x) =
      μ.withDensity (fun x ↦ (affineDataJacobian g x : ℝ≥0∞)) := by
  exact affineData_map_eq_withDensity μ g

/-- The parameter pushforward formula expressed through the affine-group action instance. -/
theorem affineParameter_group_map_eq_withDensity (ν : Measure (E × ℝ))
    [ν.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    ν.map (fun p ↦ g⁻¹ • p) =
      ν.withDensity (fun p ↦ (affineParameterJacobian g p : ℝ≥0∞)) := by
  change ν.map (affineParameterLinearEquiv g⁻¹) = _
  rw [affineParameterLinearEquiv_inv]
  exact affineParameter_map_eq_withDensity ν g

/-- The affine data action is measurable. -/
theorem affineData_measurable (g : E ≃ᵃ[ℝ] E) : Measurable fun x : E ↦ g • x :=
  g.continuous_of_finiteDimensional.measurable

/-- The affine parameter action is measurable. -/
theorem affineParameter_measurable (g : E ≃ᵃ[ℝ] E) : Measurable fun p : E × ℝ ↦ g • p :=
  (affineParameterLinearEquiv g : E × ℝ →ₗ[ℝ] E × ℝ)
    |>.continuous_of_finiteDimensional.measurable

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The constant data Jacobian is measurable. -/
theorem affineDataJacobian_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (affineDataJacobian g) := measurable_const

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The constant parameter Jacobian is measurable. -/
theorem affineParameterJacobian_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (affineParameterJacobian g) := measurable_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The data Jacobian is everywhere nonzero. -/
theorem affineDataJacobian_ne_zero (g : E ≃ᵃ[ℝ] E) (x : E) :
    affineDataJacobian g x ≠ 0 := by
  simp only [affineDataJacobian, ne_eq, nnnorm_eq_zero]
  exact g.linear.isUnit_det'.ne_zero

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The parameter Jacobian is everywhere nonzero. -/
theorem affineParameterJacobian_ne_zero (g : E ≃ᵃ[ℝ] E) (p : E × ℝ) :
    affineParameterJacobian g p ≠ 0 := by
  simp only [affineParameterJacobian, ne_eq, inv_eq_zero, nnnorm_eq_zero]
  exact g.linear.isUnit_det'.ne_zero

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The Radon--Nikodym-corrected affine data representation on Bochner `L²`. -/
noncomputable def affineDataLpUnitaryRepresentation (μ : Measure E)
    [μ.IsAddHaarMeasure] [SigmaFinite μ] :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp Y 2 μ) :=
  quasiInvariantLpUnitaryRepresentation (E := Y) affineDataJacobian
    affineData_measurable (affineData_group_map_eq_withDensity μ)
    affineDataJacobian_measurable affineDataJacobian_ne_zero
    affineDataJacobian_one affineDataJacobian_cocycle

/-- The corrected affine action on vector-valued `L²` has the expected weighted-pullback
representative.  The scalar specialization used by the Mackey analysis is recorded separately in
`HA.AffineIrreducibility`; this version is the Bochner `L²` input needed for Section 5. -/
theorem affineDataLpUnitaryRepresentation_apply_ae_vector (μ : Measure E)
    [μ.IsAddHaarMeasure] [SigmaFinite μ] (g : E ≃ᵃ[ℝ] E) (f : Lp Y 2 μ) :
    (affineDataLpUnitaryRepresentation (Y := Y) μ g).1 f =ᵐ[μ]
      quasiRegularAction (radonNikodymWeight affineDataJacobian) g fun x ↦ f x := by
  exact quasiInvariantLpUnitaryRepresentation_apply_ae (E := Y) affineDataJacobian
    affineData_measurable (affineData_group_map_eq_withDensity μ)
    affineDataJacobian_measurable affineDataJacobian_ne_zero affineDataJacobian_one
    affineDataJacobian_cocycle g f

/-- The Radon--Nikodym-corrected contragredient parameter representation on scalar `L²`. -/
noncomputable def affineParameterLpUnitaryRepresentation (ν : Measure (E × ℝ))
    [ν.IsAddHaarMeasure] [SigmaFinite ν] :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp ℂ 2 ν) :=
  quasiInvariantLpUnitaryRepresentation affineParameterJacobian
    affineParameter_measurable (affineParameter_group_map_eq_withDensity ν)
    affineParameterJacobian_measurable affineParameterJacobian_ne_zero
    affineParameterJacobian_one affineParameterJacobian_cocycle

/-- A vector-valued fully-connected depth-two feature. -/
def affineFeature (σ : ℝ → Y) (x : E) (p : E × ℝ) : Y :=
  σ (affineRidgeArgument x p)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A fully-connected affine feature is jointly invariant; equivalently, it is jointly equivariant
for the trivial output representation. -/
theorem affineFeature_jointInvariant (σ : ℝ → Y) (g : E ≃ᵃ[ℝ] E)
    (x : E) (p : E × ℝ) :
    affineFeature σ (g • x) (g • p) =
      ((1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g : Y →L[ℂ] Y)
        (affineFeature σ x p) := by
  change σ (affineRidgeArgument (g x) (affineParameterLinearEquiv g p)) =
    σ (affineRidgeArgument x p)
  rw [affineRidgeArgument_invariant]

/-- The quasi-invariant Bochner synthesis identity instantiated for the affine fully-connected
feature. -/
theorem affineBochnerSynthesis_intertwines
    (ν : Measure (E × ℝ)) [ν.IsAddHaarMeasure] (σ : ℝ → Y)
    (g : E ≃ᵃ[ℝ] E) (γ : E × ℝ → ℂ) (x : E) :
    bochnerSynthesis ν (affineFeature σ)
        (quasiRegularAction (radonNikodymWeight affineParameterJacobian) g γ) x =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g
        (bochnerSynthesis ν (affineFeature σ) γ) x := by
  exact bochnerSynthesis_quasi_intertwines ν
    (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) (affineFeature σ)
    affineDataJacobian affineParameterJacobian affineParameter_measurable
    (affineParameter_group_map_eq_withDensity ν) affineParameterJacobian_measurable
    affineParameterJacobian_ne_zero (affineFeature_jointInvariant σ)
    affine_synthesis_radonNikodym_balance g γ x

/-- The quasi-invariant Bochner ridgelet identity instantiated for the affine fully-connected
feature. -/
theorem affineBochnerRidgelet_intertwines
    (μ : Measure E) [μ.IsAddHaarMeasure] (ψ : ℝ → Y)
    (g : E ≃ᵃ[ℝ] E) (f : E → Y) (p : E × ℝ) :
    bochnerRidgelet μ (affineFeature ψ)
        (quasiUnitaryPullbackAction affineDataJacobian
          (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g f) p =
      quasiRegularAction (radonNikodymWeight affineParameterJacobian) g
        (bochnerRidgelet μ (affineFeature ψ) f) p := by
  exact bochnerRidgelet_quasi_intertwines μ
    (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) (affineFeature ψ)
    affineDataJacobian affineParameterJacobian affineData_measurable
    (affineData_group_map_eq_withDensity μ) affineDataJacobian_measurable
    affineDataJacobian_ne_zero (affineFeature_jointInvariant ψ)
    affine_ridgelet_radonNikodym_balance g f p

end Measure

end LeanRidgelet
