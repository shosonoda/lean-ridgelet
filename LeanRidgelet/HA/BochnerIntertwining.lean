/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.InducedRepresentation
public import LeanRidgelet.HA.Operators
public import LeanRidgelet.ToMathlib.QuasiInvariantIntegral

/-!
# Bochner integrals and intertwining operators

This file proves the analytic change-of-variables step behind Lemmas 3.7 and 3.9 of
arXiv:2405.13682. The statements are pointwise. They cover both invariant measures and strongly
quasi-invariant measures whose data- and parameter-side square-root Radon--Nikodym weights
balance. Boundedness and passage to `L²` equivalence classes remain separate from these integral
identities.

## Main results

* `bochnerSynthesis_intertwines` and `bochnerRidgelet_intertwines`: the invariant-measure
  identities.
* `bochnerSynthesis_quasi_intertwines` and `bochnerRidgelet_quasi_intertwines`: the
  quasi-invariant identities under an exact square-root balance of the two densities.
* `bochnerSynthesis_quasi_intertwines_of_character` and
  `bochnerRidgelet_quasi_intertwines_of_character`: the same two identities when the densities
  balance only up to a group-dependent scalar `chi g`, which then survives as a factor on the
  right-hand side of each identity.
* `bochnerReconstruction_quasi_intertwines_of_character`: the composite of the twisted ridgelet
  with the twisted synthesis, which carries the factor `chi g * chi g`.
* `bochnerReconstruction_commutes_of_character`: that composite commutes with the data action as
  soon as the factor `chi g * chi g` is trivial.
* `character_eq_one_of_balance_of_mul_self_eq_one`: the twisted balance forces `chi g` to be a
  nonnegative real, so `chi g * chi g = 1` happens only in the exactly balanced case.

## Character-twisted balance

The affine ridge feature balances the two densities exactly: its parameter action has determinant
`(det L)⁻¹` against the data determinant `det L`, so `LeanRidgelet.HA.Affine` meets the balance
hypothesis on the nose. The quadratic feature of Section 7 does not: by
`LeanRidgelet.det_quadraticParameterLinearEquiv` the parameter determinant carries an extra
congruence factor, so the two densities differ by a positive character of the group. The twisted
statements below are what such a feature satisfies: synthesis and ridgelet each intertwine the two
quasi-invariant actions only up to the scalar `chi g`.

The two twists do *not* cancel in the composite of ridgelet with synthesis. Both steps contribute
the *same* factor `chi g` — the balance hypotheses of the two twisted identities are equivalent to
each other and both say `(parameterJacobian g ξ).sqrt * (dataJacobian g x).sqrt = chi g` — so the
composite carries `chi g * chi g`, which is the content of
`bochnerReconstruction_quasi_intertwines_of_character`. Commutation with the data action therefore
needs `chi g * chi g = 1`, and `character_eq_one_of_balance_of_mul_self_eq_one` shows that this
forces `chi g = 1`, i.e. exact balance. Removing a genuine twist requires changing the parameter
measure to a relatively invariant one (or reweighting the feature), not composing the two maps.

## Deviations from the article

The article states its general Bochner intertwining lemmas using invariant data and parameter
measures, while its affine examples require quasi-invariant Lebesgue measures. The corrected
variants below expose the two pushforward densities and their square-root balance explicitly.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {G X Ξ Y : Type*} [Group G] [MulAction G X] [MulAction G Ξ]
  [MeasurableSpace X] [MeasurableSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The scalar pullback action on representatives. -/
def scalarPullbackAction (g : G) (γ : Ξ → ℂ) : Ξ → ℂ :=
  fun ξ ↦ γ (g⁻¹ • ξ)

/-- Pullback on `Y`-valued representatives, combined with an output unitary action. -/
def unitaryPullbackAction (υ : UnitaryRepresentation G Y) (g : G) (f : X → Y) : X → Y :=
  fun x ↦ (υ g : Y →L[ℂ] Y) (f (g⁻¹ • x))

/-- Pullback on `Y`-valued representatives with both an output unitary and the square-root
Radon--Nikodym multiplier associated with `jacobian`. -/
noncomputable def quasiUnitaryPullbackAction (jacobian : G → X → ℝ≥0)
    (υ : UnitaryRepresentation G Y) (g : G) (f : X → Y) : X → Y :=
  fun x ↦ radonNikodymWeight jacobian g x • (υ g : Y →L[ℂ] Y) (f (g⁻¹ • x))

/-- Pointwise Bochner synthesis of a coefficient function against a feature map. -/
def bochnerSynthesis (μ : Measure Ξ) (φ : X → Ξ → Y) (γ : Ξ → ℂ) : X → Y :=
  fun x ↦ ∫ ξ, γ ξ • φ x ξ ∂μ

/-- Pointwise ridgelet pairing. Mathlib's inner product is linear in the second argument, so this
formula is linear in `f`. -/
def bochnerRidgelet (μ : Measure X) (ψ : X → Ξ → Y) (f : X → Y) : Ξ → ℂ :=
  fun ξ ↦ ∫ x, ⟪ψ x ξ, f x⟫_ℂ ∂μ

omit [MeasurableSpace X] in
/-- Joint equivariance plus an invariant parameter measure makes the Bochner synthesis integral
intertwine the scalar pullback and the unitary data action. -/
theorem bochnerSynthesis_intertwines (μ : Measure Ξ) (υ : UnitaryRepresentation G Y)
    (φ : X → Ξ → Y)
    (h_joint : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_preserving : ∀ g : G, MeasurePreserving (fun ξ : Ξ ↦ g • ξ) μ μ)
    (h_embedding : ∀ g : G, MeasurableEmbedding fun ξ : Ξ ↦ g • ξ)
    (g : G) (γ : Ξ → ℂ) (x : X) :
    bochnerSynthesis μ φ (scalarPullbackAction g γ) x =
      unitaryPullbackAction υ g (bochnerSynthesis μ φ γ) x := by
  rw [bochnerSynthesis, ← (h_preserving g).integral_comp (h_embedding g)]
  simp only [scalarPullbackAction, inv_smul_smul]
  have hφ : ∀ ξ, φ x (g • ξ) =
      (υ g : Y →L[ℂ] Y) (φ (g⁻¹ • x) ξ) := by
    intro ξ
    simpa only [smul_inv_smul] using h_joint g (g⁻¹ • x) ξ
  simp_rw [hφ, ← (υ g : Y →L[ℂ] Y).map_smul]
  let U : Y ≃ₗᵢ[ℂ] Y := Unitary.linearIsometryEquiv (υ g)
  have hU (y : Y) : U.toLinearIsometry y = (υ g : Y →L[ℂ] Y) y := rfl
  simpa only [unitaryPullbackAction, bochnerSynthesis, hU] using
      (U.toLinearIsometry.integral_comp_comm
        (fun ξ ↦ γ ξ • φ (g⁻¹ • x) ξ))

omit [MeasurableSpace Ξ] in
/-- Joint equivariance plus an invariant data measure makes the Bochner ridgelet pairing
intertwine the unitary data action and scalar pullback on parameters. -/
theorem bochnerRidgelet_intertwines (μ : Measure X) (υ : UnitaryRepresentation G Y)
    (ψ : X → Ξ → Y)
    (h_joint : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_preserving : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (h_embedding : ∀ g : G, MeasurableEmbedding fun x : X ↦ g • x)
    (g : G) (f : X → Y) (ξ : Ξ) :
    bochnerRidgelet μ ψ (unitaryPullbackAction υ g f) ξ =
      scalarPullbackAction g (bochnerRidgelet μ ψ f) ξ := by
  rw [bochnerRidgelet, ← (h_preserving g).integral_comp (h_embedding g)]
  simp only [unitaryPullbackAction, inv_smul_smul]
  have hψ : ∀ x, ψ (g • x) ξ =
      (υ g : Y →L[ℂ] Y) (ψ x (g⁻¹ • ξ)) := by
    intro x
    simpa only [smul_inv_smul] using h_joint g x (g⁻¹ • ξ)
  simp_rw [hψ, Unitary.inner_map_map]
  rfl

omit [MeasurableSpace X] in
/-- Character-twisted form of `bochnerSynthesis_quasi_intertwines`. If the parameter Jacobian's
square root is the data-side Radon--Nikodym multiplier scaled by a group-dependent factor `chi g`,
then the Bochner synthesis integral intertwines the two quasi-invariant actions up to that same
factor. The scalar `chi` is valued in `ℂ` rather than in `ℝ≥0`: the balance equation, the
scalar multiplication on `Y` and the conclusion all already live in `ℂ`, so no coercion is
introduced, and `character_eq_one_of_balance_of_mul_self_eq_one` shows the hypothesis forces
`chi g` to be a nonnegative real anyway. -/
theorem bochnerSynthesis_quasi_intertwines_of_character
    (μ : Measure Ξ) (υ : UnitaryRepresentation G Y) (φ : X → Ξ → Y) (chi : G → ℂ)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μ.map (fun ξ ↦ g⁻¹ • ξ) =
        μ.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_joint : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = chi g * radonNikodymWeight dataJacobian g x)
    (g : G) (γ : Ξ → ℂ) (x : X) :
    bochnerSynthesis μ φ
        (quasiRegularAction (radonNikodymWeight parameterJacobian) g γ) x =
      chi g • quasiUnitaryPullbackAction dataJacobian υ g (bochnerSynthesis μ φ γ) x := by
  rw [bochnerSynthesis,
    MeasureTheory.integral_eq_integral_smul_comp_smul_of_map_eq_withDensity
      μ parameterJacobian h_parameter_measurable h_parameter_map h_parameter_jacobian g]
  simp only [quasiRegularAction, inv_smul_smul]
  have hφ : ∀ ξ, φ x (g • ξ) =
      (υ g : Y →L[ℂ] Y) (φ (g⁻¹ • x) ξ) := by
    intro ξ
    simpa only [smul_inv_smul] using h_joint g (g⁻¹ • x) ξ
  simp_rw [hφ]
  have hcancel (ξ : Ξ) (y : Y) :
      parameterJacobian g ξ •
          (((parameterJacobian g ξ).sqrt : ℂ)⁻¹ • y) =
        (parameterJacobian g ξ).sqrt • y := by
    exact NNReal.smul_inv_sqrt_smul _ (h_parameter_ne_zero g ξ) y
  have hcancel_mul (ξ : Ξ) (c : ℂ) (y : Y) :
      parameterJacobian g ξ •
          ((((parameterJacobian g ξ).sqrt : ℂ)⁻¹ • c) • y) =
        ((parameterJacobian g ξ).sqrt : ℂ) • (c • y) := by
    change parameterJacobian g ξ •
        ((((parameterJacobian g ξ).sqrt : ℂ)⁻¹ * c) • y) =
      ((parameterJacobian g ξ).sqrt : ℂ) • (c • y)
    rw [mul_smul]
    exact hcancel ξ (c • y)
  simp_rw [radonNikodymWeight_apply]
  simp only [inv_smul_smul]
  simp_rw [hcancel_mul]
  simp_rw [h_balance g x]
  have hmap (ξ : Ξ) :
      γ ξ • (υ g : Y →L[ℂ] Y) (φ (g⁻¹ • x) ξ) =
        (υ g : Y →L[ℂ] Y) (γ ξ • φ (g⁻¹ • x) ξ) := by
    exact ((υ g : Y →L[ℂ] Y).map_smul (γ ξ) (φ (g⁻¹ • x) ξ)).symm
  simp_rw [hmap, integral_smul]
  let U : Y ≃ₗᵢ[ℂ] Y := Unitary.linearIsometryEquiv (υ g)
  have hU (y : Y) : U.toLinearIsometry y = (υ g : Y →L[ℂ] Y) y := rfl
  rw [quasiUnitaryPullbackAction]
  simpa only [hU, bochnerSynthesis, mul_smul] using
    congrArg (fun y ↦ (chi g * radonNikodymWeight dataJacobian g x) • y)
      (U.toLinearIsometry.integral_comp_comm
        (fun ξ ↦ γ ξ • φ (g⁻¹ • x) ξ))

omit [MeasurableSpace X] in
/-- Joint equivariance intertwines quasi-invariant Bochner synthesis actions when the parameter
Jacobian's square root equals the data-side Radon--Nikodym multiplier. This is the explicit
Jacobian cancellation missing from the invariant-measure statement. -/
theorem bochnerSynthesis_quasi_intertwines
    (μ : Measure Ξ) (υ : UnitaryRepresentation G Y) (φ : X → Ξ → Y)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μ.map (fun ξ ↦ g⁻¹ • ξ) =
        μ.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_joint : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = radonNikodymWeight dataJacobian g x)
    (g : G) (γ : Ξ → ℂ) (x : X) :
    bochnerSynthesis μ φ
        (quasiRegularAction (radonNikodymWeight parameterJacobian) g γ) x =
      quasiUnitaryPullbackAction dataJacobian υ g (bochnerSynthesis μ φ γ) x := by
  simpa using
    bochnerSynthesis_quasi_intertwines_of_character μ υ φ (fun _ ↦ 1) dataJacobian
      parameterJacobian h_parameter_measurable h_parameter_map h_parameter_jacobian
      h_parameter_ne_zero h_joint (fun g x ξ ↦ by rw [one_mul]; exact h_balance g x ξ) g γ x

omit [MeasurableSpace Ξ] in
/-- Character-twisted form of `bochnerRidgelet_quasi_intertwines`. The twist enters the balance
hypothesis on the same side as in `bochnerSynthesis_quasi_intertwines_of_character`, because both
hypotheses say the same thing: the product
`(parameterJacobian g ξ).sqrt * (dataJacobian g x).sqrt` equals `chi g`. Consequently the factor
`chi g` again appears on the right-hand side, and not its inverse. -/
theorem bochnerRidgelet_quasi_intertwines_of_character
    (μ : Measure X) (υ : UnitaryRepresentation G Y) (ψ : X → Ξ → Y) (chi : G → ℂ)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) =
        μ.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = chi g * radonNikodymWeight parameterJacobian g ξ)
    (g : G) (f : X → Y) (ξ : Ξ) :
    bochnerRidgelet μ ψ (quasiUnitaryPullbackAction dataJacobian υ g f) ξ =
      chi g * quasiRegularAction (radonNikodymWeight parameterJacobian) g
        (bochnerRidgelet μ ψ f) ξ := by
  rw [bochnerRidgelet,
    MeasureTheory.integral_eq_integral_smul_comp_smul_of_map_eq_withDensity
      μ dataJacobian h_data_measurable h_data_map h_data_jacobian g]
  simp only [quasiUnitaryPullbackAction, inv_smul_smul]
  have hψ : ∀ x, ψ (g • x) ξ =
      (υ g : Y →L[ℂ] Y) (ψ x (g⁻¹ • ξ)) := by
    intro x
    simpa only [smul_inv_smul] using h_joint g x (g⁻¹ • ξ)
  simp_rw [hψ, inner_smul_right, Unitary.inner_map_map]
  have hcancel (x : X) (c : ℂ) :
      dataJacobian g x •
          (radonNikodymWeight dataJacobian g (g • x) * c) =
        ((dataJacobian g x).sqrt : ℂ) * c := by
    rw [radonNikodymWeight_apply]
    simp only [inv_smul_smul]
    simpa only [smul_eq_mul] using
      (NNReal.smul_inv_sqrt_smul
        (dataJacobian g x) (h_data_ne_zero g x) c)
  simp_rw [hcancel]
  have hpull : chi g *
      quasiRegularAction (radonNikodymWeight parameterJacobian) g
        (bochnerRidgelet μ ψ f) ξ =
      ∫ x, (chi g * radonNikodymWeight parameterJacobian g ξ) *
        ⟪ψ x (g⁻¹ • ξ), f x⟫_ℂ ∂μ := by
    simp only [quasiRegularAction, bochnerRidgelet, smul_eq_mul]
    rw [integral_const_mul, mul_assoc]
  rw [hpull]
  apply integral_congr_ae
  filter_upwards with x
  exact congrArg (fun z : ℂ ↦ z * ⟪ψ x (g⁻¹ • ξ), f x⟫_ℂ) (h_balance g x ξ)

omit [MeasurableSpace Ξ] in
/-- Joint equivariance intertwines a quasi-invariant Bochner ridgelet pairing when the data
Jacobian's square root equals the parameter-side Radon--Nikodym multiplier. -/
theorem bochnerRidgelet_quasi_intertwines
    (μ : Measure X) (υ : UnitaryRepresentation G Y) (ψ : X → Ξ → Y)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) =
        μ.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = radonNikodymWeight parameterJacobian g ξ)
    (g : G) (f : X → Y) (ξ : Ξ) :
    bochnerRidgelet μ ψ (quasiUnitaryPullbackAction dataJacobian υ g f) ξ =
      quasiRegularAction (radonNikodymWeight parameterJacobian) g
        (bochnerRidgelet μ ψ f) ξ := by
  simpa using
    bochnerRidgelet_quasi_intertwines_of_character μ υ ψ (fun _ ↦ 1) dataJacobian
      parameterJacobian h_data_measurable h_data_map h_data_jacobian h_data_ne_zero h_joint
      (fun g x ξ ↦ by rw [one_mul]; exact h_balance g x ξ) g f ξ

/-- The composite of the character-twisted ridgelet with the character-twisted synthesis, under
the hypotheses of `bochnerRidgelet_quasi_intertwines_of_character` and
`bochnerSynthesis_quasi_intertwines_of_character` for one common `chi`. Both steps contribute the
factor `chi g`, so the twists compound instead of cancelling and the composite carries
`chi g * chi g`. -/
theorem bochnerReconstruction_quasi_intertwines_of_character
    (μParameter : Measure Ξ) (μData : Measure X) (υ : UnitaryRepresentation G Y)
    (φ ψ : X → Ξ → Y) (chi : G → ℂ)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μParameter.map (fun ξ ↦ g⁻¹ • ξ) =
        μParameter.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μData.map (fun x ↦ g⁻¹ • x) =
        μData.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint_φ : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_joint_ψ : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_synthesis_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = chi g * radonNikodymWeight dataJacobian g x)
    (h_ridgelet_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = chi g * radonNikodymWeight parameterJacobian g ξ)
    (g : G) (f : X → Y) (x : X) :
    bochnerSynthesis μParameter φ
        (bochnerRidgelet μData ψ (quasiUnitaryPullbackAction dataJacobian υ g f)) x =
      (chi g * chi g) •
        quasiUnitaryPullbackAction dataJacobian υ g
          (bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ f)) x := by
  have h_ridgelet :
      bochnerRidgelet μData ψ (quasiUnitaryPullbackAction dataJacobian υ g f) =
        fun ξ ↦ chi g *
          quasiRegularAction (radonNikodymWeight parameterJacobian) g
            (bochnerRidgelet μData ψ f) ξ :=
    funext fun ξ ↦
      bochnerRidgelet_quasi_intertwines_of_character μData υ ψ chi dataJacobian
        parameterJacobian h_data_measurable h_data_map h_data_jacobian h_data_ne_zero
        h_joint_ψ h_ridgelet_balance g f ξ
  have h_scalar : ∀ (c : ℂ) (γ : Ξ → ℂ),
      bochnerSynthesis μParameter φ (fun ξ ↦ c * γ ξ) x =
        c • bochnerSynthesis μParameter φ γ x := by
    intro c γ
    simp only [bochnerSynthesis, mul_smul]
    exact integral_smul c _
  calc
    bochnerSynthesis μParameter φ
          (bochnerRidgelet μData ψ (quasiUnitaryPullbackAction dataJacobian υ g f)) x
        = bochnerSynthesis μParameter φ
            (fun ξ ↦ chi g *
              quasiRegularAction (radonNikodymWeight parameterJacobian) g
                (bochnerRidgelet μData ψ f) ξ) x := by
      rw [h_ridgelet]
    _ = chi g •
          bochnerSynthesis μParameter φ
            (quasiRegularAction (radonNikodymWeight parameterJacobian) g
              (bochnerRidgelet μData ψ f)) x := h_scalar _ _
    _ = chi g •
          (chi g •
            quasiUnitaryPullbackAction dataJacobian υ g
              (bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ f)) x) := by
      rw [bochnerSynthesis_quasi_intertwines_of_character μParameter υ φ chi dataJacobian
        parameterJacobian h_parameter_measurable h_parameter_map h_parameter_jacobian
        h_parameter_ne_zero h_joint_φ h_synthesis_balance g _ x]
    _ = (chi g * chi g) •
          quasiUnitaryPullbackAction dataJacobian υ g
            (bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ f)) x := by
      rw [smul_smul]

/-- The composite of the twisted ridgelet with the twisted synthesis commutes with the data
action once the compounded twist `chi g * chi g` is trivial. This is the identity the
Schur/commutant argument consumes. The hypothesis `h_chi` is not automatic: by
`character_eq_one_of_balance_of_mul_self_eq_one` it already forces `chi g = 1`, so a genuinely
twisted feature does not become untwisted by composing synthesis with ridgelet. -/
theorem bochnerReconstruction_commutes_of_character
    (μParameter : Measure Ξ) (μData : Measure X) (υ : UnitaryRepresentation G Y)
    (φ ψ : X → Ξ → Y) (chi : G → ℂ)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μParameter.map (fun ξ ↦ g⁻¹ • ξ) =
        μParameter.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μData.map (fun x ↦ g⁻¹ • x) =
        μData.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint_φ : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_joint_ψ : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_synthesis_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = chi g * radonNikodymWeight dataJacobian g x)
    (h_ridgelet_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = chi g * radonNikodymWeight parameterJacobian g ξ)
    (g : G) (h_chi : chi g * chi g = 1) (f : X → Y) (x : X) :
    bochnerSynthesis μParameter φ
        (bochnerRidgelet μData ψ (quasiUnitaryPullbackAction dataJacobian υ g f)) x =
      quasiUnitaryPullbackAction dataJacobian υ g
        (bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ f)) x := by
  rw [bochnerReconstruction_quasi_intertwines_of_character μParameter μData υ φ ψ chi
    dataJacobian parameterJacobian h_parameter_measurable h_parameter_map h_parameter_jacobian
    h_parameter_ne_zero h_data_measurable h_data_map h_data_jacobian h_data_ne_zero h_joint_φ
    h_joint_ψ h_synthesis_balance h_ridgelet_balance g f x, h_chi, one_smul]

omit [MulAction G Ξ] [MeasurableSpace X] [MeasurableSpace Ξ] in
/-- The twisted balance pins `chi g` down: it is the nonnegative real number
`(parameterJacobian g ξ).sqrt * (dataJacobian g (g⁻¹ • x)).sqrt`. Hence the cancellation
hypothesis `chi g * chi g = 1` of `bochnerReconstruction_commutes_of_character` holds only for
the untwisted value `chi g = 1`, which is the obstruction to removing a genuine density mismatch
by composing synthesis with ridgelet. -/
theorem character_eq_one_of_balance_of_mul_self_eq_one (chi : G → ℂ)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = chi g * radonNikodymWeight dataJacobian g x)
    (g : G) (x : X) (ξ : Ξ) (h_chi : chi g * chi g = 1) : chi g = 1 := by
  have h_sqrt_ne : (dataJacobian g (g⁻¹ • x)).sqrt ≠ 0 := by
    simpa using h_data_ne_zero g (g⁻¹ • x)
  have h_cast_ne : (((dataJacobian g (g⁻¹ • x)).sqrt : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast h_sqrt_ne
  have h := h_balance g x ξ
  rw [radonNikodymWeight_apply] at h
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, chi g = (t : ℂ) := by
    refine ⟨(parameterJacobian g ξ).sqrt * (dataJacobian g (g⁻¹ • x)).sqrt, ?_⟩
    rw [NNReal.coe_mul, Complex.ofReal_mul, h, mul_assoc, inv_mul_cancel₀ h_cast_ne, mul_one]
  have h_nnreal : t * t = 1 := by
    have h_complex : ((t : ℝ≥0) : ℂ) * ((t : ℝ≥0) : ℂ) = 1 := by
      rw [← ht]
      exact h_chi
    exact_mod_cast h_complex
  have h_one : t = 1 := by
    have h_sqrt := congrArg NNReal.sqrt h_nnreal
    simpa only [NNReal.sqrt_mul_self, NNReal.sqrt_one] using h_sqrt
  rw [ht, h_one]
  norm_num

section OperatorBridge

open scoped ContRepresentation

variable {K H : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Bundle a bounded Bochner synthesis map as a continuous intertwiner once its coordinate
formula and the coordinate formulas for the two representations are known. This is the formal
bridge from the integral identity above to the operator-level `JointEquivariantMachine` API. -/
def bochnerSynthesisIntertwiningMap (μ : Measure Ξ) (υ : UnitaryRepresentation G Y)
    (πParameter : ContRepresentation ℂ G K) (πData : ContRepresentation ℂ G H)
    (coefficient : K → Ξ → ℂ) (value : H → X → Y) (h_value : Function.Injective value)
    (M : K →L[ℂ] H) (φ : X → Ξ → Y)
    (hM : ∀ k, value (M k) = bochnerSynthesis μ φ (coefficient k))
    (h_parameter : ∀ g k,
      coefficient (πParameter g k) = scalarPullbackAction g (coefficient k))
    (h_data : ∀ g f, value (πData g f) = unitaryPullbackAction υ g (value f))
    (h_joint : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_preserving : ∀ g : G, MeasurePreserving (fun ξ : Ξ ↦ g • ξ) μ μ)
    (h_embedding : ∀ g : G, MeasurableEmbedding fun ξ : Ξ ↦ g • ξ) :
    JointEquivariantMachine πParameter πData where
  __ := M
  isIntertwining' g := by
    ext k
    apply h_value
    calc
      value (M (πParameter g k)) =
          bochnerSynthesis μ φ (coefficient (πParameter g k)) := hM _
      _ = bochnerSynthesis μ φ (scalarPullbackAction g (coefficient k)) := by
        rw [h_parameter]
      _ = unitaryPullbackAction υ g (bochnerSynthesis μ φ (coefficient k)) :=
        funext fun x ↦ bochnerSynthesis_intertwines μ υ φ h_joint h_preserving h_embedding g _ x
      _ = unitaryPullbackAction υ g (value (M k)) := by rw [hM]
      _ = value (πData g (M k)) := (h_data _ _).symm

/-- Bundle a bounded Bochner ridgelet map as a continuous intertwiner once its coordinate
formula and the coordinate formulas for the two representations are known. -/
def bochnerRidgeletIntertwiningMap (μ : Measure X) (υ : UnitaryRepresentation G Y)
    (πData : ContRepresentation ℂ G H) (πParameter : ContRepresentation ℂ G K)
    (value : H → X → Y) (coefficient : K → Ξ → ℂ)
    (h_coefficient : Function.Injective coefficient) (R : H →L[ℂ] K) (ψ : X → Ξ → Y)
    (hR : ∀ f, coefficient (R f) = bochnerRidgelet μ ψ (value f))
    (h_data : ∀ g f, value (πData g f) = unitaryPullbackAction υ g (value f))
    (h_parameter : ∀ g k,
      coefficient (πParameter g k) = scalarPullbackAction g (coefficient k))
    (h_joint : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_preserving : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (h_embedding : ∀ g : G, MeasurableEmbedding fun x : X ↦ g • x) :
    JointEquivariantRidgelet πData πParameter where
  __ := R
  isIntertwining' g := by
    ext f
    apply h_coefficient
    calc
      coefficient (R (πData g f)) = bochnerRidgelet μ ψ (value (πData g f)) := hR _
      _ = bochnerRidgelet μ ψ (unitaryPullbackAction υ g (value f)) := by rw [h_data]
      _ = scalarPullbackAction g (bochnerRidgelet μ ψ (value f)) :=
        funext fun ξ ↦ bochnerRidgelet_intertwines μ υ ψ h_joint h_preserving h_embedding g _ ξ
      _ = scalarPullbackAction g (coefficient (R f)) := by rw [hR]
      _ = coefficient (πParameter g (R f)) := (h_parameter _ _).symm

/-- Bundle a bounded quasi-invariant Bochner synthesis map as a continuous intertwiner. The
coordinate actions carry the same Radon--Nikodym weights as
`bochnerSynthesis_quasi_intertwines`. -/
noncomputable def bochnerSynthesisQuasiIntertwiningMap
    (μ : Measure Ξ) (υ : UnitaryRepresentation G Y)
    (πParameter : ContRepresentation ℂ G K) (πData : ContRepresentation ℂ G H)
    (coefficient : K → Ξ → ℂ) (value : H → X → Y) (h_value : Function.Injective value)
    (M : K →L[ℂ] H) (φ : X → Ξ → Y)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (hM : ∀ k, value (M k) = bochnerSynthesis μ φ (coefficient k))
    (h_parameter : ∀ g k,
      coefficient (πParameter g k) =
        quasiRegularAction (radonNikodymWeight parameterJacobian) g (coefficient k))
    (h_data : ∀ g f,
      value (πData g f) = quasiUnitaryPullbackAction dataJacobian υ g (value f))
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μ.map (fun ξ ↦ g⁻¹ • ξ) =
        μ.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_joint : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = radonNikodymWeight dataJacobian g x) :
    JointEquivariantMachine πParameter πData where
  __ := M
  isIntertwining' g := by
    ext k
    apply h_value
    calc
      value (M (πParameter g k)) =
          bochnerSynthesis μ φ (coefficient (πParameter g k)) := hM _
      _ = bochnerSynthesis μ φ
          (quasiRegularAction (radonNikodymWeight parameterJacobian) g (coefficient k)) := by
        rw [h_parameter]
      _ = quasiUnitaryPullbackAction dataJacobian υ g
          (bochnerSynthesis μ φ (coefficient k)) :=
        funext fun x ↦ bochnerSynthesis_quasi_intertwines μ υ φ dataJacobian
          parameterJacobian h_parameter_measurable h_parameter_map h_parameter_jacobian
          h_parameter_ne_zero h_joint h_balance g _ x
      _ = quasiUnitaryPullbackAction dataJacobian υ g (value (M k)) := by rw [hM]
      _ = value (πData g (M k)) := (h_data _ _).symm

/-- Bundle a bounded quasi-invariant Bochner ridgelet map as a continuous intertwiner. -/
noncomputable def bochnerRidgeletQuasiIntertwiningMap
    (μ : Measure X) (υ : UnitaryRepresentation G Y)
    (πData : ContRepresentation ℂ G H) (πParameter : ContRepresentation ℂ G K)
    (value : H → X → Y) (coefficient : K → Ξ → ℂ)
    (h_coefficient : Function.Injective coefficient) (R : H →L[ℂ] K) (ψ : X → Ξ → Y)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (hR : ∀ f, coefficient (R f) = bochnerRidgelet μ ψ (value f))
    (h_data : ∀ g f,
      value (πData g f) = quasiUnitaryPullbackAction dataJacobian υ g (value f))
    (h_parameter : ∀ g k,
      coefficient (πParameter g k) =
        quasiRegularAction (radonNikodymWeight parameterJacobian) g (coefficient k))
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) =
        μ.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = radonNikodymWeight parameterJacobian g ξ) :
    JointEquivariantRidgelet πData πParameter where
  __ := R
  isIntertwining' g := by
    ext f
    apply h_coefficient
    calc
      coefficient (R (πData g f)) = bochnerRidgelet μ ψ (value (πData g f)) := hR _
      _ = bochnerRidgelet μ ψ (quasiUnitaryPullbackAction dataJacobian υ g (value f)) := by
        rw [h_data]
      _ = quasiRegularAction (radonNikodymWeight parameterJacobian) g
          (bochnerRidgelet μ ψ (value f)) :=
        funext fun ξ ↦ bochnerRidgelet_quasi_intertwines μ υ ψ dataJacobian
          parameterJacobian h_data_measurable h_data_map h_data_jacobian h_data_ne_zero
          h_joint h_balance g _ ξ
      _ = quasiRegularAction (radonNikodymWeight parameterJacobian) g
          (coefficient (R f)) := by rw [hR]
      _ = coefficient (πParameter g (R f)) := (h_parameter _ _).symm

/-- Bundle a bounded extension of the *composite* pointwise Bochner synthesis/ridgelet formula as
an endomorphism intertwiner. Unlike `bochnerSynthesisQuasiIntertwiningMap` followed by
`bochnerRidgeletQuasiIntertwiningMap`, this construction assumes only that the composite `T` is
bounded. The two intermediate integrals remain pointwise functions and need not separately define
bounded maps between `L²` spaces. This is the weak boundedness interpretation used in Theorem 3.10
of the article. -/
noncomputable def bochnerReconstructionQuasiIntertwiningMap
    (μParameter : Measure Ξ) (μData : Measure X) (υ : UnitaryRepresentation G Y)
    (πData : ContRepresentation ℂ G H) (value : H → X → Y)
    (h_value : Function.Injective value) (T : H →L[ℂ] H) (φ ψ : X → Ξ → Y)
    (dataJacobian : G → X → ℝ≥0) (parameterJacobian : G → Ξ → ℝ≥0)
    (hT : ∀ f, value (T f) =
      bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ (value f)))
    (h_data : ∀ g f,
      value (πData g f) = quasiUnitaryPullbackAction dataJacobian υ g (value f))
    (h_parameter_measurable : ∀ g : G, Measurable fun ξ : Ξ ↦ g • ξ)
    (h_parameter_map : ∀ g : G,
      μParameter.map (fun ξ ↦ g⁻¹ • ξ) =
        μParameter.withDensity (fun ξ ↦ (parameterJacobian g ξ : ℝ≥0∞)))
    (h_parameter_jacobian : ∀ g : G, Measurable (parameterJacobian g))
    (h_parameter_ne_zero : ∀ g ξ, parameterJacobian g ξ ≠ 0)
    (h_data_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_data_map : ∀ g : G,
      μData.map (fun x ↦ g⁻¹ • x) =
        μData.withDensity (fun x ↦ (dataJacobian g x : ℝ≥0∞)))
    (h_data_jacobian : ∀ g : G, Measurable (dataJacobian g))
    (h_data_ne_zero : ∀ g x, dataJacobian g x ≠ 0)
    (h_joint_φ : ∀ g x ξ,
      φ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (φ x ξ))
    (h_joint_ψ : ∀ g x ξ,
      ψ (g • x) (g • ξ) = (υ g : Y →L[ℂ] Y) (ψ x ξ))
    (h_synthesis_balance : ∀ g x ξ,
      ((parameterJacobian g ξ).sqrt : ℂ) = radonNikodymWeight dataJacobian g x)
    (h_ridgelet_balance : ∀ g x ξ,
      ((dataJacobian g x).sqrt : ℂ) = radonNikodymWeight parameterJacobian g ξ) :
    JointEquivariantMachine πData πData where
  __ := T
  isIntertwining' g := by
    ext f
    apply h_value
    calc
      value (T (πData g f)) =
          bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ (value (πData g f))) := hT _
      _ = bochnerSynthesis μParameter φ
          (bochnerRidgelet μData ψ
            (quasiUnitaryPullbackAction dataJacobian υ g (value f))) := by
        rw [h_data]
      _ = bochnerSynthesis μParameter φ
          (quasiRegularAction (radonNikodymWeight parameterJacobian) g
            (bochnerRidgelet μData ψ (value f))) := by
        congr 1
        exact funext fun ξ ↦ bochnerRidgelet_quasi_intertwines μData υ ψ
          dataJacobian parameterJacobian h_data_measurable h_data_map h_data_jacobian
          h_data_ne_zero h_joint_ψ h_ridgelet_balance g _ ξ
      _ = quasiUnitaryPullbackAction dataJacobian υ g
          (bochnerSynthesis μParameter φ (bochnerRidgelet μData ψ (value f))) :=
        funext fun x ↦ bochnerSynthesis_quasi_intertwines μParameter υ φ
          dataJacobian parameterJacobian h_parameter_measurable h_parameter_map
          h_parameter_jacobian h_parameter_ne_zero h_joint_φ h_synthesis_balance g _ x
      _ = quasiUnitaryPullbackAction dataJacobian υ g (value (T f)) := by rw [hT]
      _ = value (πData g (T f)) := (h_data _ _).symm

end OperatorBridge

end LeanRidgelet
