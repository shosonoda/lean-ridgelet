/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.ClassicalComparison
public import LeanRidgelet.Operator.ClassicalRidgelet

/-!
# Affine equivariance of the classical depth-two operators

`LeanRidgelet.HA.Affine` proves the affine intertwining identities for the abstract Bochner
formulas, and `LeanRidgelet.HA.ClassicalComparison` identifies those formulas with the classical
operators at homogeneity index `0`. This file composes the two. The bounded `L²` synthesis
operator `LeanRidgelet.networkSynthesis`, on the Schwartz compatibility domain, and the classical
ridgelet transform, everywhere, are equivariant for the Radon--Nikodym-corrected affine actions of
`LeanRidgelet.HA.Affine`: `LeanRidgelet.quasiRegularAction` with weight
`LeanRidgelet.radonNikodymWeight LeanRidgelet.affineParameterJacobian` on ridge parameters, and
`LeanRidgelet.quasiUnitaryPullbackAction LeanRidgelet.affineDataJacobian 1` on data.

Both halves need Lebesgue measure on the ridge parameters to be an additive Haar measure. Mathlib
supplies that instance for inner-product spaces, while `LeanRidgelet.InputSpace m × ℝ` is a plain
product, so it is produced here from `MeasureTheory.Measure.volume_eq_prod` and introduced locally
rather than declared globally.

## Main results

* `LeanRidgelet.isAddHaarMeasure_volume_ridgeParameter`: Lebesgue measure on `ℝᵐ × ℝ` is an
  additive Haar measure.
* `LeanRidgelet.affineSchwartzParameterAction`: the corrected affine parameter action preserves
  the Schwartz class, with `LeanRidgelet.affineSchwartzParameterAction_coe` identifying its
  representative.
* `LeanRidgelet.networkSynthesis_parameterSchwartzRealization_ae_intertwines`: the synthesis half.
  On the Schwartz compatibility domain the bounded `L²` synthesis operator is almost everywhere
  the corrected affine data pullback of its untransformed value.
* `LeanRidgelet.euclideanRidgeletTransform_intertwines` and
  `LeanRidgelet.classicalRidgeletIntegral_intertwines`: the ridgelet half, pointwise and with no
  hypothesis, for the classical Euclidean ridgelet transform at homogeneity index `0` and for the
  `L²` track's classical ridgelet integral.

## Relation to `LeanRidgelet.HA.L2Bridge`

The four declarations of `LeanRidgelet.HA.L2Bridge` take their equivariance as an unproved
hypothesis: for all `g` and `γ`, the synthesis operator applied to `πParameter g γ` equals
`πData g` applied to the synthesis of `γ`. The results below do *not* discharge it, and no
instantiation is attempted, for three independent reasons.

First, the Hilbert spaces differ. `LeanRidgelet.ParameterSpace m s t` is the transported
coordinate model `L²(ℝᵐ; H_{s,t})`, a Bochner `L²` over the direction variable alone, whereas the
affine parameter action of `LeanRidgelet.HA.Affine` acts on functions of the full ridge parameter
`(a, b) ∈ ℝᵐ × ℝ`. In the transported model the bias variable has been replaced by the fiber
frequency, where a bias translation becomes modulation rather than translation; no unitary
identification of the two models is available in this repository.

Second, the quantifier differs. `LeanRidgelet.HA.L2Bridge` demands the identity for every `L²`
parameter class, while the comparison route runs through
`LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae`, which holds on the
Schwartz compatibility domain and under a pointwise integrability hypothesis.

Third, the data-side representation is constrained by the first two: even the honest choice
`LeanRidgelet.affineDataLpUnitaryRepresentation volume` on `LeanRidgelet.TargetSpace m`, which
does have the required type, is only usable once a parameter-side partner exists.

Passage to `MeasureTheory.Lp` classes is *not* one of the obstructions: equality in
`LeanRidgelet.TargetSpace m` is equality of almost-everywhere equivalence classes, which is what
the synthesis result below proves.

## Deviations from the article

The comparison is inherited from `LeanRidgelet.HA.ClassicalComparison` and therefore lives at
homogeneity index `0`, where the `L¹` weight `‖a‖^{±s}` is `1` and the two parameter measures
agree on the nose.

The synthesis statement is an almost-everywhere identity, and it keeps the three hypotheses
`hσcl`, `hγ`, `hint` of `LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae`
for the transformed coefficient as well as for the original one. Neither restriction is cosmetic:
`LeanRidgelet.bochnerSynthesis` carries no integrability hypothesis, so without `hint` the
underlying identity would be an identity of junk values, and the bounded operator lands in an `Lp`
quotient, so nothing stronger than an almost-everywhere identity is available for it.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

/-- Lebesgue measure on the ridge parameter space `ℝᵐ × ℝ` is an additive Haar measure. Mathlib
provides the instance for inner-product spaces; the ridge parameter space is a plain product, so
the instance is assembled from the product Haar instance and is introduced locally by the results
below rather than globally. -/
theorem isAddHaarMeasure_volume_ridgeParameter (m : ℕ) :
    (volume : Measure (InputSpace m × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The inverse affine data action is quasi measure preserving for Lebesgue measure: its
pushforward has a constant density. -/
theorem quasiMeasurePreserving_affineData_inv {m : ℕ}
    (g : InputSpace m ≃ᵃ[ℝ] InputSpace m) :
    Measure.QuasiMeasurePreserving (fun x : InputSpace m ↦ g⁻¹ • x) volume volume := by
  refine ⟨affineData_measurable g⁻¹, ?_⟩
  rw [affineData_group_map_eq_withDensity volume g]
  exact withDensity_absolutelyContinuous _ _

/-- The corrected affine data pullback respects almost-everywhere equality of representatives.
This is what lets an equality of `L²` classes be transported through the action. -/
theorem quasiUnitaryPullbackAction_affineData_congr_ae {m : ℕ}
    (g : InputSpace m ≃ᵃ[ℝ] InputSpace m) {f₁ f₂ : InputSpace m → ℂ}
    (hf : f₁ =ᵐ[volume] f₂) :
    quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g f₁ =ᵐ[volume]
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g f₂ := by
  filter_upwards [(quasiMeasurePreserving_affineData_inv g).ae_eq_comp hf] with x hx
  simp only [quasiUnitaryPullbackAction]
  rw [show f₁ (g⁻¹ • x) = f₂ (g⁻¹ • x) from hx]

/-- The corrected affine parameter action of `LeanRidgelet.HA.Affine`, realized on the Schwartz
class. Its Radon--Nikodym weight is a constant and its parameter substitution is a linear
automorphism of `ℝᵐ × ℝ`, so the Schwartz class is preserved. -/
def affineSchwartzParameterAction {m : ℕ} (g : InputSpace m ≃ᵃ[ℝ] InputSpace m)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) : SchwartzMap (InputSpace m × ℝ) ℂ :=
  radonNikodymWeight affineParameterJacobian g 0 •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (affineParameterLinearEquiv g).symm.toContinuousLinearEquiv γ

/-- The Schwartz realization of the affine parameter action has the expected representative. In
particular the hypothesis `hγg_eq` of the synthesis theorem below is never an obstruction: the
transformed coefficient function is again Schwartz. -/
theorem affineSchwartzParameterAction_coe {m : ℕ} (g : InputSpace m ≃ᵃ[ℝ] InputSpace m)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) :
    ⇑(affineSchwartzParameterAction g γ) =
      quasiRegularAction (radonNikodymWeight affineParameterJacobian) g (⇑γ) := by
  funext p
  have hweight : radonNikodymWeight affineParameterJacobian g p =
      radonNikodymWeight affineParameterJacobian g 0 := by
    simp [radonNikodymWeight, affineParameterJacobian]
  have hpoint : (g⁻¹ • p : InputSpace m × ℝ) = (affineParameterLinearEquiv g).symm p := by
    rw [← affineParameterLinearEquiv_inv]
    rfl
  rw [quasiRegularAction_apply, hweight, hpoint]
  rfl

/-- **The synthesis half of the affine equivariance, for the bounded `L²` operator.** Let `γg` be
a Schwartz coefficient function representing the corrected affine parameter action on `γ` — for
instance `LeanRidgelet.affineSchwartzParameterAction g γ`. If both lie in the Schwartz
compatibility domain of `LeanRidgelet.networkSynthesis_parameterSchwartzRealization_classical_ae`,
then the bounded synthesis operator sends the transformed coefficient to the corrected affine data
pullback of the untransformed value, almost everywhere.

The proof transports `LeanRidgelet.affineBochnerSynthesis_intertwines` through
`LeanRidgelet.networkSynthesis_ae_eq_bochnerSynthesis_affineFeature`, using the local additive
Haar instance on the ridge parameters. See the module docstring for why this does not discharge
the `hintertwines` hypotheses of `LeanRidgelet.HA.L2Bridge`. -/
theorem networkSynthesis_parameterSchwartzRealization_ae_intertwines
    {m : ℕ} [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) {σcl : ℝ → ℂ}
    (hσcl : ∀ φ : SchwartzMap ℝ ℂ,
      activationRealization s t σ φ = ∫ z : ℝ, φ z * σcl z)
    (g : InputSpace m ≃ᵃ[ℝ] InputSpace m) (γ γg : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγg_eq : ⇑γg = quasiRegularAction (radonNikodymWeight affineParameterJacobian) g (⇑γ))
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume)
    (hγg : MemLp (fourierDilationTransformFiber s t γg) 2 volume)
    (hint : ∀ x : InputSpace m,
      Integrable (fun p : InputSpace m × ℝ ↦ γ p * σcl (inner ℝ p.1 x - p.2)))
    (hintg : ∀ x : InputSpace m,
      Integrable (fun p : InputSpace m × ℝ ↦ γg p * σcl (inner ℝ p.1 x - p.2))) :
    networkSynthesis m s t σ (parameterSchwartzRealization s t γg hγg) =ᵐ[volume]
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g
        (networkSynthesis m s t σ (parameterSchwartzRealization s t γ hγ)) := by
  haveI := isAddHaarMeasure_volume_ridgeParameter m
  have hstep : bochnerSynthesis (Y := ℂ) (volume : Measure (InputSpace m × ℝ))
        (affineFeature (E := InputSpace m) σcl) (⇑γg) =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g
        (bochnerSynthesis (Y := ℂ) (volume : Measure (InputSpace m × ℝ))
          (affineFeature (E := InputSpace m) σcl) (⇑γ)) := by
    funext x
    rw [hγg_eq]
    exact affineBochnerSynthesis_intertwines volume σcl g (⇑γ) x
  refine (networkSynthesis_ae_eq_bochnerSynthesis_affineFeature s t σ hσcl γg hγg hintg).trans ?_
  rw [hstep]
  exact (quasiUnitaryPullbackAction_affineData_congr_ae g
    (networkSynthesis_ae_eq_bochnerSynthesis_affineFeature s t σ hσcl γ hγ hint)).symm

/-- **The ridgelet half of the affine equivariance, in classical Euclidean form.** The classical
Euclidean ridgelet transform at homogeneity index `0` intertwines the corrected affine data
pullback with the corrected affine parameter action, at every parameter point and with no
hypothesis. This is `LeanRidgelet.affineBochnerRidgelet_intertwines` read through
`LeanRidgelet.bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform`; Lebesgue measure on
the data space is an additive Haar measure by Mathlib's inner-product instance. -/
theorem euclideanRidgeletTransform_intertwines {m : ℕ} (ψ : ℝ → ℂ)
    (g : InputSpace m ≃ᵃ[ℝ] InputSpace m) (f : InputSpace m → ℂ)
    (p : RidgeletParameterSpace m) :
    euclideanRidgeletTransform m 0 ψ
        (quasiUnitaryPullbackAction affineDataJacobian
          (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g f) p =
      quasiRegularAction (radonNikodymWeight affineParameterJacobian) g
        (euclideanRidgeletTransform m 0 ψ f) p := by
  rw [← bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform,
    affineBochnerRidgelet_intertwines, quasiRegularAction_apply, quasiRegularAction_apply,
    bochnerRidgelet_affineFeature_eq_euclideanRidgeletTransform]

/-- The `L²` track's classical ridgelet integral is the `L¹` track's Euclidean ridgelet transform
at homogeneity index `0`: the two integrands differ by the weight `‖a‖^0 = 1`. -/
theorem classicalRidgeletIntegral_eq_euclideanRidgeletTransform {m : ℕ}
    (ρ : ℝ → ℂ) (f : InputSpace m → ℂ) (p : InputSpace m × ℝ) :
    classicalRidgeletIntegral f ρ p = euclideanRidgeletTransform m 0 ρ f p := by
  simp only [classicalRidgeletIntegral, euclideanRidgeletTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.rpow_zero, Complex.ofReal_one, mul_one]

/-- The ridgelet half of the affine equivariance, for the `L²` track's classical ridgelet
integral `R[f; ρ](a, b) = ∫ f(x) conj(ρ(⟪a, x⟫ - b)) dx`. -/
theorem classicalRidgeletIntegral_intertwines {m : ℕ} (ρ : ℝ → ℂ)
    (g : InputSpace m ≃ᵃ[ℝ] InputSpace m) (f : InputSpace m → ℂ) (p : InputSpace m × ℝ) :
    classicalRidgeletIntegral
        (quasiUnitaryPullbackAction affineDataJacobian
          (1 : UnitaryRepresentation (InputSpace m ≃ᵃ[ℝ] InputSpace m) ℂ) g f) ρ p =
      quasiRegularAction (radonNikodymWeight affineParameterJacobian) g
        (classicalRidgeletIntegral f ρ) p := by
  rw [classicalRidgeletIntegral_eq_euclideanRidgeletTransform,
    euclideanRidgeletTransform_intertwines, quasiRegularAction_apply, quasiRegularAction_apply,
    classicalRidgeletIntegral_eq_euclideanRidgeletTransform]

end LeanRidgelet
