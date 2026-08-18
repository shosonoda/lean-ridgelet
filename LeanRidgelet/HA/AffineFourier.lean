/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.AffineIrreducibility
public import LeanRidgelet.ToMathlib.FourierAffine
public import LeanRidgelet.ToMathlib.LieGroup.UnitaryConjugation

/-!
# Fourier covariance of the affine data representation

This file connects the concrete determinant-corrected affine action on `L²` with the Fourier-side
action used by the Mackey machine. First, conjugation by Mathlib's Plancherel isometry defines an
honest unitary representation on all of `L²`, with the Fourier transform and its inverse bundled
as continuous intertwiners. On the dense subspace of Schwartz vectors, its representative is then
computed explicitly as character multiplication followed by the adjoint linear action on
frequency.

Mathlib's Fourier convention uses the character `exp (2 π i x)`. This rescales the frequency
parameter relative to the angular convention of the ridgelet manuscripts but leaves the nonzero
orbit and little group unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContRepresentation ENNReal FourierTransform InnerProductSpace NNReal
  RealInnerProductSpace

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The affine data representation transported to frequency space by Mathlib's Plancherel
isometry. This is an honest unitary representation on all of `L²`; the explicit character and
adjoint-action formula is proved below on the dense Schwartz core. -/
noncomputable def affineFourierLpUnitaryRepresentation :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp ℂ 2 (volume : Measure E)) :=
  (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).conjugate
    (Lp.fourierTransformₗᵢ E ℂ)

/-- The Fourier-side affine representation indexed by the locally compact topological
semidirect-product model. -/
noncomputable def affineTopologicalFourierLpUnitaryRepresentation :
    UnitaryRepresentation (AffineEquiv.TopologicalSemidirectProduct E)
      (Lp ℂ 2 (volume : Measure E)) :=
  (affineTopologicalLpUnitaryRepresentation (volume : Measure E)).conjugate
    (Lp.fourierTransformₗᵢ E ℂ)

@[simp]
theorem affineTopologicalFourierLpUnitaryRepresentation_apply
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineTopologicalFourierLpUnitaryRepresentation g =
      affineFourierLpUnitaryRepresentation
        (AffineEquiv.topologicalSemidirectProductEquiv E g) := rfl

/-- The topologically indexed Fourier-side affine representation is strongly continuous. -/
theorem affineTopologicalFourierLpUnitaryRepresentation_isStronglyContinuous :
    (affineTopologicalFourierLpUnitaryRepresentation (E := E)).IsStronglyContinuous :=
  (affineTopologicalLpUnitaryRepresentation_isStronglyContinuous
    (volume : Measure E)).conjugate (Lp.fourierTransformₗᵢ E ℂ)

/-- The Plancherel transform, bundled as a bounded intertwiner from the physical-space affine
representation to its frequency-space conjugate. -/
noncomputable def affinePlancherelIntertwiningMap :
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation →ⁱL
      (affineFourierLpUnitaryRepresentation (E := E)).toContRepresentation :=
  UnitaryRepresentation.conjugateIntertwiningMap
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    (Lp.fourierTransformₗᵢ E ℂ)

/-- The inverse Plancherel transform, bundled as the inverse bounded intertwiner. -/
noncomputable def affinePlancherelInverseIntertwiningMap :
    (affineFourierLpUnitaryRepresentation (E := E)).toContRepresentation →ⁱL
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure E)).toContRepresentation :=
  UnitaryRepresentation.conjugateInverseIntertwiningMap
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    (Lp.fourierTransformₗᵢ E ℂ)

@[simp]
theorem affinePlancherelIntertwiningMap_apply (f : Lp ℂ 2 (volume : Measure E)) :
    affinePlancherelIntertwiningMap (E := E) f = 𝓕 f := rfl

@[simp]
theorem affinePlancherelInverseIntertwiningMap_apply (f : Lp ℂ 2 (volume : Measure E)) :
    affinePlancherelInverseIntertwiningMap (E := E) f = 𝓕⁻ f := rfl

/-- Full `L²` Fourier covariance: the Plancherel transform intertwines the physical affine
representation with its frequency-space conjugate, with no choice of representatives and no
dense-subspace restriction. -/
theorem affinePlancherelIntertwiningMap_intertwines (g : E ≃ᵃ[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    𝓕 (Unitary.linearIsometryEquiv
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g) f) =
      Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g) (𝓕 f) := by
  exact (affinePlancherelIntertwiningMap (E := E)).isIntertwining g f

/-- The physical and Fourier-conjugated affine representations are topologically irreducible
simultaneously. Thus the remaining Mackey problem may be solved entirely on frequency space. -/
theorem affineFourierLpUnitaryRepresentation_isTopologicallyIrreducible_iff :
    (affineFourierLpUnitaryRepresentation (E := E)).IsTopologicallyIrreducible ↔
      (affineDataLpUnitaryRepresentation (Y := ℂ)
        (volume : Measure E)).IsTopologicallyIrreducible :=
  UnitaryRepresentation.conjugate_isTopologicallyIrreducible_iff _ _

/-- The Schwartz representative of the determinant-corrected affine data action. It is kept as a
named definition because it is the dense core on which both the physical-space action and its
Fourier covariance can be computed pointwise. -/
noncomputable def affineDataSchwartzAction (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) :
    SchwartzMap E ℂ :=
  ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) •
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      g.linear.symm.toContinuousLinearEquiv f).compSubConstCLM ℂ (g 0))

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem affineDataSchwartzAction_apply (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) (x : E) :
    affineDataSchwartzAction g f x =
      ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) • f (g.symm x) := by
  change ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) *
      f (g.linear.symm (x - g 0)) =
    ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) * f (g.symm x)
  rw [MeasureTheory.affineEquiv_symm_apply]

/-- On Schwartz vectors, the abstract quasi-invariant `L²` representation is exactly the `L²`
class of the concrete determinant-weighted Schwartz pullback. -/
theorem affineDataLpUnitaryRepresentation_schwartz
    (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) :
    (Unitary.linearIsometryEquiv
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g))
        (f.toLp 2 volume) =
      (affineDataSchwartzAction g f).toLp 2 volume := by
  let u := affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g
  have hu (z : Lp ℂ 2 volume) :
      (Unitary.linearIsometryEquiv u) z = ((u : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume) z) := rfl
  rw [hu]
  apply Lp.ext
  have haction := affineDataLpUnitaryRepresentation_apply_ae
    (E := E) (volume : Measure E) g (f.toLp 2 volume)
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity affineDataJacobian
    affineData_measurable (affineData_group_map_eq_withDensity (volume : Measure E)) g
  have hfcomp := hqmp.ae_eq (f.coeFn_toLp 2 volume)
  have hcore := (affineDataSchwartzAction g f).coeFn_toLp 2 volume
  filter_upwards [haction, hfcomp, hcore] with x hx hfx hqx
  rw [hx, hqx, affineDataSchwartzAction_apply]
  exact congrArg (_ • ·) hfx

/-- `L²` Fourier covariance of the affine data representation on its dense Schwartz core. The
translation becomes character multiplication, while the linear part becomes the adjoint action
on frequency and the inverse square-root Jacobian becomes the forward square-root Jacobian. -/
theorem affineDataLpUnitaryRepresentation_fourier_schwartz_ae
    (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) :
    ((𝓕 ((Unitary.linearIsometryEquiv
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g))
        (f.toLp 2 volume))) : Lp ℂ 2 volume) =ᵐ[volume]
      fun xi => Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) •
          𝓕 (f : E → ℂ) (g.linear.adjoint xi)) := by
  rw [affineDataLpUnitaryRepresentation_schwartz,
    SchwartzMap.toLp_fourier_eq]
  have hcoe := (𝓕 (affineDataSchwartzAction g f)).coeFn_toLp 2 volume
  filter_upwards [hcoe] with xi hxi
  rw [hxi, SchwartzMap.fourier_coe]
  rw [show (affineDataSchwartzAction g f : E → ℂ) =
      fun x => ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ)⁻¹) •
        f (g.symm x) by
    funext x
    exact affineDataSchwartzAction_apply g f x]
  exact MeasureTheory.fourier_weighted_comp_affineEquiv_symm g f xi

/-- The explicit action formula for the Fourier-conjugated affine representation on the dense
Schwartz core. This is the form used to compare it with a Mackey induced representation. -/
theorem affineFourierLpUnitaryRepresentation_schwartz_ae
    (g : E ≃ᵃ[ℝ] E) (f : SchwartzMap E ℂ) :
    (Unitary.linearIsometryEquiv (affineFourierLpUnitaryRepresentation (E := E) g)
      (𝓕 (f.toLp 2 volume)) : Lp ℂ 2 volume) =ᵐ[volume]
      fun xi => Real.fourierChar (-⟪g 0, xi⟫_ℝ) •
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊.sqrt : ℂ) •
          𝓕 (f : E → ℂ) (g.linear.adjoint xi)) := by
  rw [← affinePlancherelIntertwiningMap_intertwines g (f.toLp 2 volume)]
  exact affineDataLpUnitaryRepresentation_fourier_schwartz_ae g f

end LeanRidgelet
