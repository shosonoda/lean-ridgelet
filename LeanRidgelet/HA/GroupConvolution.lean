/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Deep
public import LeanRidgelet.HA.BochnerIntertwining

/-!
# Group-convolutional orbit lifting

This file formalizes Section 6 and Lemmas A.4--A.5 of arXiv:2405.13682 at the algebraic and
pointwise Bochner-integral level.  A base feature `φ : X → Ξ → Y` is lifted to

`φᵗ(x, ξ)(g) = υ(g)[φ(g⁻¹ • x, ξ)]`.

The lifted feature is equivariant, its synthesis is the corresponding orbit lift of the base
synthesis, and its ridgelet transform is exactly the base ridgelet transform of the value at the
identity.  Consequently any base reconstruction identity -- in particular one supplied by the
bounded L2 synthesis and ridgelet operators -- transports directly to the group-convolutional
network.

## Deviations from the article

The theorem is stated for an arbitrary group action and complex Hilbert-valued feature.  It does
not identify `L²_G(X;Y)` with a new subtype carrying an evaluation norm; the exact property used
by the proof is exposed as `IsGroupConvolutionEquivariant` instead.  This avoids pretending that
point evaluation is defined on arbitrary `L²` equivalence classes.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

variable {G X Ξ Y : Type*} [Group G] [MulAction G X]
  [MeasurableSpace X] [MeasurableSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The `G`-convolutional/orbit lift of a base feature map. -/
def groupConvolutionalFeature (υ : UnitaryRepresentation G Y) (φ : X → Ξ → Y)
    (x : X) (ξ : Ξ) (g : G) : Y :=
  (υ g : Y →L[ℂ] Y) (φ (g⁻¹ • x) ξ)

/-- Equivariance of a function-valued map under the orbit action. -/
def IsGroupConvolutionEquivariant (υ : UnitaryRepresentation G Y) (f : X → G → Y) : Prop :=
  ∀ (h : G) (x : X) (g : G),
    f (h • x) g = (υ h : Y →L[ℂ] Y) (f x (h⁻¹ * g))

omit [MeasurableSpace X] [MeasurableSpace Ξ] in
/-- Section 6.2: the orbit-lifted feature is `G`-equivariant for every base feature. -/
theorem groupConvolutionalFeature_equivariant (υ : UnitaryRepresentation G Y)
    (φ : X → Ξ → Y) (ξ : Ξ) :
    IsGroupConvolutionEquivariant υ (fun x g ↦ groupConvolutionalFeature υ φ x ξ g) := by
  intro h x g
  simp only [groupConvolutionalFeature, mul_inv_rev, inv_inv, mul_smul]
  change (υ g : Y →L[ℂ] Y) (φ (g⁻¹ • h • x) ξ) =
    (↑((υ h) * υ (h⁻¹ * g) : unitary (Y →L[ℂ] Y)) : Y →L[ℂ] Y)
      (φ (g⁻¹ • h • x) ξ)
  rw [← map_mul]
  simp only [mul_inv_cancel_left]

/-- Pointwise synthesis of a group-convolutional feature. -/
def groupConvolutionalSynthesis (μ : Measure Ξ) (υ : UnitaryRepresentation G Y)
    (φ : X → Ξ → Y) (γ : Ξ → ℂ) (x : X) (g : G) : Y :=
  ∫ ξ, γ ξ • groupConvolutionalFeature υ φ x ξ g ∂μ

omit [MeasurableSpace X] in
/-- Appendix A.4: GCN synthesis is the orbit lift of the base synthesis. -/
theorem groupConvolutionalSynthesis_eq_orbit (μ : Measure Ξ)
    (υ : UnitaryRepresentation G Y) (φ : X → Ξ → Y) (γ : Ξ → ℂ)
    (x : X) (g : G) :
    groupConvolutionalSynthesis μ υ φ γ x g =
      (υ g : Y →L[ℂ] Y) (bochnerSynthesis μ φ γ (g⁻¹ • x)) := by
  let U : Y ≃ₗᵢ[ℂ] Y := Unitary.linearIsometryEquiv (υ g)
  have hU (y : Y) : U.toLinearIsometry y = (υ g : Y →L[ℂ] Y) y := rfl
  simpa only [groupConvolutionalSynthesis, groupConvolutionalFeature, bochnerSynthesis,
    hU, map_smul] using
      U.toLinearIsometry.integral_comp_comm (μ := μ) (fun ξ ↦ γ ξ • φ (g⁻¹ • x) ξ)

/-- The Section 6 ridgelet transform: apply the base ridgelet transform to the value at the
identity element. -/
def groupConvolutionalRidgelet (μ : Measure X) (ψ : X → Ξ → Y)
    (f : X → G → Y) : Ξ → ℂ :=
  bochnerRidgelet μ ψ (fun x ↦ f x 1)

omit [MulAction G X] [MeasurableSpace Ξ] [CompleteSpace Y] in
/-- Appendix A.5: the convolutional ridgelet is definitionally the base ridgelet at `1_G`. -/
@[simp]
theorem groupConvolutionalRidgelet_eq_base (μ : Measure X) (ψ : X → Ξ → Y)
    (f : X → G → Y) :
    groupConvolutionalRidgelet μ ψ f = bochnerRidgelet μ ψ (fun x ↦ f x 1) := rfl

omit [MeasurableSpace X] in
/-- Theorem 6.1: a reconstruction formula for the base feature transports to the
group-convolutional orbit lift.  The bounded L2 theory can provide `hrec`; this theorem performs
only the Section 6 transport and introduces no additional boundedness assumption. -/
theorem groupConvolutional_reconstruction (μParameter : Measure Ξ)
    (υ : UnitaryRepresentation G Y) (φ : X → Ξ → Y) (γ : Ξ → ℂ)
    (f : X → G → Y) (hf : IsGroupConvolutionEquivariant υ f) (c : ℂ)
    (hrec : ∀ x,
      bochnerSynthesis μParameter φ γ x = c • f x 1) (x : X) (g : G) :
    groupConvolutionalSynthesis μParameter υ φ γ x g = c • f x g := by
  rw [groupConvolutionalSynthesis_eq_orbit, hrec]
  rw [(υ g : Y →L[ℂ] Y).map_smul]
  have hfg := hf g (g⁻¹ • x) g
  simpa only [smul_inv_smul, inv_mul_cancel] using congrArg (fun y ↦ c • y) hfg.symm

/-- Theorem 6.1 with the convolutional ridgelet inserted explicitly. -/
theorem groupConvolutional_synthesis_ridgelet (μParameter : Measure Ξ)
    (μData : Measure X) (υ : UnitaryRepresentation G Y) (φ ψ : X → Ξ → Y)
    (f : X → G → Y) (hf : IsGroupConvolutionEquivariant υ f) (c : ℂ)
    (hrec : ∀ x,
      bochnerSynthesis μParameter φ
        (bochnerRidgelet μData ψ (fun y ↦ f y 1)) x = c • f x 1)
    (x : X) (g : G) :
    groupConvolutionalSynthesis μParameter υ φ
        (groupConvolutionalRidgelet μData ψ f) x g = c • f x g := by
  exact groupConvolutional_reconstruction μParameter υ φ
    (groupConvolutionalRidgelet μData ψ f) f hf c hrec x g

end LeanRidgelet
