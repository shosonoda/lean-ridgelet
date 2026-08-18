/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.Convolution

/-!
# Continuity of group convolution with a compact kernel

This file proves continuity of the noncommutative group-convolution expression
`x ↦ ∫ y, L (f y⁻¹) (g (x * y)) ∂μ` when the first factor is locally integrable and the second is
continuous with compact support. The proof transports the expression to Mathlib's additive
convolution on `Additive Gᵐᵒᵖ`; neither invariance nor local finiteness of `μ` is required.
-/
@[expose] public section

noncomputable section

open scoped Convolution

namespace MeasureTheory

private def additiveHomeomorph (X : Type*) [TopologicalSpace X] : Additive X ≃ₜ X where
  toEquiv := Additive.toMul
  continuous_toFun := continuous_toMul
  continuous_invFun := continuous_ofMul

private def opAddHomeomorph (G : Type*) [TopologicalSpace G] : G ≃ₜ Additive Gᵐᵒᵖ :=
  MulOpposite.opHomeomorph.trans (additiveHomeomorph Gᵐᵒᵖ).symm

private def invUnopHomeomorph (G : Type*) [Group G] [TopologicalSpace G] [ContinuousInv G] :
    Additive Gᵐᵒᵖ ≃ₜ G :=
  ((additiveHomeomorph Gᵐᵒᵖ).trans MulOpposite.opHomeomorph.symm).trans (Homeomorph.inv G)

@[simp]
private theorem invUnopHomeomorph_opAddHomeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] (x : G) :
    invUnopHomeomorph G (opAddHomeomorph G x) = x⁻¹ := by
  rfl

@[simp]
private theorem invUnopHomeomorph_opAddHomeomorph_sub
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] (x y : G) :
    invUnopHomeomorph G (opAddHomeomorph G (x⁻¹) - opAddHomeomorph G y) = x * y := by
  change (y⁻¹ * x⁻¹)⁻¹ = x * y
  simp

/-- A noncommutative group convolution is continuous when its first factor, after inversion, is
locally integrable and its second factor is continuous with compact support.

The formula is deliberately stated for an arbitrary measure. It is Mathlib's additive convolution
after transporting the group to `Additive Gᵐᵒᵖ`, so no Haar-invariance hypothesis is needed. -/
theorem continuous_integral_compact_mul_right
    {G E E' F 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E']
    [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    {f : G → E} {g : G → E'} (L : E →L[𝕜] E' →L[𝕜] F)
    {μ : Measure G} (hf : LocallyIntegrable (fun y ↦ f y⁻¹) μ)
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous fun x ↦ ∫ y, L (f y⁻¹) (g (x * y)) ∂μ := by
  letI : MeasurableSpace Gᵐᵒᵖ := borel Gᵐᵒᵖ
  letI : BorelSpace Gᵐᵒᵖ := ⟨rfl⟩
  let A := Additive Gᵐᵒᵖ
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  let e : G ≃ₜ A := opAddHomeomorph G
  let j : A ≃ₜ G := invUnopHomeomorph G
  let μA : Measure A := Measure.map e μ
  let fA : A → E := fun y ↦ f (j y)
  let gA : A → E' := fun y ↦ g (j y)
  have hje (y : G) : j (e y) = y⁻¹ := by
    exact invUnopHomeomorph_opAddHomeomorph y
  have hjesub (x y : G) : j (e (x⁻¹) - e y) = x * y := by
    exact invUnopHomeomorph_opAddHomeomorph_sub x y
  have hfA : LocallyIntegrable fA μA := by
    apply (locallyIntegrable_map_homeomorph e).mpr
    change LocallyIntegrable (fun y ↦ f (j (e y))) μ
    simpa only [hje] using hf
  have hgA : Continuous gA := hg.comp j.continuous
  have hcgA : HasCompactSupport gA := hcg.comp_homeomorph j
  have hconv : Continuous (convolution fA gA L μA) :=
    hcgA.continuous_convolution_right L hfA hgA
  have he : Continuous fun x : G ↦ e (x⁻¹) := e.continuous.comp continuous_inv
  apply (hconv.comp he).congr
  intro x
  simp only [Function.comp_apply, convolution]
  have hint : Integrable (fun t : A ↦ L (fA t) (gA (e (x⁻¹) - t))) μA :=
    hcgA.convolutionExists_right L hfA hgA (e (x⁻¹))
  rw [integral_map e.continuous.aemeasurable hint.aestronglyMeasurable]
  congr 1
  funext y
  change L (f (j (e y))) (g (j (e (x⁻¹) - e y))) = _
  rw [hje, hjesub]

end MeasureTheory
