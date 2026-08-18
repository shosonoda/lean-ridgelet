/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Adjoint linear equivalences and affine changes of Haar measure

This file supplies finite-dimensional linear-algebra and measure-transport lemmas used to compute
the Jacobians of affine data and contragredient parameter actions:

* the adjoint of a linear equivalence, bundled again as a linear equivalence;
* the determinant of an adjoint and of a block lower-triangular `LinearEquiv.skewProd`;
* the natural action of the affine automorphism group on its underlying affine module;
* the pushforward of an additive Haar measure by an affine equivalence, both as a scalar multiple
  and as a constant `withDensity` measure.

These statements are independent of ridgelet transforms and are candidates for upstreaming to
Mathlib.
-/

@[expose] public section

noncomputable section

open scoped ENNReal InnerProductSpace NNReal

namespace LinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The adjoint of a finite-dimensional linear equivalence, bundled as a linear equivalence in
the reverse direction. -/
def adjoint (e : E ≃ₗ[𝕜] F) : F ≃ₗ[𝕜] E where
  toLinearMap := (e : E →ₗ[𝕜] F).adjoint
  invFun := (e.symm : F →ₗ[𝕜] E).adjoint
  left_inv x := by
    have h := congrArg (fun f : F →ₗ[𝕜] F ↦ f x)
      (LinearMap.adjoint_comp (e : E →ₗ[𝕜] F) (e.symm : F →ₗ[𝕜] E))
    simpa using h.symm
  right_inv x := by
    have h := congrArg (fun f : E →ₗ[𝕜] E ↦ f x)
      (LinearMap.adjoint_comp (e.symm : F →ₗ[𝕜] E) (e : E →ₗ[𝕜] F))
    simpa using h.symm

@[simp]
theorem coe_adjoint (e : E ≃ₗ[𝕜] F) :
    (e.adjoint : F →ₗ[𝕜] E) = (e : E →ₗ[𝕜] F).adjoint := rfl

@[simp]
theorem adjoint_symm (e : E ≃ₗ[𝕜] F) : e.adjoint.symm = e.symm.adjoint := rfl

end LinearEquiv

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The determinant of the adjoint is the conjugate of the determinant. -/
theorem det_adjoint (f : E →ₗ[𝕜] E) :
    LinearMap.det f.adjoint = star (LinearMap.det f) := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose]

end LinearMap

namespace LinearEquiv

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Determinant of the bundled adjoint equivalence. -/
theorem det_adjoint (e : E ≃ₗ[𝕜] E) :
    LinearMap.det (e.adjoint : E →ₗ[𝕜] E) = star (LinearMap.det (e : E →ₗ[𝕜] E)) :=
  LinearMap.det_adjoint _

section SkewProd

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The determinant of a block lower-triangular linear equivalence is the product of the
determinants of its diagonal blocks. -/
theorem det_skewProd (e₁ : M ≃ₗ[R] M) (e₂ : N ≃ₗ[R] N) (f : M →ₗ[R] N) :
    LinearMap.det (e₁.skewProd e₂ f : M × N →ₗ[R] M × N) =
      LinearMap.det (e₁ : M →ₗ[R] M) * LinearMap.det (e₂ : N →ₗ[R] N) := by
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  rw [← LinearMap.det_toMatrix (bM.prod bN), ← LinearMap.det_toMatrix bM,
    ← LinearMap.det_toMatrix bN]
  have hmatrix :
      LinearMap.toMatrix (bM.prod bN) (bM.prod bN)
          (e₁.skewProd e₂ f : M × N →ₗ[R] M × N) =
        Matrix.fromBlocks (LinearMap.toMatrix bM bM (e₁ : M →ₗ[R] M)) 0
          (LinearMap.toMatrix bM bN f) (LinearMap.toMatrix bN bN (e₂ : N →ₗ[R] N)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, LinearEquiv.skewProd_apply]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂]

end SkewProd

end LinearEquiv

namespace AffineEquiv

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The natural action of the group of affine automorphisms on its underlying affine module. -/
instance instMulActionSelf : MulAction (E ≃ᵃ[R] E) E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end AffineEquiv

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- An affine equivalence rescales an additive Haar measure by the absolute determinant of its
inverse linear part. -/
theorem map_affineEquiv_addHaar_eq_smul_addHaar (g : E ≃ᵃ[ℝ] E) :
    map g μ = ENNReal.ofReal |LinearMap.det (g.linear.symm : E →ₗ[ℝ] E)| • μ := by
  have hlinear : Measurable (g.linear : E → E) :=
    (g.linear : E →ₗ[ℝ] E).continuous_of_finiteDimensional.measurable
  have htranslate : Measurable (fun x : E ↦ x + g 0) :=
    measurable_id.add measurable_const
  calc
    map g μ = map (fun x : E ↦ x + g 0) (map g.linear μ) := by
      rw [map_map htranslate hlinear]
      congr 1
      exact g.toAffineMap.decomp
    _ = map (fun x : E ↦ x + g 0)
          (ENNReal.ofReal |LinearMap.det (g.linear.symm : E →ₗ[ℝ] E)| • μ) := by
      congr 1
      change map (g.linear : E →ₗ[ℝ] E) μ =
        ENNReal.ofReal |LinearMap.det (g.linear.symm : E →ₗ[ℝ] E)| • μ
      simpa only [LinearEquiv.det_coe_symm, inv_inv] using
        map_linearMap_addHaar_eq_smul_addHaar μ g.linear.isUnit_det'.ne_zero
    _ = ENNReal.ofReal |LinearMap.det (g.linear.symm : E →ₗ[ℝ] E)| • μ := by
      rw [_root_.MeasureTheory.Measure.map_smul,
        Measure.IsAddRightInvariant.map_add_right_eq_self]

/-- The inverse of an affine equivalence pushes Haar measure to the constant density given by the
absolute determinant of the forward linear part. -/
theorem map_affineEquiv_symm_addHaar_eq_withDensity (g : E ≃ᵃ[ℝ] E) :
    map g.symm μ =
      μ.withDensity (fun _ ↦ (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞)) := by
  rw [map_affineEquiv_addHaar_eq_smul_addHaar]
  change ENNReal.ofReal |LinearMap.det (g.linear.symm.symm : E →ₗ[ℝ] E)| • μ = _
  rw [show g.linear.symm.symm = g.linear by rfl, withDensity_const]
  congr 1
  rw [← Real.norm_eq_abs]
  rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

end MeasureTheory.Measure
