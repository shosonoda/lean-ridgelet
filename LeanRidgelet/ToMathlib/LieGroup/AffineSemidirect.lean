/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.TopologicalSemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The affine group as a semidirect product

For a module `E` over a ring `k`, the affine automorphism group is the semidirect product of the
additive translation group by the general linear group.  Mathlib has the abstract semidirect
product and both affine and linear equivalences, but does not currently connect them.

Because `SemidirectProduct` is stated multiplicatively, translations use the type synonym
`Multiplicative E`.  The resulting equivalence sends `(t, L)` to `x ↦ t + L x` and its inverse
sends an affine automorphism `g` to `(g 0, g.linear)`.
-/

@[expose] public section

namespace AffineEquiv

variable (k E : Type*) [Ring k] [AddCommGroup E] [Module k E]

/-- The natural action of the general linear group on the multiplicative synonym of the additive
translation group. -/
def linearMultiplicativeActionHom : (E ≃ₗ[k] E) →* MulAut (Multiplicative E) where
  toFun L := L.toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    rfl
  map_mul' L M := by
    ext x
    rfl

@[simp]
theorem linearMultiplicativeActionHom_apply (L : E ≃ₗ[k] E) (x : Multiplicative E) :
    linearMultiplicativeActionHom k E L x = Multiplicative.ofAdd (L x.toAdd) := rfl

/-- The coordinate-free affine semidirect product `E ⋊ GL(E)`. -/
abbrev SemidirectProduct :=
  Multiplicative E ⋊[linearMultiplicativeActionHom k E] (E ≃ₗ[k] E)

/-- The affine automorphism represented by a translation-linear pair. -/
def ofSemidirectProduct (p : AffineEquiv.SemidirectProduct k E) : E ≃ᵃ[k] E :=
  AffineEquiv.constVAdd k E p.left.toAdd * p.right.toAffineEquiv

@[simp]
theorem ofSemidirectProduct_apply (p : AffineEquiv.SemidirectProduct k E) (x : E) :
    ofSemidirectProduct k E p x = p.left.toAdd + p.right x := rfl

@[simp]
theorem ofSemidirectProduct_zero (p : AffineEquiv.SemidirectProduct k E) :
    ofSemidirectProduct k E p 0 = p.left.toAdd := by
  simp

@[simp]
theorem ofSemidirectProduct_linear (p : AffineEquiv.SemidirectProduct k E) :
    (ofSemidirectProduct k E p).linear = p.right := rfl

/-- The translation-linear coordinates of an affine automorphism. -/
def toSemidirectProduct (g : E ≃ᵃ[k] E) : AffineEquiv.SemidirectProduct k E :=
  ⟨Multiplicative.ofAdd (g 0), g.linear⟩

@[simp]
theorem toSemidirectProduct_left (g : E ≃ᵃ[k] E) :
    (toSemidirectProduct k E g).left = Multiplicative.ofAdd (g 0) := rfl

@[simp]
theorem toSemidirectProduct_right (g : E ≃ᵃ[k] E) :
    (toSemidirectProduct k E g).right = g.linear := rfl

/-- Every affine automorphism is its translation part followed by its linear part. -/
theorem translation_mul_linear (g : E ≃ᵃ[k] E) :
    g = AffineEquiv.constVAdd k E (g 0) * g.linear.toAffineEquiv := by
  apply AffineEquiv.ext
  intro x
  simp only [AffineEquiv.coe_mul, Function.comp_apply, AffineEquiv.constVAdd_apply,
    LinearEquiv.coe_toAffineEquiv, vadd_eq_add]
  rw [add_comm]
  exact congrFun g.toAffineMap.decomp x

/-- The coordinate-free group equivalence `E ⋊ GL(E) ≃ Aff(E)`. -/
def semidirectProductEquiv : AffineEquiv.SemidirectProduct k E ≃* (E ≃ᵃ[k] E) where
  toFun := ofSemidirectProduct k E
  invFun := toSemidirectProduct k E
  left_inv p := by
    apply SemidirectProduct.ext
    · simp
    · rfl
  right_inv g := by
    exact (translation_mul_linear k E g).symm
  map_mul' p q := by
    apply AffineEquiv.ext
    intro x
    simp only [ofSemidirectProduct_apply, SemidirectProduct.mul_left,
      linearMultiplicativeActionHom_apply, toAdd_mul, toAdd_ofAdd,
      SemidirectProduct.mul_right, AffineEquiv.coe_mul, Function.comp_apply,
      map_add, LinearEquiv.mul_apply]
    ac_rfl

@[simp]
theorem semidirectProductEquiv_apply (p : AffineEquiv.SemidirectProduct k E) (x : E) :
    semidirectProductEquiv k E p x = p.left.toAdd + p.right x := rfl

@[simp]
theorem semidirectProductEquiv_symm_left (g : E ≃ᵃ[k] E) :
    ((semidirectProductEquiv k E).symm g).left = Multiplicative.ofAdd (g 0) := rfl

@[simp]
theorem semidirectProductEquiv_symm_right (g : E ≃ᵃ[k] E) :
    ((semidirectProductEquiv k E).symm g).right = g.linear := rfl

section Topological

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The action of invertible continuous endomorphisms on the translation group.  Using units of
the continuous-endomorphism ring gives the linear factor its standard topological-group
structure. -/
def continuousLinearMultiplicativeActionHom :
    (E →L[ℝ] E)ˣ →* MulAut (Multiplicative E) where
  toFun L := (ContinuousLinearEquiv.unitsEquiv ℝ E L).toLinearEquiv.toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    rfl
  map_mul' L M := by
    ext x
    rfl

@[simp]
theorem continuousLinearMultiplicativeActionHom_apply (L : (E →L[ℝ] E)ˣ)
    (x : Multiplicative E) :
    continuousLinearMultiplicativeActionHom E L x =
      Multiplicative.ofAdd ((L : E →L[ℝ] E) x.toAdd) := rfl

/-- The affine group model whose linear factor carries the units topology. -/
abbrev TopologicalSemidirectProduct :=
  Multiplicative E ⋊[continuousLinearMultiplicativeActionHom E] (E →L[ℝ] E)ˣ

theorem continuous_continuousLinearMultiplicativeAction :
    Continuous fun p : (E →L[ℝ] E)ˣ × Multiplicative E ↦
      continuousLinearMultiplicativeActionHom E p.1 p.2 := by
  change Continuous fun p : (E →L[ℝ] E)ˣ × E ↦ (p.1 : E →L[ℝ] E) p.2
  exact isBoundedBilinearMap_apply.continuous.comp
    ((Units.continuous_val.comp continuous_fst).prodMk continuous_snd)

instance instIsTopologicalGroupTopologicalSemidirectProduct :
    IsTopologicalGroup (AffineEquiv.TopologicalSemidirectProduct E) :=
  SemidirectProduct.isTopologicalGroupOfContinuous
    (continuousLinearMultiplicativeActionHom E)
    (continuous_continuousLinearMultiplicativeAction E)

/-- In finite dimension, forgetting continuity identifies the units of the continuous
endomorphism ring with the full general linear group. -/
noncomputable def continuousLinearUnitsEquivLinearEquiv [FiniteDimensional ℝ E] :
    (E →L[ℝ] E)ˣ ≃* (E ≃ₗ[ℝ] E) where
  toFun L := (ContinuousLinearEquiv.unitsEquiv ℝ E L).toLinearEquiv
  invFun L := (ContinuousLinearEquiv.unitsEquiv ℝ E).symm L.toContinuousLinearEquiv
  left_inv L := by
    apply Units.ext
    rfl
  right_inv L := by
    ext x
    rfl
  map_mul' L M := by
    ext x
    rfl

/-- The locally compact topological semidirect-product model has the same underlying group as the
affine automorphism group. -/
noncomputable def topologicalSemidirectProductEquiv [FiniteDimensional ℝ E] :
    AffineEquiv.TopologicalSemidirectProduct E ≃* (E ≃ᵃ[ℝ] E) :=
  (SemidirectProduct.congr (MulEquiv.refl (Multiplicative E))
      (continuousLinearUnitsEquivLinearEquiv E) (by
        intro L
        ext x
        rfl)).trans
    (semidirectProductEquiv ℝ E)

@[simp]
theorem topologicalSemidirectProductEquiv_apply [FiniteDimensional ℝ E]
    (p : AffineEquiv.TopologicalSemidirectProduct E) (x : E) :
    topologicalSemidirectProductEquiv E p x =
      p.left.toAdd + (p.right : E →L[ℝ] E) x := rfl

@[simp]
theorem topologicalSemidirectProductEquiv_linear [FiniteDimensional ℝ E]
    (p : AffineEquiv.TopologicalSemidirectProduct E) :
    (topologicalSemidirectProductEquiv E p).linear =
      (ContinuousLinearEquiv.unitsEquiv ℝ E p.right).toLinearEquiv := rfl

@[simp]
theorem det_topologicalSemidirectProductEquiv_linear [FiniteDimensional ℝ E]
    (p : AffineEquiv.TopologicalSemidirectProduct E) :
    LinearMap.det ((topologicalSemidirectProductEquiv E p).linear : E →ₗ[ℝ] E) =
      LinearMap.det ((p.right : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl

/-- The inverse affine map represented by a point of the topological semidirect product, bundled
as a continuous map on the underlying normed space. -/
def topologicalSemidirectProductInverseContinuousMap
    (p : AffineEquiv.TopologicalSemidirectProduct E) : C(E, E) where
  toFun x := (↑(p.right⁻¹) : E →L[ℝ] E) (x - p.left.toAdd)
  continuous_toFun := (↑(p.right⁻¹) : E →L[ℝ] E).continuous.comp
    (continuous_id.sub continuous_const)

@[simp]
theorem topologicalSemidirectProductInverseContinuousMap_apply
    [FiniteDimensional ℝ E] (p : AffineEquiv.TopologicalSemidirectProduct E) (x : E) :
    topologicalSemidirectProductInverseContinuousMap E p x =
      (topologicalSemidirectProductEquiv E p).symm x := by
  apply (topologicalSemidirectProductEquiv E p).injective
  rw [(topologicalSemidirectProductEquiv E p).apply_symm_apply]
  change p.left.toAdd + (p.right : E →L[ℝ] E)
    ((↑(p.right⁻¹) : E →L[ℝ] E) (x - p.left.toAdd)) = x
  rw [← mul_apply_eq_comp]
  simp

/-- The inverse affine maps depend continuously on the semidirect-product parameter in the
compact-open topology. -/
theorem continuous_topologicalSemidirectProductInverseContinuousMap :
    Continuous (topologicalSemidirectProductInverseContinuousMap E) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E × E ↦
    (↑(p.1.right⁻¹) : E →L[ℝ] E) (p.2 - p.1.left.toAdd)
  have hop : Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E × E ↦
      (↑(p.1.right⁻¹) : E →L[ℝ] E) :=
    Units.continuous_val.comp
      ((SemidirectProduct.continuous_right
        (φ := continuousLinearMultiplicativeActionHom E)).comp continuous_fst).inv
  have harg : Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E × E ↦
      p.2 - p.1.left.toAdd :=
    continuous_snd.sub <| (SemidirectProduct.continuous_left
      (φ := continuousLinearMultiplicativeActionHom E)).comp continuous_fst
  convert isBoundedBilinearMap_apply.continuous.comp (hop.prodMk harg) using 1
  funext p
  rfl

end Topological

end AffineEquiv
