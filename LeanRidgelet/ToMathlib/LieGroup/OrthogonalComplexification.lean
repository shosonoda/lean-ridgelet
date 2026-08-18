/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Schur
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The complexified standard representation of the orthogonal group

For a finite index type `ι`, entrywise inclusion `ℝ → ℂ` sends a real orthogonal matrix to a
complex unitary matrix.  Mathlib's star-algebra equivalence `Matrix.toEuclideanCLM` then realizes
that matrix as a unitary operator on `EuclideanSpace ℂ ι`.  This file bundles the resulting
standard complexified representation of `Matrix.orthogonalGroup ι ℝ`.

When `ι` is nonempty, the representation is topologically irreducible.  The proof only needs the
signed permutation subgroup: a coordinate reflection isolates a nonzero coordinate of a vector
in an invariant complex subspace, and permutation matrices move the resulting standard basis
vector to every coordinate.  Thus the whole standard basis, and hence the whole space, lies in
the subspace.

This coordinate construction fills the finite-dimensional complexification needed by the
fully-connected ridgelet example without introducing a project-specific complexification
structure.
-/

@[expose] public section

noncomputable section

open WithLp
open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realToComplexStarMonoidHom :
    Matrix ι ι ℝ →⋆* Matrix ι ι ℂ where
  toFun A := A.map (RCLike.ofReal : ℝ → ℂ)
  map_one' := by simp
  map_mul' A B := Matrix.map_mul
  map_star' A := by
    simpa only [star_eq_conjTranspose] using
      (Matrix.conjTranspose_map (A := A) (RCLike.ofReal : ℝ → ℂ) (by intro x; simp))

def orthogonalComplexificationMatrix :
    Matrix.orthogonalGroup ι ℝ →* Matrix.unitaryGroup ι ℂ :=
  (Unitary.map (realToComplexStarMonoidHom (ι := ι))).toMonoidHom

def standardComplexOrthogonalRepresentation :
    UnitaryRepresentation (Matrix.orthogonalGroup ι ℝ) (EuclideanSpace ℂ ι) :=
  (Unitary.map
    (StarMonoidHom.ofClass
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toStarAlgHom)).toMonoidHom.comp
      orthogonalComplexificationMatrix

theorem standardComplexOrthogonalRepresentation_apply
    (Q : Matrix.orthogonalGroup ι ℝ) (z : EuclideanSpace ℂ ι) :
    ((standardComplexOrthogonalRepresentation (ι := ι) Q :
        unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
      EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z =
        toLp 2 ((Q.1.map (RCLike.ofReal : ℝ → ℂ)) *ᵥ ofLp z) := by
  change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    (Q.1.map (RCLike.ofReal : ℝ → ℂ)) z = _
  exact Matrix.toEuclideanCLM_toLp _ _

def coordinateReflection (i : ι) : Matrix.orthogonalGroup ι ℝ :=
  ⟨Matrix.diagonal (fun j => if j = i then -1 else 1), by
    rw [Matrix.mem_orthogonalGroup_iff]
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases hjk : j = k
    · subst k
      by_cases hj : j = i <;> simp [hj]
    · simp [hjk]⟩

def coordinatePermutation (σ : Equiv.Perm ι) : Matrix.orthogonalGroup ι ℝ :=
  ⟨σ.permMatrix ℝ, by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_permMatrix]
    rw [← Matrix.permMatrix_mul]
    simp⟩

theorem coordinateReflection_mulVec (i : ι) (z : ι → ℂ) :
    ((coordinateReflection i : Matrix.orthogonalGroup ι ℝ).1.map
      (RCLike.ofReal : ℝ → ℂ)) *ᵥ z =
        Function.update z i (-z i) := by
  ext j
  change (((Matrix.diagonal (fun j => if j = i then -1 else 1)).map
    (RCLike.ofReal : ℝ → ℂ)) *ᵥ z) j = _
  rw [Matrix.diagonal_map (by simp), Matrix.mulVec_diagonal]
  by_cases hji : j = i <;> simp [hji, Function.update]

theorem coordinatePermutation_mulVec (σ : Equiv.Perm ι) (z : ι → ℂ) :
    ((coordinatePermutation σ : Matrix.orthogonalGroup ι ℝ).1.map
      (RCLike.ofReal : ℝ → ℂ)) *ᵥ z = z ∘ σ := by
  have hmap : (σ.permMatrix ℝ).map (RCLike.ofReal : ℝ → ℂ) = σ.permMatrix ℂ := by
    ext j k
    by_cases hjk : σ j = k <;> simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, hjk]
  rw [show (coordinatePermutation σ : Matrix.orthogonalGroup ι ℝ).1.map
      (RCLike.ofReal : ℝ → ℂ) = σ.permMatrix ℂ by exact hmap]
  exact Matrix.permMatrix_mulVec σ

theorem standardComplexOrthogonalRepresentation_coordinateReflection
    (i : ι) (z : EuclideanSpace ℂ ι) :
    ((standardComplexOrthogonalRepresentation (ι := ι) (coordinateReflection i) :
        unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
      EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z =
        toLp 2 (Function.update (ofLp z) i (-z i)) := by
  rw [standardComplexOrthogonalRepresentation_apply, coordinateReflection_mulVec]

theorem standardComplexOrthogonalRepresentation_coordinatePermutation
    (σ : Equiv.Perm ι) (z : EuclideanSpace ℂ ι) :
    ((standardComplexOrthogonalRepresentation (ι := ι) (coordinatePermutation σ) :
        unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :
      EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z =
        toLp 2 (ofLp z ∘ σ) := by
  rw [standardComplexOrthogonalRepresentation_apply, coordinatePermutation_mulVec]

theorem standardComplexOrthogonalRepresentation_isTopologicallyIrreducible [Nonempty ι] :
    (standardComplexOrthogonalRepresentation (ι := ι)).IsTopologicallyIrreducible := by
  refine ⟨inferInstance, ?_⟩
  intro K hK
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  right
  have hsub : K.toSubmodule ≠ ⊥ := by
    intro h
    apply hbot
    apply ClosedSubmodule.toSubmodule_injective
    simpa using h
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsub
  have hxCoord : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    apply PiLp.ext
    exact h
  obtain ⟨i, hi⟩ := hxCoord
  have hreflection := hK (coordinateReflection i) hxK
  rw [standardComplexOrthogonalRepresentation_coordinateReflection] at hreflection
  have hisolateRaw := K.sub_mem hxK hreflection
  have hisolate : PiLp.single 2 i (2 * x i) ∈ K := by
    have heq : x - toLp 2 (Function.update (ofLp x) i (-x i)) =
        PiLp.single 2 i (2 * x i) := by
      apply PiLp.ext
      intro j
      by_cases hji : j = i
      · subst j
        simp [Function.update, two_mul]
      · simp [Function.update, hji]
    rwa [heq] at hisolateRaw
  have hbasis_i : PiLp.single 2 i (1 : ℂ) ∈ K := by
    have hs := K.smul_mem ((2 * x i)⁻¹) hisolate
    have heq : (2 * x i)⁻¹ •
        (PiLp.single 2 i (2 * x i) : EuclideanSpace ℂ ι) =
        (PiLp.single 2 i (1 : ℂ) : EuclideanSpace ℂ ι) := by
      apply PiLp.ext
      intro j
      by_cases hji : j = i
      · subst j
        simp
        field_simp
      · simp [hji]
    rwa [heq] at hs
  have hbasis : ∀ j : ι, PiLp.single 2 j (1 : ℂ) ∈ K := by
    intro j
    have hp := hK (coordinatePermutation (Equiv.swap i j)) hbasis_i
    rw [standardComplexOrthogonalRepresentation_coordinatePermutation] at hp
    convert hp using 1
    apply PiLp.ext
    intro k
    simp [PiLp.single_apply, Equiv.swap_apply_def]
    aesop
  apply top_unique
  intro z hz
  rw [← (EuclideanSpace.basisFun ι ℂ).toBasis.sum_repr z]
  exact K.sum_mem fun j _ ↦ K.smul_mem _ (by simpa using hbasis j)

end Matrix
