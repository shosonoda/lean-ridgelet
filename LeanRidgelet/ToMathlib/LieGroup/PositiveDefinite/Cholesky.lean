/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Matrix.LDL

/-!
# The Cholesky diagonal of a positive definite real matrix

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

On the symmetric space `ℙ_m = GL(m,ℝ)/O(m)` of positive definite matrices the Iwasawa
decomposition `G = KAN` is the Cholesky decomposition: every `x ∈ ℙ_m` factors as
`x = ν λ ν^⊤` with `ν` unit lower triangular (the `N` part) and `λ` positive diagonal (the `A`
part), and the composite distance of the Helgason--Fourier theory is `⟨x, kM⟩ = ½ log λ(k^⊤ x k)`.

**Mathlib already has this decomposition**, as `LDL.lower_conj_diag`: it builds `L` by
Gram--Schmidt with respect to the inner product induced by the matrix, which produces exactly a
unit lower triangular factor. What the symmetric-space theory needs on top of it is that the
diagonal factor is *positive*, so that its logarithm is defined. That is what this file adds.

The positivity is not a computation: conjugating a positive definite matrix by an invertible one
preserves positive definiteness, and a positive definite matrix has positive diagonal entries.

## Main definitions

* `Matrix.choleskyDiag`: the diagonal `λ` of the Cholesky decomposition of a positive definite
  real matrix, as a function on the index type.
* `Matrix.choleskyDiagTotal`: the same as a total function, junk `1` off the positive definite
  matrices, so that it can be used inside a definition without carrying a proof.

## Main results

* `Matrix.choleskyDiag_pos`: it is positive, so `log ∘ choleskyDiag` is defined. This is the
  scalar-valued datum out of which the composite distance of `ℙ_m` is built.
* `Matrix.cholesky_conj_diag`: the decomposition itself, `L * diagonal (choleskyDiag) * L^⊤ = S`,
  restated over `ℝ` with the transpose in place of the conjugate transpose.
* `Matrix.posDef_transpose_mul_mul`: conjugating a positive definite matrix by an invertible one,
  `g^⊤ S g`, is positive definite. On the symmetric space `ℙ_m` this is the statement that the
  action of `GL(m,ℝ)` preserves the space.
-/

@[expose] public section

noncomputable section

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]
variable {S : Matrix n n ℝ}

/-- The diagonal factor of the Cholesky decomposition of a positive definite real matrix, as a
function on the index type: the vector `λ` in `x = ν λ ν^⊤` with `ν` unit lower triangular.

This is Mathlib's `LDL.diagEntries` under a name that matches the use made of it on the symmetric
space `ℙ_m`, where the Cholesky decomposition is the Iwasawa decomposition. -/
def choleskyDiag (hS : S.PosDef) : n → ℝ := LDL.diagEntries hS

theorem choleskyDiag_eq (hS : S.PosDef) : choleskyDiag hS = LDL.diagEntries hS := rfl

/-- The diagonal matrix of the Cholesky decomposition is positive definite: it is the conjugate of
`S` by the invertible matrix `LDL.lowerInv`. -/
theorem posDef_ldlDiag (hS : S.PosDef) : (LDL.diag hS).PosDef := by
  classical
  have hunit : IsUnit (LDL.lowerInv hS) := isUnit_of_invertible _
  have h : LDL.diag hS = LDL.lowerInv hS * S * star (LDL.lowerInv hS) := by
    rw [LDL.diag_eq_lowerInv_conj hS, star_eq_conjTranspose]
  rw [h]
  exact (hunit.posDef_star_right_conjugate_iff).2 hS

/-- **The Cholesky diagonal is positive.** This is what makes `log ∘ choleskyDiag` — and with it
the composite distance `⟨x, kM⟩ = ½ log λ(k^⊤ x k)` of the symmetric space `ℙ_m` — well defined. -/
theorem choleskyDiag_pos (hS : S.PosDef) (i : n) : 0 < choleskyDiag hS i := by
  classical
  have h := (posDef_ldlDiag hS).diag_pos (i := i)
  rwa [LDL.diag, diagonal_apply_eq] at h

/-- **The Cholesky decomposition** of a positive definite real matrix, `S = L D L^⊤` with `L` unit
lower triangular and `D` the positive diagonal matrix of `Matrix.choleskyDiag`.

This is `LDL.lower_conj_diag` over `ℝ`, where the conjugate transpose is the transpose. -/
theorem cholesky_conj_diag (hS : S.PosDef) :
    LDL.lower hS * Matrix.diagonal (choleskyDiag hS) * (LDL.lower hS)ᵀ = S := by
  classical
  have h := LDL.lower_conj_diag hS
  rwa [LDL.diag, conjTranspose_eq_transpose_of_trivial] at h

/-! ## The total Cholesky diagonal -/

/-- The Cholesky diagonal as a *total* function of the matrix, taking the junk value `1` off the
positive definite matrices.

The composite distance of `ℙ_m` is `⟨x, kM⟩ = ½ log λ(k^⊤ x k)`, and reading it as a plain function
of the matrix — rather than one carrying a positive-definiteness proof — is what lets it be used
inside the definition of the Helgason--Fourier transform. The junk value is `1` rather than `0` so
that the total function is positive everywhere and its logarithm is defined. -/
def choleskyDiagTotal (S : Matrix n n ℝ) : n → ℝ :=
  @dite _ S.PosDef (Classical.dec _) (fun h => choleskyDiag h) fun _ => 1

theorem choleskyDiagTotal_of_posDef (hS : S.PosDef) : choleskyDiagTotal S = choleskyDiag hS := by
  simp only [choleskyDiagTotal, dif_pos hS]

theorem choleskyDiagTotal_of_not_posDef {S : Matrix n n ℝ} (hS : ¬ S.PosDef) :
    choleskyDiagTotal S = 1 := by
  simp only [choleskyDiagTotal, dif_neg hS]

theorem choleskyDiagTotal_pos (S : Matrix n n ℝ) (i : n) : 0 < choleskyDiagTotal S i := by
  by_cases h : S.PosDef
  · rw [choleskyDiagTotal_of_posDef h]
    exact choleskyDiag_pos h i
  · rw [choleskyDiagTotal_of_not_posDef h]
    exact zero_lt_one

theorem choleskyDiagTotal_ne_zero (S : Matrix n n ℝ) (i : n) : choleskyDiagTotal S i ≠ 0 :=
  ne_of_gt (choleskyDiagTotal_pos S i)

/-! ## The action of the general linear group -/

omit [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n] in
/-- Conjugating a positive definite matrix by an invertible one preserves positive definiteness:
`g^⊤ S g` is positive definite. This is the action `g · x = g x g^⊤` of `GL(m,ℝ)` on the symmetric
space `ℙ_m` of positive definite matrices, read with `g^⊤` in place of `g`. -/
theorem posDef_transpose_mul_mul [DecidableEq n] {g : Matrix n n ℝ} (hg : IsUnit g)
    (hS : S.PosDef) : (gᵀ * S * g).PosDef := by
  have h : star g = gᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [← h]
  exact (hg.posDef_star_left_conjugate_iff).2 hS

end Matrix

end

end
