/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.Cholesky
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Leading principal minors, and the coordinates of harmonic analysis on `ℙ_m`

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Harmonic analysis on the symmetric space `ℙ_m = GL(m,ℝ)/O(m)` is written, following A. Terras,
*Harmonic Analysis on Symmetric Spaces*, Ch. 1, in terms of the **power function**

`p_s(Y) = ∏_j |Y_j|^{s_j}`,

where `Y_j` is the upper-left `j × j` corner of `Y`. So the composite distance of `ℙ_m` in those
coordinates is the vector `j ↦ log|Y_j|` of logarithms of the leading principal minors, and this
file supplies it.

*Why these coordinates and not the Cholesky diagonal.* The article being formalized writes the
composite distance as `½ log λ`, with `λ` the diagonal of the Cholesky decomposition. The two are
equivalent — `|Y_j| = ∏_{i ≤ j} λ_i`, recorded here as `Matrix.cornerDet_of_ldl`, so the corner
determinants are the partial products of the Cholesky diagonal — but they are not equally easy to
work with. The composite distance has to be shown invariant under the nilpotent factor `N` of the
Iwasawa decomposition and under `M = D_{±1}`, the first because horospheres are `N`-orbits and the
second because the boundary is `K/M` rather than `K`. In the Cholesky diagonal those two facts need
*uniqueness* of the LDL decomposition, which Mathlib does not have. In the corner determinants they
are elementary, and that is what this file exploits: for lower triangular `L` the corner of a
conjugate is the conjugate of the corner,

`(L Y Lᵀ)_j = L_j Y_j L_jᵀ`,

because the first `j` rows of a lower triangular matrix are supported in the first `j` columns; and
`det L_j = 1` when `L` has unit diagonal, and `(det L_j)² = 1` when `L` is a sign matrix.

## Main definitions

* `Matrix.cornerDet`: the determinant of the upper-left `(i+1) × (i+1)` corner.
* `Matrix.cornerDetTotal`: the same with junk value `1` off the positive definite matrices, so that
  it can be used inside a definition without carrying a proof.

## Main results

* `Matrix.submatrix_cornerEmb_mul_of_lowerTriangular`: the corner of `L * Y` is the product of the
  corners, for lower triangular `L`. This is the one computation in the file.
* `Matrix.cornerDet_conj_of_lowerTriangular_unit`: `N`-invariance,
  `cornerDet (L Y Lᵀ) = cornerDet Y` for `L` lower triangular with unit diagonal.
* `Matrix.cornerDet_conj_diagonal_sign`: `M`-invariance, conjugation by a `±1` diagonal matrix,
  and `Matrix.cornerDetTotal_conj_diagonal_sign` for the total form.
* `Matrix.cornerDet_of_ldl`: the dictionary to the Cholesky diagonal, `|Y_j| = ∏_{i ≤ j} λ_i`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Matrix

variable {m : ℕ}

/-! ## The leading principal minors -/

/-- The inclusion of the upper-left `(i+1) × (i+1)` corner into the whole index set. Naming it keeps
`Fin.castLE i.isLt` — whose proof argument has type `↑i < m` where `Fin.castLE` wants `↑i + 1 ≤ m` —
from appearing in every statement, where the mismatch obstructs rewriting. -/
def cornerEmb (i : Fin m) : Fin (i + 1) → Fin m := Fin.castLE i.isLt

@[simp] theorem coe_cornerEmb (i : Fin m) (a : Fin (i + 1)) :
    ((cornerEmb i a : Fin m) : ℕ) = (a : ℕ) := rfl

theorem cornerEmb_injective (i : Fin m) : Function.Injective (cornerEmb i) :=
  Fin.castLE_injective _

/-- The determinant of the upper-left `(i+1) × (i+1)` corner of `Y`, the `(i+1)`-st leading
principal minor. Terras' power function on `ℙ_m` is the product of real powers of these. -/
def cornerDet (Y : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : ℝ :=
  (Y.submatrix (cornerEmb i) (cornerEmb i)).det

theorem posDef_submatrix_cornerEmb {Y : Matrix (Fin m) (Fin m) ℝ} (hY : Y.PosDef) (i : Fin m) :
    (Y.submatrix (cornerEmb i) (cornerEmb i)).PosDef :=
  hY.submatrix (cornerEmb_injective i)

/-- The leading principal minors of a positive definite matrix are positive: each corner is itself
positive definite, and a positive definite matrix has positive determinant. -/
theorem cornerDet_pos {Y : Matrix (Fin m) (Fin m) ℝ} (hY : Y.PosDef) (i : Fin m) :
    0 < cornerDet Y i :=
  (posDef_submatrix_cornerEmb hY i).det_pos

/-- The leading principal minors as a *total* function of the matrix, junk value `1` off the
positive definite matrices, so that the composite distance of `ℙ_m` can be a plain function. -/
def cornerDetTotal (Y : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : ℝ :=
  @dite _ Y.PosDef (Classical.dec _) (fun _ => cornerDet Y i) fun _ => 1

theorem cornerDetTotal_of_posDef {Y : Matrix (Fin m) (Fin m) ℝ} (hY : Y.PosDef) :
    cornerDetTotal Y = cornerDet Y := by
  funext i
  simp only [cornerDetTotal, dif_pos hY]

theorem cornerDetTotal_of_not_posDef {Y : Matrix (Fin m) (Fin m) ℝ} (hY : ¬ Y.PosDef) :
    cornerDetTotal Y = 1 := by
  funext i
  simp only [cornerDetTotal, dif_neg hY, Pi.one_apply]

theorem cornerDetTotal_pos (Y : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    0 < cornerDetTotal Y i := by
  by_cases h : Y.PosDef
  · rw [cornerDetTotal_of_posDef h]
    exact cornerDet_pos h i
  · rw [cornerDetTotal_of_not_posDef h]
    exact zero_lt_one

theorem cornerDetTotal_ne_zero (Y : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    cornerDetTotal Y i ≠ 0 :=
  ne_of_gt (cornerDetTotal_pos Y i)

/-! ## The corner of a product with a lower triangular factor -/

/-- **The one computation in this file.** For `L` lower triangular, the corner of `L * Y` is the
product of the corners.

The reason is that the first `i+1` rows of a lower triangular matrix are supported in the first
`i+1` columns, so in the sum defining `(L * Y) (e a) (e b)` every term whose summation index lies
beyond the corner has `L (e a) k = 0`. -/
theorem submatrix_cornerEmb_mul_of_lowerTriangular {L Y : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (i : Fin m) :
    (L * Y).submatrix (cornerEmb i) (cornerEmb i)
      = (L.submatrix (cornerEmb i) (cornerEmb i)) * (Y.submatrix (cornerEmb i) (cornerEmb i)) := by
  ext a b
  simp only [submatrix_apply, mul_apply]
  symm
  have hmap : (∑ c : Fin (i + 1),
        L (cornerEmb i a) (cornerEmb i c) * Y (cornerEmb i c) (cornerEmb i b))
      = ∑ k ∈ Finset.univ.map (Fin.castLEEmb i.isLt),
        L (cornerEmb i a) k * Y k (cornerEmb i b) :=
    (Finset.sum_map Finset.univ (Fin.castLEEmb i.isLt)
      fun k => L (cornerEmb i a) k * Y k (cornerEmb i b)).symm
  rw [hmap]
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
  have hik : (i : ℕ) < (k : ℕ) := by
    by_contra hcon
    exact hk (Finset.mem_map.2 ⟨⟨(k : ℕ), by omega⟩, Finset.mem_univ _, by ext; simp⟩)
  have hak : cornerEmb i a < k := by
    have ha : (a : ℕ) ≤ (i : ℕ) := by omega
    rw [Fin.lt_def, coe_cornerEmb]
    omega
  rw [hL _ _ hak, zero_mul]

/-- The transposed companion: for `L` lower triangular, the corner of `Y * Lᵀ` is the product of the
corners. -/
theorem submatrix_cornerEmb_mul_transpose_of_lowerTriangular {L Y : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (i : Fin m) :
    (Y * Lᵀ).submatrix (cornerEmb i) (cornerEmb i)
      = (Y.submatrix (cornerEmb i) (cornerEmb i)) *
        (L.submatrix (cornerEmb i) (cornerEmb i))ᵀ := by
  calc (Y * Lᵀ).submatrix (cornerEmb i) (cornerEmb i)
      = ((L * Yᵀ)ᵀ).submatrix (cornerEmb i) (cornerEmb i) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = ((L * Yᵀ).submatrix (cornerEmb i) (cornerEmb i))ᵀ := by
        rw [← Matrix.transpose_submatrix]
    _ = ((L.submatrix (cornerEmb i) (cornerEmb i)) *
          (Yᵀ.submatrix (cornerEmb i) (cornerEmb i)))ᵀ := by
        rw [submatrix_cornerEmb_mul_of_lowerTriangular hL i]
    _ = (Yᵀ.submatrix (cornerEmb i) (cornerEmb i))ᵀ *
          (L.submatrix (cornerEmb i) (cornerEmb i))ᵀ := by
        rw [Matrix.transpose_mul]
    _ = (Y.submatrix (cornerEmb i) (cornerEmb i)) *
          (L.submatrix (cornerEmb i) (cornerEmb i))ᵀ := by
        rw [← Matrix.transpose_submatrix, Matrix.transpose_transpose]

/-- The corner of a conjugate by a lower triangular matrix is the conjugate of the corner. -/
theorem submatrix_cornerEmb_conj_of_lowerTriangular {L Y : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (i : Fin m) :
    (L * Y * Lᵀ).submatrix (cornerEmb i) (cornerEmb i)
      = (L.submatrix (cornerEmb i) (cornerEmb i)) * (Y.submatrix (cornerEmb i) (cornerEmb i)) *
        (L.submatrix (cornerEmb i) (cornerEmb i))ᵀ := by
  rw [submatrix_cornerEmb_mul_transpose_of_lowerTriangular hL i,
    submatrix_cornerEmb_mul_of_lowerTriangular hL i]

/-! ## Invariance of the leading principal minors -/

/-- The corner of a lower triangular matrix is lower triangular. -/
theorem blockTriangular_submatrix_cornerEmb {L : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (i : Fin m) :
    (L.submatrix (cornerEmb i) (cornerEmb i)).BlockTriangular OrderDual.toDual := by
  intro p q hpq
  have h : p < q := hpq
  refine hL _ _ ?_
  rw [Fin.lt_def, coe_cornerEmb, coe_cornerEmb]
  exact Fin.lt_def.1 h

/-- The determinant of the corner of a lower triangular matrix is the product of the first diagonal
entries. -/
theorem det_submatrix_cornerEmb_of_lowerTriangular {L : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (i : Fin m) :
    (L.submatrix (cornerEmb i) (cornerEmb i)).det
      = ∏ c : Fin (i + 1), L (cornerEmb i c) (cornerEmb i c) :=
  Matrix.det_of_lowerTriangular _ (blockTriangular_submatrix_cornerEmb hL i)

/-- **`N`-invariance of the leading principal minors.** Conjugating by a lower triangular matrix
with unit diagonal does not change them. Horospheres in `ℙ_m` are the orbits of the nilpotent factor
of the Iwasawa decomposition, so this is what makes the composite distance a function of the
horosphere.

In the Cholesky diagonal the same statement needs uniqueness of the LDL decomposition, which Mathlib
does not have; here it is the corner identity together with `det L_j = 1`. -/
theorem cornerDet_conj_of_lowerTriangular_unit {L Y : Matrix (Fin m) (Fin m) ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (hd : ∀ p, L p p = 1) (i : Fin m) :
    cornerDet (L * Y * Lᵀ) i = cornerDet Y i := by
  rw [cornerDet, cornerDet, submatrix_cornerEmb_conj_of_lowerTriangular hL i, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, det_submatrix_cornerEmb_of_lowerTriangular hL i]
  simp [hd]

/-- **`M`-invariance of the leading principal minors.** Conjugating by a diagonal matrix of signs
does not change them, because the corner determinant of such a matrix squares to `1`. The boundary
of `ℙ_m` is `K/M` with `M = D_{±1}`, so this is what makes the composite distance well defined on
the boundary. -/
theorem cornerDet_conj_diagonal_sign {Y : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hd : ∀ p, d p = 1 ∨ d p = -1) (i : Fin m) :
    cornerDet (diagonal d * Y * (diagonal d)ᵀ) i = cornerDet Y i := by
  have hL : ∀ p q : Fin m, p < q → diagonal d p q = 0 := fun p q hpq =>
    diagonal_apply_ne d (ne_of_lt hpq)
  have hsq : ∀ p : Fin m, d p * d p = 1 := by
    intro p
    rcases hd p with h | h <;> rw [h] <;> norm_num
  rw [cornerDet, cornerDet, submatrix_cornerEmb_conj_of_lowerTriangular hL i, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, det_submatrix_cornerEmb_of_lowerTriangular hL i]
  simp only [diagonal_apply_eq]
  have hprod : (∏ c : Fin (i + 1), d (cornerEmb i c)) * (∏ c : Fin (i + 1), d (cornerEmb i c))
      = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [hsq]
  linear_combination (Y.submatrix (cornerEmb i) (cornerEmb i)).det * hprod

/-! ## The total form under a sign conjugation -/

/-- A diagonal matrix of signs is its own inverse. -/
theorem diagonal_sign_mul_self {d : Fin m → ℝ} (hd : ∀ p, d p = 1 ∨ d p = -1) :
    diagonal d * diagonal d = 1 := by
  have hdd : (fun p => d p * d p) = (1 : Fin m → ℝ) := by
    funext p
    rcases hd p with h | h <;> simp [h]
  rw [diagonal_mul_diagonal, hdd, diagonal_one']

theorem isUnit_diagonal_sign {d : Fin m → ℝ} (hd : ∀ p, d p = 1 ∨ d p = -1) :
    IsUnit (diagonal d) :=
  ⟨⟨diagonal d, diagonal d, diagonal_sign_mul_self hd, diagonal_sign_mul_self hd⟩, rfl⟩

/-- Conjugating by a diagonal matrix of signs preserves positive definiteness in both directions,
the conjugation being an involution. -/
theorem posDef_conj_diagonal_sign_iff {Y : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hd : ∀ p, d p = 1 ∨ d p = -1) :
    (diagonal d * Y * (diagonal d)ᵀ).PosDef ↔ Y.PosDef := by
  have hT : (diagonal d)ᵀ = diagonal d := diagonal_transpose d
  have hu := isUnit_diagonal_sign hd
  have hsq := diagonal_sign_mul_self hd
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hc := posDef_transpose_mul_mul hu h
    have key : (diagonal d)ᵀ * (diagonal d * Y * (diagonal d)ᵀ) * diagonal d = Y := by
      rw [hT]
      calc diagonal d * (diagonal d * Y * diagonal d) * diagonal d
          = diagonal d * diagonal d * Y * (diagonal d * diagonal d) := by
            simp only [mul_assoc]
        _ = Y := by rw [hsq, Matrix.one_mul, Matrix.mul_one]
    rwa [key] at hc
  · have hc := posDef_transpose_mul_mul hu h
    rwa [hT] at hc ⊢

/-- **`M`-invariance of the total form of the leading principal minors.** The junk value off the
positive definite cone is unaffected because the conjugation preserves the cone. -/
theorem cornerDetTotal_conj_diagonal_sign {Y : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hd : ∀ p, d p = 1 ∨ d p = -1) (i : Fin m) :
    cornerDetTotal (diagonal d * Y * (diagonal d)ᵀ) i = cornerDetTotal Y i := by
  by_cases hY : Y.PosDef
  · rw [cornerDetTotal_of_posDef ((posDef_conj_diagonal_sign_iff hd).2 hY),
      cornerDetTotal_of_posDef hY, cornerDet_conj_diagonal_sign hd]
  · rw [cornerDetTotal_of_not_posDef fun h => hY ((posDef_conj_diagonal_sign_iff hd).1 h),
      cornerDetTotal_of_not_posDef hY]

/-! ## The dictionary to the Cholesky diagonal -/

/-- **The corner determinants are the partial products of the Cholesky diagonal.** If
`Y = L (diagonal d) Lᵀ` with `L` lower triangular with unit diagonal, then `|Y_j| = ∏_{i ≤ j} d_i`.

This is the translation between the two coordinate systems in which harmonic analysis on `ℙ_m` is
written: the article's composite distance is `½ log λ` in the Cholesky diagonal, Terras' power
function is built from `log|Y_j|`, and the two therefore differ by a triangular partial-sum
substitution. -/
theorem cornerDet_of_ldl {L Y : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hL : ∀ p q : Fin m, p < q → L p q = 0) (hone : ∀ p, L p p = 1)
    (hY : Y = L * diagonal d * Lᵀ) (i : Fin m) :
    cornerDet Y i = ∏ c : Fin (i + 1), d (cornerEmb i c) := by
  have hLd : ∀ p q : Fin m, p < q → diagonal d p q = 0 := fun p q hpq =>
    diagonal_apply_ne d (ne_of_lt hpq)
  rw [hY, cornerDet, submatrix_cornerEmb_conj_of_lowerTriangular hL i, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, det_submatrix_cornerEmb_of_lowerTriangular hL i,
    det_submatrix_cornerEmb_of_lowerTriangular hLd i]
  simp [hone]

end Matrix

end

end
