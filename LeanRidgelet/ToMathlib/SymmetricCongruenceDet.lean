/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The determinant of congruence on symmetric matrices

For a square matrix `M` the *congruence* `A ↦ Mᵀ * A * M` preserves symmetry, hence restricts to
an endomorphism of the space of symmetric matrices.  This file computes the determinant of that
endomorphism:
$$\det\bigl(A\mapsto M^{\mathsf T}AM\bigr)=(\det M)^{n+1}.$$

## Main results

* `Matrix.symmetricSubmodule`: the symmetric matrices as a submodule, with the basis
  `Matrix.symmetricBasis` indexed by the pairs `(i, j)` with `i ≤ j`.
* `Matrix.congrMap M`: the congruence `A ↦ Mᵀ * A * M` as an endomorphism of that submodule.
* `Matrix.det_congrMap`: **the theorem**, `(congrMap M).det = M.det ^ (n + 1)`.
* `ContinuousLinearMap.det_congrSelfAdjoint`: the basis-free form.  For a finite-dimensional real
  inner product space `E` and `M : E →L[ℝ] E`, congruence `A ↦ star M * A * M` on
  `selfAdjoint (E →L[ℝ] E)` has determinant `M.det ^ (finrank ℝ E + 1)`.

## Implementation notes

The basis is obtained from the linear equivalence `Matrix.symmetricEquivFun` sending a symmetric
matrix to its entries above the diagonal; `Basis.ofEquivFun` then produces the expected basis
`E i i` for `i = j` and `E i j + E j i` for `i < j`, but without any linear independence or
spanning argument.

The determinant is computed by the standard reduction of `M` to diagonal matrices and
transvections (`Matrix.diagonal_transvection_induction_of_det_ne_zero`):

* `M ↦ (congrMap M).det` turns products into products, because `congrMap` is an
  anti-homomorphism and the target is commutative (`Matrix.det_congrMap_mul`);
* on `diagonal d` the congruence is diagonal in the above basis, with eigenvalue `d i * d j` at
  the index `(i, j)`, and `∏_{i ≤ j} d i * d j = (∏ i, d i) ^ (n + 1)` because each index `i`
  occurs `(n - i) + (i + 1) = n + 1` times (`Matrix.det_congrMap_diagonal`);
* on a transvection `T = transvection i j c` the determinant is `1`
  (`Matrix.det_congrMap_transvection`).  This is proved without any nilpotency argument: writing
  `f c := (congrMap (transvection i j c)).det`, the identity
  `transvection i j c * transvection i j c' = transvection i j (c + c')` gives
  `f (2 * c) = f c ^ 2`, while conjugating `transvection i j c` by a diagonal matrix rescales `c`
  and gives `f (2 * c) = f c`; as `f c ≠ 0` this forces `f c = 1`.

Singular `M` are handled separately: if `det M = 0` then `Mᵀ *ᵥ v = 0` for some `v ≠ 0`, and the
symmetric matrix `vecMulVec v v ≠ 0` lies in the kernel of `congrMap M`.

Everything is stated over `ℝ`, which is what the intended application needs; the only place where
the base field matters is `Matrix.det_congrMap_transvection`, whose proof uses `(2 : ℝ) ≠ 0`, so
the matrix part of the file generalises verbatim to any field of characteristic `≠ 2`.

The basis-free version is obtained by transporting along the standard orthonormal basis
(`stdOrthonormalBasis`), under which the adjoint becomes the transpose
(`LinearMap.toMatrix_adjoint`) and hence `IsSelfAdjoint` becomes `Matrix.IsSymm`; the star-algebra
equivalence doing that is `ContinuousLinearMap.toMatrixStarAlgEquiv`, and the resulting linear
equivalence of the two coefficient spaces is `ContinuousLinearMap.selfAdjointEquivSymmetric`.
Conjugating by it does not change the determinant (`LinearMap.det_conj`).

The intended application is the relatively invariant measure on the space of positive definite
symmetric matrices: the congruence action of `GL(n, ℝ)` multiplies Lebesgue measure on the
`n (n + 1) / 2`-dimensional space of symmetric matrices by `|det M| ^ (n + 1)`.
-/

@[expose] public section

noncomputable section

open Module

namespace Matrix

variable {n : ℕ}

/-! ### The submodule of symmetric matrices and its basis -/

/-- The symmetric matrices, as a submodule of all matrices. -/
def symmetricSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm}
  add_mem' hA hB := hA.add hB
  zero_mem' := isSymm_zero
  smul_mem' c _ hA := hA.smul c

@[simp]
theorem mem_symmetricSubmodule {A : Matrix (Fin n) (Fin n) ℝ} :
    A ∈ symmetricSubmodule n ↔ A.IsSymm := Iff.rfl

theorem isSymm_coe (A : symmetricSubmodule n) : (A : Matrix (Fin n) (Fin n) ℝ).IsSymm := A.2

/-- The index set of the basis of `Matrix.symmetricSubmodule n`: the pairs `(i, j)` with
`i ≤ j`. -/
abbrev SymIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- A symmetric matrix is determined by, and can be prescribed by, its entries on and above the
diagonal.  This is the linear equivalence recording that. -/
def symmetricEquivFun (n : ℕ) : symmetricSubmodule n ≃ₗ[ℝ] (SymIdx n → ℝ) where
  toFun A p := (A : Matrix (Fin n) (Fin n) ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    ⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else f ⟨(j, i), le_of_not_ge h⟩, by
      refine IsSymm.ext fun i j => ?_
      by_cases hij : i ≤ j
      · by_cases hji : j ≤ i
        · obtain rfl : i = j := le_antisymm hij hji
          rfl
        · simp [hij, hji]
      · have hji : j ≤ i := le_of_not_ge hij
        by_cases h : j = i
        · subst h; rfl
        · simp [hij, hji]⟩
  left_inv A := by
    ext i j
    by_cases hij : i ≤ j
    · simp [hij]
    · simpa [hij] using (isSymm_coe A).apply i j
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    simp [h]

@[simp]
theorem symmetricEquivFun_apply (A : symmetricSubmodule n) (p : SymIdx n) :
    symmetricEquivFun n A p = (A : Matrix (Fin n) (Fin n) ℝ) p.1.1 p.1.2 := rfl

/-- The basis of the symmetric matrices indexed by the pairs `(i, j)` with `i ≤ j`: the basis
vector at `(i, i)` is `Matrix.single i i 1`, and the one at `(i, j)` with `i < j` is
`Matrix.single i j 1 + Matrix.single j i 1`. -/
def symmetricBasis (n : ℕ) : Basis (SymIdx n) ℝ (symmetricSubmodule n) :=
  Basis.ofEquivFun (symmetricEquivFun n)

@[simp]
theorem symmetricBasis_repr (A : symmetricSubmodule n) (p : SymIdx n) :
    (symmetricBasis n).repr A p = (A : Matrix (Fin n) (Fin n) ℝ) p.1.1 p.1.2 := rfl

theorem coe_symmetricBasis_apply (p q : SymIdx n) :
    ((symmetricBasis n p : Matrix (Fin n) (Fin n) ℝ) q.1.1 q.1.2) = if p = q then 1 else 0 := by
  rw [← symmetricBasis_repr, Basis.repr_self, Finsupp.single_apply]

/-! ### The congruence map -/

/-- Congruence by `M`, that is `A ↦ Mᵀ * A * M`, as an endomorphism of the symmetric matrices. -/
def congrMap (M : Matrix (Fin n) (Fin n) ℝ) : symmetricSubmodule n →ₗ[ℝ] symmetricSubmodule n where
  toFun A := ⟨Mᵀ * (A : Matrix (Fin n) (Fin n) ℝ) * M, by
    change (Mᵀ * (A : Matrix (Fin n) (Fin n) ℝ) * M).IsSymm
    simp only [IsSymm, transpose_mul, transpose_transpose, (isSymm_coe A).eq, Matrix.mul_assoc]⟩
  map_add' A B := by ext i j; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by ext i j; simp

@[simp]
theorem coe_congrMap_apply (M : Matrix (Fin n) (Fin n) ℝ) (A : symmetricSubmodule n) :
    (congrMap M A : Matrix (Fin n) (Fin n) ℝ) = Mᵀ * (A : Matrix (Fin n) (Fin n) ℝ) * M := rfl

@[simp]
theorem congrMap_one : congrMap (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id := by
  ext A i j
  simp

/-- Congruence is an anti-homomorphism: `congrMap (M * N) = congrMap N ∘ congrMap M`. -/
theorem congrMap_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    congrMap (M * N) = (congrMap N).comp (congrMap M) := by
  ext A i j
  simp only [LinearMap.comp_apply, coe_congrMap_apply, transpose_mul]
  simp [Matrix.mul_assoc]

/-- The determinant of the congruence is multiplicative in `M`. -/
theorem det_congrMap_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    (congrMap (M * N)).det = (congrMap M).det * (congrMap N).det := by
  rw [congrMap_mul, LinearMap.det_comp, mul_comm]

@[simp]
theorem det_congrMap_one : (congrMap (1 : Matrix (Fin n) (Fin n) ℝ)).det = 1 := by
  rw [congrMap_one, LinearMap.det_id]

/-- The determinant of a congruence never vanishes when `M` is invertible; here is the special
case used below, phrased through an explicit inverse. -/
theorem det_congrMap_ne_zero_of_mul_eq_one {M N : Matrix (Fin n) (Fin n) ℝ} (h : M * N = 1) :
    (congrMap M).det ≠ 0 := by
  intro hM
  have : (congrMap (M * N)).det = 1 := by rw [h, det_congrMap_one]
  rw [det_congrMap_mul, hM, zero_mul] at this
  exact zero_ne_one this

/-! ### The counting identity for the diagonal case -/

/-- Each index `i` occurs `(n - i) + (i + 1) = n + 1` times among the products `d i * d j` over
the pairs `i ≤ j`. -/
theorem prod_symIdx (d : Fin n → ℝ) :
    (∏ p : SymIdx n, d p.1.1 * d p.1.2) = (∏ i, d i) ^ (n + 1) := by
  classical
  have hfilter : ∀ p : Fin n × Fin n,
      p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2) ↔ p.1 ≤ p.2 := by
    intro p; simp
  rw [← Finset.prod_subtype _ hfilter (fun p : Fin n × Fin n => d p.1 * d p.2),
    Finset.prod_filter, Fintype.prod_prod_type]
  have key : ∀ i j : Fin n, (if i ≤ j then d i * d j else 1)
      = (if i ≤ j then d i else 1) * (if i ≤ j then d j else 1) := by
    intro i j; split <;> simp
  simp only [key, Finset.prod_mul_distrib]
  have h1 : ∀ i : Fin n, (∏ _j ∈ Finset.univ.filter (fun j : Fin n => i ≤ j), d i)
      = d i ^ (n - (i : ℕ)) := by
    intro i
    rw [Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun j : Fin n => i ≤ j) = Finset.Ici i by ext j; simp,
      Fin.card_Ici]
  have h2 : ∀ j : Fin n, (∏ _i ∈ Finset.univ.filter (fun i : Fin n => i ≤ j), d j)
      = d j ^ ((j : ℕ) + 1) := by
    intro j
    rw [Finset.prod_const]
    congr 1
    rw [show Finset.univ.filter (fun i : Fin n => i ≤ j) = Finset.Iic j by ext i; simp,
      Fin.card_Iic]
  rw [show (∏ i : Fin n, ∏ j : Fin n, if i ≤ j then d i else 1)
      = ∏ i : Fin n, d i ^ (n - (i : ℕ)) from
    Finset.prod_congr rfl fun i _ => by rw [← Finset.prod_filter, h1 i],
    show (∏ i : Fin n, ∏ j : Fin n, if i ≤ j then d j else 1)
      = ∏ j : Fin n, d j ^ ((j : ℕ) + 1) from by
        rw [Finset.prod_comm]
        exact Finset.prod_congr rfl fun j _ => by rw [← Finset.prod_filter, h2 j],
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  have := i.isLt
  omega

/-! ### Diagonal matrices -/

/-- Congruence by a diagonal matrix is diagonal in the basis `Matrix.symmetricBasis`, with
eigenvalue `d i * d j` at the index `(i, j)`. -/
theorem toMatrix_congrMap_diagonal (d : Fin n → ℝ) :
    LinearMap.toMatrix (symmetricBasis n) (symmetricBasis n) (congrMap (diagonal d)) =
      Matrix.diagonal fun p : SymIdx n => d p.1.1 * d p.1.2 := by
  ext p q
  rw [LinearMap.toMatrix_apply, symmetricBasis_repr, coe_congrMap_apply, diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, coe_symmetricBasis_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h, Ne.symm h]

theorem det_congrMap_diagonal (d : Fin n → ℝ) :
    (congrMap (diagonal d)).det = (diagonal d).det ^ (n + 1) := by
  rw [← LinearMap.det_toMatrix (symmetricBasis n), toMatrix_congrMap_diagonal, Matrix.det_diagonal,
    Matrix.det_diagonal, prod_symIdx]

/-! ### Transvections -/

/-- Conjugating a transvection by a diagonal matrix rescales its parameter.  Only diagonal
matrices with a single entry `t` at the index `i` and `1` elsewhere are needed. -/
theorem diagonal_mul_transvection {i j : Fin n} (hij : i ≠ j) (c t : ℝ) :
    diagonal (fun k : Fin n => if k = i then t else 1) * transvection i j c =
      transvection i j (t * c) * diagonal (fun k : Fin n => if k = i then t else 1) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [transvection, Matrix.add_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.one_apply_ne hij, Ne.symm hij]
  · rw [if_neg h, if_neg h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]

/-- **Congruence by a transvection has determinant one.**

Write `f e` for the determinant of congruence by `transvection i j e`.  Adding the parameters
multiplies the determinants, so `f (2 * c) = f c ^ 2`; conjugating by the diagonal matrix with a
single entry `2` doubles the parameter without changing the determinant, so `f (2 * c) = f c`.
Since `f c ≠ 0`, these force `f c = 1`. -/
theorem det_congrMap_transvection {i j : Fin n} (hij : i ≠ j) (c : ℝ) :
    (congrMap (transvection i j c)).det = 1 := by
  have hne : ∀ e : ℝ, (congrMap (transvection i j e)).det ≠ 0 := by
    intro e
    refine det_congrMap_ne_zero_of_mul_eq_one (N := transvection i j (-e)) ?_
    rw [transvection_mul_transvection_same _ _ hij, add_neg_cancel, transvection_zero]
  have hD : (congrMap (diagonal fun k : Fin n => if k = i then (2 : ℝ) else 1)).det ≠ 0 := by
    rw [det_congrMap_diagonal, Matrix.det_diagonal]
    refine pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    split <;> norm_num
  have hconj : (congrMap (transvection i j (2 * c))).det
      = (congrMap (transvection i j c)).det := by
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => (congrMap N).det)
      (diagonal_mul_transvection hij c 2)
    simp only [det_congrMap_mul] at h
    exact (mul_left_cancel₀ hD (h.trans (mul_comm _ _))).symm
  have hsq : (congrMap (transvection i j (2 * c))).det
      = (congrMap (transvection i j c)).det * (congrMap (transvection i j c)).det := by
    rw [two_mul, ← transvection_mul_transvection_same _ _ hij, det_congrMap_mul]
  refine (mul_left_cancel₀ (hne c) ?_).symm
  rw [mul_one]
  exact hconj.symm.trans hsq

/-! ### The determinant of a congruence -/

/-- The determinant of congruence by an invertible matrix. -/
theorem det_congrMap_of_det_ne_zero (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    (congrMap M).det = M.det ^ (n + 1) := by
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun N => (congrMap N).det = N.det ^ (n + 1)) M hM (fun D _ => det_congrMap_diagonal D)
    (fun t => ?_) (fun A B _ _ hA hB => ?_)
  · obtain ⟨a, b, hab, e⟩ := t
    rw [TransvectionStruct.toMatrix_mk, det_congrMap_transvection hab,
      det_transvection_of_ne _ _ hab, one_pow]
  · rw [det_congrMap_mul, hA, hB, Matrix.det_mul, mul_pow]

/-- **The determinant of congruence on symmetric matrices.**  Congruence by `M`, that is
`A ↦ Mᵀ * A * M`, acts on the `n (n + 1) / 2`-dimensional space of symmetric `n × n` matrices
with determinant `(det M) ^ (n + 1)`. -/
theorem det_congrMap (M : Matrix (Fin n) (Fin n) ℝ) :
    (congrMap M).det = M.det ^ (n + 1) := by
  rcases eq_or_ne M.det 0 with h | h
  · rw [h, zero_pow (Nat.succ_ne_zero n)]
    obtain ⟨v, hv, hMv⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr (show Mᵀ.det = 0 by rwa [det_transpose])
    have hsymm : (vecMulVec v v).IsSymm := by
      refine IsSymm.ext fun a b => ?_
      simp [vecMulVec_apply, mul_comm]
    have hker : Mᵀ * vecMulVec v v * M = 0 := by
      have h0 : Mᵀ * vecMulVec v v = 0 := by
        ext a b
        have ha : (Mᵀ *ᵥ v) a = 0 := by rw [hMv]; rfl
        have hsum : ∑ k, Mᵀ a k * vecMulVec v v k b = (Mᵀ *ᵥ v) a * v b := by
          simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [Matrix.mul_apply, Matrix.zero_apply, hsum, ha, zero_mul]
      rw [h0, Matrix.zero_mul]
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    refine ⟨⟨vecMulVec v v, hsymm⟩, ?_, ?_⟩
    · simpa [LinearMap.mem_ker, Subtype.ext_iff] using hker
    · simpa [Subtype.ext_iff] using hv
  · exact det_congrMap_of_det_ne_zero M h

end Matrix

/-! ### The basis-free version

Congruence on the self-adjoint endomorphisms of a finite-dimensional real inner product space,
obtained from the matrix statement by transporting along the standard orthonormal basis.
-/

namespace ContinuousLinearMap

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Congruence `A ↦ star M * A * M`, that is `A ↦ Mᵀ A M` with the adjoint for transpose, as an
endomorphism of the self-adjoint continuous endomorphisms of `E`. -/
def congrSelfAdjoint (M : E →L[ℝ] E) :
    selfAdjoint (E →L[ℝ] E) →ₗ[ℝ] selfAdjoint (E →L[ℝ] E) where
  toFun A := ⟨star M * (A : E →L[ℝ] E) * M, A.2.conjugate' M⟩
  map_add' A B := by refine Subtype.ext ?_; simp [mul_add, add_mul]
  map_smul' c A := by refine Subtype.ext ?_; simp

@[simp]
theorem coe_congrSelfAdjoint_apply (M : E →L[ℝ] E) (A : selfAdjoint (E →L[ℝ] E)) :
    (congrSelfAdjoint M A : E →L[ℝ] E) = star M * (A : E →L[ℝ] E) * M := rfl

/-- Bundling a linear endomorphism of a finite-dimensional inner product space as a continuous
one is a star-algebra equivalence, the star being the adjoint on either side. -/
def toContinuousStarAlgEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →ₗ[ℝ] E) ≃⋆ₐ[ℝ] (E →L[ℝ] E) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ => rfl
    map_star' := LinearMap.adjoint_toContinuousLinearMap }

/-- The matrix of a continuous endomorphism in the standard orthonormal basis, as a star-algebra
equivalence.  The point is that it carries the adjoint to the transpose. -/
def toMatrixStarAlgEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    (E →L[ℝ] E) ≃⋆ₐ[ℝ] Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
  (toContinuousStarAlgEquiv E).symm.trans
    (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℝ E))

theorem toMatrixStarAlgEquiv_apply (M : E →L[ℝ] E) :
    toMatrixStarAlgEquiv E M = LinearMap.toMatrix (stdOrthonormalBasis ℝ E).toBasis
      (stdOrthonormalBasis ℝ E).toBasis (M : E →ₗ[ℝ] E) := rfl

theorem det_toMatrixStarAlgEquiv (M : E →L[ℝ] E) :
    (toMatrixStarAlgEquiv E M).det = M.det := by
  rw [toMatrixStarAlgEquiv_apply, LinearMap.det_toMatrix]

theorem isSymm_toMatrixStarAlgEquiv {A : E →L[ℝ] E} (hA : IsSelfAdjoint A) :
    (toMatrixStarAlgEquiv E A).IsSymm := by
  have h : star (toMatrixStarAlgEquiv E A) = toMatrixStarAlgEquiv E A := by
    rw [← map_star]
    exact congrArg _ hA
  rw [Matrix.star_eq_conjTranspose] at h
  exact (Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans h

theorem isSelfAdjoint_symm_toMatrixStarAlgEquiv
    {B : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ} (hB : B.IsSymm) :
    IsSelfAdjoint ((toMatrixStarAlgEquiv E).symm B) := by
  have h : star B = B := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hB
  change star ((toMatrixStarAlgEquiv E).symm B) = _
  rw [← map_star]
  exact congrArg _ h

/-- Under the standard orthonormal basis the self-adjoint continuous endomorphisms of `E`
correspond to the symmetric matrices of size `finrank ℝ E`. -/
def selfAdjointEquivSymmetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    selfAdjoint (E →L[ℝ] E) ≃ₗ[ℝ] Matrix.symmetricSubmodule (finrank ℝ E) where
  toFun A := ⟨toMatrixStarAlgEquiv E A, isSymm_toMatrixStarAlgEquiv A.2⟩
  invFun B := ⟨(toMatrixStarAlgEquiv E).symm B, isSelfAdjoint_symm_toMatrixStarAlgEquiv B.2⟩
  map_add' A B := by refine Subtype.ext ?_; simp
  map_smul' c A := by refine Subtype.ext ?_; simp
  left_inv A := by refine Subtype.ext ?_; simp
  right_inv B := by refine Subtype.ext ?_; simp

/-- **The determinant of congruence on self-adjoint operators.**  For `M : E →L[ℝ] E` on a
finite-dimensional real inner product space, the congruence `A ↦ star M * A * M` on the
self-adjoint endomorphisms has determinant `M.det ^ (finrank ℝ E + 1)`.

A `Submodule ℝ (E →L[ℝ] E)` carved out by `IsSelfAdjoint` carries the same coercion to a type and
the same `ℝ`-module structure as `selfAdjoint (E →L[ℝ] E)`, definitionally; the identity map is a
`LinearEquiv` between the two with `rfl` for all four proof fields, so this statement transports
to such a formulation without work. -/
theorem det_congrSelfAdjoint (M : E →L[ℝ] E) :
    LinearMap.det (congrSelfAdjoint M) = M.det ^ (finrank ℝ E + 1) := by
  set e := selfAdjointEquivSymmetric E
  have hconj : (e : selfAdjoint (E →L[ℝ] E) →ₗ[ℝ] Matrix.symmetricSubmodule (finrank ℝ E)) ∘ₗ
      (congrSelfAdjoint M) ∘ₗ
      (e.symm : Matrix.symmetricSubmodule (finrank ℝ E) →ₗ[ℝ] selfAdjoint (E →L[ℝ] E))
      = Matrix.congrMap (toMatrixStarAlgEquiv E M) := by
    refine LinearMap.ext fun B => Subtype.ext ?_
    change toMatrixStarAlgEquiv E (star M * ((toMatrixStarAlgEquiv E).symm B : E →L[ℝ] E) * M)
        = (toMatrixStarAlgEquiv E M)ᵀ * (B : Matrix _ _ ℝ) * toMatrixStarAlgEquiv E M
    rw [map_mul, map_mul, map_star, StarAlgEquiv.apply_symm_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hdet := LinearMap.det_conj (congrSelfAdjoint M) e
  rw [hconj] at hdet
  rw [← hdet, Matrix.det_congrMap, det_toMatrixStarAlgEquiv]

end ContinuousLinearMap
