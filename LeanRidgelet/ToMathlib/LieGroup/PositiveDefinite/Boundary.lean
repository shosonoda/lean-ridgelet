/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.HelgasonFourier

/-!
# The boundary of `ℙ_m` is a quotient, and the composite distance descends to it

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

The boundary of `ℙ_m = GL(m,ℝ)/O(m)` is `K/M = O(m)/D_{±1}`, the orthogonal group modulo the
diagonal matrices of signs. `LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.HelgasonFourier`
integrates over `O(m)` itself rather than over the quotient, and justifies that by the
`M`-invariance of the composite distance. This file proves that invariance, at the level of the
orthogonal group rather than at the level of matrices: `Matrix.cornerDet_conj_diagonal_sign` is a
statement about conjugating a matrix, and what the justification needs is a statement about
multiplying a boundary point by an element of `M`.

The two are separated by the star-algebra equivalence between matrices and operators on
`EuclideanSpace`, which is how the orthogonal group is presented throughout this development —
coordinate-free, as the unitary group of an operator algebra. Being an algebra map it carries the
sign matrices into the unitary group and turns multiplication of boundary points into multiplication
of matrices, which is all that is needed.

## Main definitions

* `SpdSpace.signUnitary`: an element of `M = D_{±1}` as a boundary point.

## Main results

* `SpdSpace.boundaryMatrix_mul`: the matrix of a product is the product of the matrices.
* `SpdSpace.compositeDistance_mul_signUnitary`: **the composite distance is `M`-invariant**, so it
  is a function on `K/M` and the integral over `O(m)` is the integral over the boundary.
* `SpdSpace.helgasonFourier_mul_signUnitary`: consequently the Helgason--Fourier transform of `ℙ_m`
  is `M`-invariant in its boundary argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace SpdSpace

variable {m : ℕ}

/-! ## The matrix of a boundary point -/

/-- The matrix of a product of boundary points is the product of their matrices: the map is the
inverse of a star-algebra equivalence. -/
theorem boundaryMatrix_mul (Q R : Boundary m) :
    boundaryMatrix (Q * R) = boundaryMatrix Q * boundaryMatrix R := by
  simp only [boundaryMatrix, Submonoid.coe_mul, map_mul]

@[simp] theorem boundaryMatrix_one : boundaryMatrix (1 : Boundary m) = 1 := by
  simp only [boundaryMatrix, Submonoid.coe_one, map_one]

/-! ## The finite factor `M = D_{±1}` -/

/-- **An element of `M = D_{±1}` as a boundary point.** A diagonal matrix of signs is orthogonal, so
it is a unitary of the operator algebra; the hypothesis is carried in the definition because there
is no reason to name the non-orthogonal diagonal matrices. -/
def signUnitary (d : Fin m → ℝ) (hd : ∀ p, d p = 1 ∨ d p = -1) : Boundary m :=
  ⟨Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (Matrix.diagonal d), by
    have hstar : star (Matrix.diagonal d) = Matrix.diagonal d := by
      rw [star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      simp
    refine Unitary.mem_iff.2 ⟨?_, ?_⟩ <;>
      rw [← map_star, hstar, ← map_mul, Matrix.diagonal_sign_mul_self hd, map_one]⟩

@[simp] theorem boundaryMatrix_signUnitary (d : Fin m → ℝ) (hd : ∀ p, d p = 1 ∨ d p = -1) :
    boundaryMatrix (signUnitary d hd) = Matrix.diagonal d := by
  simp only [boundaryMatrix, signUnitary, StarAlgEquiv.symm_apply_apply]

/-! ## `M`-invariance -/

/-- **The composite distance of `ℙ_m` is `M`-invariant.** Multiplying a boundary point on the right
by a diagonal matrix of signs conjugates the argument of the leading principal minors by that
matrix, and `Matrix.cornerDetTotal_conj_diagonal_sign` says the minors do not see it.

This is what makes the Helgason--Fourier transform of `ℙ_m` an integral over the boundary
`K/M = O(m)/D_{±1}` even though it is written as an integral over `O(m)`: the integrand is constant
on the fibres of `O(m) → K/M`. -/
theorem compositeDistance_mul_signUnitary (c : EuclideanSpace ℝ (UpperIdx m)) (Q : Boundary m)
    (d : Fin m → ℝ) (hd : ∀ p, d p = 1 ∨ d p = -1) :
    compositeDistance c (Q * signUnitary d hd) = compositeDistance c Q := by
  have hkey : (boundaryMatrix (Q * signUnitary d hd))ᵀ * ofUpper c *
        boundaryMatrix (Q * signUnitary d hd)
      = Matrix.diagonal d * ((boundaryMatrix Q)ᵀ * ofUpper c * boundaryMatrix Q) *
        (Matrix.diagonal d)ᵀ := by
    rw [boundaryMatrix_mul, boundaryMatrix_signUnitary]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, mul_assoc]
  ext i
  simp only [compositeDistance_apply, hkey, Matrix.cornerDetTotal_conj_diagonal_sign hd]

/-- The Helgason--Fourier transform of `ℙ_m` is `M`-invariant in its boundary argument, and so is a
function on `K/M`. Immediate from the `M`-invariance of the composite distance, the transform
depending on the boundary point through nothing else. -/
theorem helgasonFourier_mul_signUnitary (rho : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (UpperIdx m) → ℂ) (lam : EuclideanSpace ℝ (Fin m)) (Q : Boundary m)
    (d : Fin m → ℝ) (hd : ∀ p, d p = 1 ∨ d p = -1) :
    helgasonFourier rho f lam (Q * signUnitary d hd) = helgasonFourier rho f lam Q := by
  simp only [helgasonFourier_eq, compositeDistance_mul_signUnitary]

end SpdSpace

end

end
