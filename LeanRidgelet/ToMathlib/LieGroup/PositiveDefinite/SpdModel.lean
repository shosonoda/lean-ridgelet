/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.Cholesky
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The manifold of positive definite matrices as a measured space

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`ℙ_m = GL(m,ℝ)/O(m)` is the space of symmetric positive definite `m × m` matrices, acted on by
`g · x = g x g^⊤`, with invariant measure

`dμ(x) = |det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`.

Two things have to be arranged before that formula is a measure, and the way they are arranged here
follows the precedent of the hyperbolic ball rather than building manifold theory.

*The carrier.* The formula integrates over the `m(m+1)/2` independent entries of a symmetric matrix,
so the underlying Lebesgue measure lives on the space of *upper-triangular coordinates*, not on all
matrices: restricting Lebesgue measure of `Matrix (Fin m) (Fin m) ℝ` to the symmetric matrices
would give zero, they being a proper subspace. So `ℙ_m` is modelled by the *chart*
`EuclideanSpace ℝ (UpperIdx m)`, on which Lebesgue measure is exactly `∏_{i ≤ j} dx_{ij}`, with
`ofUpper` the symmetric matrix a coordinate vector names. This is the same device as the
singular-value chart of the `d`-plane development, and it also sidesteps a gap: Mathlib gives
`Matrix` neither an inner product nor a measurable space, deliberately not inheriting the `Pi`
instances.

*The positivity.* The measure is concentrated on the positive definite cone by restricting to
`chart m`, the preimage of `ℙ_m` under `ofUpper`. Everything depending on the matrix rather than
its coordinates — the determinant, the Cholesky diagonal of `k^⊤ x k` — is applied through
`ofUpper`, which stays a plain function.

## Main definitions

* `SpdSpace.UpperIdx`: the index type of the upper-triangular coordinates.
* `SpdSpace.ofUpper`: the symmetric matrix with prescribed upper-triangular coordinates.
* `SpdSpace.chart`: the positive definite cone read in those coordinates.
* `SpdSpace.invariantMeasure`: the measure `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}` on the chart.
* `SpdSpace.act`: the action `g · x = g x g^⊤` of `GL(m,ℝ)`.

## Main results

* `SpdSpace.ofUpper_isSymm`: the chart lands in the symmetric matrices.
* `SpdSpace.measurable_ofUpper_apply`: the chart is measurable entrywise.
* `SpdSpace.posDef_act`: the action preserves `ℙ_m`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace SpdSpace

variable {m : ℕ}

/-! ## The chart -/

/-- The index type of the upper-triangular coordinates of a symmetric `m × m` matrix: the pairs
`(i,j)` with `i ≤ j`. Its cardinality is `m(m+1)/2`, the dimension of `ℙ_m`. -/
abbrev UpperIdx (m : ℕ) : Type := {p : Fin m × Fin m // p.1 ≤ p.2}

/-- The symmetric matrix with prescribed upper-triangular coordinates. Together with
`SpdSpace.invariantMeasure` this is the chart in which the article's `∏_{i ≤ j} dx_{ij}` is
Lebesgue measure. -/
def ofUpper (c : EuclideanSpace ℝ (UpperIdx m)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if h : i ≤ j then c ⟨(i, j), h⟩ else c ⟨(j, i), (not_le.1 h).le⟩

theorem ofUpper_apply_of_le (c : EuclideanSpace ℝ (UpperIdx m)) {i j : Fin m} (h : i ≤ j) :
    ofUpper c i j = c ⟨(i, j), h⟩ := by
  simp only [ofUpper, Matrix.of_apply, dif_pos h]

theorem ofUpper_apply_of_not_le (c : EuclideanSpace ℝ (UpperIdx m)) {i j : Fin m}
    (h : ¬ i ≤ j) :
    ofUpper c i j = c ⟨(j, i), (not_le.1 h).le⟩ := by
  simp only [ofUpper, Matrix.of_apply, dif_neg h]

/-- The chart lands in the symmetric matrices. -/
theorem ofUpper_isSymm (c : EuclideanSpace ℝ (UpperIdx m)) : (ofUpper c).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases lt_trichotomy i j with h | h | h
  · rw [ofUpper_apply_of_not_le c (not_le.2 h), ofUpper_apply_of_le c (le_of_lt h)]
  · rw [h]
  · rw [ofUpper_apply_of_le c (le_of_lt h), ofUpper_apply_of_not_le c (not_le.2 h)]

/-- The chart is measurable entrywise. Stated this way because Mathlib puts no measurable space on
`Matrix`, deliberately not inheriting the `Pi` instance. -/
theorem measurable_ofUpper_apply (i j : Fin m) :
    Measurable fun c : EuclideanSpace ℝ (UpperIdx m) => ofUpper c i j := by
  by_cases h : i ≤ j
  · simp only [ofUpper, Matrix.of_apply, dif_pos h]
    fun_prop
  · simp only [ofUpper, Matrix.of_apply, dif_neg h]
    fun_prop

/-! ## The invariant measure -/

/-- The positive definite cone read in the upper-triangular coordinates. -/
def chart (m : ℕ) : Set (EuclideanSpace ℝ (UpperIdx m)) := {c | (ofUpper c).PosDef}

/-- The density `|det x|^{-(m+1)/2}` of the invariant measure of `ℙ_m` against Lebesgue measure in
the upper-triangular coordinates. -/
def invariantDensity (m : ℕ) (c : EuclideanSpace ℝ (UpperIdx m)) : ℝ :=
  |(ofUpper c).det| ^ (-((m : ℝ) + 1) / 2)

/-- **The `G`-invariant measure of `ℙ_m`**, `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`, read on
the chart and concentrated on the positive definite cone.

No manifold theory and no normed-space structure on the symmetric matrices is needed: Lebesgue
measure of the chart *is* `∏_{i ≤ j} dx_{ij}`. The invariance under `g · x = g x g^⊤` is the
Jacobian statement of a later file; here the measure is only defined. -/
def invariantMeasure (m : ℕ) : Measure (EuclideanSpace ℝ (UpperIdx m)) :=
  (volume.restrict (chart m)).withDensity fun c => ENNReal.ofReal (invariantDensity m c)

/-! ## The action of the general linear group -/

/-- The action of `GL(m,ℝ)` on `ℙ_m`, `g · x = g x g^⊤`, which identifies `ℙ_m` with
`GL(m,ℝ)/O(m)` through `gK ↦ g g^⊤`. -/
def act (g x : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ := g * x * gᵀ

@[simp] theorem act_one (x : Matrix (Fin m) (Fin m) ℝ) : act 1 x = x := by
  simp [act]

/-- The action preserves the symmetric matrices. -/
theorem isSymm_act {g x : Matrix (Fin m) (Fin m) ℝ} (hx : x.IsSymm) : (act g x).IsSymm := by
  rw [act, Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hx.eq, Matrix.mul_assoc]

/-- **The action preserves `ℙ_m`.** This is `Matrix.posDef_transpose_mul_mul` read for the action:
`g x g^⊤` is the conjugate of `x` by the invertible matrix `g^⊤`. -/
theorem posDef_act {g x : Matrix (Fin m) (Fin m) ℝ} (hg : IsUnit g) (hx : x.PosDef) :
    (act g x).PosDef := by
  have hgt : IsUnit gᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det] at hg ⊢
    rwa [Matrix.det_transpose]
  have h := Matrix.posDef_transpose_mul_mul hgt hx
  rwa [Matrix.transpose_transpose] at h

end SpdSpace

end

end
