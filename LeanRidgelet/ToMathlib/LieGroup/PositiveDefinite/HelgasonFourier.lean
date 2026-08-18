/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.CornerDet
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.SpdModel
public import LeanRidgelet.ToMathlib.LieGroup.OrthogonalGroup
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Inversion
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Helgason--Fourier transform on the manifold of positive definite matrices

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

`ℙ_m = GL(m,ℝ)/O(m)` is the second example the Fourier slice article instantiates its Section 5 at,
and the first of higher rank: the rank is `m`, so the scale variable of the network is a vector
rather than a scalar. This file supplies the data of the abstract Helgason--Fourier layer for it and
so turns the inversion formula on `ℙ_m` into a proposition.

The four pieces of data.

* The space is the chart of `LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.SpdModel`, carrying
  the invariant measure `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`.
* `𝔞` is the diagonal, `EuclideanSpace ℝ (Fin m)`, and the composite distance is the vector of
  logarithms of the *leading principal minors*, `⟨x, kM⟩_j = log|(k^⊤ x k)_j|`. With this choice
  `e^{s·⟨x,u⟩}` is exactly Terras' power function `p_s(Y) = ∏_j |Y_j|^{s_j}`, so her contour, her
  constant and her `c`-function apply verbatim. The article writes the composite distance instead as
  `½ log λ` in the Cholesky diagonal; the two are equivalent, `|Y_j| = ∏_{i ≤ j} λ_i`
  (`Matrix.cornerDet_of_ldl`), differing by a triangular partial-sum substitution, but they are not
  equally workable — see `CornerDet.lean` for why the minors are the right primitive.
* The boundary is `K/M = O(m)/D_{±1}`. Rather than construct the quotient, the integral is taken
  over `O(m)` itself with its Haar probability measure, which is legitimate because the composite
  distance is `M`-invariant. That invariance is not left as a remark: it is
  `SpdSpace.compositeDistance_mul_signUnitary` in
  `LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.Boundary`, and in these coordinates its proof is
  elementary — conjugating by a sign matrix multiplies each leading principal minor by the square of
  a sign. The orthogonal group is used in its coordinate-free form, the unitary group of the
  operator algebra, as everywhere else in this development; `boundaryMatrix` is its matrix.
* `ϱ` is **fixed**, to `SpdSpace.spdRho`. Because the composite distance is in Terras' coordinates,
  her contour `Re s = -ρ` with `ρ = (½,…,½,(1-n)/4)` (Thm 1.3.1(1)) transfers directly: the kernel
  here is `e^{(iλ+ϱ)·⟨x,u⟩} = p_{ϱ+iλ}(x[k])`, so `ϱ = -ρ = (-½,…,-½,(m-1)/4)`. That is exactly the
  value the article's appendix states, which is therefore correct and not — as this development
  briefly recorded — a mis-transcription of the half-sum of the positive restricted roots; it is
  Terras' contour, in Terras' coordinates.
* The order of the Weyl group and the `c`-function remain arguments. Terras' `c_n(s)` is an explicit
  product of beta quotients and her `ω_n` an explicit product of gamma factors, both of which now
  apply verbatim; what is not yet pinned is the conversion between her contour integral `ds` over
  `Re s = -ρ` — whose `(2πi)^{-n}` sits inside `ω_n` — and Lebesgue measure `dλ` on `ℝ^m`, which is
  the project's convention. That conversion is a computation, and the discipline here is that
  constants come out of proofs.

## Main definitions

* `SpdSpace.Boundary`: the orthogonal group, standing in for `K/M`.
* `SpdSpace.spdRho`: Terras' `-ρ = (-½,…,-½,(m-1)/4)`, the shift of the transform.
* `SpdSpace.compositeDistance`: `⟨x, kM⟩_j = log|(k^⊤ x k)_j|`, Terras' coordinates.
* `SpdSpace.helgasonFourier`: the Helgason--Fourier transform of `ℙ_m`.
* `SpdSpace.HasInversion`: **the Helgason--Fourier inversion formula on `ℙ_m`**, as a proposition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace SpdSpace

variable {m : ℕ}

/-! ## The boundary -/

/-- The orthogonal group of `ℝ^m`, in the coordinate-free form used throughout this development:
the unitary group of the algebra of continuous operators. It stands in for the boundary
`∂ℙ_m = K/M = O(m)/D_{±1}` of `ℙ_m`, the composite distance being `M`-invariant. -/
abbrev Boundary (m : ℕ) : Type :=
  unitary (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))

/-- The matrix of an element of the orthogonal group, through the star-algebra equivalence between
matrices and operators on `EuclideanSpace`. -/
def boundaryMatrix (Q : Boundary m) : Matrix (Fin m) (Fin m) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))

/-! ## The composite distance -/

/-- **The vector-valued composite distance of `ℙ_m`**, `⟨x, kM⟩_j = log|(k^⊤ x k)_j|`, the vector of
logarithms of the leading principal minors.

The rank of `ℙ_m` is `m`, so this is genuinely vector valued — unlike the rank-one hyperbolic case,
where the composite distance is a scalar. Pairing it against `s` and exponentiating returns Terras'
power function `p_s(Y) = ∏_j|Y_j|^{s_j}` exactly, which is what lets her `ϱ`, `c`-function and
constant be used without a change of variables. The minors are read through
`Matrix.cornerDetTotal`, the total form, so that no positive-definiteness proof has to be carried
into the definition; on the chart the matrix is positive definite and the total form agrees with the
minors. -/
def compositeDistance (c : EuclideanSpace ℝ (UpperIdx m)) (Q : Boundary m) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i =>
    Real.log (Matrix.cornerDetTotal ((boundaryMatrix Q)ᵀ * ofUpper c * boundaryMatrix Q) i)

theorem compositeDistance_apply (c : EuclideanSpace ℝ (UpperIdx m)) (Q : Boundary m) (i : Fin m) :
    compositeDistance c Q i
      = Real.log
        (Matrix.cornerDetTotal ((boundaryMatrix Q)ᵀ * ofUpper c * boundaryMatrix Q) i) := rfl

/-- **Terras' shift** `ϱ = -ρ = (-½,…,-½,(m-1)/4)`, the constant of the Helgason--Fourier transform
of `ℙ_m` in the coordinates of the power function. The last coordinate is the exceptional one; the
contour of the inversion formula is `Re s = ϱ`. -/
def spdRho (m : ℕ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => if (i : ℕ) + 1 = m then ((m : ℝ) - 1) / 4 else -(1 / 2)

/-! ## The transform -/

/-- **The Helgason--Fourier transform on `ℙ_m`**,
`f̂(λ,u) = ∫ f(x) e^{(-iλ+ϱ)⟨x,u⟩} dμ(x)`,
with `μ` the invariant measure of `ℙ_m` and `ϱ` a parameter. -/
def helgasonFourier (rho : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (UpperIdx m) → ℂ) (lam : EuclideanSpace ℝ (Fin m)) (Q : Boundary m) :
    ℂ :=
  SymmetricSpace.helgasonFourier (invariantMeasure m) compositeDistance rho f lam Q

theorem helgasonFourier_eq (rho : EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (UpperIdx m) → ℂ) (lam : EuclideanSpace ℝ (Fin m)) (Q : Boundary m) :
    helgasonFourier rho f lam Q
      = ∫ c : EuclideanSpace ℝ (UpperIdx m), f c *
          SymmetricSpace.horosphericalCharacter rho (-lam) (compositeDistance c Q)
        ∂(invariantMeasure m) := rfl

/-! ## The inversion formula -/

/-- **The Helgason--Fourier inversion formula on `ℙ_m`**, as a proposition:

`f(x) = |W|^{-1} ∫_{𝔞*} ∫_{∂ℙ_m} f̂(λ,u) e^{(iλ+ϱ)⟨x,u⟩} |c(λ)|^{-2} du dλ`

with `dλ` Lebesgue measure on `𝔞* ≅ ℝ^m`, `du` the Haar probability measure of the orthogonal
group, and `dμ` the invariant measure `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`.

Rank `m`, so the frequency is a vector and the Jacobian exponent of the reconstruction formula is
`m` — the opposite extreme from the hyperbolic case, where the rank is one whatever the dimension.
`ϱ` is Terras' `spdRho`; the order of the Weyl group and the `c`-function remain parameters, for
the reason given in the module docstring. -/
def HasInversion (W : ℝ)
    (c : EuclideanSpace ℝ (Fin m) → ℂ) (f : EuclideanSpace ℝ (UpperIdx m) → ℂ) : Prop :=
  SymmetricSpace.HasHelgasonInversion (invariantMeasure m)
    (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (ContinuousLinearMap.orthogonalHaar (E := EuclideanSpace ℝ (Fin m)))
    compositeDistance (spdRho m) W c f

theorem hasInversion_iff (W : ℝ)
    (c : EuclideanSpace ℝ (Fin m) → ℂ) (f : EuclideanSpace ℝ (UpperIdx m) → ℂ) :
    HasInversion W c f
      ↔ ∀ x : EuclideanSpace ℝ (UpperIdx m),
        (∫ lam : EuclideanSpace ℝ (Fin m), (∫ Q : Boundary m,
            helgasonFourier (spdRho m) f lam Q *
            ((SymmetricSpace.plancherelDensity W c lam : ℝ) : ℂ) *
            SymmetricSpace.horosphericalCharacter (spdRho m) lam (compositeDistance x Q)
          ∂(ContinuousLinearMap.orthogonalHaar
            (E := EuclideanSpace ℝ (Fin m)))) ∂(volume)) = f x :=
  Iff.rfl

end SpdSpace

end

end
