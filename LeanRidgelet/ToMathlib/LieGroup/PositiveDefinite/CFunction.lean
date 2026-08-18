/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.HelgasonFourier
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Terras' explicit `c`-function and constant for `ℙ_m`

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

A. Terras, *Harmonic Analysis on Symmetric Spaces — Higher Rank Spaces, Positive Definite Matrix
Space and Generalizations*, 2nd ed., Springer, 2016, Thm 1.3.1(1) states the Helgason--Fourier
inversion formula on `ℙ_n = GL(n,ℝ)/O(n)` as

`f(Y) = ω_n ∫_{Re s = -ρ} ∫_{K/M} Hf(s,k) p_s(Y[k]) dk |c_n(s)|^{-2} ds`,

with `ρ = (½,…,½,(1-n)/4)`, the boundary measure normalized by `∫_{K/M} dk = 1`, the kernel the
power function `p_s(Y) = ∏_{j=1}^{n} |Y_j|^{s_j}` of her (1.41) over the leading principal minors
`Y_j`, and the two explicit constants

`ω_n = ∏_{j=1}^{n} Γ(j/2) / ( j (2πi) π^{j/2} )`,
`c_n(s) = ∏_{1 ≤ i ≤ j ≤ n-1} B(½, s_i + ⋯ + s_j + ½(j-i+1)) / B(½, ½(j-i+1))`.

This file transcribes those two constants, over `ℂ`, in the coordinates of
`LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.HelgasonFourier`: there the composite distance is
`⟨x, kM⟩_j = log|(kᵀ x k)_j|`, so `e^{s·⟨x,u⟩}` is `p_s(x[k])` on the nose and Terras' contour
`Re s = -ρ` is `Re s = ϱ` for `ϱ = SpdSpace.spdRho m = (-½,…,-½,(m-1)/4)`. Terras' `n` is this
development's `m`.

*What is not proved here.* Harish-Chandra's `c`-function is the integral
`c(λ) = ∫_{N̄} e^{-(iλ+ϱ)(H(n̄))} dn̄`, which is what
`LeanRidgelet.ToMathlib.LieGroup.Symmetric.CFunction` takes as the definition, and the identity
between that integral and Terras' product of beta quotients — the Gindikin--Karpelevich formula for
`ℙ_m` — is a theorem. It is not proved in this development, and no declaration here asserts it.
Until it is proved, `SpdSpace.cFunction` is a *definition transcribed from Terras* rather than an
object derived from the geometry, and the same holds for `SpdSpace.weylConstant`. The conversion
between Terras' contour integral `ds` over `Re s = -ρ`, whose `(2πi)^{-n}` sits inside `ω_n`, and
Lebesgue measure `dλ` on `𝔞* ≅ ℝ^m`, which is this development's convention, is likewise not
carried out; so
`weylConstant` keeps the `2πi` literally as Terras writes it rather than absorbing it into a real
constant.

*Why the beta function is the gamma quotient and not `Complex.betaIntegral`.* Terras defines
`B(x,y) = Γ(x)Γ(y)/Γ(x+y)` in the statement of Thm 1.3.1(1) itself, and she needs it on the contour,
where the second argument of every factor of `c_n(s)` has real part exactly `0`: for
`1 ≤ i ≤ j ≤ n-1` the contour gives `Re s_i = ⋯ = Re s_j = -½`, hence
`Re(s_i + ⋯ + s_j + ½(j-i+1)) = 0`. Mathlib's `Complex.betaIntegral` is the Euler integral, which
converges only for arguments of positive real part, so it is not defined at the values that actually
occur. `SpdSpace.beta` is therefore the gamma quotient, that is the meromorphic continuation; the
agreement with the Euler integral where the latter converges is recorded as
`SpdSpace.betaIntegral_eq_beta`.

## Main definitions

* `SpdSpace.beta`: the Euler beta function as the gamma quotient `Γ(a)Γ(b)/Γ(a+b)`.
* `SpdSpace.partialSum`: the block sum `s_i + ⋯ + s_j`.
* `SpdSpace.blockLength`: the number `j-i+1` of indices in the block, as a cardinality.
* `SpdSpace.cIndex`: the index set `1 ≤ i ≤ j ≤ m-1` of Terras' product, as a `Finset` of pairs.
* `SpdSpace.cFactor`: one factor `B(½, s_i+⋯+s_j+½(j-i+1)) / B(½, ½(j-i+1))` of the product.
* `SpdSpace.cFunction`: **Terras' `c_m(s)`**.
* `SpdSpace.weylConstant`: **Terras' `ω_m`**.
* `SpdSpace.contourCFunction`: `c_m` restricted to the contour, `λ ↦ c_m(ϱ + iλ)`.
* `SpdSpace.plancherelDensity`: the Plancherel density `(|W| ‖c_m(ϱ+iλ)‖²)^{-1}` built from it.

## Main results

* `SpdSpace.betaIntegral_eq_beta`: the gamma quotient is the Euler integral where the latter
  converges.
* `SpdSpace.cFunction_one`: `c_1(s) = 1`, the product being empty.
* `SpdSpace.cFunction_two`: `c_2(s) = B(½, s_1+½)/B(½, ½)`, the single-factor case. Together with
  `cFunction_one` this pins the index range of the product, which is the whole content of the
  definition.
-/

@[expose] public section

noncomputable section

namespace SpdSpace

variable {m : ℕ}

/-! ## The Euler beta function -/

/-- **The Euler beta function** `B(a,b) = Γ(a)Γ(b)/Γ(a+b)`, in the form Terras uses it in
Thm 1.3.1(1).

Mathlib's `Complex.betaIntegral` is the Euler integral `∫_0^1 x^{a-1}(1-x)^{b-1} dx`, which needs
both arguments to have positive real part. Terras' `c`-function is evaluated on a contour where the
second argument has real part exactly `0`, so the integral is not available there and the gamma
quotient — its meromorphic continuation — is what is meant. The two agree where both are defined;
see `SpdSpace.betaIntegral_eq_beta`. -/
def beta (a b : ℂ) : ℂ := Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b)

theorem beta_eq (a b : ℂ) :
    beta a b = Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := rfl

theorem beta_comm (a b : ℂ) : beta a b = beta b a := by
  rw [beta_eq, beta_eq, mul_comm (Complex.Gamma a) (Complex.Gamma b), add_comm a b]

/-- Where the Euler integral converges it is the gamma quotient. This is Mathlib's
`Complex.betaIntegral_eq_Gamma_mul_div`, restated as the agreement of the two beta functions; it is
what justifies calling the quotient a beta function at all. -/
theorem betaIntegral_eq_beta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.betaIntegral a b = beta a b :=
  Complex.betaIntegral_eq_Gamma_mul_div a b ha hb

/-! ## The blocks of Terras' product -/

/-- The block sum `s_i + ⋯ + s_j` appearing in each factor of Terras' `c`-function. The block is
`Finset.Icc i j` in `Fin m`, so it is empty unless `i ≤ j`. -/
def partialSum (s : Fin m → ℂ) (i j : Fin m) : ℂ := ∑ k ∈ Finset.Icc i j, s k

theorem partialSum_apply (s : Fin m → ℂ) (i j : Fin m) :
    partialSum s i j = ∑ k ∈ Finset.Icc i j, s k := rfl

@[simp] theorem partialSum_self (s : Fin m → ℂ) (i : Fin m) : partialSum s i i = s i := by
  rw [partialSum_apply, Finset.Icc_self, Finset.sum_singleton]

/-- The length `j-i+1` of the block, as the cardinality of `Finset.Icc i j`. Terras' factors carry
`½(j-i+1)`, which is half this number; writing it as a cardinality avoids truncated subtraction and
makes the empty block `i > j` — which never occurs in `SpdSpace.cIndex` — harmless. -/
def blockLength (i j : Fin m) : ℕ := (Finset.Icc i j).card

theorem blockLength_eq (i j : Fin m) : blockLength i j = (j : ℕ) + 1 - (i : ℕ) :=
  Fin.card_Icc i j

@[simp] theorem blockLength_self (i : Fin m) : blockLength i i = 1 := by
  rw [blockLength, Finset.Icc_self, Finset.card_singleton]

/-! ## The `c`-function -/

/-- The index set of Terras' product, `{(i,j) : 1 ≤ i ≤ j ≤ m-1}`, transcribed to the `0`-based
indexing of `Fin m`: the Lean pair `(i,j)` is Terras' `(i+1, j+1)`, so her `j ≤ n-1` is
`(j : ℕ) + 1 < m` here.

The two smallest cases, which are what an off-by-one would break:

* `m = 1`: the condition `(j : ℕ) + 1 < 1` is false, the set is empty, and `c_1(s) = 1` — Terras'
  `n = 1` case, where Thm 1.3.1(1) is Mellin inversion.
* `m = 2`: the only pair is `(0,0)`, Terras' `(i,j) = (1,1)`, giving the single factor
  `B(½, s_1 + ½)/B(½, ½)`.

Both are checked below as `example`s, together with `m = 3`, where the three pairs `(0,0)`, `(0,1)`,
`(1,1)` are Terras' `(1,1)`, `(1,2)`, `(2,2)`. -/
def cIndex (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 ≤ p.2 ∧ (p.2 : ℕ) + 1 < m

theorem mem_cIndex {p : Fin m × Fin m} :
    p ∈ cIndex m ↔ p.1 ≤ p.2 ∧ (p.2 : ℕ) + 1 < m := by
  simp [cIndex]

example : cIndex 1 = ∅ := by decide
example : cIndex 2 = {(0, 0)} := by decide
example : cIndex 3 = {(0, 0), (0, 1), (1, 1)} := by decide

/-- One factor `B(½, s_i + ⋯ + s_j + ½(j-i+1)) / B(½, ½(j-i+1))` of Terras' `c`-function. -/
def cFactor (s : Fin m → ℂ) (i j : Fin m) : ℂ :=
  beta (1 / 2) (partialSum s i j + (blockLength i j : ℂ) / 2) /
    beta (1 / 2) ((blockLength i j : ℂ) / 2)

theorem cFactor_eq (s : Fin m → ℂ) (i j : Fin m) :
    cFactor s i j
      = beta (1 / 2) (partialSum s i j + (blockLength i j : ℂ) / 2) /
        beta (1 / 2) ((blockLength i j : ℂ) / 2) := rfl

/-- **Terras' `c`-function of `ℙ_m`** (*Harmonic Analysis on Symmetric Spaces — Higher Rank Spaces,
Positive Definite Matrix Space and Generalizations*, 2nd ed., Thm 1.3.1(1)),

`c_m(s) = ∏_{1 ≤ i ≤ j ≤ m-1} B(½, s_i + ⋯ + s_j + ½(j-i+1)) / B(½, ½(j-i+1))`.

This is a transcription, not a derivation: it is *not* proved here to be the Harish-Chandra integral
`SymmetricSpace.cFunctionIntegral` of the model, and nothing in this file asserts that it is. See
the module docstring. -/
def cFunction (m : ℕ) (s : Fin m → ℂ) : ℂ := ∏ p ∈ cIndex m, cFactor s p.1 p.2

theorem cFunction_eq (m : ℕ) (s : Fin m → ℂ) :
    cFunction m s = ∏ p ∈ cIndex m, cFactor s p.1 p.2 := rfl

/-- `c_1(s) = 1`: for `m = 1` the range `1 ≤ i ≤ j ≤ 0` is empty. Terras' `n = 1` case of
Thm 1.3.1(1) is ordinary Mellin inversion, which carries no `c`-function. -/
@[simp] theorem cFunction_one (s : Fin 1 → ℂ) : cFunction 1 s = 1 := by
  rw [cFunction_eq, show cIndex 1 = ∅ from by decide, Finset.prod_empty]

/-- `c_2(s)` has the single factor `B(½, s_1 + ½)/B(½, ½)`, Terras' pair `(i,j) = (1,1)`. -/
theorem cFunction_two (s : Fin 2 → ℂ) :
    cFunction 2 s = beta (1 / 2) (s 0 + 1 / 2) / beta (1 / 2) (1 / 2) := by
  rw [cFunction_eq, show cIndex 2 = {((0 : Fin 2), (0 : Fin 2))} from by decide,
    Finset.prod_singleton, cFactor_eq, partialSum_self, blockLength_self]
  norm_num

/-! ## Terras' constant -/

/-- **Terras' constant `ω_m`** of the inversion formula on `ℙ_m`
(*Harmonic Analysis on Symmetric Spaces — Higher Rank Spaces, Positive Definite Matrix Space and
Generalizations*, 2nd ed., Thm 1.3.1(1)),

`ω_m = ∏_{j=1}^{m} Γ(j/2) / ( j (2πi) π^{j/2} )`.

The `2πi` is kept literally rather than simplified into a real constant, because it belongs to
Terras' contour measure `ds` on `Re s = -ρ` and the conversion of that measure to Lebesgue measure
`dλ` on `𝔞* ≅ ℝ^m` has not been carried out in this development. Simplifying it would silently pick
a normalization; the discipline here is that constants come out of proofs.

At `m = 2` the product evaluates to `-1/(8π³)`: the `j = 1` factor is
`Γ(½)/(2πi√π) = (2πi)^{-1}` and the `j = 2` factor is `Γ(1)/(2·2πi·π) = (4π²i)^{-1}`, so the product
is `(2πi)^{-2}(2π)^{-1}`. That is an arithmetic check on the transcription, not a quotation. -/
def weylConstant (m : ℕ) : ℂ :=
  ∏ j ∈ Finset.Icc 1 m, Complex.Gamma ((j : ℂ) / 2) /
    ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((Real.pi ^ ((j : ℝ) / 2) : ℝ) : ℂ))

theorem weylConstant_eq (m : ℕ) :
    weylConstant m
      = ∏ j ∈ Finset.Icc 1 m, Complex.Gamma ((j : ℂ) / 2) /
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * ((Real.pi ^ ((j : ℝ) / 2) : ℝ) : ℂ)) := rfl

@[simp] theorem weylConstant_zero : weylConstant 0 = 1 := by
  rw [weylConstant_eq, show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.prod_empty]

/-! ## The contour -/

/-- The coordinates of `SpdSpace.spdRho`: `-½` except at the last index, where it is `(m-1)/4`. -/
theorem spdRho_apply (m : ℕ) (k : Fin m) :
    spdRho m k = if (k : ℕ) + 1 = m then ((m : ℝ) - 1) / 4 else -(1 / 2) := rfl

/-- On a block of Terras' product the shift is constantly `-½`: the block ends at `j` with
`j + 1 < m`, so none of its indices is the exceptional last one. -/
theorem spdRho_eq_neg_half_of_mem_Icc {i j k : Fin m} (hj : (j : ℕ) + 1 < m)
    (hk : k ∈ Finset.Icc i j) : spdRho m k = -(1 / 2) := by
  have hkj : (k : ℕ) ≤ (j : ℕ) := Fin.le_def.1 (Finset.mem_Icc.1 hk).2
  rw [spdRho_apply, if_neg (by omega)]

/-- **Terras' contour** `s = ϱ + iλ`, that is `Re s = -ρ` in her notation, parametrized by the real
frequency `λ ∈ 𝔞* ≅ ℝ^m` that the abstract Helgason--Fourier layer uses. -/
def contourParam (m : ℕ) (lam : EuclideanSpace ℝ (Fin m)) (j : Fin m) : ℂ :=
  ((spdRho m j : ℝ) : ℂ) + Complex.I * ((lam j : ℝ) : ℂ)

theorem contourParam_apply (m : ℕ) (lam : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    contourParam m lam j = ((spdRho m j : ℝ) : ℂ) + Complex.I * ((lam j : ℝ) : ℂ) := rfl

/-- **On the contour the beta functions of `c_m` sit exactly on the boundary of convergence of the
Euler integral.** For every block `(i,j)` of Terras' product the second argument
`s_i + ⋯ + s_j + ½(j-i+1)` of the numerator has real part `0`, because the shift contributes
`-½(j-i+1)` and the frequency contributes nothing.

This is what forces `SpdSpace.beta` to be the gamma quotient: `Complex.betaIntegral` needs positive
real part in both arguments, so it is undefined at precisely the values `c_m` is evaluated at. -/
theorem re_partialSum_add_blockLength_eq_zero {i j : Fin m} (h : (i, j) ∈ cIndex m)
    (lam : EuclideanSpace ℝ (Fin m)) :
    (partialSum (contourParam m lam) i j + (blockLength i j : ℂ) / 2).re = 0 := by
  have hj : (j : ℕ) + 1 < m := (mem_cIndex.1 h).2
  have key : ∀ k ∈ Finset.Icc i j, (contourParam m lam k).re = -(1 / 2 : ℝ) := fun k hk => by
    simp [contourParam, spdRho_eq_neg_half_of_mem_Icc hj hk]
  rw [blockLength, Complex.add_re, partialSum_apply, Complex.re_sum,
    Finset.sum_congr rfl key, Finset.sum_const,
    show (((Finset.Icc i j).card : ℂ) / 2) = ((((Finset.Icc i j).card : ℝ) / 2 : ℝ) : ℂ) by
      push_cast; ring,
    Complex.ofReal_re, nsmul_eq_mul]
  ring

/-! ## The Plancherel density -/

/-- **Terras' `c`-function on the contour** `Re s = ϱ`, that is `λ ↦ c_m(ϱ + iλ)` with
`ϱ = SpdSpace.spdRho m = (-½,…,-½,(m-1)/4)`.

This is the shape the abstract layer wants: `SymmetricSpace.plancherelDensity` and
`SpdSpace.HasInversion` take the `c`-function as a function of the real frequency `λ ∈ 𝔞* ≅ ℝ^m`,
while Terras' `c_m` is a function of the complex `s`, the two being related by her contour. -/
def contourCFunction (m : ℕ) (lam : EuclideanSpace ℝ (Fin m)) : ℂ :=
  cFunction m (contourParam m lam)

theorem contourCFunction_eq (m : ℕ) (lam : EuclideanSpace ℝ (Fin m)) :
    contourCFunction m lam
      = cFunction m fun j => ((spdRho m j : ℝ) : ℂ) + Complex.I * ((lam j : ℝ) : ℂ) := rfl

/-- The Plancherel density of `ℙ_m` built from Terras' `c`-function,
`κ(λ) = (|W| ‖c_m(ϱ+iλ)‖²)^{-1}`.

The order `W` of the Weyl group stays a parameter, and no value is fixed for it here. Terras'
Thm 1.3.1(1) carries no factor `|W|^{-1}` at all: her whole constant is `ω_m`, in front of
`|c_m(s)|^{-2}` and against her contour measure `ds`. So the split between `|W|` and `c` in
`SymmetricSpace.plancherelDensity` is a convention that has to be matched to Terras' by the same
computation that converts `ds` to Lebesgue measure `dλ`, and that computation is not done here.
Feeding this density into `SpdSpace.HasInversion` gives the inversion formula of `ℙ_m` with Terras'
`c`-function in place of an abstract one; that is a proposition about `f`, not a theorem proved
here. -/
def plancherelDensity (m : ℕ) (W : ℝ) (lam : EuclideanSpace ℝ (Fin m)) : ℝ :=
  SymmetricSpace.plancherelDensity W (contourCFunction m) lam

theorem plancherelDensity_eq (m : ℕ) (W : ℝ) (lam : EuclideanSpace ℝ (Fin m)) :
    plancherelDensity m W lam = (W * ‖contourCFunction m lam‖ ^ 2)⁻¹ := rfl

/-- The density is positive wherever Terras' `c`-function does not vanish, for a positive order of
the Weyl group. -/
theorem plancherelDensity_pos {W : ℝ} (hW : 0 < W) {lam : EuclideanSpace ℝ (Fin m)}
    (hc : contourCFunction m lam ≠ 0) : 0 < plancherelDensity m W lam :=
  SymmetricSpace.plancherelDensity_pos hW _ hc

end SpdSpace

end

end
