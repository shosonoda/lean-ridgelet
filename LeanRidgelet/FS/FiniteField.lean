/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.CyclicFourier

/-!
# Fourier slice method, Case I: networks on a finite field

Section 3 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984).

The depth-2 fully-connected network over `𝔽_p` is obtained from the Euclidean one by replacing
every integral with a finite sum, and the three steps of the method go through verbatim. Because
nothing here converges — every sum is finite — this case isolates the combinatorial content of the
derivation from its analytic packaging, and each of the three steps appears below as a named
theorem.

The dimension is `Fintype.card ι`, written `m` in the article, and the input space is `ι → ZMod p`
with the dot product as its pairing. Primality of `p` is used exactly once, in Step 2: it makes
`a ↦ ω • a` a bijection of the weight space for every nonzero `ω`.

## Main definitions and results

* `finiteFieldSynthesis`, `finiteFieldRidgelet`, `finiteFieldPairing`: the network `S[γ]`, the
  ridgelet transform `R[f;ρ]`, and the scalar `⦅σ,ρ⦆`.
* `fs_finiteField_fourierExpression`: Step 1, the Fourier expression of the network.
* `fs_finiteField_changeOfVariables`: Step 2, the change of variables `ξ = ω a`.
* `fs_dft_finiteFieldRidgelet`: Step 3, the ridgelet transform is in separation-of-variables form,
  `γ♯(a, ω) = f̂(ω a) conj (ρ♯(ω))`.
* `fs_finiteField_synthesis_ridgelet`: the master identity, with no hypothesis on `ρ`.
* `fs_finiteField_reconstruction`: the reconstruction formula `S[R[f;ρ]] = ⦅σ,ρ⦆ f` for a ridgelet
  function of vanishing mean.
* `fs_finiteFieldPairing_meanZeroPart`, `fs_finiteField_reconstruction_meanZeroPart`: subtracting
  its mean makes any `ρ` admissible without changing the scalar.

## Deviations from the article

The article's Theorem 3.2 states `S[R[f;ρ]] = ⦅σ,ρ⦆ f` for every `ρ`, with
`⦅σ,ρ⦆ = |𝔽_p|^{-(m-1)} ∑_ω σ♯(ω) conj (ρ♯(ω))`. Three changes are made here.

* **The scalar carries `|𝔽_p|^{m-1}`, not its reciprocal.** The article's own proof produces
  `|𝔽_p|^{m-1}`; the reciprocal in the statement of the theorem does not match it.
* **The frequency `ω = 0` is excluded from the sum.** Step 2 changes variables by `ξ = ω a`, which
  is a bijection of `𝔽_p^m` only for `ω ≠ 0`. Over `ℝ` the excluded frequency is a null set and
  the weight `|ω|^{-m}` is singular there anyway, so the restriction is invisible; over `𝔽_p` it
  is an atom.
* **The ridgelet function is assumed to have vanishing mean.** Excluding `ω = 0` from the scalar
  is not by itself enough, because the coefficient function `R[f;ρ]` still has a nonzero
  `ω = 0` mode. What that mode contributes is computed without hypotheses in
  `fs_finiteField_synthesis_ridgelet`: a rank-one defect
  `|𝔽_p|^{m-1} σ♯(0) conj (ρ♯(0)) ∑_y f(y)`, which is a multiple of the constant function and so
  is not absorbed by any choice of scalar. Taking `∑_b ρ b = 0` kills it. This is the
  vanishing-moment convention for a wavelet, and it is the discrete counterpart of admissibility
  in the continuous theory, where the singular weight `|ω|^{-m}` plays the same role — compare
  `LeanRidgelet.IsAdmissiblePair`, whose defining integral is over `{0}ᶜ`. It costs nothing:
  `fs_finiteField_reconstruction_meanZeroPart` runs the theorem for an arbitrary `ρ` after
  subtracting its mean, and `fs_finiteFieldPairing_meanZeroPart` shows the scalar is unchanged.

Without the third change the theorem is false. Taking `σ = ρ = 1` gives `R[f;ρ] = ∑_y f y` and
`S[R[f;ρ]] = p^{m+1} ∑_y f y`, a constant function, whereas `⦅σ,ρ⦆ f` is a multiple of `f`.
-/

@[expose] public section

noncomputable section

open Finset ZMod
open scoped ComplexConjugate

namespace LeanRidgelet

variable {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The hidden parameter space `𝔽_p^m × 𝔽_p` of weights and biases. -/
abbrev FiniteFieldParameter (p : ℕ) (ι : Type*) := (ι → ZMod p) × ZMod p

/-- The depth-2 fully-connected network over `𝔽_p`,
`S[γ](x) = ∑_{(a,b)} γ(a,b) σ(a ⬝ x - b)`. -/
def finiteFieldSynthesis (σ : ZMod p → ℂ) (γ : FiniteFieldParameter p ι → ℂ)
    (x : ι → ZMod p) : ℂ :=
  ∑ q : FiniteFieldParameter p ι, γ q * σ (q.1 ⬝ᵥ x - q.2)

/-- The ridgelet transform over `𝔽_p`,
`R[f;ρ](a,b) = ∑_x f(x) conj (ρ (a ⬝ x - b))`. -/
def finiteFieldRidgelet (ρ : ZMod p → ℂ) (f : (ι → ZMod p) → ℂ)
    (q : FiniteFieldParameter p ι) : ℂ :=
  ∑ x : ι → ZMod p, f x * conj (ρ (q.1 ⬝ᵥ x - q.2))

/-- The scalar `⦅σ,ρ⦆ = |𝔽_p|^{m-1} ∑_{ω ≠ 0} σ♯(ω) conj (ρ♯(ω))` of the reconstruction formula,
written `p^m / p` so that it is also correct when `ι` is empty. -/
def finiteFieldPairing (p : ℕ) (ι : Type*) [NeZero p] [Fintype ι] (σ ρ : ZMod p → ℂ) : ℂ :=
  (p : ℂ) ^ Fintype.card ι / p *
    ∑ ω ∈ ({0} : Finset (ZMod p))ᶜ, dft σ ω * conj (dft ρ ω)

/-- The number of points of the input space, `|𝔽_p^m| = p^m`. -/
theorem fs_card_finiteInput :
    (Fintype.card (ι → ZMod p) : ℂ) = (p : ℂ) ^ Fintype.card ι := by
  simp [ZMod.card]

/-! ## Step 1: the Fourier expression -/

/-- **Step 1**: the Fourier expression of the network. Convolving in the bias turns `S[γ](x)`
into `p⁻¹ ∑_{a,ω} γ♯(a,ω) σ♯(ω) e(ω (a ⬝ x))`.

The article writes the activation itself where its spectrum is meant; the convolution theorem
produces `σ♯`. -/
theorem fs_finiteField_fourierExpression (σ : ZMod p → ℂ) (γ : FiniteFieldParameter p ι → ℂ)
    (x : ι → ZMod p) :
    finiteFieldSynthesis σ γ x
      = (p : ℂ)⁻¹ * ∑ a : ι → ZMod p, ∑ ω : ZMod p,
          dft (fun b => γ (a, b)) ω * dft σ ω * stdAddChar (ω * (a ⬝ᵥ x)) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  rw [finiteFieldSynthesis, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_dft_mul_dft_mul_stdAddChar, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-! ## Step 2: the change of variables -/

/-- **Step 2**: the change of variables `ξ = ω a`. For `ω ≠ 0` the map `a ↦ ω • a` permutes the
weight space, because `𝔽_p` is a field. This is the only place primality is used. -/
theorem fs_finiteField_changeOfVariables [Fact p.Prime] {ω : ZMod p} (hω : ω ≠ 0)
    (F : (ι → ZMod p) → ℂ) :
    ∑ a : ι → ZMod p, F (ω • a) = ∑ ξ : ι → ZMod p, F ξ :=
  Fintype.sum_equiv
    { toFun := fun a : ι → ZMod p => ω • a
      invFun := fun ξ : ι → ZMod p => ω⁻¹ • ξ
      left_inv := fun a => by
        change ω⁻¹ • ω • a = a
        rw [smul_smul, inv_mul_cancel₀ hω, one_smul]
      right_inv := fun ξ => by
        change ω • ω⁻¹ • ξ = ξ
        rw [smul_smul, mul_inv_cancel₀ hω, one_smul] }
    _ _ fun _ => rfl

/-! ## Step 3: the separation-of-variables form -/

/-- **Step 3**: the ridgelet transform is already in separation-of-variables form. Its bias
spectrum factors as a principal part carrying the target function and an auxiliary part carrying
the ridgelet function, `γ♯(a, ω) = f̂(ω a) conj (ρ♯(ω))`.

Reindexing the bias by `c = a ⬝ x - b` is what produces the factorization. -/
theorem fs_dft_finiteFieldRidgelet (ρ : ZMod p → ℂ) (f : (ι → ZMod p) → ℂ)
    (a : ι → ZMod p) (ω : ZMod p) :
    dft (fun b => finiteFieldRidgelet ρ f (a, b)) ω
      = piDFT f (ω • a) * conj (dft ρ ω) := by
  have hconj : conj (dft ρ ω) = ∑ c : ZMod p, stdAddChar (c * ω) * conj (ρ c) := by
    rw [dft_apply, map_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [smul_eq_mul, map_mul, conj_stdAddChar, neg_neg]
  have hinner : ∀ y : ι → ZMod p,
      ∑ b : ZMod p, stdAddChar (-(b * ω)) * conj (ρ (a ⬝ᵥ y - b))
        = stdAddChar (-((ω • a) ⬝ᵥ y)) * conj (dft ρ ω) := by
    intro y
    have hreindex : ∑ b : ZMod p, stdAddChar (-(b * ω)) * conj (ρ (a ⬝ᵥ y - b))
        = ∑ c : ZMod p, stdAddChar (-((a ⬝ᵥ y - c) * ω)) * conj (ρ c) :=
      Fintype.sum_equiv (Equiv.subLeft (a ⬝ᵥ y)) _ _ fun c => by
        simp only [Equiv.subLeft_apply, sub_sub_cancel]
    rw [hreindex, hconj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, smul_dotProduct, smul_eq_mul]
    congr 2
    ring
  calc dft (fun b => finiteFieldRidgelet ρ f (a, b)) ω
      = ∑ y : ι → ZMod p, f y * ∑ b : ZMod p,
          stdAddChar (-(b * ω)) * conj (ρ (a ⬝ᵥ y - b)) := by
        rw [dft_apply]
        simp only [finiteFieldRidgelet, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun b _ => by ring
    _ = piDFT f (ω • a) * conj (dft ρ ω) := by
        simp only [hinner, piDFT_apply, smul_eq_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring

/-! ## Assembling the three steps -/

/-- The weight sum at a fixed bias frequency, which is where Steps 2 and 3 meet. At `ω ≠ 0` the
change of variables turns it into the Fourier inversion of `f` at `x`; at `ω = 0` the change of
variables is unavailable and the sum collapses onto the total mass of `f` instead.

This asymmetry is the whole difference between the finite field and the Euclidean case. -/
theorem fs_finiteField_sum_slice [Fact p.Prime] (f : (ι → ZMod p) → ℂ) (ω : ZMod p)
    (x : ι → ZMod p) :
    ∑ a : ι → ZMod p, piDFT f (ω • a) * stdAddChar (ω * (a ⬝ᵥ x))
      = if ω = 0 then (p : ℂ) ^ Fintype.card ι * ∑ y : ι → ZMod p, f y
        else (p : ℂ) ^ Fintype.card ι * f x := by
  have hpair : ∀ a : ι → ZMod p, ω * (a ⬝ᵥ x) = (ω • a) ⬝ᵥ x := fun a => by
    rw [smul_dotProduct, smul_eq_mul]
  simp only [hpair]
  split_ifs with hω
  · subst hω
    simp only [zero_smul, ZMod.piDFT_apply_zero, zero_dotProduct, AddChar.map_zero_eq_one,
      mul_one, Finset.sum_const, card_univ, nsmul_eq_mul, fs_card_finiteInput]
  · calc ∑ a : ι → ZMod p, piDFT f (ω • a) * stdAddChar ((ω • a) ⬝ᵥ x)
        = ∑ ξ : ι → ZMod p, piDFT f ξ * stdAddChar (ξ ⬝ᵥ x) :=
          fs_finiteField_changeOfVariables hω fun ξ => piDFT f ξ * stdAddChar (ξ ⬝ᵥ x)
      _ = ∑ ξ : ι → ZMod p, stdAddChar (ξ ⬝ᵥ x) • piDFT f ξ :=
          Finset.sum_congr rfl fun ξ _ => by rw [smul_eq_mul, mul_comm]
      _ = ((p : ℂ) ^ Fintype.card ι) • f x := ZMod.sum_stdAddChar_smul_piDFT f x
      _ = (p : ℂ) ^ Fintype.card ι * f x := smul_eq_mul _ _

/-- **The master identity.** With no hypothesis on the ridgelet function, the network built from
the ridgelet transform reproduces `⦅σ,ρ⦆ f` plus a rank-one defect carried by the bias frequency
`ω = 0`, where Step 2 breaks down. The defect is a multiple of the constant function `∑ y, f y`
and so cannot be absorbed into the scalar. -/
theorem fs_finiteField_synthesis_ridgelet [Fact p.Prime] (σ ρ : ZMod p → ℂ)
    (f : (ι → ZMod p) → ℂ) (x : ι → ZMod p) :
    finiteFieldSynthesis σ (finiteFieldRidgelet ρ f) x
      = finiteFieldPairing p ι σ ρ * f x
        + (p : ℂ) ^ Fintype.card ι / p * (dft σ 0 * conj (dft ρ 0)) *
          ∑ y : ι → ZMod p, f y := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  have hcollect : finiteFieldSynthesis σ (finiteFieldRidgelet ρ f) x
      = (p : ℂ)⁻¹ * ∑ ω : ZMod p, dft σ ω * conj (dft ρ ω) *
          ∑ a : ι → ZMod p, piDFT f (ω • a) * stdAddChar (ω * (a ⬝ᵥ x)) := by
    rw [fs_finiteField_fourierExpression]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [fs_dft_finiteFieldRidgelet]; ring
  rw [hcollect, ← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)),
    fs_finiteField_sum_slice, if_pos rfl]
  have herase : ∑ ω ∈ univ.erase (0 : ZMod p), dft σ ω * conj (dft ρ ω) *
        ∑ a : ι → ZMod p, piDFT f (ω • a) * stdAddChar (ω * (a ⬝ᵥ x))
      = (∑ ω ∈ univ.erase (0 : ZMod p), dft σ ω * conj (dft ρ ω)) *
        ((p : ℂ) ^ Fintype.card ι * f x) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [fs_finiteField_sum_slice, if_neg (Finset.ne_of_mem_erase hω)]
  rw [herase, finiteFieldPairing, ← Finset.compl_singleton]
  field_simp
  ring

/-- **The reconstruction formula over a finite field** (Theorem 3.2). A ridgelet function of
vanishing mean kills the `ω = 0` defect, and the network reproduces the target exactly up to the
scalar `⦅σ,ρ⦆`. -/
theorem fs_finiteField_reconstruction [Fact p.Prime] (σ ρ : ZMod p → ℂ)
    (f : (ι → ZMod p) → ℂ) (hρ : ∑ b : ZMod p, ρ b = 0) :
    finiteFieldSynthesis σ (finiteFieldRidgelet ρ f)
      = fun x => finiteFieldPairing p ι σ ρ * f x := by
  have hzero : dft ρ 0 = 0 := by rw [dft_apply_zero]; exact hρ
  funext x
  rw [fs_finiteField_synthesis_ridgelet, hzero]
  simp

/-! ## Any ridgelet function becomes admissible after subtracting its mean -/

/-- The mean-zero part `ρ - p⁻¹ ∑ ρ` of a ridgelet function. -/
def meanZeroPart (p : ℕ) [NeZero p] (ρ : ZMod p → ℂ) : ZMod p → ℂ :=
  fun b => ρ b - (p : ℂ)⁻¹ * ∑ c : ZMod p, ρ c

/-- The mean-zero part has vanishing mean. -/
theorem fs_sum_meanZeroPart (ρ : ZMod p → ℂ) : ∑ b : ZMod p, meanZeroPart p ρ b = 0 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  simp only [meanZeroPart, Finset.sum_sub_distrib, Finset.sum_const, card_univ, ZMod.card,
    nsmul_eq_mul]
  field_simp
  ring

/-- Subtracting the mean changes no nonzero bias frequency, since the spectrum of a constant is
supported at the origin. -/
theorem fs_dft_meanZeroPart {ω : ZMod p} (hω : ω ≠ 0) (ρ : ZMod p → ℂ) :
    dft (meanZeroPart p ρ) ω = dft ρ ω := by
  have hconst : dft (fun _ : ZMod p => (p : ℂ)⁻¹ * ∑ c : ZMod p, ρ c) ω = 0 := by
    rw [dft_apply]
    simp only [smul_eq_mul, ← Finset.sum_mul]
    have hchar : ∑ j : ZMod p, stdAddChar (-(j * ω)) = 0 := by
      have hsum := sum_stdAddChar_mul (-ω)
      rw [if_neg (neg_ne_zero.2 hω)] at hsum
      simpa [mul_neg] using hsum
    rw [hchar, zero_mul]
  have hsub : meanZeroPart p ρ
      = ρ - fun _ : ZMod p => (p : ℂ)⁻¹ * ∑ c : ZMod p, ρ c := rfl
  rw [hsub, map_sub, Pi.sub_apply, hconst, sub_zero]

omit [DecidableEq ι] in
/-- Subtracting the mean does not change the scalar of the reconstruction formula, because the
scalar only sees the nonzero bias frequencies. -/
theorem fs_finiteFieldPairing_meanZeroPart (σ ρ : ZMod p → ℂ) :
    finiteFieldPairing p ι σ (meanZeroPart p ρ) = finiteFieldPairing p ι σ ρ := by
  rw [finiteFieldPairing, finiteFieldPairing]
  congr 1
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [fs_dft_meanZeroPart (by simpa using (Finset.mem_compl.1 hω))]

/-- **Every ridgelet function is usable after normalization.** Running the reconstruction formula
with the mean-zero part of an arbitrary `ρ` reproduces `f` up to the same scalar `⦅σ,ρ⦆`, so the
vanishing-mean hypothesis is a normalization rather than a restriction. -/
theorem fs_finiteField_reconstruction_meanZeroPart [Fact p.Prime] (σ ρ : ZMod p → ℂ)
    (f : (ι → ZMod p) → ℂ) :
    finiteFieldSynthesis σ (finiteFieldRidgelet (meanZeroPart p ρ) f)
      = fun x => finiteFieldPairing p ι σ ρ * f x := by
  rw [fs_finiteField_reconstruction σ _ f (fs_sum_meanZeroPart ρ),
    fs_finiteFieldPairing_meanZeroPart]

end LeanRidgelet
