/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.Convention

/-!
# Fourier slice method: the pairing shared by every case

Definitions common to the Fourier slice derivations of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984),

whose four instances — networks on a finite field, group convolutional networks on a Hilbert
space, networks on a noncompact symmetric space, and the `d`-plane (pooling) layer — are developed
in the other files of `LeanRidgelet/FS/`.

The derivation turns a network into its Fourier expression, changes the scale variable
`a ∈ ℝ^r` into a frequency `λ = ω a` with Jacobian `|ω|^{-r}`, and closes with a
separation-of-variables ansatz. Whatever the input domain is, the scalar left over in front of the
reconstructed function is the pairing of the activation spectrum against the ridgelet spectrum
against the Jacobian weight, and it is the same expression in every case: only the exponent `r`,
the dimension of the scale variable, changes. That scalar is `fourierSlicePairing` below.

The domain-dependent normalization of the inversion formula does *not* enter here; it is carried
by the density that the separation-of-variables ansatz puts into the coefficient function. So for
the Euclidean network with an `m`-dimensional weight vector the manuscript's constant
`(2π)^{m-1} ∫ σ♯ conj(ρ♯) |ω|^{-m}` is `(2π)^m` times `fourierSlicePairing m`, the factor `(2π)^m`
being the normalization of the Fourier inversion on `ℝ^m` that the manuscript keeps outside its
coefficient function. Compare `LeanRidgelet.admissibilityConstant` of the L1 theory, which is the
same scalar in the same convention with `ψ` and `Fη` in place of the two spectra.

The integral runs over `ℝ \ {0}`: the change of variables `a ↦ ω a` is a bijection only for
`ω ≠ 0`, and the weight `|ω|^{-r}` is singular there. Over `ℝ` that set is null and the
restriction costs nothing, which is why the manuscript can leave it implicit. It is not free in
every case — see the finite-field development, where the excluded frequency is an atom.

## Main definitions

* `LeanRidgelet.fourierSlicePairing`: the scalar `(2π)⁻¹ ∫_{ω ≠ 0} σ♯(ω) conj(ρ♯(ω)) |ω|^{-r} dω`.

## Deviations from the article

None yet; this file only fixes notation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LeanRidgelet

/-- The Fourier slice pairing `⦅σ, ρ⦆_r = (2π)⁻¹ ∫_{ω ≠ 0} σ♯(ω) conj (ρ♯(ω)) |ω|^{-r} dω`
of an activation spectrum `Fσ` against a ridgelet spectrum `Fρ`, at scale dimension `r`.

The arguments are the spectra rather than the functions themselves, because the activation is a
tempered distribution in the manuscript and only its spectrum is ever used. -/
def fourierSlicePairing (r : ℝ) (Fσ Fρ : ℝ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ ω in {(0 : ℝ)}ᶜ, Fσ ω * conj (Fρ ω) / ((|ω| ^ r : ℝ) : ℂ)

/-- The pairing vanishes on a zero activation spectrum. -/
theorem fs_fourierSlicePairing_zero_left (r : ℝ) (Fρ : ℝ → ℂ) :
    fourierSlicePairing r (fun _ => 0) Fρ = 0 := by
  simp [fourierSlicePairing]

/-- The pairing vanishes on a zero ridgelet spectrum. -/
theorem fs_fourierSlicePairing_zero_right (r : ℝ) (Fσ : ℝ → ℂ) :
    fourierSlicePairing r Fσ (fun _ => 0) = 0 := by
  simp [fourierSlicePairing]

/-- The pairing is homogeneous in the activation spectrum. -/
theorem fs_fourierSlicePairing_const_mul_left (r : ℝ) (c : ℂ) (Fσ Fρ : ℝ → ℂ) :
    fourierSlicePairing r (fun ω => c * Fσ ω) Fρ = c * fourierSlicePairing r Fσ Fρ := by
  have h : (∫ ω in {(0 : ℝ)}ᶜ, c * Fσ ω * conj (Fρ ω) / ((|ω| ^ r : ℝ) : ℂ))
      = c * ∫ ω in {(0 : ℝ)}ᶜ, Fσ ω * conj (Fρ ω) / ((|ω| ^ r : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  simp only [fourierSlicePairing, h]
  ring

/-- Swapping the two spectra conjugates the pairing: the manuscript's scalar product of the
activation against the ridgelet function is a genuine sesquilinear pairing. -/
theorem fs_fourierSlicePairing_conj (r : ℝ) (Fσ Fρ : ℝ → ℂ) :
    conj (fourierSlicePairing r Fσ Fρ) = fourierSlicePairing r Fρ Fσ := by
  have hconst : conj ((2 * (Real.pi : ℂ))⁻¹) = (2 * (Real.pi : ℂ))⁻¹ := by
    rw [map_inv₀, map_mul, Complex.conj_ofReal, map_ofNat]
  have hint : conj (∫ ω in {(0 : ℝ)}ᶜ, Fσ ω * conj (Fρ ω) / ((|ω| ^ r : ℝ) : ℂ))
      = ∫ ω in {(0 : ℝ)}ᶜ, Fρ ω * conj (Fσ ω) / ((|ω| ^ r : ℝ) : ℂ) := by
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [fourierSlicePairing, fourierSlicePairing, map_mul, hconst, hint]

end LeanRidgelet

end

end
