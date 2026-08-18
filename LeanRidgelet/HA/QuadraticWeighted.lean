/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.AngularWeightedSobolev
public import LeanRidgelet.HA.QuadraticTransfer

/-!
# The frequency-weighted estimate for the quadratic analysis transform

Two facts already proved in this development meet here.
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature`
(`LeanRidgelet.HA.QuadraticTransfer`) says that, for a sequence of analysis features each the
derivative of the previous one, the `k`-th derivative of the analysis transform in the constant
coefficient of a quadratic parameter is the analysis transform of the `k`-th feature; the constant
coefficient enters the quadratic argument additively, so the transform is a convolution in it.
`LeanRidgelet.Fourier.eLpNorm_pow_smul_angularFourierIntegralInner`
(`LeanRidgelet.Fourier.AngularWeightedSobolev`) says that, on the line, the `L²` norm of the angular
Fourier transform weighted by the `k`-th power of the frequency is `√(2π)` times the `L²` norm of
the `k`-th derivative.

Composing them gives the weighted estimate that plan item P1.7 (d) of the development plan asks
for,
in the one parameter direction where the quadratic argument is additive: freeze the symmetric
coefficient `A` and the linear coefficient `b`, take the slice
`c ↦ bochnerRidgelet volume (quadraticVectorFeature (ρ 0)) f (A, b, c)` of the analysis transform,
and its angular Fourier transform in `c` weighted by `|ζ|^k` has `L²` norm exactly `√(2π)` times the
`L²` norm of the slice of the analysis transform of the `k`-th feature `ρ k`.  This is the sense in
which the transform lands in a coefficient space weighted by the `2k`-th power of the frequency,
with its size controlled by the `k`-th derivative of the ridgelet function — the weight that the
plan puts on the coefficient space, since the balance of
`LeanRidgelet.HA.QuadraticRelativeMeasure` fixes the parameter measure up to a constant and leaves
no room for a weight there.

## Main results

* `LeanRidgelet.eLpNorm_pow_smul_angularFourier_bochnerRidgelet_slice`: the weighted `L²` identity
  for the slice, with constant `√(2π)`.
* `LeanRidgelet.memLp_two_pow_smul_angularFourier_bochnerRidgelet_slice`: the same data makes the
  weighted angular Fourier transform of the slice square integrable.

## What is assumed

Nothing is discharged here; both inputs are used at full strength and their hypotheses are explicit
hypotheses of the statements below.  From the transfer: the feature sequence is a derivative
sequence (`hderiv`), each pairing of the data with a feature is measurable (`hmeas`) and integrable
(`hint`),
and the next pairing is dominated uniformly in the constant coefficient by an integrable function
(`hbound`, `hboundint`).  From the weighted Sobolev identity: the slice is `C^N` (`hsmooth`), the
slices of the transforms of the features up to order `N` are integrable in the constant coefficient
(`hsliceint`), the order is admissible (`hk`), and the slice of the `k`-th transform is square
integrable (`hmem`).  The two Sobolev-side hypotheses about derivatives are stated on the slices of
the transforms of `ρ n`, not on iterated derivatives of the slice of `ρ 0`; the transfer identifies
them, and the feature-side form is the one a concrete ridgelet function is checked against.

## What remains

The integrated statement over the remaining parameters is **not** proved, and the obstruction is the
parameter measure rather than the estimate.  `LeanRidgelet.quadraticRelativeMeasure lam` is
`(lam.restrict (quadraticNondegenerate E)).withDensity quadraticRelativeWeight` for an abstract
additive Haar measure `lam` on `QuadraticParameter E = QuadraticSymmetric E × E × ℝ`.  Three things
are missing, and only the first is bookkeeping.

* The restricting set and the density are harmless: `LeanRidgelet.quadraticNondegenerate` and
  `LeanRidgelet.quadraticRelativeWeight` are both defined through `quadraticSymmetricDet ξ`, hence
  depend only on the symmetric block, so they do not obstruct a factorization over the constant
  coefficient.
* `lam` itself does not factor.  Tonelli needs the measure presented as a product with a measure on
  the constant coefficient in the last slot, and an abstract Haar measure on the triple product is
  not such a product; producing one means transporting along the associativity equivalence
  `QuadraticSymmetric E × E × ℝ ≃ (QuadraticSymmetric E × E) × ℝ` and invoking uniqueness of Haar
  measure to write `lam` as a positive multiple of a product.  That development does not exist in
  this repository.
* Even granted the factorization, the weighted side is not a function on the parameter space: the
  constant coefficient has been replaced by its dual frequency, so the object to be integrated lives
  over a space whose last coordinate is a frequency and whose measure in that coordinate is the
  Lebesgue measure of the Plancherel theorem, not the restricted weighted Haar measure.  Applying
  Tonelli to it would also need joint measurability in `(A, b, ζ)` of the partial Fourier transform
  of the slice, and there is no measurability of `bochnerRidgelet` in the parameter anywhere in this
  development; the identity below is proved for each frozen `(A, b)` separately, with no measurable
  dependence on them.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The frequency-weighted estimate for the quadratic analysis transform, one slice.**  Freeze the
symmetric coefficient `A` and the linear coefficient `b`.  The `L²` norm in the frequency dual to
the constant coefficient, weighted by the `k`-th power of that frequency, of the angular Fourier
transform of the slice of the analysis transform, equals `√(2π)` times the `L²` norm of the slice of
the analysis transform of the `k`-th feature.

This is `LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature` substituted into
`LeanRidgelet.Fourier.eLpNorm_pow_smul_angularFourierIntegralInner`: the transfer turns the iterated
derivative of the slice into the slice of the transform of `ρ k`, and the weighted Sobolev identity
turns that derivative into the frequency weight.  The constant `√(2π)` is the square root of the
Plancherel constant of the angular convention; no further normalization enters. -/
theorem eLpNorm_pow_smul_angularFourier_bochnerRidgelet_slice {ρ : ℕ → ℝ → ℂ} (f : E → ℂ)
    (A : QuadraticSymmetric E) (b : E) {bound : ℕ → E → ℝ} {N : ℕ∞} {k : ℕ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ i c, AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ i c, Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ i, ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound i x)
    (hboundint : ∀ i, Integrable (bound i) (volume : Measure E))
    (hsmooth : ContDiff ℝ N
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f (A, b, c)))
    (hsliceint : ∀ n : ℕ, n ≤ N → Integrable
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ n)) f (A, b, c))
      volume)
    (hk : k ≤ N)
    (hmem : MemLp
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ k)) f (A, b, c))
      2 volume) :
    eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • Fourier.angularFourierIntegralInner
        (fun c ↦ bochnerRidgelet (volume : Measure E)
          (quadraticVectorFeature (ρ 0)) f (A, b, c)) ζ) 2 volume
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
        eLpNorm (fun c ↦ bochnerRidgelet (volume : Measure E)
          (quadraticVectorFeature (ρ k)) f (A, b, c)) 2 volume := by
  have hiter : ∀ n : ℕ, iteratedDeriv n
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c)) =
      fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ n)) f (A, b, c) :=
    fun n ↦ iteratedDeriv_bochnerRidgelet_quadraticVectorFeature f A b hderiv hmeas hint hbound
      hboundint n
  have hint' : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c))) volume := by
    intro n hn
    rw [hiter n]
    exact hsliceint n hn
  have hmem' : MemLp (iteratedDeriv k
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c))) 2 volume := by
    rw [hiter k]
    exact hmem
  have h := Fourier.eLpNorm_pow_smul_angularFourierIntegralInner hsmooth hint' hk hmem'
  rwa [hiter k] at h

/-- **Square integrability of the weighted transform, one slice.**  Under the hypotheses of
`LeanRidgelet.eLpNorm_pow_smul_angularFourier_bochnerRidgelet_slice` the frequency-weighted angular
Fourier transform of the slice of the analysis transform is square integrable, so the slice really
does lie in the coefficient space weighted by the `2k`-th power of the frequency. -/
theorem memLp_two_pow_smul_angularFourier_bochnerRidgelet_slice {ρ : ℕ → ℝ → ℂ} (f : E → ℂ)
    (A : QuadraticSymmetric E) (b : E) {bound : ℕ → E → ℝ} {N : ℕ∞} {k : ℕ}
    (hderiv : ∀ i z, HasDerivAt (ρ i) (ρ (i + 1) z) z)
    (hmeas : ∀ i c, AEStronglyMeasurable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hint : ∀ i c, Integrable
      (fun x ↦ f x * conj (quadraticVectorFeature (ρ i) x (A, b, c))) (volume : Measure E))
    (hbound : ∀ i, ∀ᵐ x ∂(volume : Measure E), ∀ c : ℝ,
      ‖f x * conj (quadraticVectorFeature (ρ (i + 1)) x (A, b, c))‖ ≤ bound i x)
    (hboundint : ∀ i, Integrable (bound i) (volume : Measure E))
    (hsmooth : ContDiff ℝ N
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ 0)) f (A, b, c)))
    (hsliceint : ∀ n : ℕ, n ≤ N → Integrable
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ n)) f (A, b, c))
      volume)
    (hk : k ≤ N)
    (hmem : MemLp
      (fun c ↦ bochnerRidgelet (volume : Measure E) (quadraticVectorFeature (ρ k)) f (A, b, c))
      2 volume) :
    MemLp (fun ζ : ℝ ↦ (|ζ| ^ k : ℝ) • Fourier.angularFourierIntegralInner
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c)) ζ) 2 volume := by
  have hiter : ∀ n : ℕ, iteratedDeriv n
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c)) =
      fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ n)) f (A, b, c) :=
    fun n ↦ iteratedDeriv_bochnerRidgelet_quadraticVectorFeature f A b hderiv hmeas hint hbound
      hboundint n
  have hint' : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c))) volume := by
    intro n hn
    rw [hiter n]
    exact hsliceint n hn
  have hmem' : MemLp (iteratedDeriv k
      (fun c ↦ bochnerRidgelet (volume : Measure E)
        (quadraticVectorFeature (ρ 0)) f (A, b, c))) 2 volume := by
    rw [hiter k]
    exact hmem
  exact Fourier.memLp_two_pow_smul_angularFourierIntegralInner hsmooth hint' hk hmem'

end LeanRidgelet
