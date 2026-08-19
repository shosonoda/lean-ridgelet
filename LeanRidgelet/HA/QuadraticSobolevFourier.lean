/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticSobolevCarrier
public import LeanRidgelet.Fourier.AngularWeightedSobolev

/-!
# The intermediate space on the Fourier side of the constant coefficient

The intermediate coefficient space was designed in the constant coefficient of the parameter rather
than in its dual, because the action is a shear there and the Sobolev structure is therefore carried
along; transporting to the dual side was the route not taken.  This file shows the two are the same
space.

Plancherel in one variable turns the order-`k` Sobolev seminorm in the constant coefficient into a
frequency-weighted `L²` norm of the angular Fourier transform in that coefficient, slice by slice
and then over the base.  So the space of `LeanRidgelet.HA.QuadraticSobolevSpace` *is* the weighted
space the other route would have built, and the choice between the two was a choice of which side
to make the invariance visible on, not a choice of space.  The invariance is visible in the constant
coefficient, where the action is a shear; the synthesis bound is visible on the frequency side,
where the activation appears through its own Fourier transform.

## Where the activation enters, and why the synthesis side is still open

Read the synthesis integral in the constant coefficient.  For a frozen base parameter it is a
pairing `∫ γ(c) σ(a + c) dc` with `a` the part of the scalar argument that does not involve `c`, so
the data variable enters the pairing **only through a translation of the activation** -- and on the
frequency side a translation is a phase, which is
`LeanRidgelet.angularFourierIntegralInner_comp_const_add` below.  The pairing therefore becomes an
integral of the transform of the coefficient function against the transform of the activation,
modulated by the phase; and the frequency weight `|ζ|^k` that the seminorm carries is exactly what
has to absorb the singularity of the activation's transform.  For the rectified linear unit that
transform has a second-order pole at the origin, so the natural order is `k ≥ 2`.  That is the
negative-order condition on the synthesis feature, made concrete.

It is not a theorem here, and the modulation lemma shows why not.  An activation of polynomial
growth has no Fourier transform as a function -- the defining integral does not converge, and both
sides of the modulation identity degenerate to zero -- so the pairing is a distributional one and
Parseval does not literally apply.  Making the synthesis bound a theorem needs a duality statement
against the distributional transform, not the identity below.  What the identity does settle is the
*shape*: the data variable is a phase, the activation is a fixed frequency profile, and the order
`k` is what pairs against it.

## Main results

* `LeanRidgelet.eLpNorm_pow_smul_angularFourier_quadraticConstSlice`: **the slice-wise Plancherel
  description.**  The frequency-weighted `L²` norm of the angular Fourier transform of a slice is
  `√(2π)` times the `L²` norm of the slice's `j`-th derivative.
* `LeanRidgelet.quadraticBaseSobolevSeminorm_eq_angularFourier`: **the same over the base.**  The
  base-level order-`k` seminorm is, up to that one constant, the sum over `j ≤ k` of the base
  integrals of the squared frequency-weighted transforms.
* `LeanRidgelet.angularFourierIntegralInner_comp_const_add`: translating a function translates
  nothing on the frequency side but the phase.  This is the structural fact behind the synthesis
  pairing.

## What is assumed

Only the hypotheses of the one-variable identity, taken slice by slice: the coefficient function is
`N` times continuously differentiable, each of its derivatives up to order `N` is integrable in the
constant coefficient, and the `j`-th one is square integrable there.  These are conditions on a
member of the space, not on the activation; nothing here assumes anything about the activation, and
the modulation lemma assumes nothing at all.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-! ### The slice-wise Plancherel description -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- **The seminorm of a slice, on the frequency side.**  For a slice of a coefficient function in
the constant coefficient, the `L²` norm of the angular Fourier transform weighted by the `j`-th
power of the frequency is `√(2π)` times the `L²` norm of the `j`-th derivative of the slice.  This
is the one-variable weighted Sobolev identity of `LeanRidgelet.Fourier.AngularWeightedSobolev`
instantiated at a slice; the constant is the square root of the Plancherel constant of the angular
convention. -/
theorem eLpNorm_pow_smul_angularFourier_quadraticConstSlice {T : QuadraticParameter E → ℂ}
    {N : ℕ∞} {j : ℕ} (p : QuadraticSymmetric E × E) (hT : ContDiff ℝ (N : WithTop ℕ∞) T)
    (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n (quadraticConstSlice T p)) volume)
    (hj : j ≤ N) (hmem : MemLp (iteratedDeriv j (quadraticConstSlice T p)) 2 volume) :
    eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ j : ℝ) •
        Fourier.angularFourierIntegralInner (quadraticConstSlice T p) ζ) 2 volume
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
        eLpNorm (iteratedDeriv j (quadraticConstSlice T p)) 2 volume :=
  Fourier.eLpNorm_pow_smul_angularFourierIntegralInner
    (contDiff_quadraticConstSlice hT p) hint hj hmem

/-! ### The description over the base -/

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- **The intermediate space is the weighted space of the other route.**  The base-level order-`k`
Sobolev seminorm in the constant coefficient is, up to the single constant `√(2π)`, the sum over
`j ≤ k` of the base integrals of the squared frequency-weighted angular Fourier transforms of the
slices.  So the space designed in the constant coefficient, where the action is a shear and the
invariance is visible, coincides with the frequency-weighted space in which the synthesis pairing is
visible.  The two candidates for the intermediate space were one space. -/
theorem quadraticBaseSobolevSeminorm_eq_angularFourier
    (κ : Measure (QuadraticSymmetric E × E)) (k : ℕ) {T : QuadraticParameter E → ℂ} {N : ℕ∞}
    (hT : ContDiff ℝ (N : WithTop ℕ∞) T)
    (hint : ∀ (p : QuadraticSymmetric E × E) (n : ℕ), n ≤ N →
      Integrable (iteratedDeriv n (quadraticConstSlice T p)) volume)
    (hk : k ≤ N)
    (hmem : ∀ (p : QuadraticSymmetric E × E) (j : ℕ), j ≤ k →
      MemLp (iteratedDeriv j (quadraticConstSlice T p)) 2 volume) :
    ∑ j ∈ Finset.range (k + 1),
        (∫⁻ p : QuadraticSymmetric E × E,
          eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ j : ℝ) •
            Fourier.angularFourierIntegralInner (quadraticConstSlice T p) ζ) 2 volume ^ 2
          ∂(quadraticBaseRelativeMeasure κ)) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * quadraticBaseSobolevSeminorm κ k T := by
  rw [quadraticBaseSobolevSeminorm_eq_lintegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≤ k := Finset.mem_range_succ_iff.1 hj
  have hjN : j ≤ N := le_trans (by exact_mod_cast hjk) hk
  have hterm : ∀ p : QuadraticSymmetric E × E,
      eLpNorm (fun ζ : ℝ ↦ (|ζ| ^ j : ℝ) •
          Fourier.angularFourierIntegralInner (quadraticConstSlice T p) ζ) 2 volume ^ 2
        = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) ^ 2 *
          ∫⁻ t, ‖iteratedDeriv j (quadraticConstSlice T p) t‖ₑ ^ 2 ∂(volume : Measure ℝ) := by
    intro p
    rw [eLpNorm_pow_smul_angularFourier_quadraticConstSlice p hT (hint p) hjN (hmem p j hjk),
      mul_pow, eLpNorm_two_sq_eq_lintegral_enorm_sq]
  rw [lintegral_congr hterm,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast (ENNReal.ofReal (Real.sqrt (2 * Real.pi))) 2, ← ENNReal.rpow_mul]
  norm_num

/-! ### Translation is a phase -/

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- **Translating the argument multiplies the transform by a phase.**  In the constant coefficient
the data variable enters the synthesis pairing only by translating the activation, so on the
frequency side it enters only through this phase.  Nothing is assumed: for a function whose defining
integral diverges both sides are zero, which is exactly the case of an activation of polynomial
growth, and the reason the synthesis pairing has to be read distributionally. -/
theorem angularFourierIntegralInner_comp_const_add (σ : ℝ → ℂ) (a ζ : ℝ) :
    Fourier.angularFourierIntegralInner (fun c : ℝ ↦ σ (a + c)) ζ =
      Complex.exp (Complex.I * (a * ζ : ℝ)) * Fourier.angularFourierIntegralInner σ ζ := by
  have hshift : ∀ c : ℝ, Complex.exp (-Complex.I * ((inner ℝ c ζ : ℝ) : ℂ)) * σ (a + c)
      = Complex.exp (Complex.I * (a * ζ : ℝ)) *
        (Complex.exp (-Complex.I * ((inner ℝ (a + c) ζ : ℝ) : ℂ)) * σ (a + c)) := by
    intro c
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    · push_cast [RCLike.inner_apply, conj_trivial]
      ring_nf
  simp only [Fourier.angularFourierIntegralInner]
  rw [integral_congr_ae (Filter.Eventually.of_forall hshift), integral_const_mul,
    integral_add_left_eq_self
      (fun u : ℝ ↦ Complex.exp (-Complex.I * ((inner ℝ u ζ : ℝ) : ℂ)) * σ u) a]

end LeanRidgelet
