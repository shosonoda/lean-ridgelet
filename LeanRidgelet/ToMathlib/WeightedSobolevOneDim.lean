/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.FourierPlancherel
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The one-variable weighted Sobolev identity

The `L²` norm of the `k`-th derivative of a function on `ℝ` equals the `L²` norm of its Fourier
transform weighted by the `k`-th power of the frequency. Combining
`Real.fourier_iteratedDeriv` — the Fourier transform of an iterated derivative is a power of the
frequency times the transform — with Plancherel's theorem
(`MeasureTheory.Integrable.lintegral_enorm_fourier_sq` in
`LeanRidgelet.ToMathlib.FourierPlancherel`) turns differentiation into multiplication by the
frequency *isometrically*, which is what converts a derivative identity into a bound in a
frequency-weighted `L²` space.

## Main results

In Mathlib's `2π` convention, where `𝓕 g ω = ∫ x, e^{-2πi x ω} g x dx`, the weight is
`(2π|ω|)^k` — the modulus of the factor `(2πiω)^k` produced by `Real.fourier_iteratedDeriv`:

* `MeasureTheory.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier`:
  `‖g^{(k)}‖_{L²} = ‖(2π|ω|)^k 𝓕 g‖_{L²}`, for `g` smooth of order `N ≥ k` with all
  derivatives up to order `N` integrable and `g^{(k)} ∈ L²`.
* `SchwartzMap.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier`: the same for a Schwartz
  function, where every hypothesis is automatic.
* `MeasureTheory.memLp_two_pow_smul_fourier` and `SchwartzMap.memLp_two_pow_smul_fourier`: the
  weighted transform is square-integrable.

In the angular-frequency convention of the ridgelet manuscripts,
`g♯ ζ = ∫ z, e^{-i z ζ} g z dz = 𝓕 g ((2π)⁻¹ ζ)`
(`LeanRidgelet.Fourier.angularFourierIntegralInner`, whose one-dimensional case is
`LeanRidgelet.angularFourier1D`), the frequency rescaling of the bridge
`LeanRidgelet.Fourier.angularFourierIntegralInner_eq_fourier` — the function-level form of
`LeanRidgelet.angularFourier1D_eq_mathlib` — cancels the `2π` in the weight and moves it into
the Plancherel constant `(2π)^{dim} = 2π` of
`LeanRidgelet.Fourier.lintegral_enorm_angularFourierIntegralInner_sq`:

* `LeanRidgelet.Fourier.angularFourierIntegralInner_iteratedDeriv`: `(g^{(k)})♯ ζ = (iζ)^k g♯ ζ`.
* `LeanRidgelet.Fourier.lintegral_enorm_pow_smul_angularFourierIntegralInner_sq`:
  `∫ |ζ|^{2k} ‖g♯ ζ‖² dζ = 2π ∫ ‖g^{(k)} x‖² dx`.
* `LeanRidgelet.Fourier.eLpNorm_pow_smul_angularFourierIntegralInner`, the `eLpNorm` form of the
  previous item, whose constant is therefore `√(2π)`; the Schwartz specialization is
  `LeanRidgelet.Fourier.eLpNorm_pow_smul_angularFourierIntegralInner_of_schwartz`.
* `LeanRidgelet.Fourier.memLp_two_pow_smul_angularFourierIntegralInner` and its Schwartz
  specialization `..._of_schwartz`: the weighted angular transform is square-integrable.

No new normalization constant is introduced anywhere: in each convention the constant is the one
forced by the two inputs.

Since `LeanRidgelet.angularFourier1D` is *by definition*
`LeanRidgelet.Fourier.angularFourierIntegralInner` at `V = ℝ`, the angular statements apply to it
after `rw [LeanRidgelet.angularFourier1D]`, exactly as elsewhere in the L1 development. They are
stated for `angularFourierIntegralInner` so that this file stays below `LeanRidgelet.L1` in the
import order.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The `L²` seminorm as the square root of the `lintegral` of the squared enorm; the shape in
which Plancherel's theorem is stated in `LeanRidgelet.ToMathlib.FourierPlancherel`. -/
theorem eLpNorm_two_eq_rpow {α G : Type*} [MeasurableSpace α] [NormedAddCommGroup G]
    {μ : Measure α} (v : α → G) :
    eLpNorm v 2 μ = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num [ENNReal.rpow_natCast]

/-- Equal norms have equal extended norms; used to compare a phase-carrying weight with its
modulus inside an `lintegral`. -/
theorem enorm_eq_enorm_of_norm_eq {G H : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup H] {x : G} {y : H} (h : ‖x‖ = ‖y‖) : ‖x‖ₑ = ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, h]

/-- **Plancherel's theorem on `L¹ ∩ L²`**, `eLpNorm` form: the Fourier integral is an `L²`
isometry on `L¹ ∩ L²`. Restatement of `MeasureTheory.Integrable.lintegral_enorm_fourier_sq`. -/
theorem Integrable.eLpNorm_fourier {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → F} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [eLpNorm_two_eq_rpow, eLpNorm_two_eq_rpow, hf.lintegral_enorm_fourier_sq h2]

omit [CompleteSpace F] in
/-- The modulus of the multiplier `(2πiω)^k` of `Real.fourier_iteratedDeriv` is `(2π|ω|)^k`. -/
private theorem norm_two_pi_I_mul_pow_smul {k : ℕ} (ω : ℝ) (z : F) :
    ‖(2 * Real.pi * Complex.I * ω) ^ k • z‖ = ‖((2 * Real.pi * |ω|) ^ k : ℝ) • z‖ := by
  have hbase : ‖(2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ))‖ = 2 * Real.pi * |ω| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [norm_smul, norm_smul, norm_pow, hbase, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * |ω|)]

/-- **The one-variable weighted Sobolev identity**, Mathlib's `2π` Fourier convention:
`‖g^{(k)}‖_{L²} = ‖(2π|ω|)^k 𝓕 g‖_{L²}`.

The hypotheses are exactly those of `Real.fourier_iteratedDeriv` (`g` is `C^N` and all its
derivatives up to order `N` are integrable, with `k ≤ N`) together with the square-integrability
of `g^{(k)}` needed by Plancherel. The weight `(2π|ω|)^k` is the modulus of the multiplier
`(2πiω)^k` produced by `Real.fourier_iteratedDeriv`. -/
theorem eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier {g : ℝ → F} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (hmem : MemLp (iteratedDeriv k g) 2 volume) :
    eLpNorm (iteratedDeriv k g) 2 volume
      = eLpNorm (fun ω : ℝ ↦ ((2 * Real.pi * |ω|) ^ k : ℝ) • 𝓕 g ω) 2 volume := by
  have hF : 𝓕 (iteratedDeriv k g)
      = fun ω : ℝ ↦ (2 * Real.pi * Complex.I * ω) ^ k • 𝓕 g ω :=
    Real.fourier_iteratedDeriv hg hint hk
  calc eLpNorm (iteratedDeriv k g) 2 volume
      = eLpNorm (𝓕 (iteratedDeriv k g)) 2 volume :=
        ((hint k hk).eLpNorm_fourier hmem).symm
    _ = eLpNorm (fun ω : ℝ ↦ (2 * Real.pi * Complex.I * ω) ^ k • 𝓕 g ω) 2 volume := by rw [hF]
    _ = eLpNorm (fun ω : ℝ ↦ ((2 * Real.pi * |ω|) ^ k : ℝ) • 𝓕 g ω) 2 volume :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω =>
          norm_two_pi_I_mul_pow_smul ω (𝓕 g ω))

/-- The frequency-weighted Fourier transform of a function whose `k`-th derivative is
square-integrable is itself square-integrable, Mathlib's `2π` convention. -/
theorem memLp_two_pow_smul_fourier {g : ℝ → F} {N : ℕ∞} {k : ℕ}
    (hg : ContDiff ℝ N g) (hint : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n g) volume)
    (hk : k ≤ N) (hmem : MemLp (iteratedDeriv k g) 2 volume) :
    MemLp (fun ω : ℝ ↦ ((2 * Real.pi * |ω|) ^ k : ℝ) • 𝓕 g ω) 2 volume := by
  have hg0 : Integrable g volume := by
    have h := hint 0 (by simp)
    rwa [iteratedDeriv_zero] at h
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hg0
  have hweight : Continuous fun ω : ℝ => ((2 * Real.pi * |ω|) ^ k : ℝ) := by fun_prop
  refine ⟨(hweight.smul hcont).aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier hg hint hk hmem]
  exact hmem.eLpNorm_lt_top

end MeasureTheory

namespace SchwartzMap

section Deriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `k`-th derivative of a Schwartz function on `ℝ` is the `k`-fold iterate of
`SchwartzMap.derivCLM`, in particular again a Schwartz function. -/
theorem iteratedDeriv_eq_iterate_derivCLM (k : ℕ) (g : 𝓢(ℝ, F)) :
    iteratedDeriv k ⇑g = ⇑((derivCLM ℝ F)^[k] g) := by
  induction k generalizing g with
  | zero => simp
  | succ n ih =>
      have hstep : deriv (⇑g) = ⇑(derivCLM ℝ F g) := funext fun x => (derivCLM_apply ℝ g x).symm
      rw [iteratedDeriv_succ', hstep, ih, Function.iterate_succ_apply]

/-- Every derivative of a Schwartz function on `ℝ` is integrable. -/
theorem integrable_iteratedDeriv (k : ℕ) (g : 𝓢(ℝ, F)) :
    Integrable (iteratedDeriv k ⇑g) volume := by
  rw [iteratedDeriv_eq_iterate_derivCLM]
  exact SchwartzMap.integrable _

/-- Every derivative of a Schwartz function on `ℝ` is square-integrable. -/
theorem memLp_two_iteratedDeriv (k : ℕ) (g : 𝓢(ℝ, F)) :
    MemLp (iteratedDeriv k ⇑g) 2 volume := by
  rw [iteratedDeriv_eq_iterate_derivCLM]
  exact SchwartzMap.memLp _ 2 volume

end Deriv

section Fourier

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The one-variable weighted Sobolev identity for Schwartz functions**, Mathlib's `2π`
Fourier convention: `‖g^{(k)}‖_{L²} = ‖(2π|ω|)^k 𝓕 g‖_{L²}`. Every hypothesis of
`MeasureTheory.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier` is automatic here. -/
theorem eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier (k : ℕ) (g : 𝓢(ℝ, F)) :
    eLpNorm (iteratedDeriv k ⇑g) 2 volume
      = eLpNorm (fun ω : ℝ ↦ ((2 * Real.pi * |ω|) ^ k : ℝ) • 𝓕 (⇑g) ω) 2 volume :=
  MeasureTheory.eLpNorm_iteratedDeriv_eq_eLpNorm_pow_smul_fourier (N := ⊤) (g.smooth ⊤)
    (fun n _ => integrable_iteratedDeriv n g) le_top (memLp_two_iteratedDeriv k g)

/-- The frequency-weighted Fourier transform of a Schwartz function on `ℝ` is
square-integrable, Mathlib's `2π` convention. -/
theorem memLp_two_pow_smul_fourier (k : ℕ) (g : 𝓢(ℝ, F)) :
    MemLp (fun ω : ℝ ↦ ((2 * Real.pi * |ω|) ^ k : ℝ) • 𝓕 (⇑g) ω) 2 volume :=
  MeasureTheory.memLp_two_pow_smul_fourier (N := ⊤) (g.smooth ⊤)
    (fun n _ => integrable_iteratedDeriv n g) le_top (memLp_two_iteratedDeriv k g)

end Fourier

end SchwartzMap
