/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Balancing
public import LeanRidgelet.Transform.ClassicalSection
public import LeanRidgelet.ToMathlib.L2Duality

/-!
# L1 theory: the Fourier expression of the ridgelet transform

The identity `eq:fstridge`

`(R_ψ f (a, ·))^(ζ) = f̂(ζ a) ⬝ conj (ψ̂ ζ) ⬝ ‖a‖^s`

says that in the bias-frequency domain the ridgelet transform factors as Fourier slice data of
the signal times the conjugate spectrum of the ridgelet function. It is the engine behind
`thm:parseval`, `thm:L2` and the bridge to the unitary Fourier--dilation coordinates of the L2
theory.

## Main results

* `LeanRidgelet.integrable_euclideanRidgeletTransform_bias`,
  `LeanRidgelet.memLp_two_euclideanRidgeletTransform_bias`: the bias sections of the ridgelet
  transform are integrable, and square-integrable for a bounded ridgelet function.
* `LeanRidgelet.angularFourier1D_euclideanRidgeletTransform`: the identity `eq:fstridge`, for
  `f ∈ L¹(ℝ^m)`, `ψ ∈ L¹(ℝ)` and every `(a, ζ)`.

The proof uses the measure-preserving preactivation shear `(a, z) ↦ (a, ⟨a, x⟩ - z)` of
`LeanRidgelet.Transform.ClassicalSection` and a one-dimensional reflected translation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Bias sections of the ridgelet transform -/

/-- Product-space integrability of the ridgelet bias kernel
`(b, x) ↦ f x ⋅ conj (ψ (⟪a,x⟫ - b))`, through the measure-preserving preactivation shear. -/
theorem integrable_ridgelet_bias_kernel {m : ℕ} {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume) (a : InputSpace m) :
    Integrable (fun q : ℝ × InputSpace m => f q.2 * conj (ψ (inner ℝ a q.2 - q.1)))
      ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := by
  have hψconj : Integrable (fun z : ℝ => conj (ψ z)) volume :=
    hψ.norm.mono' (RCLike.continuous_conj.comp_aestronglyMeasurable hψ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by simp)
  have hbase : Integrable (fun q : InputSpace m × ℝ => f q.1 * conj (ψ q.2)) volume := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod hf hψconj
  have hshear : Integrable
      (fun q : InputSpace m × ℝ => f q.1 * conj (ψ (inner ℝ a q.1 - q.2))) volume := by
    have h := integrable_comp_preactivationShear a
      (F := fun q : InputSpace m × ℝ => f q.1 * conj (ψ q.2)) hbase
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    rw [real_inner_comm]
  rw [Measure.volume_eq_prod] at hshear
  exact hshear.swap

/-- For `f ∈ L¹(ℝ^m)` and `ψ ∈ L¹(ℝ)`, the ridgelet transform is integrable in the bias
variable at every fixed weight `a`; the `L¹` half of the fiberwise `L²` theory behind
`thm:parseval` and `thm:L2`. -/
theorem integrable_euclideanRidgeletTransform_bias (m : ℕ) (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume) (a : InputSpace m) :
    Integrable (fun b => euclideanRidgeletTransform m s ψ f (a, b)) volume := by
  have h1 := ((integrable_ridgelet_bias_kernel hf hψ a).integral_prod_left).mul_const
    ((‖a‖ ^ s : ℝ) : ℂ)
  refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
  dsimp only
  rw [← integral_mul_const]
  rfl

/-- For `f ∈ L¹(ℝ^m)` and a bounded continuous `ψ ∈ L¹(ℝ)`, the ridgelet transform is
square-integrable in the bias variable at every fixed weight `a`. -/
theorem memLp_two_euclideanRidgeletTransform_bias (m : ℕ) [NeZero m] (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ} {C : ℝ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume)
    (hψc : Continuous ψ) (hψb : ∀ z, ‖ψ z‖ ≤ C) (a : InputSpace m) :
    MemLp (fun b => euclideanRidgeletTransform m s ψ f (a, b)) 2 volume := by
  refine memLp_two_of_integrable_of_bound
    (integrable_euclideanRidgeletTransform_bias m s hf hψ a)
    (M := (∫ x, ‖f x‖) * C * ‖a‖ ^ s) fun b => ?_
  exact (l1_ridgelet_pointwise_convergent_L1_bounded m s hf hψc hψb (a, b)).2

/-! ## The Fourier expression `eq:fstridge` -/

/-- The Fourier expression of the ridgelet transform in the bias variable (`eq:fstridge`): for
`f ∈ L¹(ℝ^m)` and `ψ ∈ L¹(ℝ)`, at every weight `a` and bias frequency `ζ`,
`(R_ψ f (a, ·))^(ζ) = f̂(ζ a) ⋅ conj (ψ̂ ζ) ⋅ ‖a‖^s`.

This identity is the key link of plan item M7 (B) between the L1 theory and the L2 theory: in
the bias-frequency domain the ridgelet transform is the Fourier slice data `f̂(ζ a)` weighted by
the conjugate activation spectrum, which is exactly the shape of the unitary Fourier--dilation
coordinates `T` of arXiv:2106.04770v2, and it is the engine behind `thm:parseval` and
`thm:L2`. -/
theorem angularFourier1D_euclideanRidgeletTransform (m : ℕ) (s : ℝ)
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ}
    (hf : Integrable f volume) (hψ : Integrable ψ volume)
    (a : InputSpace m) (ζ : ℝ) :
    angularFourier1D (fun b => euclideanRidgeletTransform m s ψ f (a, b)) ζ =
      Fourier.angularFourierIntegralInner f (ζ • a) * conj (angularFourier1D ψ ζ) *
        ((‖a‖ ^ s : ℝ) : ℂ) := by
  set c : ℂ := ((‖a‖ ^ s : ℝ) : ℂ) with hc_def
  set K : ℝ → InputSpace m → ℂ := fun b x =>
    Complex.exp (-Complex.I * ((b * ζ : ℝ) : ℂ)) *
      (f x * conj (ψ (inner ℝ a x - b)) * c) with hK_def
  have hinner1 : ∀ w : ℝ, inner ℝ w ζ = w * ζ := fun w => by
    rw [RCLike.inner_apply, conj_trivial]
    ring
  have hKint : Integrable (Function.uncurry K)
      ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := by
    have hswap := integrable_ridgelet_bias_kernel hf hψ a
    have h1 : Integrable
        (fun q : ℝ × InputSpace m => f q.2 * conj (ψ (inner ℝ a q.2 - q.1)) * c)
        ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := hswap.mul_const c
    have h2 : Integrable
        (fun q : ℝ × InputSpace m => Complex.exp (-Complex.I * ((q.1 * ζ : ℝ) : ℂ)) *
          (f q.2 * conj (ψ (inner ℝ a q.2 - q.1)) * c))
        ((volume : Measure ℝ).prod (volume : Measure (InputSpace m))) := by
      refine Integrable.bdd_mul (c := 1) h1 ?_ (Filter.Eventually.of_forall fun q => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · rw [Complex.norm_exp]
        simp [Complex.mul_re]
    exact h2
  -- the left-hand side as the iterated integral of the kernel
  have hlhs : angularFourier1D (fun b => euclideanRidgeletTransform m s ψ f (a, b)) ζ
      = ∫ b : ℝ, ∫ x : InputSpace m, K b x := by
    unfold angularFourier1D Fourier.angularFourierIntegralInner
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    dsimp only
    rw [hinner1 b]
    unfold euclideanRidgeletTransform
    dsimp only
    rw [← integral_const_mul]
  -- the inner bias integral at a fixed input point
  have hx : ∀ x : InputSpace m, (∫ b : ℝ, K b x)
      = f x * c * (Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ)) *
          conj (angularFourier1D ψ ζ)) := by
    intro x
    set Φ : ℝ → ℂ := fun w =>
      Complex.exp (-Complex.I * (((inner ℝ a x - w) * ζ : ℝ) : ℂ)) * conj (ψ w) with hΦ_def
    have hstep1 : (∫ b : ℝ, K b x) = f x * c * ∫ b : ℝ, Φ (inner ℝ a x - b) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only [hK_def, hΦ_def, sub_sub_cancel]
      ring
    have hstep2 : (∫ b : ℝ, Φ (inner ℝ a x - b)) = ∫ w : ℝ, Φ w :=
      integral_sub_left_eq_self Φ volume (inner ℝ a x)
    have hstep3 : (∫ w : ℝ, Φ w)
        = Complex.exp (-Complex.I * ((inner ℝ a x * ζ : ℝ) : ℂ)) *
            ∫ w : ℝ, Complex.exp (Complex.I * ((w * ζ : ℝ) : ℂ)) * conj (ψ w) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [hΦ_def]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hstep4 : (∫ w : ℝ, Complex.exp (Complex.I * ((w * ζ : ℝ) : ℂ)) * conj (ψ w))
        = conj (angularFourier1D ψ ζ) := by
      unfold angularFourier1D Fourier.angularFourierIntegralInner
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      dsimp only
      rw [hinner1 w, map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
        Complex.conj_ofReal]
      ring_nf
    rw [hstep1, hstep2, hstep3, hstep4]
  -- assemble by Fubini and the definition of the `m`-dimensional angular Fourier integral
  calc angularFourier1D (fun b => euclideanRidgeletTransform m s ψ f (a, b)) ζ
      = ∫ b : ℝ, ∫ x : InputSpace m, K b x := hlhs
    _ = ∫ x : InputSpace m, ∫ b : ℝ, K b x := integral_integral_swap hKint
    _ = ∫ x : InputSpace m,
          Complex.exp (-Complex.I * ((inner ℝ x (ζ • a) : ℝ) : ℂ)) * f x *
            (conj (angularFourier1D ψ ζ) * c) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [hx x]
        have hip : inner ℝ x (ζ • a) = inner ℝ a x * ζ := by
          rw [real_inner_smul_right, real_inner_comm]
          ring
        rw [hip]
        ring
    _ = Fourier.angularFourierIntegralInner f (ζ • a) * conj (angularFourier1D ψ ζ) *
          ((‖a‖ ^ s : ℝ) : ℂ) := by
        rw [← hc_def, mul_assoc, Fourier.angularFourierIntegralInner, ← integral_mul_const]

end LeanRidgelet
