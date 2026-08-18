/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Hilbert-Schmidt integral operators are bounded on `L²`

An integral operator whose kernel is square integrable for the product measure is bounded on `L²`,
with operator norm at most the `L²` norm of the kernel. The two arguments of the kernel range over
two possibly different measure spaces `(α, μ)` and `(β, ν)`: for `k : α × β → ℂ` the operator

  `T f x = ∫ y, f y * conj (k (x, y)) ∂ν`

carries `L² ν` into `L² μ`. This two-space form is what the same-space statement was really proving,
the argument never comparing a point of the source space with a point of the target space; the
same-space case is recovered by taking `β = α` and `ν = μ`.

The proof runs in two steps. Tonelli's theorem turns the square of the product-measure `L²` norm of
`k` into the integral over `x` of the squares of the slice norms `‖k (x, ·)‖_{L²(ν)}`; in particular
almost every slice is again square integrable. On such a slice Cauchy-Schwarz, in the guise of
Hölder's inequality for the exponents `2, 2, 1`, makes `y ↦ f y * conj (k (x, y))` integrable and
bounds `‖T f x‖` by `‖f‖_{L²} * ‖k (x, ·)‖_{L²}`. Squaring that bound and integrating in `x` gives
the estimate, Tonelli reassembling the slice norms into `‖k‖_{L²(μ ⊗ ν)}`.

## Condition T2: a composite of two square-integrable feature maps

The estimate is then applied twice, to prove the second sufficient condition for boundedness of
`lm ∘ ridge` given in the appendix of arXiv:2405.13682: square integrability of both feature maps
already makes the composite bounded. With a data space `(α, μ)`, a parameter space `(β, ν)` and
feature maps `φ ψ : α × β → ℂ` in `L² (μ ⊗ ν)`, the ridgelet transform

  `R f ξ = ∫ y, f y * conj (ψ (y, ξ)) ∂μ`

is the kernel operator from `(α, μ)` to `(β, ν)` whose kernel is `ψ` with its two arguments
exchanged, and the synthesis

  `T f x = ∫ ξ, R f ξ * conj (φ (x, ξ)) ∂ν`

is the kernel operator from `(β, ν)` to `(α, μ)` with kernel `φ`. Composing the two estimates gives
`‖T f‖_{L²(μ)} ≤ ‖φ‖_{L²(μ ⊗ ν)} * ‖ψ‖_{L²(μ ⊗ ν)} * ‖f‖_{L²(μ)}`. The conjugation in the synthesis
is placed on the feature map `φ`, which is what makes `T` a literal instance of the estimate; the
convention with `φ` unconjugated is this same statement read for the conjugate feature map, whose
`L²` norm is the same.

Only `MeasureTheory.SFinite` is assumed: it is exactly what the Fubini-Tonelli lemmas for
`MeasureTheory.Measure.prod` consume, and it is implied by `MeasureTheory.SigmaFinite`. All
statements are about plain functions together with `MeasureTheory.MemLp` hypotheses, not about the
quotients `MeasureTheory.Lp`, and all norms are the `ℝ≥0∞`-valued `MeasureTheory.eLpNorm`, so that
no finiteness side conditions are needed to state them.

The estimate is also bundled: a square-integrable kernel gives a continuous linear map between the
two scalar `L²` spaces, of operator norm at most the `L²` norm of the kernel.  That bundled form is
what supplies a bounded machine or ridgelet transform to a reconstruction argument, which is the
role the article's boundedness appendix plays.
-/
@[expose] public section

noncomputable section

open scoped ENNReal ComplexConjugate

namespace MeasureTheory

section Slices

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
  {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞}

/-- For a finite nonzero exponent the `p`-th power of `MeasureTheory.eLpNorm` is the
`ℝ≥0∞`-valued integral of `‖·‖ₑ ^ p`. This is the form in which both sides of Tonelli's theorem are
recognised below. -/
theorem eLpNorm_rpow_toReal_eq_lintegral {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    {g : γ → E} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm g p ρ ^ p.toReal = ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂ρ := by
  rw [eLpNorm_eq_eLpNorm' hp0 hptop,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hptop)]

/-- Tonelli's theorem in the form used for Hilbert-Schmidt kernels: the `p`-th power of the
`Lᵖ (μ ⊗ ν)` norm of `k` is the integral over `x` of the `p`-th powers of the slice norms
`‖k (x, ·)‖_{Lᵖ(ν)}`. Both sides are the `ℝ≥0∞`-valued integral of `‖k‖ₑ ^ p`, computed either on
the product or as an iterated integral. -/
theorem lintegral_eLpNorm_rpow_prodMk_left [SFinite ν] (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    {k : α × β → E} (hk : AEStronglyMeasurable k (μ.prod ν)) :
    ∫⁻ x, eLpNorm (fun y ↦ k (x, y)) p ν ^ p.toReal ∂μ = eLpNorm k p (μ.prod ν) ^ p.toReal := by
  have hmeas : AEMeasurable (fun z : α × β ↦ ‖k z‖ₑ ^ p.toReal) (μ.prod ν) :=
    hk.enorm.pow_const _
  calc ∫⁻ x, eLpNorm (fun y ↦ k (x, y)) p ν ^ p.toReal ∂μ
      = ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ p.toReal ∂ν ∂μ :=
        lintegral_congr fun _ ↦ eLpNorm_rpow_toReal_eq_lintegral hp0 hptop
    _ = ∫⁻ z, ‖k z‖ₑ ^ p.toReal ∂μ.prod ν := (lintegral_prod _ hmeas).symm
    _ = eLpNorm k p (μ.prod ν) ^ p.toReal := (eLpNorm_rpow_toReal_eq_lintegral hp0 hptop).symm

/-- Almost every slice of an `Lᵖ` function on a product measure is again `Lᵖ`. This is the
`MeasureTheory.MemLp` analogue of `MeasureTheory.Integrable.prod_right_ae`, and the exponent `p` is
arbitrary: for `0 < p < ∞` it follows from Tonelli, for `p = ∞` from the almost-everywhere bound by
the essential supremum, and for `p = 0` it is measurability alone. -/
theorem MemLp.prodMk_left [SFinite ν] {k : α × β → E} (hk : MemLp k p (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ k (x, y)) p ν := by
  rcases eq_or_ne p 0 with rfl | hp0
  · filter_upwards [hk.1.prodMk_left] with x hx using ⟨hx, by simp⟩
  rcases eq_or_ne p ∞ with rfl | hptop
  · have hbound : ∀ᵐ z ∂μ.prod ν, ‖k z‖ₑ ≤ eLpNormEssSup k (μ.prod ν) := ae_le_eLpNormEssSup
    filter_upwards [hk.1.prodMk_left, Measure.ae_ae_of_ae_prod hbound] with x hx hxb
    refine ⟨hx, ?_⟩
    rw [eLpNorm_exponent_top]
    exact lt_of_le_of_lt (essSup_le_of_ae_le _ hxb) (by simpa using hk.2)
  · have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    have hfin : ∫⁻ x, eLpNorm (fun y ↦ k (x, y)) p ν ^ p.toReal ∂μ ≠ ∞ := by
      rw [lintegral_eLpNorm_rpow_prodMk_left hp0 hptop hk.1]
      exact (ENNReal.rpow_lt_top_of_nonneg hq.le hk.2.ne).ne
    have hmeas : AEMeasurable (fun x ↦ eLpNorm (fun y ↦ k (x, y)) p ν ^ p.toReal) μ := by
      have h : AEMeasurable (fun x ↦ ∫⁻ y, ‖k (x, y)‖ₑ ^ p.toReal ∂ν) μ :=
        (hk.1.enorm.pow_const _).lintegral_prod_right'
      exact h.congr (.of_forall fun x ↦ (eLpNorm_rpow_toReal_eq_lintegral hp0 hptop).symm)
    filter_upwards [hk.1.prodMk_left, ae_lt_top' hmeas hfin] with x hx hxfin
    refine ⟨hx, ?_⟩
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos hq] at hxfin
    exact hxfin.ne rfl

end Slices

section Swap

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {p : ℝ≥0∞} {k : α × β → E}

/-- Exchanging the two arguments of a kernel leaves its `Lᵖ` norm unchanged, because
`Prod.swap` is measure preserving from `ν ⊗ μ` to `μ ⊗ ν`. -/
theorem eLpNorm_prod_swap (hk : AEStronglyMeasurable k (μ.prod ν)) :
    eLpNorm (fun z : β × α ↦ k z.swap) p (ν.prod μ) = eLpNorm k p (μ.prod ν) :=
  eLpNorm_comp_measurePreserving hk Measure.measurePreserving_swap

/-- Exchanging the two arguments of an `Lᵖ` kernel gives an `Lᵖ` kernel for the exchanged product
measure. This is `MeasureTheory.AEMeasurable.prod_swap` for `MeasureTheory.MemLp`. -/
theorem MemLp.prod_swap (hk : MemLp k p (μ.prod ν)) :
    MemLp (fun z : β × α ↦ k z.swap) p (ν.prod μ) :=
  hk.comp_measurePreserving Measure.measurePreserving_swap

end Swap

section CauchySchwarz

variable {β : Type*} [MeasurableSpace β] {ν : Measure β} {f g : β → ℂ}

/-- Cauchy-Schwarz for the sesquilinear pairing of two square-integrable functions: the pairing is
dominated in absolute value by the product of the two `L²` norms. This is Hölder's inequality for
the exponents `2, 2, 1` applied to `y ↦ f y * conj (g y)`, preceded by the triangle inequality for
the Bochner integral. -/
theorem enorm_integral_mul_conj_le (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖∫ y, f y * conj (g y) ∂ν‖ₑ ≤ eLpNorm f 2 ν * eLpNorm g 2 ν := by
  calc ‖∫ y, f y * conj (g y) ∂ν‖ₑ
      ≤ ∫⁻ y, ‖f y * conj (g y)‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y ↦ f y * conj (g y)) 1 ν := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ 1 * eLpNorm f 2 ν * eLpNorm g 2 ν :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 (fun a b ↦ a * conj b) 1
          (.of_forall fun y ↦ by simp)
    _ = eLpNorm f 2 ν * eLpNorm g 2 ν := by rw [one_mul]

/-- The product of two square-integrable functions, one of them conjugated, is integrable.
Hölder's inequality for the exponents `2, 2, 1`. -/
theorem integrable_mul_conj (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun y ↦ f y * conj (g y)) ν :=
  hf.integrable_mul hg.star

end CauchySchwarz

section HilbertSchmidt

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite ν] {k : α × β → ℂ} {f : β → ℂ}

/-- **Slice integrability.** If the kernel `k` is square integrable for the product measure and `f`
is square integrable, then for almost every `x` the integrand `y ↦ f y * conj (k (x, y))` defining
`T f x` is integrable: almost every slice `k (x, ·)` lies in `L²` by
`MeasureTheory.MemLp.prodMk_left`, and the product of two `L²` functions is `L¹`. -/
theorem integrable_mul_conj_kernel_ae (hk : MemLp k 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f y * conj (k (x, y))) ν := by
  filter_upwards [hk.prodMk_left] with x hx using integrable_mul_conj hf hx

/-- **Pointwise bound.** For almost every `x` the value `T f x` is bounded by the product of the
`L²` norm of `f` and the `L²` norm of the slice `k (x, ·)`. This is Cauchy-Schwarz on the slice,
available for almost every `x` because almost every slice is square integrable. -/
theorem enorm_integral_mul_conj_kernel_le_ae (hk : MemLp k 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ
      ≤ eLpNorm f 2 ν * eLpNorm (fun y ↦ k (x, y)) 2 ν := by
  filter_upwards [hk.prodMk_left] with x hx using enorm_integral_mul_conj_le hf hx

/-- Almost everywhere strong measurability of `T f`, from the a.e. strong measurability of the
integrand on the product measure. -/
theorem aestronglyMeasurable_integral_mul_conj_kernel (hk : MemLp k 2 (μ.prod ν))
    (hf : MemLp f 2 ν) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f y * conj (k (x, y)) ∂ν) μ := by
  have hconj : AEStronglyMeasurable (fun z : α × β ↦ conj (k z)) (μ.prod ν) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hk.1
  exact (hf.1.comp_snd.mul hconj).integral_prod_right'

/-- **The main estimate.** The operator `T` with square-integrable kernel `k` maps `L² ν` into
`L² μ` with `‖T f‖_{L²(μ)} ≤ ‖k‖_{L²(μ ⊗ ν)} * ‖f‖_{L²(ν)}`. The pointwise Cauchy-Schwarz bound is
squared and integrated in `x`, and Tonelli reassembles the squared slice norms into the
product-measure norm of `k`. -/
theorem eLpNorm_integral_mul_conj_kernel_le (hk : MemLp k 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    eLpNorm (fun x ↦ ∫ y, f y * conj (k (x, y)) ∂ν) 2 μ
      ≤ eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hFne : eLpNorm f 2 ν ^ (2 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf.2.ne).ne
  have hpow : ∀ᵐ x ∂μ, ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ ^ (2 : ℝ)
      ≤ eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm (fun y ↦ k (x, y)) 2 ν ^ (2 : ℝ) := by
    filter_upwards [enorm_integral_mul_conj_kernel_le_ae hk hf] with x hx
    calc ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ ^ (2 : ℝ)
        ≤ (eLpNorm f 2 ν * eLpNorm (fun y ↦ k (x, y)) 2 ν) ^ (2 : ℝ) := by gcongr
      _ = eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm (fun y ↦ k (x, y)) 2 ν ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hint : ∫⁻ x, ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ ^ (2 : ℝ) ∂μ
      ≤ eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm k 2 (μ.prod ν) ^ (2 : ℝ) := by
    calc ∫⁻ x, ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ∫⁻ x, eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm (fun y ↦ k (x, y)) 2 ν ^ (2 : ℝ) ∂μ :=
          lintegral_mono_ae hpow
      _ = eLpNorm f 2 ν ^ (2 : ℝ) * ∫⁻ x, eLpNorm (fun y ↦ k (x, y)) 2 ν ^ (2 : ℝ) ∂μ :=
          lintegral_const_mul' _ _ hFne
      _ = eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm k 2 (μ.prod ν) ^ (2 : ℝ) := by
          rw [← htwo, lintegral_eLpNorm_rpow_prodMk_left two_ne_zero (by simp) hk.1]
  have hroot : ∀ a : ℝ≥0∞, (a ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = a := fun a ↦ by
    rw [← ENNReal.rpow_mul]; norm_num
  calc eLpNorm (fun x ↦ ∫ y, f y * conj (k (x, y)) ∂ν) 2 μ
      = (∫⁻ x, ‖∫ y, f y * conj (k (x, y)) ∂ν‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero (by simp), htwo]
    _ ≤ (eLpNorm f 2 ν ^ (2 : ℝ) * eLpNorm k 2 (μ.prod ν) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = eLpNorm f 2 ν * eLpNorm k 2 (μ.prod ν) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot, hroot]
    _ = eLpNorm k 2 (μ.prod ν) * eLpNorm f 2 ν := mul_comm _ _

/-- **The main estimate, membership half.** With a square-integrable kernel, `T f` is again square
integrable whenever `f` is. -/
theorem memLp_integral_mul_conj_kernel (hk : MemLp k 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    MemLp (fun x ↦ ∫ y, f y * conj (k (x, y)) ∂ν) 2 μ :=
  ⟨aestronglyMeasurable_integral_mul_conj_kernel hk hf,
    lt_of_le_of_lt (eLpNorm_integral_mul_conj_kernel_le hk hf) (ENNReal.mul_lt_top hk.2 hf.2)⟩

end HilbertSchmidt

section FeatureComposite

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν] {φ ψ : α × β → ℂ} {f : α → ℂ}

/-- **The ridgelet transform is bounded.** As an operator from the data space `(α, μ)` to the
parameter space `(β, ν)`, the transform against `ψ` has kernel `ψ` with its two arguments
exchanged, so the Hilbert-Schmidt estimate applies and `MeasureTheory.eLpNorm_prod_swap` restores
the original order in the bound. -/
theorem eLpNorm_integral_feature_analysis_le (hψ : MemLp ψ 2 (μ.prod ν)) (hf : MemLp f 2 μ) :
    eLpNorm (fun ξ ↦ ∫ y, f y * conj (ψ (y, ξ)) ∂μ) 2 ν
      ≤ eLpNorm ψ 2 (μ.prod ν) * eLpNorm f 2 μ := by
  have hswap : eLpNorm (fun z : β × α ↦ ψ z.swap) 2 (ν.prod μ) = eLpNorm ψ 2 (μ.prod ν) :=
    eLpNorm_prod_swap hψ.1
  have hle := eLpNorm_integral_mul_conj_kernel_le hψ.prod_swap hf
  rw [hswap] at hle
  exact hle

/-- **The ridgelet transform is bounded, membership half.** The transform of a square-integrable
function against a square-integrable feature map is square integrable on the parameter space. -/
theorem memLp_integral_feature_analysis (hψ : MemLp ψ 2 (μ.prod ν)) (hf : MemLp f 2 μ) :
    MemLp (fun ξ ↦ ∫ y, f y * conj (ψ (y, ξ)) ∂μ) 2 ν :=
  memLp_integral_mul_conj_kernel hψ.prod_swap hf

/-- **Condition T2.** If both feature maps are square integrable for `μ ⊗ ν`, then the composite of
the ridgelet transform against `ψ` and the synthesis against `φ` is bounded on `L² μ`, with
`‖T f‖_{L²(μ)} ≤ ‖φ‖_{L²(μ ⊗ ν)} * ‖ψ‖_{L²(μ ⊗ ν)} * ‖f‖_{L²(μ)}`. Both halves are instances of
`MeasureTheory.eLpNorm_integral_mul_conj_kernel_le`, the analysis with kernel `ψ` from `(α, μ)` to
`(β, ν)`, the synthesis with kernel `φ` from `(β, ν)` back to `(α, μ)`. -/
theorem eLpNorm_integral_feature_composite_le (hφ : MemLp φ 2 (μ.prod ν))
    (hψ : MemLp ψ 2 (μ.prod ν)) (hf : MemLp f 2 μ) :
    eLpNorm (fun x ↦ ∫ ξ, (∫ y, f y * conj (ψ (y, ξ)) ∂μ) * conj (φ (x, ξ)) ∂ν) 2 μ
      ≤ eLpNorm φ 2 (μ.prod ν) * eLpNorm ψ 2 (μ.prod ν) * eLpNorm f 2 μ :=
  calc eLpNorm (fun x ↦ ∫ ξ, (∫ y, f y * conj (ψ (y, ξ)) ∂μ) * conj (φ (x, ξ)) ∂ν) 2 μ
      ≤ eLpNorm φ 2 (μ.prod ν) * eLpNorm (fun ξ ↦ ∫ y, f y * conj (ψ (y, ξ)) ∂μ) 2 ν :=
        eLpNorm_integral_mul_conj_kernel_le hφ (memLp_integral_feature_analysis hψ hf)
    _ ≤ eLpNorm φ 2 (μ.prod ν) * (eLpNorm ψ 2 (μ.prod ν) * eLpNorm f 2 μ) := by
        gcongr
        exact eLpNorm_integral_feature_analysis_le hψ hf
    _ = eLpNorm φ 2 (μ.prod ν) * eLpNorm ψ 2 (μ.prod ν) * eLpNorm f 2 μ := (mul_assoc _ _ _).symm

/-- **Condition T2, membership half.** With two square-integrable feature maps the composite of the
ridgelet transform and the synthesis maps `L² μ` into itself. -/
theorem memLp_integral_feature_composite (hφ : MemLp φ 2 (μ.prod ν)) (hψ : MemLp ψ 2 (μ.prod ν))
    (hf : MemLp f 2 μ) :
    MemLp (fun x ↦ ∫ ξ, (∫ y, f y * conj (ψ (y, ξ)) ∂μ) * conj (φ (x, ξ)) ∂ν) 2 μ :=
  memLp_integral_mul_conj_kernel hφ (memLp_integral_feature_analysis hψ hf)

end FeatureComposite


section Bundled

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite ν] {k : α × β → ℂ}

/-- The integral operator of a square-integrable kernel, as a linear map between the scalar `L²`
spaces.  The image lies in `L²` by `MeasureTheory.memLp_integral_mul_conj_kernel`, and additivity
uses the almost-everywhere slice integrability that lets the integral be split. -/
def hilbertSchmidtKernelLinearMap (hk : MemLp k 2 (μ.prod ν)) : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_integral_mul_conj_kernel hk (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_integral_mul_conj_kernel hk (Lp.memLp f)).toLp _)
        ((memLp_integral_mul_conj_kernel hk (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp g)),
      integrable_mul_conj_kernel_ae hk (Lp.memLp f),
      integrable_mul_conj_kernel_ae hk (Lp.memLp g)] with x h1 h2 h3 h4 hif hig
    have hsplit : ∫ y, (↑↑(f + g) : β → ℂ) y * conj (k (x, y)) ∂ν =
        ∫ y, ((↑↑f : β → ℂ) y * conj (k (x, y)) +
          (↑↑g : β → ℂ) y * conj (k (x, y))) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add f g] with y hy
      rw [hy]
      simp [add_mul]
    rw [h1, h2, Pi.add_apply, h3, h4, hsplit, integral_add hif hig]
  map_smul' c f := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((memLp_integral_mul_conj_kernel hk (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp f))] with x h1 h2 h3
    have hsmul : ∫ y, (↑↑(c • f) : β → ℂ) y * conj (k (x, y)) ∂ν =
        c * ∫ y, (↑↑f : β → ℂ) y * conj (k (x, y)) ∂ν := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c f] with y hy
      rw [hy]
      simp [mul_assoc]
    simp only [RingHom.id_apply]
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, hsmul]

/-- The representative of the operator's value is the pointwise integral. -/
theorem coeFn_hilbertSchmidtKernelLinearMap (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    (hilbertSchmidtKernelLinearMap hk f : α → ℂ) =ᵐ[μ]
      fun x ↦ ∫ y, (f : β → ℂ) y * conj (k (x, y)) ∂ν :=
  MemLp.coeFn_toLp (memLp_integral_mul_conj_kernel hk (Lp.memLp f))

/-- The value of the operator has norm at most the `L²` norm of the kernel times the norm of the
input. -/
theorem norm_hilbertSchmidtKernelLinearMap_le (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ‖hilbertSchmidtKernelLinearMap hk f‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal * ‖f‖ := by
  have hne : eLpNorm k 2 (μ.prod ν) * eLpNorm (f : β → ℂ) 2 ν ≠ ∞ :=
    ENNReal.mul_ne_top hk.2.ne (Lp.eLpNorm_ne_top f)
  have hle := eLpNorm_integral_mul_conj_kernel_le hk (Lp.memLp f)
  have hnorm : ‖hilbertSchmidtKernelLinearMap hk f‖ =
      (eLpNorm (fun x ↦ ∫ y, (f : β → ℂ) y * conj (k (x, y)) ∂ν) 2 μ).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae (coeFn_hilbertSchmidtKernelLinearMap hk f))
  calc ‖hilbertSchmidtKernelLinearMap hk f‖
      = (eLpNorm (fun x ↦ ∫ y, (f : β → ℂ) y * conj (k (x, y)) ∂ν) 2 μ).toReal := hnorm
    _ ≤ (eLpNorm k 2 (μ.prod ν) * eLpNorm (f : β → ℂ) 2 ν).toReal := ENNReal.toReal_mono hne hle
    _ = (eLpNorm k 2 (μ.prod ν)).toReal * ‖f‖ := by
        rw [ENNReal.toReal_mul, Lp.norm_def]

/-- **Hilbert--Schmidt integral operators are bounded.**  A square-integrable kernel defines a
continuous linear map between the scalar `L²` spaces, of norm at most the `L²` norm of the kernel.
This is the bundled form of condition T1 of the article's boundedness appendix, and it is what
supplies a bounded machine or ridgelet transform to the reconstruction argument. -/
def hilbertSchmidtKernelOperator (hk : MemLp k 2 (μ.prod ν)) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (hilbertSchmidtKernelLinearMap hk) (eLpNorm k 2 (μ.prod ν)).toReal
    (norm_hilbertSchmidtKernelLinearMap_le hk)

@[simp]
theorem hilbertSchmidtKernelOperator_apply (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    hilbertSchmidtKernelOperator hk f = hilbertSchmidtKernelLinearMap hk f := rfl

/-- The representative of the bundled operator's value is the pointwise integral. -/
theorem coeFn_hilbertSchmidtKernelOperator (hk : MemLp k 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    (hilbertSchmidtKernelOperator hk f : α → ℂ) =ᵐ[μ]
      fun x ↦ ∫ y, (f : β → ℂ) y * conj (k (x, y)) ∂ν :=
  coeFn_hilbertSchmidtKernelLinearMap hk f

/-- The operator norm of a Hilbert--Schmidt integral operator is at most the `L²` norm of its
kernel. -/
theorem norm_hilbertSchmidtKernelOperator_le (hk : MemLp k 2 (μ.prod ν)) :
    ‖hilbertSchmidtKernelOperator hk‖ ≤ (eLpNorm k 2 (μ.prod ν)).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    (norm_hilbertSchmidtKernelLinearMap_le hk)

end Bundled


section Weighted

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite ν]

/-- **Synthesis from a weighted coefficient space.**  Splitting a positive weight between the
coefficient and the feature turns the kernel estimate into a bound from the weighted `L²` of
coefficients: the operator is controlled by the `L²` norm of the feature divided by the square root
of the weight, against the `L²` norm of the coefficient multiplied by it.  This is the pattern by
which the L1 theory bounds its transforms against a weighted parameter measure.

Note what the hypothesis says.  Finiteness of the weighted feature norm is square integrability of
the feature divided by the square root of the weight, so the operator is again Hilbert--Schmidt, and
a weight cannot by itself escape that: any bound obtained from Cauchy--Schwarz pointwise in the data
variable carries an `L²` majorant and hence a square-integrable kernel.  Escaping compactness
requires orthogonality in the parameter variable, which is what a Plancherel argument supplies and
this estimate does not. -/
theorem eLpNorm_integral_weighted_le {w : β → ℝ} (hw : ∀ y, 0 < w y) {φ : α × β → ℂ} {γ : β → ℂ}
    {K : α × β → ℂ} {Γ : β → ℂ}
    (hKdef : ∀ p : α × β, K p = φ p / (Real.sqrt (w p.2) : ℂ))
    (hΓdef : ∀ y, Γ y = γ y * (Real.sqrt (w y) : ℂ))
    (hK : MemLp K 2 (μ.prod ν)) (hΓ : MemLp Γ 2 ν) :
    eLpNorm (fun x ↦ ∫ y, γ y * conj (φ (x, y)) ∂ν) 2 μ ≤
      eLpNorm K 2 (μ.prod ν) * eLpNorm Γ 2 ν := by
  have hrw : (fun x ↦ ∫ y, γ y * conj (φ (x, y)) ∂ν) =
      fun x ↦ ∫ y, Γ y * conj (K (x, y)) ∂ν := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    have hwy : (Real.sqrt (w y) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.sqrt_pos.2 (hw y))
    simp only [hKdef, hΓdef, map_div₀, Complex.conj_ofReal]
    field_simp
  rw [hrw]
  exact eLpNorm_integral_mul_conj_kernel_le hK hΓ

end Weighted

end MeasureTheory
