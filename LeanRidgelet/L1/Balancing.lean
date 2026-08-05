/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs
public import LeanRidgelet.ToMathlib.YoungConvolution
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# L1 theory: well-definedness of the ridgelet transform and duality

The formalized rows of the balancing theorem `thm:existence`, the continuity proposition
`prop:conti.L1`, and the duality `thm:dual`.

## Main results

* `LeanRidgelet.l1_ridgelet_pointwise_convergent_L1_bounded`: for `f ∈ L¹(ℝ^m)` and a bounded
  continuous `ψ` the ridgelet integral converges absolutely at every parameter, with
  `‖R_ψ f (a, b)‖ ≤ ‖f‖₁ ‖ψ‖_∞ ‖a‖^s`.
* `LeanRidgelet.l1_weakRidgeletTransform_eq_euclidean`: the weak (Radon) definition of the
  transform agrees with the strong Euclidean one at `s = 1`.
* `LeanRidgelet.l1_balancing_weakRidgeletTransform_memLp`: the `L^p` row, through the
  convolution form `eq:convridge` and Young's inequality.
* `LeanRidgelet.l1_ridgeletTransform_bounded_L1_Linfty`: `prop:conti.L1`.
* `LeanRidgelet.l1_dualRidgeletTransform_pairing`: `thm:dual`.

## Deviations from the article

* `l1_balancing_weakRidgeletTransform_memLp` adds `1 ≤ p`, implicit in the article's use of
  `L^p` as a Banach space. No almost-everywhere refinement in the direction `u` is needed: the
  line--hyperplane splitting gives the statement for every fixed direction.
* `l1_ridgeletTransform_bounded_L1_Linfty` is stated in the `s = 0` normalization; see its
  docstring for the counterexample at `s = 1`.
* The remaining rows of `thm:existence` (`𝒟 × 𝒟'`, `ℰ' × 𝒟'`, `𝒮 × 𝒮'`, `𝒪_C' × 𝒮'`,
  `𝒟_{L¹}' × 𝒟_{L^p}'`) need the distribution classes on `𝕐^{m+1}` and are deferred.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Absolute convergence and the agreement of the weak and Euclidean definitions -/

/-- Section 3.1 and the `L¹ × (L^p ∩ C⁰)` row of the balancing theorem `thm:existence`, strong
form: for `f ∈ L¹(ℝ^m)` and a bounded continuous `ψ`, the Euclidean ridgelet integral converges
absolutely at every parameter and satisfies `‖R_ψ f (a, b)‖ ≤ ‖f‖₁ ‖ψ‖_∞ ‖a‖^s`. -/
theorem l1_ridgelet_pointwise_convergent_L1_bounded (m : ℕ) [NeZero m] (s : ℝ)
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ} {C : ℝ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∀ z, ‖ψ z‖ ≤ C)
    (p : RidgeletParameterSpace m) :
    Integrable (fun x => f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ))
      volume ∧
    ‖euclideanRidgeletTransform m s ψ f p‖ ≤ (∫ x, ‖f x‖) * C * ‖p.1‖ ^ s := by
  have hr : (0 : ℝ) ≤ ‖p.1‖ ^ s := Real.rpow_nonneg (norm_nonneg _) s
  have hgc : Continuous fun x : InputSpace m =>
      conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ) :=
    ((RCLike.continuous_conj.comp
      (hψc.comp ((continuous_const.inner continuous_id).sub continuous_const))).mul
      continuous_const)
  have hgb : ∀ x : InputSpace m,
      ‖conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖ ≤ C * ‖p.1‖ ^ s := by
    intro x
    have hnr : ‖((‖p.1‖ ^ s : ℝ) : ℂ)‖ = ‖p.1‖ ^ s := by
      simp [abs_of_nonneg hr]
    rw [norm_mul, RCLike.norm_conj, hnr]
    exact mul_le_mul_of_nonneg_right (hψb _) hr
  have hint : Integrable (fun x => f x *
      (conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ))) volume :=
    hf.mul_bdd hgc.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  refine ⟨by simpa [mul_assoc] using hint, ?_⟩
  have hle : ‖euclideanRidgeletTransform m s ψ f p‖ ≤
      ∫ x, ‖f x‖ * (C * ‖p.1‖ ^ s) := by
    simp only [euclideanRidgeletTransform]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (hf.norm.mul_const _) (Filter.Eventually.of_forall fun x => ?_)
    calc ‖f x * conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖
        = ‖f x‖ * ‖conj (ψ (inner ℝ p.1 x - p.2)) * ((‖p.1‖ ^ s : ℝ) : ℂ)‖ := by
          rw [mul_assoc, norm_mul]
      _ ≤ ‖f x‖ * (C * ‖p.1‖ ^ s) := mul_le_mul_of_nonneg_left (hgb x) (norm_nonneg _)
  refine hle.trans_eq ?_
  rw [integral_mul_const, mul_assoc]

/-- Remark after Definition 4.1: for a locally integrable ridgelet function the weak (Radon)
definition of the ridgelet transform coincides with the strong Euclidean one at `s = 1`, via
`a = u / α`, `b = β / α`. -/
theorem l1_weakRidgeletTransform_eq_euclidean (m : ℕ) [NeZero m]
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    {u : InputSpace m} (hu : ‖u‖ = 1) {α β : ℝ} (hα : 0 < α) :
    weakRidgeletTransform m ψ f u α β =
      euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) := by
  obtain ⟨C, hψC⟩ := hψb
  have hα' : α ≠ 0 := ne_of_gt hα
  -- the Euclidean integrand with the constants factored out
  set g : InputSpace m → ℂ := fun x =>
    f x * conj (ψ ((inner ℝ u x - β) / α)) with hg_def
  set F : ℝ → ℂ := fun p =>
    radonTransform f u p * conj (ψ ((p - β) / α)) with hF_def
  have hgint : Integrable g volume := by
    refine hf.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (RCLike.continuous_conj.comp
        (hψc.comp (by fun_prop))).aestronglyMeasurable
    · rw [RCLike.norm_conj]
      exact hψC _
  -- the measure-preserving orthogonal splitting `(p, y) ↦ p • u + y`
  let j : ℝ ≃ₗᵢ[ℝ] ↥(ℝ ∙ u) := LinearIsometryEquiv.toSpanUnitSingleton u hu
  let Ψ : WithLp 2 (ℝ × ↥((ℝ ∙ u)ᗮ)) ≃ₗᵢ[ℝ] InputSpace m :=
    (LinearIsometryEquiv.withLpProdCongr 2 j
      (LinearIsometryEquiv.refl ℝ ↥((ℝ ∙ u)ᗮ))).trans
      (ℝ ∙ u).orthogonalDecomposition.symm
  let M : (ℝ × ↥((ℝ ∙ u)ᗮ)) ≃ᵐ InputSpace m :=
    (MeasurableEquiv.toLp 2 (ℝ × ↥((ℝ ∙ u)ᗮ))).trans Ψ.toMeasurableEquiv
  have hM : ∀ py : ℝ × ↥((ℝ ∙ u)ᗮ), M py = py.1 • u + (py.2 : InputSpace m) := by
    intro py
    change Ψ (WithLp.toLp 2 py) = _
    simp [Ψ, j, LinearIsometryEquiv.withLpProdCongr]
  have hmp : MeasurePreserving (⇑M)
      (volume : Measure (ℝ × ↥((ℝ ∙ u)ᗮ))) (volume : Measure (InputSpace m)) :=
    (Ψ.measurePreserving).comp (WithLp.volume_preserving_toLp ℝ ↥((ℝ ∙ u)ᗮ))
  -- the inner integral over the orthogonal complement
  have hip : ∀ (p : ℝ) (y : ↥((ℝ ∙ u)ᗮ)),
      inner ℝ u ((p • u + (y : InputSpace m)) : InputSpace m) = p := by
    intro p y
    have hy : inner ℝ u (y : InputSpace m) = 0 :=
      ((Submodule.mem_orthogonal (ℝ ∙ u) (y : InputSpace m)).mp y.2) u
        (Submodule.mem_span_singleton_self u)
    rw [inner_add_right, real_inner_smul_right, hy, real_inner_self_eq_norm_sq, hu]
    simp
  have hinner : ∀ p : ℝ, (∫ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m))) = F p := by
    intro p
    have hcongr : ∀ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m)) =
          f (p • u + (y : InputSpace m)) * conj (ψ ((p - β) / α)) := by
      intro y
      simp only [hg_def, hip p y]
    calc (∫ y : ↥((ℝ ∙ u)ᗮ), g (p • u + (y : InputSpace m)))
        = ∫ y : ↥((ℝ ∙ u)ᗮ),
            f (p • u + (y : InputSpace m)) * conj (ψ ((p - β) / α)) :=
          integral_congr_ae (Filter.Eventually.of_forall hcongr)
      _ = (∫ y : ↥((ℝ ∙ u)ᗮ), f (p • u + (y : InputSpace m))) * conj (ψ ((p - β) / α)) :=
          integral_mul_const _ _
      _ = F p := rfl
  -- Fubini through the splitting
  have hFg : ∫ p : ℝ, F p = ∫ x, g x := by
    have hcomp : ∫ x, g x = ∫ py : ℝ × ↥((ℝ ∙ u)ᗮ), g (M py) :=
      (hmp.integral_comp M.measurableEmbedding g).symm
    have hint : Integrable (fun py : ℝ × ↥((ℝ ∙ u)ᗮ) => g (M py)) volume := by
      have := (hmp.integrable_comp_emb M.measurableEmbedding (g := g)).mpr hgint
      exact this
    rw [hcomp]
    rw [Measure.volume_eq_prod] at hint ⊢
    rw [MeasureTheory.integral_prod _ hint]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)).symm
    rw [← hinner p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change g (M (p, y)) = g (p • u + (y : InputSpace m))
    rw [hM (p, y)]
  -- affine change of variables in the radial variable
  have hsub : ∫ z : ℝ, F (α * z + β) = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := by
    calc ∫ z : ℝ, F (α * z + β)
        = ∫ z : ℝ, (fun w : ℝ => F (w + β)) (α • z) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp [smul_eq_mul]
      _ = |(α ^ Module.finrank ℝ ℝ)⁻¹| • ∫ w : ℝ, F (w + β) :=
          Measure.integral_comp_smul volume (fun w : ℝ => F (w + β)) α
      _ = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := by
          rw [integral_add_right_eq_self (μ := volume) F β]
          congr 1
          rw [Module.finrank_self, pow_one, abs_inv, abs_of_pos hα]
  -- the Euclidean side with the constants factored out
  have hrhs : euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) =
      (α⁻¹ : ℝ) • ∫ x, g x := by
    have hna : (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) = ((α⁻¹ : ℝ) : ℂ) := by
      rw [Real.rpow_one, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hα)]
    have hpt : ∀ x : InputSpace m,
        f x * conj (ψ (inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α)) *
            (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) = ((α⁻¹ : ℝ) : ℂ) * g x := by
      intro x
      have harg : inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α =
          (inner ℝ u x - β) / α := by
        rw [real_inner_smul_left]
        field_simp
      rw [hna, hg_def, harg]
      ring
    calc euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α)
        = ∫ x, f x * conj (ψ (inner ℝ ((α⁻¹ • u : InputSpace m)) x - β / α)) *
            (((‖(α⁻¹ • u : InputSpace m)‖ ^ (1 : ℝ)) : ℝ) : ℂ) := rfl
      _ = ∫ x, ((α⁻¹ : ℝ) : ℂ) * g x :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ((α⁻¹ : ℝ) : ℂ) * ∫ x, g x := integral_const_mul _ _
      _ = (α⁻¹ : ℝ) • ∫ x, g x := by rw [Complex.real_smul]
  -- assemble
  have hweak : ∀ z : ℝ,
      radonTransform f u (α * z + β) * conj (ψ z) = F (α * z + β) := by
    intro z
    have hz : (α * z + β - β) / α = z := by field_simp; ring
    rw [hF_def]
    simp only [hz]
  calc weakRidgeletTransform m ψ f u α β
      = ∫ z : ℝ, F (α * z + β) := by
        unfold weakRidgeletTransform
        exact integral_congr_ae (Filter.Eventually.of_forall hweak)
    _ = (α⁻¹ : ℝ) • ∫ p : ℝ, F p := hsub
    _ = (α⁻¹ : ℝ) • ∫ x, g x := by rw [hFg]
    _ = euclideanRidgeletTransform m 1 ψ f (α⁻¹ • u, β / α) := hrhs.symm

/-! ## The `L^p` row, through the convolution form `eq:convridge` -/

/-- Balancing theorem `thm:existence`, `L¹ × (L^p ∩ C⁰)` row, range statement: for `f ∈ L¹(ℝ^m)`
and a continuous `ψ ∈ L^p(ℝ)` with `1 ≤ p`, the weak ridgelet transform belongs to `L^p` in the
shift `β`, uniformly in the direction `u` and the scale `α`.

The proof is the convolution form `eq:convridge`,
`R_ψ f (u, α, β) = (R[f](u, ·) ⋆ conj ψ~_α)(β)`: the Radon factor is integrable on `ℝ` by
`integrable_radonTransform` and the dilated reflected kernel is in `L^p`, so Young's inequality
`L¹ ⋆ L^p ⊆ L^p` (`MeasureTheory.Integrable.convolution_memLp`) applies. The hypothesis
`1 ≤ p` is implicit in the manuscript's use of `L^p` as a Banach space; the continuity of `ψ`
belongs to the manuscript's class `L^p ∩ C⁰` but is not needed for the membership conclusion.
The remaining rows of `tab:weakridge` require the distribution classes on `𝕐^{m+1}` and are
deferred. -/
theorem l1_balancing_weakRidgeletTransform_memLp (m : ℕ) [NeZero m] (p : ℝ≥0∞) (hp : 1 ≤ p)
    {f : InputSpace m → ℂ} {ψ : ℝ → ℂ}
    (hf : Integrable f volume) (_hψc : Continuous ψ) (hψp : MemLp ψ p volume)
    {u : InputSpace m} (hu : ‖u‖ = 1) {α : ℝ} (hα : 0 < α) :
    MemLp (fun β => weakRidgeletTransform m ψ f u α β) p volume := by
  have hα' : α ≠ 0 := ne_of_gt hα
  -- the dilated, reflected, conjugated convolution kernel of `eq:convridge`
  set k : ℝ → ℂ := fun w => (α⁻¹ : ℝ) • conj (ψ (-α⁻¹ * w)) with hk_def
  -- the weak transform is the convolution of the Radon transform with `k`
  have hconv : ∀ β : ℝ, weakRidgeletTransform m ψ f u α β
      = ∫ t, radonTransform f u t * k (β - t) := by
    intro β
    set H : ℝ → ℂ := fun t => radonTransform f u t * conj (ψ ((t - β) / α)) with hH_def
    have h4 : ∫ t, radonTransform f u t * k (β - t) = (α⁻¹ : ℝ) • ∫ t, H t := by
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have harg : -α⁻¹ * (β - t) = (t - β) / α := by
        field_simp
        ring
      simp only [hk_def, hH_def, harg]
      rw [mul_smul_comm]
    calc weakRidgeletTransform m ψ f u α β
        = ∫ z, (fun w => H (w + β)) (α • z) := by
          unfold weakRidgeletTransform
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          have hz : (α * z + β - β) / α = z := by
            field_simp
            ring
          simp only [hH_def, smul_eq_mul, hz]
      _ = |(α ^ Module.finrank ℝ ℝ)⁻¹| • ∫ w, H (w + β) :=
          Measure.integral_comp_smul volume (fun w => H (w + β)) α
      _ = (α⁻¹ : ℝ) • ∫ t, H t := by
          rw [integral_add_right_eq_self (μ := volume) H β]
          congr 1
          rw [Module.finrank_self, pow_one, abs_inv, abs_of_pos hα]
      _ = ∫ t, radonTransform f u t * k (β - t) := h4.symm
  -- the kernel is in `L^p`
  have hc : (-α⁻¹ : ℝ) ≠ 0 := by
    simp [hα']
  have hdil : MemLp (fun w : ℝ => ψ (-α⁻¹ * w)) p volume := by
    have hemb : MeasurableEmbedding (fun w : ℝ => -α⁻¹ * w) :=
      (Homeomorph.mulLeft₀ (-α⁻¹) hc).measurableEmbedding
    have h1 : MemLp ψ p (Measure.map (fun w : ℝ => -α⁻¹ * w) volume) := by
      rw [Real.map_volume_mul_left hc]
      exact hψp.smul_measure ENNReal.ofReal_ne_top
    exact hemb.memLp_map_measure_iff.mp h1
  have hstar : MemLp (fun w : ℝ => conj (ψ (-α⁻¹ * w))) p volume := by
    have hfun2 : (fun w : ℝ => conj (ψ (-α⁻¹ * w)))
        = star fun w : ℝ => ψ (-α⁻¹ * w) := by
      funext w
      simp
    rw [hfun2]
    exact hdil.star
  have hkp : MemLp k p volume := by
    rw [hk_def]
    exact hstar.const_smul (α⁻¹ : ℝ)
  -- Young's inequality through the Radon transform
  have hR : Integrable (radonTransform f u) volume := integrable_radonTransform hf u hu
  have hY := hR.convolution_memLp hp hkp
  have hfun : (fun β => weakRidgeletTransform m ψ f u α β)
      = fun x => ∫ t, radonTransform f u t * k (x - t) := funext hconv
  rw [hfun]
  exact hY

/-! ## Continuity (`prop:conti.L1`) and duality (`thm:dual`) -/

/-- The explicit constant behind `prop:conti.L1`: in the `s = 0` normalization the ridgelet
transform of an integrable signal is bounded at *every* parameter point by the sup norm of the
ridgelet function, `‖R⁰_ψ f (a, b)‖ ≤ ‖ψ‖_∞ ‖f‖₁`, with `‖ψ‖_∞` the Schwartz seminorm `(0, 0)`.
This is the witness used by `l1_ridgeletTransform_bounded_L1_Linfty`, and it is what makes the
value of the operator-norm bound checkable rather than existential. -/
theorem norm_euclideanRidgeletTransform_zero_le (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ)
    {f : InputSpace m → ℂ} (hf : Integrable f volume) (q : RidgeletParameterSpace m) :
    ‖euclideanRidgeletTransform m 0 (⇑ψ) f q‖
      ≤ (SchwartzMap.seminorm ℝ 0 0) ψ * ∫ x, ‖f x‖ := by
  have hb : ∀ z : ℝ, ‖ψ z‖ ≤ (SchwartzMap.seminorm ℝ 0 0) ψ := fun z =>
    SchwartzMap.norm_le_seminorm ℝ ψ z
  have h := (l1_ridgelet_pointwise_convergent_L1_bounded m 0 hf ψ.continuous hb q).2
  rw [Real.rpow_zero, mul_one] at h
  calc ‖euclideanRidgeletTransform m 0 (⇑ψ) f q‖
      ≤ (∫ x, ‖f x‖) * (SchwartzMap.seminorm ℝ 0 0) ψ := h
    _ = (SchwartzMap.seminorm ℝ 0 0) ψ * ∫ x, ‖f x‖ := mul_comm _ _

/-- Proposition 4.3 (`prop:conti.L1`) in the `s = 0` normalization: for a Schwartz ridgelet
function, the ridgelet transform is bounded from `L¹(ℝ^m)` to `L^∞(𝕐^{m+1})` with operator
norm at most `‖ψ‖_∞`; the bound in fact holds at every parameter point, which is stronger
than the essential supremum with respect to any reference measure on `𝕐^{m+1}`.

**Normalization memo (author decision 2026-07-22).** The manuscript states this proposition
in the `s = 1` normalization, where its proof bounds the operator norm by
`sup_{r,β} |r ψ(r β)|`, which is infinite for every `ψ ≠ 0`. Adding `ψ 0 = 0` and all integer
vanishing moments does not repair it: in `m = 1` take `f (x) = |x|^{-1/2} 𝟙_{|x| ≤ 1} ∈ L¹`;
then `R_ψ f (a, 0) = a^{1/2} ∫_{-a}^{a} |z|^{-1/2} conj (ψ z) dz` for `a > 0`, and a `ψ` with
`ψ̂ ∈ C_c^∞` supported away from `0`, `∫ ψ̂ = 0`, and `∫ |ζ|^{-1/2} ψ̂ ζ dζ ≠ 0` has all
integer moments vanishing while the fractional moment `∫ |z|^{-1/2} conj (ψ z) dz` is nonzero,
so `|R_ψ f (a, 0)| → ∞` as `a → ∞`. Following the author's decision, the statement is read in
the `s = 0` normalization of Section 3 (Murata's Euclidean normalization, see the remark after
`eq:eucrid`), with no moment conditions; wherever boundedness of the ridgelet transform
matters, the L1 theory may be read in the `s = 0` normalization throughout, replacing the
weighted measure `‖a‖⁻² da db` of the `s = 1` pairing by the unweighted `da db`. -/
theorem l1_ridgeletTransform_bounded_L1_Linfty (m : ℕ) [NeZero m] (ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, ∀ f : InputSpace m → ℂ, Integrable f volume →
      ∀ q : RidgeletParameterSpace m,
        ‖euclideanRidgeletTransform m 0 (⇑ψ) f q‖ ≤ C * ∫ x, ‖f x‖ := by
  exact ⟨(SchwartzMap.seminorm ℝ 0 0) ψ, fun f hf q =>
    norm_euclideanRidgeletTransform_zero_le m ψ hf q⟩

/-- Theorem 4.5 (`thm:dual`) at function level: the dual ridgelet transform is the dual operator
of the ridgelet transform with respect to the pairing of `L²(𝕐^{m+1}, ‖a‖⁻² da db)` and
`L²(ℝ^m)`. -/
theorem l1_dualRidgeletTransform_pairing (m : ℕ) [NeZero m]
    {ψ : ℝ → ℂ} {f : InputSpace m → ℂ} {T : RidgeletParameterSpace m → ℂ}
    (hf : Integrable f volume) (hψc : Continuous ψ) (hψb : ∃ C, ∀ z, ‖ψ z‖ ≤ C)
    (hT : Integrable
      (fun q : RidgeletParameterSpace m => T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹) volume) :
    ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m =
      ∫ x, f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) := by
  obtain ⟨C, hψC⟩ := hψb
  set g : RidgeletParameterSpace m → ℂ := fun q => T q * ((‖q.1‖ : ℝ) : ℂ)⁻¹ with hg_def
  set K : RidgeletParameterSpace m → InputSpace m → ℂ := fun q x =>
    f x * conj (ψ (inner ℝ q.1 x - q.2)) * conj (g q) with hK_def
  -- almost every parameter has a nonzero weight component
  have hae : ∀ᵐ q : RidgeletParameterSpace m ∂volume, q.1 ≠ 0 := by
    rw [ae_iff]
    have hset : {q : RidgeletParameterSpace m | ¬ q.1 ≠ 0} =
        ({0} : Set (InputSpace m)) ×ˢ (Set.univ : Set ℝ) := by
      ext q
      simp [Set.mem_prod]
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  -- unfold the weighted parameter measure
  have hwmeas : Measurable fun q : RidgeletParameterSpace m =>
      ENNReal.ofReal ((‖q.1‖ ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.norm.pow_const 2).inv)
  have hstep1 :
      ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m =
        ∫ q : RidgeletParameterSpace m,
          ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) := by
    unfold ridgeletParameterMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hwmeas
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (by positivity)]
  -- pointwise identity in the parameter variable
  have hq : ∀ᵐ q : RidgeletParameterSpace m ∂volume,
      ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) =
        ∫ x, K q x := by
    filter_upwards [hae] with q hq1
    have hna : (‖q.1‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hq1
    simp only [euclideanRidgeletTransform, Real.rpow_one, hK_def]
    rw [Complex.real_smul, mul_comm ((((‖q.1‖ ^ 2)⁻¹ : ℝ) : ℂ))
      ((∫ x, f x * conj (ψ (inner ℝ q.1 x - q.2)) * ((‖q.1‖ : ℝ) : ℂ)) * conj (T q)),
      mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg_def, map_mul, map_inv₀, Complex.conj_ofReal]
    have hcne : ((‖q.1‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hna
    push_cast
    field_simp
  -- integrability of the kernel on the product space
  have hKint : Integrable (Function.uncurry K)
      ((volume : Measure (RidgeletParameterSpace m)).prod
        (volume : Measure (InputSpace m))) := by
    have hdom : Integrable (fun p : RidgeletParameterSpace m × InputSpace m =>
        ‖g p.1‖ * (C * ‖f p.2‖))
        ((volume : Measure (RidgeletParameterSpace m)).prod
          (volume : Measure (InputSpace m))) :=
      Integrable.mul_prod hT.norm (hf.norm.const_mul C)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable
          (fun p : RidgeletParameterSpace m × InputSpace m => f p.2)
          ((volume : Measure (RidgeletParameterSpace m)).prod
            (volume : Measure (InputSpace m))) :=
        hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      have h2 : AEStronglyMeasurable
          (fun p : RidgeletParameterSpace m × InputSpace m => conj (g p.1))
          ((volume : Measure (RidgeletParameterSpace m)).prod
            (volume : Measure (InputSpace m))) :=
        (RCLike.continuous_conj.comp_aestronglyMeasurable
          (hT.aestronglyMeasurable.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_fst))
      have h3 : Continuous
          (fun p : RidgeletParameterSpace m × InputSpace m =>
            conj (ψ (inner ℝ p.1.1 p.2 - p.1.2))) := by
        refine RCLike.continuous_conj.comp (hψc.comp ?_)
        exact (Continuous.inner (continuous_fst.fst) continuous_snd).sub
          (continuous_fst.snd)
      exact (h1.mul h3.aestronglyMeasurable).mul h2
    · rw [Function.uncurry_apply_pair, hK_def]
      simp only [norm_mul, RCLike.norm_conj]
      calc ‖f p.2‖ * ‖ψ (inner ℝ p.1.1 p.2 - p.1.2)‖ * ‖g p.1‖
          ≤ ‖f p.2‖ * C * ‖g p.1‖ := by
            have h0 : (0 : ℝ) ≤ ‖g p.1‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hψC _) (norm_nonneg _)) h0
        _ = ‖g p.1‖ * (C * ‖f p.2‖) := by ring
  -- pointwise identity in the input variable
  have hx : ∀ x : InputSpace m,
      ∫ q : RidgeletParameterSpace m, K q x =
        f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) := by
    intro x
    simp only [euclideanDualRidgeletTransform, Real.rpow_one, hK_def]
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hg_def, map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  calc ∫ q, euclideanRidgeletTransform m 1 ψ f q * conj (T q) ∂ridgeletParameterMeasure m
      = ∫ q : RidgeletParameterSpace m,
          ((‖q.1‖ ^ 2)⁻¹ : ℝ) • (euclideanRidgeletTransform m 1 ψ f q * conj (T q)) := hstep1
    _ = ∫ q : RidgeletParameterSpace m, ∫ x, K q x := integral_congr_ae hq
    _ = ∫ x, ∫ q : RidgeletParameterSpace m, K q x := integral_integral_swap hKint
    _ = ∫ x, f x * conj (euclideanDualRidgeletTransform m 1 ψ T x) :=
        integral_congr_ae (Filter.Eventually.of_forall hx)

end LeanRidgelet
