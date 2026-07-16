/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.FiberSynthesis
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Adjoint, null space, and general solution

The definitions here are the abstract forms of equations (25)--(32) in the L2 manuscript.
-/

@[expose] public section

noncomputable section

open scoped InnerProduct ComplexConjugate
open MeasureTheory InnerProductSpace

namespace LeanRidgelet

variable {α H : Type*} [MeasurableSpace α] (μ : Measure α)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalized adjoint `S† / c_L`. -/
def normalizedRightInverse (L : H →L[ℂ] ℂ) : L2 α μ →L[ℂ] BochnerL2 α H μ :=
  ((fiberNormalization L : ℂ)⁻¹) • (fiberSynthesis μ L)†

/-- Projection onto the visible component `(ker S)ᗮ`. -/
def visibleProjection (L : H →L[ℂ] ℂ) :
    BochnerL2 α H μ →L[ℂ] BochnerL2 α H μ :=
  normalizedRightInverse μ L ∘L fiberSynthesis μ L

/-- Pointwise synthesis composed with its adjoint is scalar multiplication by `c_L`. -/
theorem fiberSynthesis_comp_adjoint (L : H →L[ℂ] ℂ) :
    fiberSynthesis μ L ∘L (fiberSynthesis μ L)† =
    (fiberNormalization L : ℂ) • ContinuousLinearMap.id ℂ (L2 α μ) := by
  rw [adjoint_fiberSynthesis, fiberSynthesis_comp_fiberRidgelet,
    apply_rieszRepresenter]

/-- For a nonzero fiber functional, the normalized adjoint is a right inverse of synthesis. -/
theorem normalizedRightInverse_rightInverse {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    Function.RightInverse (normalizedRightInverse μ L) (fiberSynthesis μ L) := by
  intro f
  have hc : (fiberNormalization L : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (fiberNormalization_pos hL))
  change fiberSynthesis μ L
    (((fiberNormalization L : ℂ)⁻¹ • (fiberSynthesis μ L)†) f) = f
  rw [smul_apply, map_smul]
  change (fiberNormalization L : ℂ)⁻¹ •
    ((fiberSynthesis μ L ∘L (fiberSynthesis μ L)†) f) = f
  rw [fiberSynthesis_comp_adjoint]
  simpa only [smul_apply, ContinuousLinearMap.id_apply] using
    inv_smul_smul₀ hc f

/-- The visible projection associated with a nonzero fiber functional is idempotent. -/
theorem isIdempotentElem_visibleProjection {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    IsIdempotentElem (visibleProjection μ L) := by
  change visibleProjection μ L ∘L visibleProjection μ L = visibleProjection μ L
  apply ContinuousLinearMap.ext
  intro γ
  change normalizedRightInverse μ L
      (fiberSynthesis μ L (normalizedRightInverse μ L (fiberSynthesis μ L γ))) =
    normalizedRightInverse μ L (fiberSynthesis μ L γ)
  rw [normalizedRightInverse_rightInverse μ hL]

/-- The adjoint of the visible projection is itself. -/
theorem adjoint_visibleProjection {L : H →L[ℂ] ℂ} :
    (visibleProjection μ L)† = visibleProjection μ L := by
  rw [visibleProjection, normalizedRightInverse, ContinuousLinearMap.adjoint_comp,
    map_smulₛₗ, ContinuousLinearMap.adjoint_adjoint]
  simp

/-- The visible projection is self-adjoint, also when the fiber functional is zero. -/
theorem isSelfAdjoint_visibleProjection {L : H →L[ℂ] ℂ} :
    IsSelfAdjoint (visibleProjection μ L) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact adjoint_visibleProjection μ

/-- The invisible component is exactly the kernel of the visible projection. -/
theorem ker_visibleProjection {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    (visibleProjection μ L).ker = (fiberSynthesis μ L).ker := by
  ext γ
  constructor
  · intro hγ
    change visibleProjection μ L γ = 0 at hγ
    change fiberSynthesis μ L γ = 0
    calc
      fiberSynthesis μ L γ =
          fiberSynthesis μ L (normalizedRightInverse μ L (fiberSynthesis μ L γ)) :=
        (normalizedRightInverse_rightInverse μ hL (fiberSynthesis μ L γ)).symm
      _ = fiberSynthesis μ L (visibleProjection μ L γ) := rfl
      _ = 0 := by rw [hγ, map_zero]
  · intro hγ
    change fiberSynthesis μ L γ = 0 at hγ
    change normalizedRightInverse μ L (fiberSynthesis μ L γ) = 0
    rw [hγ, map_zero]

/-- The range of the visible projection is the orthogonal complement of the synthesis kernel. -/
theorem range_visibleProjection {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    (visibleProjection μ L).range = (fiberSynthesis μ L).kerᗮ := by
  let P := visibleProjection μ L
  have hP : IsIdempotentElem P := isIdempotentElem_visibleProjection μ hL
  calc
    P.range = P.range.topologicalClosure := by
      apply SetLike.coe_injective
      simpa only [Submodule.topologicalClosure_coe] using
        (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP).closure_eq.symm
    _ = P.kerᗮ := by
      symm
      calc
        P.kerᗮ = (P†).range.topologicalClosure := P.orthogonal_ker
        _ = P.range.topologicalClosure := by rw [adjoint_visibleProjection μ]
    _ = (fiberSynthesis μ L).kerᗮ := by rw [ker_visibleProjection μ hL]

omit [CompleteSpace H] in
/-- Pointwise characterization of the null space, corresponding to equation (28). -/
theorem mem_ker_fiberSynthesis_iff (L : H →L[ℂ] ℂ) (γ : BochnerL2 α H μ) :
    γ ∈ LinearMap.ker (fiberSynthesis μ L).toLinearMap ↔ ∀ᵐ x ∂μ, L (γ x) = 0 := by
  change fiberSynthesis μ L γ = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    filter_upwards [h, fiberSynthesis_apply_ae μ L γ] with x hx hS
    exact hS.symm.trans hx
  · intro h
    filter_upwards [h, fiberSynthesis_apply_ae μ L γ] with x hx hS
    exact hS.trans hx

/-- Every solution is a fixed normalized solution plus an element of the kernel. -/
theorem solution_iff_kernel_translate {L : H →L[ℂ] ℂ} (hL : L ≠ 0)
    (f : L2 α μ) (γ : BochnerL2 α H μ) :
    fiberSynthesis μ L γ = f ↔
      γ - normalizedRightInverse μ L f ∈ LinearMap.ker (fiberSynthesis μ L).toLinearMap := by
  change fiberSynthesis μ L γ = f ↔
    fiberSynthesis μ L (γ - normalizedRightInverse μ L f) = 0
  rw [map_sub, normalizedRightInverse_rightInverse μ hL, sub_eq_zero]

/-- The normalized-adjoint solution is the unique minimum-norm solution. -/
theorem normalizedRightInverse_unique_minimal {L : H →L[ℂ] ℂ} (hL : L ≠ 0)
    (f : L2 α μ) :
    ∀ γ : BochnerL2 α H μ,
      fiberSynthesis μ L γ = f →
      ‖normalizedRightInverse μ L f‖ ≤ ‖γ‖ ∧
        (‖normalizedRightInverse μ L f‖ = ‖γ‖ →
          normalizedRightInverse μ L f = γ) := by
  intro γ hγ
  let x := normalizedRightInverse μ L f
  let η := γ - x
  have hη : fiberSynthesis μ L η = 0 := by
    exact (solution_iff_kernel_translate μ hL f γ).mp hγ
  have horth : ⟪x, η⟫_ℂ = 0 := by
    change ⟪(fiberNormalization L : ℂ)⁻¹ • ((fiberSynthesis μ L)†) f, η⟫_ℂ = 0
    rw [inner_smul_left, ContinuousLinearMap.adjoint_inner_left, hη, inner_zero_right,
      mul_zero]
  have hdecomp : γ = x + η := by
    simp [η]
  have hnorm : ‖γ‖ ^ 2 = ‖x‖ ^ 2 + ‖η‖ ^ 2 := by
    rw [hdecomp]
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x η horth
  constructor
  · nlinarith [norm_nonneg γ, norm_nonneg x, sq_nonneg ‖η‖]
  · intro heq
    change ‖x‖ = ‖γ‖ at heq
    rw [← heq] at hnorm
    have hηsq : ‖η‖ ^ 2 = 0 := by
      nlinarith
    have hηnorm : ‖η‖ = 0 := by
      simpa only [sq_eq_zero_iff] using hηsq
    have hηzero : η = 0 := norm_eq_zero.mp hηnorm
    rw [hdecomp, hηzero, add_zero]

section Series

variable {ι : Type*}

omit [CompleteSpace H] in
/-- The product defining a fiber coefficient is Bochner integrable by Hölder's inequality. -/
theorem integrable_fiberCoefficient (e : L2 α μ) (γ : BochnerL2 α H μ) :
    Integrable (fun x ↦ conj (e x) • γ x) μ := by
  have he : MemLp (fun x ↦ conj (e x)) 2 μ := by
    simpa [Function.comp_def, RCLike.conjLIE_apply] using
      RCLike.conjLIE.isometry.lipschitz.comp_memLp (by simp) (Lp.memLp e)
  exact memLp_one_iff_integrable.mp ((Lp.memLp γ).smul he)

/-- The `H`-valued coefficient of `γ` along a scalar `L²` vector `e`. -/
def fiberCoefficient (e : L2 α μ) (γ : BochnerL2 α H μ) : H :=
  ∫ x, conj (e x) • γ x ∂μ

/-- Simple tensors with a fixed scalar factor, as a continuous linear map in the fiber. -/
def fiberEmbedding (e : L2 α μ) : H →L[ℂ] BochnerL2 α H μ :=
  (ContinuousLinearMap.apply ℂ (BochnerL2 α H μ) e).comp
    (((ContinuousLinearMap.lsmul ℂ ℂ).flip : H →L[ℂ] ℂ →L[ℂ] H).compLpL₂ 2 μ)

omit [CompleteSpace H] in
theorem fiberEmbedding_apply (e : L2 α μ) (q : H) :
    fiberEmbedding μ e q = fiberRidgelet μ q e := by
  rfl

/-- The fiber coefficient map is the adjoint of simple-tensor embedding. -/
theorem fiberCoefficient_eq_adjoint_fiberEmbedding (e : L2 α μ)
    (γ : BochnerL2 α H μ) :
    fiberCoefficient μ e γ = ((fiberEmbedding μ e)†) γ := by
  apply ext_inner_left ℂ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_right, fiberCoefficient,
    ← integral_inner (integrable_fiberCoefficient μ e γ), L2.inner_def]
  apply integral_congr_ae
  have hE : fiberEmbedding μ e q =ᵐ[μ] fun x => e x • q := by
    rw [fiberEmbedding_apply]
    exact fiberRidgelet_apply_ae μ q e
  filter_upwards [hE] with x hx
  rw [hx, inner_smul_right, inner_smul_left]

theorem adjoint_fiberEmbedding_comp_apply (e f : L2 α μ) (q : H) :
    ((fiberEmbedding μ e)†) (fiberEmbedding μ f q) = ⟪e, f⟫_ℂ • q := by
  apply ext_inner_left ℂ
  intro r
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def,
    inner_smul_right]
  have he : fiberEmbedding μ e r =ᵐ[μ] fun x => e x • r := by
    rw [fiberEmbedding_apply]
    exact fiberRidgelet_apply_ae μ r e
  have hf : fiberEmbedding μ f q =ᵐ[μ] fun x => f x • q := by
    rw [fiberEmbedding_apply]
    exact fiberRidgelet_apply_ae μ q f
  calc
    (∫ x, ⟪(fiberEmbedding μ e r) x, (fiberEmbedding μ f q) x⟫_ℂ ∂μ) =
        ∫ x, ⟪e x, f x⟫_ℂ * ⟪r, q⟫_ℂ ∂μ := by
      apply integral_congr_ae
      filter_upwards [he, hf] with x hxe hxf
      rw [hxe, hxf, inner_smul_left, inner_smul_right, RCLike.inner_apply']
      ring
    _ = (∫ x, ⟪e x, f x⟫_ℂ ∂μ) * ⟪r, q⟫_ℂ := integral_mul_const _ _

/-- The orthogonal projection onto simple tensors with scalar factor `e`. -/
def fiberProjection (e : L2 α μ) :
    BochnerL2 α H μ →L[ℂ] BochnerL2 α H μ :=
  fiberEmbedding μ e ∘L (fiberEmbedding μ e)†

theorem fiberProjection_apply (e : L2 α μ) (γ : BochnerL2 α H μ) :
    fiberProjection μ e γ =
      fiberRidgelet μ (fiberCoefficient μ e γ) e := by
  rw [fiberProjection, ContinuousLinearMap.comp_apply,
    ← fiberCoefficient_eq_adjoint_fiberEmbedding, fiberEmbedding_apply]

theorem isSelfAdjoint_fiberProjection (e : L2 α μ) :
    IsSelfAdjoint (fiberProjection (H := H) μ e) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', fiberProjection,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem fiberProjection_basis_mul [DecidableEq ι]
    (b : HilbertBasis ι ℂ (L2 α μ)) (i j : ι) :
    fiberProjection (H := H) μ (b i) * fiberProjection (H := H) μ (b j) =
      if i = j then fiberProjection (H := H) μ (b i) else 0 := by
  apply ContinuousLinearMap.ext
  intro γ
  change (fiberEmbedding μ (b i))
      (((fiberEmbedding μ (b i))†) (fiberEmbedding μ (b j)
        (((fiberEmbedding μ (b j))†) γ))) = _
  rw [adjoint_fiberEmbedding_comp_apply,
    (orthonormal_iff_ite.mp b.orthonormal i j)]
  split_ifs with hij
  · subst j
    simp [fiberProjection]
  · simp

/-- Finite sums of the scalar-basis fiber projections. -/
def fiberPartialSum (b : HilbertBasis ι ℂ (L2 α μ)) (s : Finset ι) :
    BochnerL2 α H μ →L[ℂ] BochnerL2 α H μ :=
  ∑ i ∈ s, fiberProjection (H := H) μ (b i)

theorem isStarProjection_fiberPartialSum (b : HilbertBasis ι ℂ (L2 α μ))
    (s : Finset ι) : IsStarProjection (fiberPartialSum (H := H) μ b s) := by
  classical
  constructor
  · rw [fiberPartialSum, IsIdempotentElem, Finset.sum_mul_sum]
    simp_rw [fiberProjection_basis_mul]
    simp
  · exact isSelfAdjoint_sum s fun i _ =>
      isSelfAdjoint_fiberProjection (H := H) μ (b i)

theorem norm_fiberPartialSum_apply_le (b : HilbertBasis ι ℂ (L2 α μ))
    (s : Finset ι) (γ : BochnerL2 α H μ) :
    ‖fiberPartialSum (H := H) μ b s γ‖ ≤ ‖γ‖ := by
  calc
    ‖fiberPartialSum (H := H) μ b s γ‖ ≤
        ‖fiberPartialSum (H := H) μ b s‖ * ‖γ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖γ‖ := by
      gcongr
      exact IsStarProjection.norm_le (fiberPartialSum (H := H) μ b s)
        (isStarProjection_fiberPartialSum (H := H) μ b s)
    _ = ‖γ‖ := one_mul _

omit [CompleteSpace H] in
theorem fiberEmbedding_smul (e : L2 α μ) (c : ℂ) (q : H) :
    fiberEmbedding μ e (c • q) = fiberRidgelet μ q (c • e) := by
  apply Lp.ext
  have hleft : fiberEmbedding μ e (c • q) =ᵐ[μ] fun x => e x • (c • q) := by
    rw [fiberEmbedding_apply]
    exact fiberRidgelet_apply_ae μ (c • q) e
  filter_upwards [hleft,
    fiberRidgelet_apply_ae μ q (c • e), Lp.coeFn_smul c e] with x hleft hright he
  rw [hleft, hright, he]
  simp [smul_smul, mul_comm]

theorem hasSum_fiberProjection_fiberEmbedding
    (b : HilbertBasis ι ℂ (L2 α μ)) (f : L2 α μ) (q : H) :
    HasSum (fun i => fiberProjection μ (b i) (fiberEmbedding μ f q))
      (fiberEmbedding μ f q) := by
  convert (fiberRidgelet μ q).hasSum (b.hasSum_repr f) using 1
  · ext i
    rw [fiberProjection, ContinuousLinearMap.comp_apply,
      adjoint_fiberEmbedding_comp_apply, HilbertBasis.repr_apply_apply,
      fiberEmbedding_smul]
  · rw [fiberEmbedding_apply]

omit [CompleteSpace H] in
theorem indicatorConstLp_eq_fiberEmbedding {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (q : H) :
    indicatorConstLp 2 hs hμs q =
      fiberEmbedding μ (indicatorConstLp 2 hs hμs (1 : ℂ)) q := by
  apply Lp.ext
  have hE : fiberEmbedding μ (indicatorConstLp 2 hs hμs (1 : ℂ)) q =ᵐ[μ]
      fun x => indicatorConstLp 2 hs hμs (1 : ℂ) x • q := by
    rw [fiberEmbedding_apply]
    exact fiberRidgelet_apply_ae μ q _
  filter_upwards [indicatorConstLp_coeFn (μ := μ) (s := s) (c := q),
    indicatorConstLp_coeFn (μ := μ) (s := s) (c := (1 : ℂ)), hE] with x hq hscalar hE
  rw [hq, hE, hscalar]
  by_cases hx : x ∈ s <;> simp [hx]

theorem isClosed_hasSum_fiberProjection
    (b : HilbertBasis ι ℂ (L2 α μ)) :
    IsClosed {γ : BochnerL2 α H μ |
      HasSum (fun i => fiberProjection μ (b i) γ) γ} := by
  apply IsSeqClosed.isClosed
  intro γn γ hγn hγn_lim
  change HasSum (fun i => fiberProjection μ (b i) γ) γ
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  have hlim := (Metric.tendsto_nhds.mp hγn_lim) (ε / 3) (by positivity)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hlim
  have hseries := hγn n
  change HasSum (fun i => fiberProjection μ (b i) (γn n)) (γn n) at hseries
  rw [HasSum, Metric.tendsto_nhds] at hseries
  filter_upwards [hseries (ε / 3) (by positivity)] with s hs
  have hP (δ : BochnerL2 α H μ) :
      fiberPartialSum μ b s δ = ∑ i ∈ s, fiberProjection μ (b i) δ := by
    simp [fiberPartialSum]
  rw [← hP γ]
  rw [← hP (γn n)] at hs
  rw [dist_eq_norm] at hn hs ⊢
  calc
    ‖fiberPartialSum μ b s γ - γ‖ =
        ‖fiberPartialSum μ b s (γ - γn n) +
          (fiberPartialSum μ b s (γn n) - γn n) + (γn n - γ)‖ := by
      congr 1
      simp only [map_sub]
      abel
    _ ≤ ‖fiberPartialSum μ b s (γ - γn n)‖ +
          ‖fiberPartialSum μ b s (γn n) - γn n‖ + ‖γn n - γ‖ := by
      calc
        _ ≤ ‖fiberPartialSum μ b s (γ - γn n) +
              (fiberPartialSum μ b s (γn n) - γn n)‖ + ‖γn n - γ‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖γ - γn n‖ + ‖fiberPartialSum μ b s (γn n) - γn n‖ +
          ‖γn n - γ‖ := by
      gcongr
      exact norm_fiberPartialSum_apply_le μ b s (γ - γn n)
    _ < ε / 3 + ε / 3 + ε / 3 := by
      have hn' : ‖γ - γn n‖ < ε / 3 := by
        simpa [norm_sub_rev] using hn
      nlinarith
    _ = ε := by ring

/-- Abstract Bochner-space ridgelet series relative to a Hilbert basis of scalar `L²`. -/
theorem hasSum_fiberRidgelet_coefficients (b : HilbertBasis ι ℂ (L2 α μ))
    (γ : BochnerL2 α H μ) :
    HasSum (fun i => fiberRidgelet μ (fiberCoefficient μ (b i) γ) (b i)) γ := by
  have hprojection : HasSum (fun i => fiberProjection μ (b i) γ) γ := by
    induction γ using Lp.induction (p := (2 : ENNReal))
      (hp_ne_top := ENNReal.ofNat_ne_top) with
    | @indicatorConst q s hs hμs =>
        rw [Lp.simpleFunc.coe_indicatorConst,
          indicatorConstLp_eq_fiberEmbedding (H := H) μ hs hμs.ne]
        exact hasSum_fiberProjection_fiberEmbedding μ b _ q
    | @add f g hf hg _ hf_sum hg_sum =>
        simpa only [map_add, Pi.add_apply] using hf_sum.add hg_sum
    | isClosed =>
      exact isClosed_hasSum_fiberProjection μ b
  simpa only [fiberProjection_apply] using hprojection

/-- Fiber coefficients are the unique coefficients in the scalar-basis ridgelet series. -/
theorem eq_fiberCoefficient_of_hasSum_fiberRidgelet
    (b : HilbertBasis ι ℂ (L2 α μ)) (q : ι → H) (γ : BochnerL2 α H μ)
    (hq : HasSum (fun i => fiberRidgelet μ (q i) (b i)) γ) (i : ι) :
    q i = fiberCoefficient μ (b i) γ := by
  classical
  have hmap := ((fiberEmbedding μ (b i))†).hasSum hq
  rw [← fiberCoefficient_eq_adjoint_fiberEmbedding] at hmap
  have hterms :
      (fun j => ((fiberEmbedding μ (b i))†) (fiberRidgelet μ (q j) (b j))) =
        fun j => if i = j then q i else 0 := by
    funext j
    rw [← fiberEmbedding_apply, adjoint_fiberEmbedding_comp_apply,
      (orthonormal_iff_ite.mp b.orthonormal i j)]
    split_ifs with hji
    · subst j
      simp
    · simp
  rw [hterms] at hmap
  have hsingle : HasSum (fun j => if i = j then q i else 0) (q i) := by
    simpa only [eq_comm] using hasSum_ite_eq i (q i)
  exact hsingle.unique hmap

/-- Coefficients of a null element lie in the kernel of the fiber functional. -/
theorem apply_fiberCoefficient_eq_zero_of_mem_ker (L : H →L[ℂ] ℂ)
    (b : HilbertBasis ι ℂ (L2 α μ)) (γ : BochnerL2 α H μ)
    (hγ : γ ∈ LinearMap.ker (fiberSynthesis μ L).toLinearMap) (i : ι) :
    L (fiberCoefficient μ (b i) γ) = 0 := by
  rw [fiberCoefficient, ← L.integral_comp_comm (integrable_fiberCoefficient μ (b i) γ)]
  apply integral_eq_zero_of_ae
  filter_upwards [(mem_ker_fiberSynthesis_iff μ L γ).mp hγ] with x hx
  simp [hx]

end Series

end LeanRidgelet
