/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.LambdaOperator
public import LeanRidgelet.L1.PairingExtension

/-!
# L1 theory: Fourier data away from the origin

Two structural facts about `LeanRidgelet.HasFourierAwayFromOrigin`, the function-level stand-in
for a Lizorkin distribution `η̂ ∈ 𝒮₀'(ℝ)`. Together they translate the *physical* backprojection
equation `Λ^m u = conj (ψ~) ⋆ (η - Q)` of the structure theorem `thm:eq.ac` into its *spectral*
form `conj (ψ̂) Fη = |ζ|^m û`.

## Main results

* `LeanRidgelet.hasFourierAwayFromOrigin_ae_eq`: **uniqueness of Fourier data**. Two
  representatives of the Fourier transform of the same function away from the origin agree
  almost everywhere on `ℝ \ {0}`.
* `LeanRidgelet.hasFourierAwayFromOrigin_reflectedConjConvolution`: the **convolution theorem
  away from the origin**. The Fourier data of `conj (ψ~) ⋆ v` is `conj (ψ̂) Fv`, for a Schwartz
  ridgelet function `ψ` and an activation `v` carrying Fourier data `Fv`.
* `LeanRidgelet.angularFourier1D_mul_conj_angularFourier1D`: the identity behind the previous
  item, `(θ ⬝ conj (ψ̂))^(s) = ∫ conj (ψ (s - z)) θ̂(z) dz`.
* `LeanRidgelet.HasFourierAwayFromOrigin.congr_data`: Fourier data only depends on its values
  away from the origin.

Uniqueness is the localized version of the fundamental lemma of the calculus of variations
(`MeasureTheory.IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) applied on the open set
`ℝ \ {0}`: a compactly supported bump there is a legitimate test function for
`HasFourierAwayFromOrigin`. The convolution theorem is a Fubini computation whose dominating
function factorizes after the submultiplicativity estimate `1 + |z - t| ≤ (1 + |z|) (1 + |t|)`
of `one_add_abs_add_le_mul`; the shear `(z, t) ↦ (z, z - t)` that exchanges the two iterated
orders is `MeasureTheory.measurePreserving_skewSubLeft`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Convolution ENNReal FourierTransform Topology

namespace LeanRidgelet

/-! ## Uniqueness of Fourier data away from the origin -/

/-- Fourier data away from the origin depends only on the values of the representative away
from the origin. -/
theorem HasFourierAwayFromOrigin.congr_data {η F₁ F₂ : ℝ → ℂ}
    (h : HasFourierAwayFromOrigin η F₁) (hF : Set.EqOn F₁ F₂ {(0 : ℝ)}ᶜ) :
    HasFourierAwayFromOrigin η F₂ := by
  obtain ⟨hloc, hpoly, hF₁loc, hpair⟩ := h
  have hae : F₁ =ᵐ[volume] F₂ := by
    have h0 : ∀ᵐ ζ : ℝ, ζ ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with ζ hζ
    exact hF (by simpa using hζ)
  refine ⟨hloc, hpoly, ?_, ?_⟩
  · rw [MeasureTheory.locallyIntegrableOn_iff isOpen_compl_singleton.isLocallyClosed] at hF₁loc ⊢
    intro k hks hk
    exact (hF₁loc k hks hk).congr_fun (fun x hx => hF (hks hx)) hk.measurableSet
  · intro φ hφ
    rw [← hpair φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ζ hζ
    rw [hζ]

/-- A locally integrable function on `ℝ \ {0}` is integrable against every Schwartz function
whose (compact) support avoids the origin. This is the integrability that makes the defining
pairing of `HasFourierAwayFromOrigin` an honest Bochner integral for compactly supported test
functions. -/
theorem integrable_mul_of_tsupport_subset_compl_singleton {F φ : ℝ → ℂ}
    (hF : LocallyIntegrableOn F {(0 : ℝ)}ᶜ volume) (hφcont : Continuous φ)
    (hφcs : HasCompactSupport φ) (hφts : tsupport φ ⊆ {(0 : ℝ)}ᶜ) :
    Integrable (fun ζ => F ζ * φ ζ) volume := by
  have hK : IsCompact (tsupport φ) := hφcs
  have hFK : IntegrableOn F (tsupport φ) volume := hF.integrableOn_compact_subset hφts hK
  have hIK : IntegrableOn (fun ζ => F ζ * φ ζ) (tsupport φ) volume :=
    hFK.mul_continuousOn hφcont.continuousOn hK
  have hind : (tsupport φ).indicator (fun ζ => F ζ * φ ζ) = fun ζ => F ζ * φ ζ := by
    refine Set.indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx => ?_)
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hind]
  exact (integrable_indicator_iff hK.measurableSet).2 hIK

/-- **Uniqueness of Fourier data away from the origin.** A function has at most one Fourier
transform away from the origin, up to a null set of `ℝ \ {0}`. Together with
`LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial` this says that `η ↦ Fη` realizes the
Lizorkin quotient `𝒮'(ℝ)/𝒫 ≅ 𝒮₀'(ℝ)` faithfully at function level. -/
theorem hasFourierAwayFromOrigin_ae_eq {η F₁ F₂ : ℝ → ℂ}
    (h₁ : HasFourierAwayFromOrigin η F₁) (h₂ : HasFourierAwayFromOrigin η F₂) :
    F₁ =ᵐ[volume.restrict {(0 : ℝ)}ᶜ] F₂ := by
  obtain ⟨-, -, hF₁, hp₁⟩ := h₁
  obtain ⟨-, -, hF₂, hp₂⟩ := h₂
  have hopen : IsOpen ({(0 : ℝ)}ᶜ : Set ℝ) := isOpen_compl_singleton
  have key : ∀ᵐ ζ : ℝ, ζ ∈ ({(0 : ℝ)}ᶜ : Set ℝ) → (F₁ - F₂) ζ = 0 := by
    refine hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF₁.sub hF₂) ?_
    intro g hgdiff hgcs hgts
    -- realize the real bump `g` as a complex Schwartz test function supported away from `0`
    have hsupp : Function.support (fun x : ℝ => ((g x : ℝ) : ℂ)) = Function.support g := by
      ext x
      simp
    have htseq : tsupport (fun x : ℝ => ((g x : ℝ) : ℂ)) = tsupport g := by
      rw [tsupport, tsupport, hsupp]
    have hcs' : HasCompactSupport (fun x : ℝ => ((g x : ℝ) : ℂ)) := by
      change IsCompact (tsupport (fun x : ℝ => ((g x : ℝ) : ℂ)))
      rw [htseq]
      exact hgcs
    set φ : SchwartzMap ℝ ℂ :=
      hcs'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgdiff) with hφ_def
    have hφc : ⇑φ = fun x : ℝ => ((g x : ℝ) : ℂ) := rfl
    have hφts : tsupport ⇑φ ⊆ {(0 : ℝ)}ᶜ := by
      rw [hφc, htseq]
      exact hgts
    have hφcs : HasCompactSupport ⇑φ := by
      rw [hφc]
      exact hcs'
    have hI₁ : Integrable (fun ζ => F₁ ζ * φ ζ) volume :=
      integrable_mul_of_tsupport_subset_compl_singleton hF₁ φ.continuous hφcs hφts
    have hI₂ : Integrable (fun ζ => F₂ ζ * φ ζ) volume :=
      integrable_mul_of_tsupport_subset_compl_singleton hF₂ φ.continuous hφcs hφts
    have hpair : (∫ ζ : ℝ, F₁ ζ * φ ζ) = ∫ ζ : ℝ, F₂ ζ * φ ζ := by
      rw [hp₁ φ hφts, hp₂ φ hφts]
    calc (∫ ζ : ℝ, g ζ • (F₁ - F₂) ζ)
        = (∫ ζ : ℝ, F₁ ζ * φ ζ) - ∫ ζ : ℝ, F₂ ζ * φ ζ := by
          rw [← integral_sub hI₁ hI₂]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
          simp only [Pi.sub_apply, hφc, Complex.real_smul]
          ring
      _ = 0 := by rw [hpair, sub_self]
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet]
  filter_upwards [key] with ζ hζ hζ0
  have := hζ hζ0
  simpa [sub_eq_zero] using this

/-! ## The convolution theorem away from the origin -/

/-- The angular Fourier transform of the product of a Schwartz test function `θ` with the
conjugate transform `conj (ψ̂)` of a Schwartz function: `(θ ⬝ conj (ψ̂))^(s) =
∫ conj (ψ (s - z)) θ̂(z) dz`. In the manuscript's convention the product-convolution theorem
carries the factor `(2π)⁻¹`, which here cancels against the factor `2π` of the double transform
`angularFourier1D² = 2π ⬝ (reflection)`. -/
theorem angularFourier1D_mul_conj_angularFourier1D (ψ θ : SchwartzMap ℝ ℂ) (s : ℝ) :
    angularFourier1D (fun ζ => θ ζ * conj (angularFourier1D (⇑ψ) ζ)) s
      = ∫ z : ℝ, conj (ψ (s - z)) * angularFourier1D (⇑θ) z := by
  classical
  set K : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-Complex.I * ((p.1 * s : ℝ) : ℂ)) * θ p.1 *
      (Complex.exp (Complex.I * ((p.2 * p.1 : ℝ) : ℂ)) * conj (ψ p.2)) with hK_def
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (-Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show -Complex.I * (r : ℂ) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hexp2 : ∀ r : ℝ, ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hKcont : Continuous K := by
    refine Continuous.mul (Continuous.mul ?_ (θ.continuous.comp continuous_fst)) ?_
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact (Complex.continuous_exp.comp (by fun_prop)).mul
        (RCLike.continuous_conj.comp (ψ.continuous.comp continuous_snd))
  have hKint : Integrable K (volume.prod volume) := by
    refine ((SchwartzMap.integrable θ).norm.mul_prod (SchwartzMap.integrable ψ).norm).mono'
      hKcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hnorm : ‖K p‖ = ‖θ p.1‖ * ‖ψ p.2‖ := by
      rw [hK_def]
      simp only [norm_mul, hexp1, hexp2, RCLike.norm_conj]
      ring
    exact le_of_eq hnorm
  have h1 : (∫ p : ℝ × ℝ, K p ∂(volume.prod volume))
      = angularFourier1D (fun ζ => θ ζ * conj (angularFourier1D (⇑ψ) ζ)) s := by
    rw [integral_prod K hKint, angularFourier1D_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    have hconj : conj (angularFourier1D (⇑ψ) ζ)
        = ∫ y : ℝ, Complex.exp (Complex.I * ((y * ζ : ℝ) : ℂ)) * conj (ψ y) := by
      rw [angularFourier1D_apply, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [map_mul, ← Complex.exp_conj]
      congr 2
      simp
    rw [hK_def]
    simp only []
    rw [integral_const_mul, hconj, mul_assoc]
  have h2 : (∫ p : ℝ × ℝ, K p ∂(volume.prod volume))
      = ∫ y : ℝ, conj (ψ y) * angularFourier1D (⇑θ) (s - y) := by
    rw [integral_prod_symm K hKint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [angularFourier1D_apply]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    have hexp : Complex.exp (-Complex.I * ((ζ * s : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((y * ζ : ℝ) : ℂ))
        = Complex.exp (-Complex.I * ((ζ * (s - y) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hK_def]
    change Complex.exp (-Complex.I * ((ζ * s : ℝ) : ℂ)) * θ ζ *
        (Complex.exp (Complex.I * ((y * ζ : ℝ) : ℂ)) * conj (ψ y))
      = conj (ψ y) * (Complex.exp (-Complex.I * ((ζ * (s - y) : ℝ) : ℂ)) * θ ζ)
    rw [← hexp]
    ring
  rw [← h1, h2, ← integral_sub_left_eq_self
    (fun y : ℝ => conj (ψ y) * angularFourier1D (⇑θ) (s - y)) volume s]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel]

/-- **The convolution theorem away from the origin.** If the activation `v` carries the Fourier
data `Fv` away from the origin then the convolution `conj (ψ~) ⋆ v` with a Schwartz ridgelet
function carries the Fourier data `conj (ψ̂) Fv`. This is what turns the physical backprojection
equation of `thm:eq.ac` into its spectral form. -/
theorem hasFourierAwayFromOrigin_reflectedConjConvolution (ψ : SchwartzMap ℝ ℂ)
    {v Fv : ℝ → ℂ} (hv : HasFourierAwayFromOrigin v Fv) :
    HasFourierAwayFromOrigin (reflectedConjConvolution (⇑ψ) v)
      (fun ζ => conj (angularFourier1D (⇑ψ) ζ) * Fv ζ) := by
  classical
  obtain ⟨hvloc, ⟨Cv, k, hvk⟩, hFvloc, hvpair⟩ := hv
  have hCv : 0 ≤ Cv := polynomiallyBounded_nonneg_const hvk
  have hvm : AEStronglyMeasurable v volume := hvloc.aestronglyMeasurable
  have hψk : Integrable (fun s : ℝ => (1 + |s|) ^ k * ‖ψ s‖) volume :=
    integrable_one_add_abs_pow_mul_schwartz ψ k
  have hψneg : Integrable (fun t : ℝ => (1 + |t|) ^ k * ‖ψ (-t)‖) volume := by
    refine hψk.comp_neg.congr (Filter.Eventually.of_forall fun t => ?_)
    simp [abs_neg]
  set M : ℝ := ∫ s : ℝ, (1 + |s|) ^ k * ‖ψ s‖ with hM_def
  have hM : 0 ≤ M := integral_nonneg fun s => by positivity
  have hwbound : ∀ z : ℝ, ‖reflectedConjConvolution (⇑ψ) v z‖ ≤ Cv * M * (1 + |z|) ^ k :=
    fun z => norm_reflectedConjConvolution_le k hψk hvk z
  have hconv : reflectedConjConvolution (⇑ψ) v
      = fun z : ℝ => ∫ t : ℝ, conj (ψ (-t)) * v (z - t) := by
    funext z
    simp only [reflectedConjConvolution, convolution_def, ContinuousLinearMap.mul_apply']
  -- joint measurability of the shifted activation
  have hshear : MeasurePreserving (fun q : ℝ × ℝ => (q.1, q.1 - q.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_skewSubLeft (c := (id : ℝ → ℝ)) (volume : Measure ℝ) (volume : Measure ℝ)
      measurable_id
  have hvprod : AEStronglyMeasurable (fun p : ℝ × ℝ => v (p.1 - p.2)) (volume.prod volume) :=
    hvm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_skewSubLeft (c := (id : ℝ → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ) measurable_id)
  have hψsnd : Continuous fun p : ℝ × ℝ => conj (ψ (-p.2)) :=
    RCLike.continuous_conj.comp (ψ.continuous.comp (continuous_neg.comp continuous_snd))
  -- the convolution is measurable, hence locally integrable by its growth bound
  have hwm : AEStronglyMeasurable (reflectedConjConvolution (⇑ψ) v) volume := by
    rw [hconv]
    exact (hψsnd.aestronglyMeasurable.mul hvprod).integral_prod_right'
  have hwloc : LocallyIntegrable (reflectedConjConvolution (⇑ψ) v) volume := by
    have hg : Continuous fun z : ℝ => Cv * M * (1 + |z|) ^ k := by fun_prop
    refine hg.locallyIntegrable.mono hwm (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hCv hM) (by positivity))]
    exact hwbound z
  -- the candidate Fourier data is locally integrable away from the origin
  have hψhatcont : Continuous fun ζ : ℝ => conj (angularFourier1D (⇑ψ) ζ) := by
    simp only [angularFourier1D_coe_schwartz]
    exact RCLike.continuous_conj.comp (Fourier.angularFourierSchwartz ψ).continuous
  have hFloc : LocallyIntegrableOn (fun ζ => conj (angularFourier1D (⇑ψ) ζ) * Fv ζ)
      {(0 : ℝ)}ᶜ volume :=
    hFvloc.continuousOn_mul hψhatcont.continuousOn
      (isOpen_compl_singleton.isLocallyClosed)
  refine ⟨hwloc, ⟨Cv * M, k, hwbound⟩, hFloc, ?_⟩
  intro θ hθ
  -- the test function `Θ ζ = θ ζ ⬝ conj (ψ̂ ζ)`, again Schwartz and supported away from `0`
  have hgrowth : Function.HasTemperateGrowth (fun ζ : ℝ => conj (angularFourier1D (⇑ψ) ζ)) := by
    have heq : ⇑(Fourier.schwartzConjugation (Fourier.angularFourierSchwartz ψ))
        = fun ζ : ℝ => conj (angularFourier1D (⇑ψ) ζ) := by
      funext ζ
      rw [Fourier.schwartzConjugation_apply, ← angularFourier1D_coe_schwartz]
    rw [← heq]
    exact SchwartzMap.hasTemperateGrowth _
  set Θ : SchwartzMap ℝ ℂ :=
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hgrowth θ with hΘ_def
  have hΘc : ⇑Θ = fun ζ : ℝ => θ ζ * conj (angularFourier1D (⇑ψ) ζ) := by
    funext ζ
    rw [hΘ_def, SchwartzMap.bilinLeftCLM_apply]
    rfl
  have hΘts : tsupport ⇑Θ ⊆ {(0 : ℝ)}ᶜ := by
    refine subset_trans (closure_mono ?_) hθ
    intro x hx
    simp only [Function.mem_support, hΘc] at hx ⊢
    exact fun hzero => hx (by rw [hzero, zero_mul])
  -- Step 1: the left-hand pairing is the pairing of `Fv` against `Θ`
  have hstep1 : (∫ ζ : ℝ, (fun ζ => conj (angularFourier1D (⇑ψ) ζ) * Fv ζ) ζ * θ ζ)
      = ∫ ζ : ℝ, Fv ζ * Θ ζ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    rw [hΘc]
    ring
  rw [hstep1, hvpair Θ hΘts]
  -- Step 2: Fubini in the two orders, exchanged by the shear `(z, t) ↦ (z, z - t)`
  set Fθ : SchwartzMap ℝ ℂ := Fourier.angularFourierSchwartz θ with hFθ_def
  have hFθc : ⇑Fθ = angularFourier1D (⇑θ) := (angularFourier1D_coe_schwartz θ).symm
  set G : ℝ × ℝ → ℂ :=
    fun p => conj (ψ (-p.2)) * v (p.1 - p.2) * angularFourier1D (⇑θ) p.1 with hG_def
  set H : ℝ × ℝ → ℂ :=
    fun p => conj (ψ (p.2 - p.1)) * v p.2 * angularFourier1D (⇑θ) p.1 with hH_def
  have hθhatcont : Continuous (angularFourier1D (⇑θ)) := by
    rw [← hFθc]
    exact Fθ.continuous
  have hGmeas : AEStronglyMeasurable G (volume.prod volume) :=
    (hψsnd.aestronglyMeasurable.mul hvprod).mul
      (hθhatcont.comp continuous_fst).aestronglyMeasurable
  have hGint : Integrable G (volume.prod volume) := by
    have hbdd : Integrable (fun p : ℝ × ℝ =>
        (Cv * ((1 + |p.1|) ^ k * ‖angularFourier1D (⇑θ) p.1‖)) *
          ((1 + |p.2|) ^ k * ‖ψ (-p.2)‖)) (volume.prod volume) := by
      have hFθint : Integrable
          (fun z : ℝ => Cv * ((1 + |z|) ^ k * ‖angularFourier1D (⇑θ) z‖)) volume := by
        have h := integrable_one_add_abs_pow_mul_schwartz Fθ k
        rw [hFθc] at h
        exact h.const_mul Cv
      exact hFθint.mul_prod hψneg
    refine hbdd.mono' hGmeas (Filter.Eventually.of_forall fun p => ?_)
    have hsub : (1 + |p.1 - p.2|) ^ k ≤ ((1 + |p.1|) * (1 + |p.2|)) ^ k := by
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have := one_add_abs_add_le_mul p.1 (-p.2)
      simpa [sub_eq_add_neg, abs_neg] using this
    have hbound : ‖G p‖ ≤ (Cv * ((1 + |p.1|) ^ k * ‖angularFourier1D (⇑θ) p.1‖)) *
        ((1 + |p.2|) ^ k * ‖ψ (-p.2)‖) := by
      rw [hG_def]
      simp only [norm_mul, RCLike.norm_conj]
      calc ‖ψ (-p.2)‖ * ‖v (p.1 - p.2)‖ * ‖angularFourier1D (⇑θ) p.1‖
          ≤ ‖ψ (-p.2)‖ * (Cv * ((1 + |p.1|) * (1 + |p.2|)) ^ k) *
              ‖angularFourier1D (⇑θ) p.1‖ := by
            gcongr
            exact (hvk _).trans (by gcongr)
        _ = (Cv * ((1 + |p.1|) ^ k * ‖angularFourier1D (⇑θ) p.1‖)) *
              ((1 + |p.2|) ^ k * ‖ψ (-p.2)‖) := by
            rw [mul_pow]
            ring
    exact hbound
  have hHG : ∀ p : ℝ × ℝ, H p = G (p.1, p.1 - p.2) := by
    intro p
    rw [hG_def, hH_def]
    simp only []
    rw [neg_sub, sub_sub_cancel]
  have hHint : Integrable H (volume.prod volume) := by
    have h := hshear.integrable_comp_of_integrable hGint
    exact h.congr (Filter.Eventually.of_forall fun p => (hHG p).symm)
  have hHGint : (∫ p : ℝ × ℝ, H p ∂(volume.prod volume))
      = ∫ p : ℝ × ℝ, G p ∂(volume.prod volume) := by
    have hGmeas' : AEStronglyMeasurable G
        (Measure.map (fun q : ℝ × ℝ => (q.1, q.1 - q.2)) (volume.prod volume)) := by
      rw [hshear.map_eq]
      exact hGmeas
    calc (∫ p : ℝ × ℝ, H p ∂(volume.prod volume))
        = ∫ p : ℝ × ℝ, G (p.1, p.1 - p.2) ∂(volume.prod volume) :=
          integral_congr_ae (Filter.Eventually.of_forall hHG)
      _ = ∫ q : ℝ × ℝ, G q
            ∂(Measure.map (fun q : ℝ × ℝ => (q.1, q.1 - q.2)) (volume.prod volume)) :=
          (integral_map hshear.measurable.aemeasurable hGmeas').symm
      _ = ∫ p : ℝ × ℝ, G p ∂(volume.prod volume) := by rw [hshear.map_eq]
  have hleft : (∫ p : ℝ × ℝ, G p ∂(volume.prod volume))
      = ∫ z : ℝ, reflectedConjConvolution (⇑ψ) v z * angularFourier1D (⇑θ) z := by
    rw [integral_prod G hGint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [hconv]
    simp only [hG_def]
    exact integral_mul_const _ _
  have hright : (∫ p : ℝ × ℝ, H p ∂(volume.prod volume))
      = ∫ s : ℝ, v s * angularFourier1D (⇑Θ) s := by
    rw [integral_prod_symm H hHint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hΘc]
    rw [angularFourier1D_mul_conj_angularFourier1D ψ θ s, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hH_def]
    ring
  rw [← hright, hHGint, hleft]

end LeanRidgelet
