/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Fourier.AngularPlancherel
public import LeanRidgelet.FS.DPlane.Defs
public import LeanRidgelet.ToMathlib.LieGroup.MatrixPolar

/-!
# Fourier slice method, Case IV: the Stiefel manifold in general codimension

Section 6 of `arXiv:2402.15984` at every codimension, over the Stiefel manifold. The derivation is
the codimension-one one with the sphere replaced by the manifold of frames: the frame integral is
evaluated by the matrix polar integration formula of `ToMathlib.LieGroup.MatrixPolar` and the
remaining Euclidean integral by the inversion formula. There is still no Step 2, the Stiefel case
having no scale parameter.

## Main definitions and results

* `inner_dPlaneCoord`: the coordinate map is the transpose of the frame, which is what makes the
  `d`-plane neuron a plane wave in `U ω`.
* `stiefelFourierExpression`, `fs_stiefel_fourierExpression_of_bias`: Step 1.
* `fs_stiefel_reconstruction_of_inversion`: **the master identity.**
* `fs_angularFourier_slice_dPlaneTransform`, `fs_angularFourier_dPlaneTransform_fractional`: the
  Fourier slice theorem and the fractional-derivative identity in the angular convention. The two
  conventions genuinely differ here: a multiplier `‖ξ‖^s` in the Mathlib convention is `(2π)^s‖ξ‖^s`
  in the angular one, so the reconstruction formula needs the angular form and not
  `fs_fourier_dPlaneTransform_fractional`.
* `fs_stiefel_reconstruction`: **the article's `thm:stiefel`**, for an activation of spectrum
  `‖ω‖^t` and the coefficient function `P_d[△^{(d-t)/2}f]`, with the constant `c_{m,k}(2π)^d`. It
  carries no convergence hypothesis: the ones the matrix polar formula needs are discharged from
  continuity of the Fourier transform of the target.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The reconstruction formula in general codimension

With an invariant measure on the Stiefel manifold and the matrix polar integration formula
available, the codimension-one derivation carries over unchanged: the master identity is the same
three moves — the separation-of-variables condition on the product of the two spectra, the matrix
polar formula, and Fourier inversion — with the sphere replaced by the Stiefel manifold. There is
still no Step 2, since the Stiefel case has no scale parameter.
-/

section GeneralCodim

open Metric

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coordinate map is the transpose of the frame.** Pairing a bias frequency against the
coordinate vector `Uᵀ x` is pairing the frequency pushed into the input space against `x`, which is
what makes the `d`-plane neuron a plane wave in `U ω`. -/
theorem inner_dPlaneCoord (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (x : E)
    (ω : EuclideanSpace ℝ (Fin k)) :
    inner ℝ ω (dPlaneCoord L x) = inner ℝ (L ω) x := by
  have hsum : ∑ i, ω i • EuclideanSpace.single i (1 : ℝ) = ω := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr ω
  have key : inner ℝ (L ω) x
      = ∑ i, ω i * inner ℝ (L (EuclideanSpace.single i (1 : ℝ))) x := by
    conv_lhs => rw [← hsum]
    rw [map_sum, sum_inner]
    exact Finset.sum_congr rfl fun i _ => by
      rw [L.map_smul, real_inner_smul_left]
  rw [key, dPlaneCoord]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The Fourier expression of the `d`-plane layer over the Stiefel manifold, the output of Step 1:
`S[γ](x) = (2π)^{-k} ∫_{V_{m,k}} ∫_{ℝ^k} γ♯(U,ω) σ♯(ω) e^{i⟪ω, Uᵀx⟫} dω dU`. -/
def stiefelFourierExpression (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E))
    (Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
    ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
      Γ L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (dPlaneCoord L x))) ∂ν

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Step 1 over the Stiefel manifold**: the layer equals its Fourier expression. As at codimension
one the analytic input is the bias identity at each frame, now `k`-dimensional, and no Fubini
rearrangement is needed because with no scale parameter the bias frequency may stay inside the frame
integral. -/
theorem fs_stiefel_fourierExpression_of_bias
    (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E))
    (σ Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E)
    (hbias : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ b : EuclideanSpace ℝ (Fin k), γ L b * σ (dPlaneCoord L x - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k),
            Γ L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (dPlaneCoord L x))) :
    stiefelSynthesis ν σ γ x = stiefelFourierExpression ν Fσ Γ x := by
  rw [stiefelSynthesis, stiefelFourierExpression, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hbias)

variable [Nontrivial E] [Nontrivial (EuclideanSpace ℝ (Fin k))]

/-- **The reconstruction formula of the Fourier slice method over the Stiefel manifold.** The
separation-of-variables condition of the Stiefel case is that the product of the bias spectrum of
the coefficient function with the activation spectrum be a constant multiple of `f̂(Uω)|Uω|^{d}`,
`d = m - k` — the article's `eq:sov.hom`, whose auxiliary factor `φ♯` is required to be constant.
Under it the network reproduces the target up to the constant `c · c_{m,k} (2π)^{d}`, with
`c_{m,k} = |𝕊^{k-1}|/|𝕊^{m-1}|` for the probability normalization of the invariant measure used
here.

The proof is the codimension-one one with the sphere replaced by the Stiefel manifold: the frame
integral is evaluated by the matrix polar integration formula, and the remaining Euclidean integral
by the inversion formula. The three integrability hypotheses are the ones the matrix polar formula
carries, which is the article's standing assumption of Section 2. -/
theorem fs_stiefel_reconstruction_of_inversion (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (c : ℂ)
    (Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (Ff f : E → ℂ)
    (x : E)
    (hansatz : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E, ∀ᵐ ω : EuclideanSpace ℝ (Fin k),
      Γ L ω * Fσ ω
        = c * ((‖L ω‖ ^ (Module.finrank ℝ E - k) : ℝ) : ℂ) * Ff (L ω))
    (hFfm : StronglyMeasurable Ff)
    (hF : Integrable (fun ξ : E => Ff ξ * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hinv : (∫ ξ : E, Ff ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ Module.finrank ℝ E : ℝ) : ℂ) * f x) :
    ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        stiefelFourierExpression (ContinuousLinearMap.stiefelMeasure L₀) Fσ Γ x
      = c * (((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere.real Set.univ : ℝ) : ℂ) *
          ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) * f x := by
  have hkE : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hk : 0 < k := hkE ▸ Module.finrank_pos
  have hkm : k ≤ Module.finrank ℝ E := by
    have := LinearMap.finrank_le_finrank_of_injective (f := L₀.toLinearMap) L₀.injective
    rwa [hkE] at this
  set F : E → ℂ := fun ξ => Ff ξ * fourierSlicePhase (inner ℝ ξ x) with hFdef
  have hFsm : StronglyMeasurable F :=
    hFfm.mul (continuous_fourierSlicePhase.comp
      (Continuous.inner continuous_id continuous_const)).stronglyMeasurable
  -- the frame integral, after substituting the ansatz
  have hstep : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ ω : EuclideanSpace ℝ (Fin k),
          Γ L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (dPlaneCoord L x)))
        = c * ∫ ω : EuclideanSpace ℝ (Fin k),
            ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) •
              F (L ω) := by
    intro L
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hansatz L] with ω hω
    simp only [hω, hFdef, inner_dPlaneCoord, hkE, Complex.real_smul]
    ring
  have hpolar :=
    MeasureTheory.toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable L₀ hFsm hF
  rw [stiefelFourierExpression, integral_congr_ae (Filter.Eventually.of_forall hstep),
    integral_const_mul]
  have hpow : ((2 * (Real.pi : ℂ)) ^ Module.finrank ℝ E)
      = ((2 * (Real.pi : ℂ)) ^ k) * ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) := by
    rw [← pow_add]
    congr 1
    omega
  have hpi : ((2 * (Real.pi : ℂ)) ^ k) ≠ 0 := pow_ne_zero _ Fourier.two_mul_pi_complex_ne_zero
  have hcollect : ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        (((2 * (Real.pi : ℂ)) ^ k)⁻¹ * (c * ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
          ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (L ω))
          ∂(ContinuousLinearMap.stiefelMeasure L₀)))
      = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ * c *
        ((((volume : Measure E).toSphere.real Set.univ : ℝ)) •
          ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
            ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (L ω))
            ∂(ContinuousLinearMap.stiefelMeasure L₀)) := by
    rw [Complex.real_smul]
    ring
  rw [hcollect, hpolar, hFdef, hinv, Complex.real_smul]
  push_cast
  rw [hpow]
  field_simp

/-- **The inversion formula for the `d`-plane transform**, the article's Lemma 6.2: the Fourier data
of the target, read along the frames and weighted by `‖Uω‖^{m-k}`, recovers the target.

The article proves this first and derives the reconstruction formulas from it; here it comes out of
the same two ingredients they do — the matrix polar integration formula and Fourier inversion — so
it is a corollary rather than a lemma. Stating it separately is worth doing because it is where the
article's constant can be compared.

*Deviation.* The article writes `f(x) = (2π)^{-m} ∫_{V×ℝ^k} f̂(Uω)|Uω|^{m-k} e^{i⟪Uω,x⟫} dω dU`,
with no `c_{m,k}`. Its own Lemma C.2 reads `c_{m,k} ∫_{ℝ^m} g = ∫_{V×ℝ^k} g(Ub)|Ub|^{m-k}`, so the
change of variables in its proof carries a factor `c_{m,k}` that the statement drops: the correct
form is `f(x) = (c_{m,k}(2π)^m)^{-1} ∫ ⋯`. That is what is proved here, in the normalization of
`ToMathlib.LieGroup.MatrixPolar`, where `c_{m,k}` appears as the ratio `|𝕊^{k-1}|/|𝕊^{m-1}|` and the
statement is multiplied out so that no division occurs. -/
theorem fs_dPlaneInversion (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (Ff f : E → ℂ) (x : E)
    (hFfm : StronglyMeasurable Ff)
    (hF : Integrable (fun ξ : E => Ff ξ * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hinv : (∫ ξ : E, Ff ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ Module.finrank ℝ E : ℝ) : ℂ) * f x) :
    ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
            ((‖L ω‖ ^ (Module.finrank ℝ E - k) : ℝ) : ℂ) *
              (Ff (L ω) * fourierSlicePhase (inner ℝ (L ω) x)))
          ∂(ContinuousLinearMap.stiefelMeasure L₀)
      = (((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere.real Set.univ : ℝ) : ℂ) *
          ((2 * (Real.pi : ℂ)) ^ Module.finrank ℝ E) * f x := by
  have hkE : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  set F : E → ℂ := fun ξ => Ff ξ * fourierSlicePhase (inner ℝ ξ x) with hFdef
  have hFsm : StronglyMeasurable F :=
    hFfm.mul (continuous_fourierSlicePhase.comp
      (Continuous.inner continuous_id continuous_const)).stronglyMeasurable
  have hstep : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ ω : EuclideanSpace ℝ (Fin k),
          ((‖L ω‖ ^ (Module.finrank ℝ E - k) : ℝ) : ℂ) *
            (Ff (L ω) * fourierSlicePhase (inner ℝ (L ω) x)))
        = ∫ ω : EuclideanSpace ℝ (Fin k),
            ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) •
              F (L ω) := by
    intro L
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hkE, hFdef]
    rw [Complex.real_smul]
  have hpolar :=
    MeasureTheory.toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable L₀ hFsm hF
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  have hcollect : ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        (∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
          ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (L ω))
          ∂(ContinuousLinearMap.stiefelMeasure L₀))
      = (((volume : Measure E).toSphere.real Set.univ : ℝ)) •
        ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k),
          ‖L ω‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (L ω))
          ∂(ContinuousLinearMap.stiefelMeasure L₀) := by
    rw [Complex.real_smul]
  rw [hcollect, hpolar, hFdef, hinv, Complex.real_smul]
  push_cast
  ring

/-! ### The article's form: the coefficient function is a `d`-plane transform -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Over the frame space the singular frequency is negligible, as it is over `ℝ`. -/
theorem fs_ae_ne_zero_frame : ∀ᵐ ω : EuclideanSpace ℝ (Fin k), ω ≠ 0 := by
  have h : (volume : Measure (EuclideanSpace ℝ (Fin k))) {(0 : EuclideanSpace ℝ (Fin k))} = 0 := by
    simp
  filter_upwards [compl_mem_ae_iff.mpr h] with ω hω
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hω
  exact hω

omit [Nontrivial E] [Nontrivial (EuclideanSpace ℝ (Fin k))] in
/-- **The Fourier slice theorem in the article's angular convention**, in general codimension: the
bias spectrum of the `d`-plane transform of `f` along a frame is the angular Fourier data of `f` on
the range of that frame. Rescaling the frequency does not disturb the slice theorem. -/
theorem fs_angularFourier_slice_dPlaneTransform {f : E → ℂ} (hf : Integrable f volume)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (ω : EuclideanSpace ℝ (Fin k)) :
    Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform f L) ω
      = Fourier.angularFourierIntegralInner f (L ω) := by
  rw [Fourier.angularFourierIntegralInner_eq_mathlib,
    Fourier.angularFourierIntegralInner_eq_mathlib, ← L.map_smul]
  exact (MeasureTheory.fourier_slice_dPlaneTransform hf L ((2 * Real.pi)⁻¹ • ω)).symm

omit [Nontrivial E] [Nontrivial (EuclideanSpace ℝ (Fin k))] in
/-- **The coefficient function is the `d`-plane transform of a fractional derivative**, in the
convention the reconstruction formula is stated in. If `g` is the fractional derivative of order `s`
of `f`, in the sense that its angular Fourier transform is `‖ξ‖^s` times that of `f`, then the bias
spectrum of `P_d[g](U,·)` is `‖ω‖^s` times the Fourier data of `f` along the frame.

This is the angular-convention counterpart of `fs_fourier_dPlaneTransform_fractional`. The two
conventions do not agree here: a multiplier `‖ξ‖^s` becomes `(2π)^s ‖ξ‖^s` under the rescaling of
the frequency, so the reconstruction formula needs this form and not that one. The fractional
Laplacian
is not in Mathlib, so its multiplier property is the hypothesis rather than a definition. -/
theorem fs_angularFourier_dPlaneTransform_fractional {s : ℝ} {f g : E → ℂ}
    (hg : Integrable g volume)
    (hmul : ∀ ξ : E, Fourier.angularFourierIntegralInner g ξ
      = ((‖ξ‖ ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner f ξ)
    (L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (ω : EuclideanSpace ℝ (Fin k)) :
    Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform g L) ω
      = ((‖ω‖ ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner f (L ω) := by
  rw [fs_angularFourier_slice_dPlaneTransform hg L ω, hmul, L.norm_map]

/-- **The reconstruction formula over the Stiefel manifold in general codimension** — the article's
`thm:stiefel`. The activation has spectrum `σ♯(ω) = ‖ω‖^t`, and the coefficient function is the
`d`-plane transform of the fractional derivative `g = △^{(d-t)/2} f` of the target, `d = m - k`:
this is the article's `R[f](U,b) = P_d[△^{(d-t)/2}f](U,b)`, whose bias spectrum
`fs_angularFourier_dPlaneTransform_fractional` computes. The conclusion is
`S[R[f]](x) = c_{m,k} (2π)^{d} f(x)`.

*The constant is the reciprocal of the article's, and the value of `c_{m,k}` differs*; see the
*Deviations from the article* section of this module. Here `c_{m,k} = |𝕊^{k-1}|/|𝕊^{m-1}|`, the
invariant measure on the Stiefel manifold being a probability measure, and the statement is written
multiplied out so that no division appears. -/
theorem fs_stiefel_reconstruction (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (t : ℝ)
    (σ : EuclideanSpace ℝ (Fin k) → ℂ) (f g : E → ℂ) (x : E)
    (hf : Integrable f volume) (hFf : Integrable (𝓕 f) volume) (hx : ContinuousAt f x)
    (hg : Integrable g volume)
    (hfrac : ∀ ξ : E, Fourier.angularFourierIntegralInner g ξ
      = ((‖ξ‖ ^ (((Module.finrank ℝ E - k : ℕ) : ℝ) - t) : ℝ) : ℂ) *
        Fourier.angularFourierIntegralInner f ξ)
    (hbias : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ b : EuclideanSpace ℝ (Fin k),
          MeasureTheory.dPlaneTransform g L b * σ (dPlaneCoord L x - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k),
            Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform g L) ω *
              ((‖ω‖ ^ t : ℝ) : ℂ) * fourierSlicePhase (inner ℝ ω (dPlaneCoord L x))) :
    ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        stiefelSynthesis (ContinuousLinearMap.stiefelMeasure L₀) σ
          (fun L => MeasureTheory.dPlaneTransform g L) x
      = (((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere.real Set.univ : ℝ) : ℂ) *
          ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) * f x := by
  have hkE : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hansatz : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E, ∀ᵐ ω : EuclideanSpace ℝ (Fin k),
      Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform g L) ω *
            ((‖ω‖ ^ t : ℝ) : ℂ)
        = 1 * ((‖L ω‖ ^ (Module.finrank ℝ E - k) : ℝ) : ℂ) *
            Fourier.angularFourierIntegralInner f (L ω) := by
    intro L
    filter_upwards [fs_ae_ne_zero_frame] with ω hω
    have hpos : (0 : ℝ) < ‖ω‖ := norm_pos_iff.mpr hω
    have hexp : (((Module.finrank ℝ E - k : ℕ) : ℝ) - t) + t
        = ((Module.finrank ℝ E - k : ℕ) : ℝ) := by ring
    have hsplit : ((‖ω‖ ^ (((Module.finrank ℝ E - k : ℕ) : ℝ) - t) : ℝ) : ℂ) *
          ((‖ω‖ ^ t : ℝ) : ℂ)
        = ((‖L ω‖ ^ (Module.finrank ℝ E - k) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, hexp, ← L.norm_map ω, Real.rpow_natCast]
    rw [fs_angularFourier_dPlaneTransform_fractional hg hfrac L ω, ← hsplit]
    ring
  rw [fs_stiefel_fourierExpression_of_bias (ContinuousLinearMap.stiefelMeasure L₀) σ
      (fun ω : EuclideanSpace ℝ (Fin k) => ((‖ω‖ ^ t : ℝ) : ℂ))
      (fun L => MeasureTheory.dPlaneTransform g L)
      (fun L => Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform g L)) x hbias,
    fs_stiefel_reconstruction_of_inversion L₀ 1
      (fun ω : EuclideanSpace ℝ (Fin k) => ((‖ω‖ ^ t : ℝ) : ℂ))
      (fun L => Fourier.angularFourierIntegralInner (MeasureTheory.dPlaneTransform g L))
      (Fourier.angularFourierIntegralInner f) f x hansatz
      (Fourier.continuous_angularFourierIntegralInner hf).stronglyMeasurable
      (fs_integrable_angularFourier_mul_phase hFf x)
      (fs_angularFourier_inversion_inner hf hFf hx)]
  ring

end GeneralCodim
end LeanRidgelet
