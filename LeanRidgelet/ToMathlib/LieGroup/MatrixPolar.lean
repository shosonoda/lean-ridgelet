/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.SphereInvariantMeasure

/-!
# The matrix polar integration formula

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Polar coordinates write an integral over `ℝ^m` as an integral over `𝕊^{m-1} × (0,∞)`. The *matrix*
polar formula does the same with a `k`-frame in place of a direction: an integral over `ℝ^m` becomes
an integral over `V_{m,k} × ℝ^k`, of the same function read at `U b`, against the weight
`|U b|^{m-k}`. It is Lemma C.2 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984),

which cites Rubin's Lemma 2.1, and it is what the `d`-plane reconstruction formulas of that article
need in codimension greater than one.

The proof is three reductions and no new analysis. Polar coordinates on the frame space `ℝ^k` turn
the weight `|U b|^{m-k}` together with the Jacobian `r^{k-1}` into `r^{m-1}`, which is the Jacobian
of polar coordinates on `ℝ^m`; the direction integral over frames is then an integral over the unit
sphere of `ℝ^m`, because the direction of a random frame is uniform there
(`MeasureTheory.map_frameDirection_stiefelMeasure`); and polar coordinates on `ℝ^m` put it back
together.

## Main results

* `MeasureTheory.toSphere_real_smul_integral_directionAverage`: **the direction average.** Averaging
  a function of the direction `U ω` over frames and over unit vectors of the frame space is
  averaging it over the sphere of `E`, up to the ratio of the two sphere areas. This is the shared
  core of the reconstruction formulas over the Stiefel manifold and over the similitude group:
  whatever the weight family, the derivation ends by reducing the parameter integral to this
  average.
* `MeasureTheory.toSphere_real_smul_integral_stiefelMeasure`: **the matrix polar integration
  formula.** The constant is a ratio of two sphere areas, `|𝕊^{k-1}|/|𝕊^{m-1}|`, and the statement
  is written multiplied out so that no division appears.
* `MeasureTheory.toSphere_mul_lintegral_directionAverage`,
  `MeasureTheory.toSphere_mul_lintegral_stiefelMeasure`: **both, unsigned.** For the lower Lebesgue
  integral the only hypothesis is measurability, the two reductions being Tonelli rather than
  Fubini; and the frame section needs no almost-everywhere qualifier either, a frame being an
  isometry.
* `MeasureTheory.ae_integrable_weighted_frameSection`,
  `MeasureTheory.integrable_prod_radialIntegral`,
  `MeasureTheory.toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable`: **the
  convergence hypotheses, discharged.** For a strongly measurable integrand the two hypotheses of
  the signed formula follow from integrability, by computing the integral of the norm with the
  unsigned formula.

## The constant, and the article's

The invariant measure on the Stiefel manifold used here is a *probability* measure, which is why the
constant comes out as a ratio. In the classical normalization, where the Stiefel manifold carries
total mass `σ_{m,k} = ∏_{j<k} |𝕊^{m-1-j}|` — Rubin's `2^k π^{mk/2}/Γ_k(m/2)` — the constant
becomes `|𝕊^{k-1}| · σ_{m-1,k-1}`, i.e. the article's `c_{m,k}` with frames of the *orthogonal
complement* of the direction rather than of the whole space. The two readings agree at `k = 1`,
which is why the codimension-one development did not see the difference. The formula proved here is
the one in terms of sphere areas, which is independent of how the Stiefel manifold is normalized;
the translation above uses the mass recursion `|V_{m,k}| = |𝕊^{m-1}| · |V_{m-1,k-1}|`, which is not
formalized.

## Why the discharged form needs measurability

`Integrable F volume` alone does not suffice, and the reason is not a technicality. The left-hand
side of the formula reads the integrand only along the ranges of the frames, each of which is a null
set of `E` when `k < m`, so an integrable `F` may be modified there — off a null set of `E`, hence
without disturbing the right-hand side — into something whose frame sections are not even
measurable. What the unsigned formula does say is that a *measurable* null set is met in a null set
by almost every frame; so the formula is insensitive to modifying a strongly measurable integrand on
a null set, even though no individual frame section is.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric ContinuousLinearMap
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  [MeasurableSpace F'] [BorelSpace F'] [Nontrivial F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [Nontrivial F'] in
/-- **The average of a function of the direction, over frames and unit vectors.** For a function `H`
on the unit sphere of `E`, averaging `H` at the direction `U ω` over frames and over unit vectors
`ω` of the frame space is averaging `H` over the sphere of `E`, up to the ratio of the two sphere
areas.

This is the shared core of the reconstruction formulas over the Stiefel manifold and over the
similitude group: whatever the weight family, the derivation ends by reducing the parameter integral
to this average. It is `map_frameDirection_stiefelMeasure` — the direction of a random frame is
uniform on the sphere — with a Fubini exchange in front of it, and the statement is multiplied out
so that no division appears. -/
theorem toSphere_real_smul_integral_directionAverage (L₀ : F' →ₗᵢ[ℝ] E) {H : sphere (0 : E) 1 → G}
    (hH : Integrable H (volume : Measure E).toSphere)
    (hprod : Integrable (fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 => H (frameDirection p.1 p.2))
      ((stiefelMeasure L₀).prod ((volume : Measure F').toSphere))) :
    ((volume : Measure E).toSphere.real univ) •
        (∫ L, (∫ ω : sphere (0 : F') 1, H (frameDirection L ω)
          ∂(volume : Measure F').toSphere) ∂(stiefelMeasure L₀))
      = ((volume : Measure F').toSphere.real univ) • ∫ v, H v ∂(volume : Measure E).toSphere := by
  have hA : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have hAtop : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  have hAreal : (volume : Measure E).toSphere.real univ ≠ 0 := by
    change ((volume : Measure E).toSphere univ).toReal ≠ 0
    rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hA, hAtop⟩
  have h3 : ∀ ω : sphere (0 : F') 1,
      (∫ L, H (frameDirection L ω) ∂(stiefelMeasure L₀))
        = (((volume : Measure E).toSphere.real univ)⁻¹) •
            ∫ v, H v ∂(volume : Measure E).toSphere := by
    intro ω
    have hmap := map_frameDirection_stiefelMeasure L₀ ω
    have hmeas : AEStronglyMeasurable H
        (Measure.map (fun L : F' →ₗᵢ[ℝ] E => frameDirection L ω) (stiefelMeasure L₀)) := by
      rw [hmap]
      exact hH.aestronglyMeasurable.smul_measure _
    rw [← integral_map (continuous_frameDirection ω).measurable.aemeasurable hmeas, hmap,
      integral_smul_measure, ENNReal.toReal_inv]
    rfl
  rw [integral_integral_swap hprod, integral_congr_ae (Filter.Eventually.of_forall h3),
    integral_const, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **The matrix polar integration formula**, the article's Lemma C.2: an integral over `E` may be
read as an integral over frames and coordinate vectors, of the same function at `U b` against the
weight `|U b|^{m-k}`. The constant is the ratio of the areas of the two unit spheres, and the
statement is multiplied out so that no division appears.

The two integrability hypotheses are the absolute convergence the article assumes: the weighted
section along almost every frame, and the doubly iterated integrand on the product. -/
theorem toSphere_real_smul_integral_stiefelMeasure (L₀ : F' →ₗᵢ[ℝ] E) {F : E → G}
    (hF : Integrable F volume)
    (hsec : ∀ᵐ L ∂(stiefelMeasure L₀),
      Integrable (fun b : F' =>
        ‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F') • F (L b)) volume)
    (hprod : Integrable
      (fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 =>
        ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) • F (r • (frameDirection p.1 p.2 : E)))
      ((stiefelMeasure L₀).prod ((volume : Measure F').toSphere))) :
    ((volume : Measure E).toSphere.real univ) •
        (∫ L, (∫ b : F',
            ‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F') • F (L b)) ∂(stiefelMeasure L₀))
      = ((volume : Measure F').toSphere.real univ) • ∫ x : E, F x := by
  have hk : 0 < Module.finrank ℝ F' := Module.finrank_pos
  have hkm : Module.finrank ℝ F' ≤ Module.finrank ℝ E :=
    LinearMap.finrank_le_finrank_of_injective (f := L₀.toLinearMap) L₀.injective
  -- the radial integral over a ray of `E`, the inner integral of polar coordinates
  set H : sphere (0 : E) 1 → G := fun v =>
    ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) • F (r • (v : E)) with hHdef
  have hHint : Integrable H (volume : Measure E).toSphere :=
    integrable_toSphere_integral_Ioi (volume : Measure E) hF
  have hHpolar : (∫ v, H v ∂(volume : Measure E).toSphere) = ∫ x : E, F x :=
    (integral_eq_integral_toSphere_integral_Ioi (volume : Measure E) hF).symm
  -- Step 1: polar coordinates on the frame space turn the weight into the Jacobian on `E`
  have h1 : (∫ L, (∫ b : F',
        ‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F') • F (L b)) ∂(stiefelMeasure L₀))
      = ∫ L, (∫ ω : sphere (0 : F') 1, H (frameDirection L ω)
          ∂(volume : Measure F').toSphere) ∂(stiefelMeasure L₀) := by
    refine integral_congr_ae ?_
    filter_upwards [hsec] with L hL
    rw [integral_eq_integral_toSphere_integral_Ioi (volume : Measure F') hL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    rw [hHdef]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hval : L (r • (ω : F')) = r • (frameDirection L ω : E) := by
      simp
    have hnorm : ‖r • (frameDirection L ω : E)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0,
        mem_sphere_zero_iff_norm.1 (frameDirection L ω).2, mul_one]
    rw [hval, hnorm, smul_smul, ← pow_add]
    congr 2
    omega
  -- Steps 2 and 3: the direction average, and polar coordinates on `E`
  rw [h1, toSphere_real_smul_integral_directionAverage L₀ hHint hprod, hHpolar]

/-! ## The unsigned form

The lower Lebesgue integral needs no convergence hypothesis, only measurability: the two reductions
above are Tonelli rather than Fubini. This is the form to prove an absolute convergence *statement*
with, since deciding that a product integrand is integrable means computing the integral of its
norm.
-/

/-- The radial integral over a ray. This is the inner integral of polar coordinates on `E`, as a
function of the direction. -/
def radialIntegral (F : E → G) (v : sphere (0 : E) 1) : G :=
  ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) • F (r • (v : E))

/-- The radial integral over a ray, unsigned. This is the inner integral of polar coordinates on
`E`, as a function of the direction. -/
def radialLIntegral (F : E → ℝ≥0∞) (v : sphere (0 : E) 1) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • (v : E))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem measurable_radialLIntegral {F : E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (radialLIntegral F) := by
  have hg : Measurable fun p : sphere (0 : E) 1 × ℝ =>
      ENNReal.ofReal (p.2 ^ (Module.finrank ℝ E - 1)) * F (p.2 • (p.1 : E)) := by
    refine Measurable.mul (by fun_prop) (hF.comp ?_)
    exact (continuous_snd.smul (continuous_subtype_val.comp continuous_fst)).measurable
  exact hg.lintegral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))

omit [Nontrivial F'] in
/-- **The direction average, unsigned.** The counterpart of
`MeasureTheory.toSphere_real_smul_integral_directionAverage` for the lower Lebesgue integral: only
measurability is assumed, the exchange of the two integrals being Tonelli. -/
theorem toSphere_mul_lintegral_directionAverage (L₀ : F' →ₗᵢ[ℝ] E)
    {H : sphere (0 : E) 1 → ℝ≥0∞} (hH : Measurable H) :
    ((volume : Measure E).toSphere univ) *
        (∫⁻ L, (∫⁻ ω : sphere (0 : F') 1, H (frameDirection L ω)
          ∂(volume : Measure F').toSphere) ∂(stiefelMeasure L₀))
      = ((volume : Measure F').toSphere univ) * ∫⁻ v, H v ∂(volume : Measure E).toSphere := by
  have hA : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have hAtop : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  have h3 : ∀ ω : sphere (0 : F') 1,
      (∫⁻ L, H (frameDirection L ω) ∂(stiefelMeasure L₀))
        = ((volume : Measure E).toSphere univ)⁻¹ * ∫⁻ v, H v ∂(volume : Measure E).toSphere := by
    intro ω
    rw [← lintegral_map hH (continuous_frameDirection ω).measurable,
      map_frameDirection_stiefelMeasure L₀ ω, lintegral_smul_measure]
    rfl
  have hswap : (∫⁻ L, (∫⁻ ω : sphere (0 : F') 1, H (frameDirection L ω)
        ∂(volume : Measure F').toSphere) ∂(stiefelMeasure L₀))
      = ∫⁻ ω : sphere (0 : F') 1, (∫⁻ L, H (frameDirection L ω) ∂(stiefelMeasure L₀))
        ∂(volume : Measure F').toSphere :=
    lintegral_lintegral_swap
      ((hH.comp continuous_frameDirection_prod.measurable).aemeasurable)
  have hcancel : ∀ a b c : ℝ≥0∞, a ≠ 0 → a ≠ ∞ → a * ((a⁻¹ * c) * b) = b * c := by
    intro a b c ha hatop
    rw [show a * ((a⁻¹ * c) * b) = (a * a⁻¹) * (c * b) from by ring,
      ENNReal.mul_inv_cancel ha hatop, one_mul, mul_comm]
  rw [hswap, lintegral_congr h3, lintegral_const]
  exact hcancel _ _ _ hA hAtop

/-- **The matrix polar integration formula, unsigned.** The counterpart of
`MeasureTheory.toSphere_real_smul_integral_stiefelMeasure` for the lower Lebesgue integral: the only
hypothesis is measurability of the integrand, since both reductions are Tonelli.

The frame section needs no almost-everywhere qualifier here either: a frame is an isometry, so the
weight `|U b|^{m-k}` is `|b|^{m-k}` and the reduction holds at *every* frame. -/
theorem toSphere_mul_lintegral_stiefelMeasure (L₀ : F' →ₗᵢ[ℝ] E) {F : E → ℝ≥0∞}
    (hF : Measurable F) :
    ((volume : Measure E).toSphere univ) *
        (∫⁻ L, (∫⁻ b : F', ENNReal.ofReal (‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F'))
            * F (L b)) ∂(stiefelMeasure L₀))
      = ((volume : Measure F').toSphere univ) * ∫⁻ x : E, F x := by
  have hk : 0 < Module.finrank ℝ F' := Module.finrank_pos
  have hkm : Module.finrank ℝ F' ≤ Module.finrank ℝ E :=
    LinearMap.finrank_le_finrank_of_injective (f := L₀.toLinearMap) L₀.injective
  have hHpolar : (∫⁻ v, radialLIntegral F v ∂(volume : Measure E).toSphere) = ∫⁻ x : E, F x :=
    (lintegral_eq_lintegral_toSphere_lintegral_Ioi (volume : Measure E) hF).symm
  -- Step 1: polar coordinates on the frame space turn the weight into the Jacobian on `E`
  have h1 : ∀ L : F' →ₗᵢ[ℝ] E,
      (∫⁻ b : F', ENNReal.ofReal (‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F'))
          * F (L b))
        = ∫⁻ ω : sphere (0 : F') 1, radialLIntegral F (frameDirection L ω)
          ∂(volume : Measure F').toSphere := by
    intro L
    have hmeas : Measurable fun b : F' =>
        ENNReal.ofReal (‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F')) * F (L b) := by
      refine Measurable.mul (by fun_prop) (hF.comp L.continuous.measurable)
    rw [lintegral_eq_lintegral_toSphere_lintegral_Ioi (volume : Measure F') hmeas]
    refine lintegral_congr fun ω => ?_
    rw [radialLIntegral]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have hval : L (r • (ω : F')) = r • (frameDirection L ω : E) := by simp
    have hnorm : ‖r • (frameDirection L ω : E)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0,
        mem_sphere_zero_iff_norm.1 (frameDirection L ω).2, mul_one]
    rw [hval, hnorm, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), ← pow_add]
    congr 3
    omega
  -- Steps 2 and 3: the direction average, and polar coordinates on `E`
  rw [lintegral_congr h1,
    toSphere_mul_lintegral_directionAverage L₀ (measurable_radialLIntegral hF), hHpolar]

/-! ## Removing the convergence hypotheses

With the unsigned formula available, the two convergence hypotheses of the matrix polar formula
follow from integrability of the integrand — provided the integrand is *honestly* measurable and not
merely almost everywhere so. That proviso is not a technicality: the left-hand side reads the
integrand only along the ranges of the frames, each of which is a null set of `E` when `k < m`, so
`Integrable F volume` alone says nothing about the values the left-hand side depends on. What the
unsigned formula does say is that a *measurable* null set is met in a null set by almost every
frame, which is why the formula is insensitive to modifying a strongly measurable integrand on a
null set even though each frame section is not.
-/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [FiniteDimensional ℝ F'] [MeasurableSpace F'] [BorelSpace F'] [Nontrivial F'] in
/-- Applying a frame to a vector is jointly continuous. -/
theorem continuous_frameApply : Continuous fun p : (F' →ₗᵢ[ℝ] E) × F' => p.1 p.2 :=
  isBoundedBilinearMap_apply.continuous.comp
    ((ContinuousLinearMap.continuous_toContinuousLinearMap.comp continuous_fst).prodMk
      continuous_snd)

omit [CompleteSpace G] in
/-- **The weighted frame section of an integrable function is integrable at almost every frame.**
This is the first convergence hypothesis of the matrix polar formula, derived from its unsigned
form. -/
theorem ae_integrable_weighted_frameSection (L₀ : F' →ₗᵢ[ℝ] E) {F : E → G}
    (hFm : StronglyMeasurable F) (hF : Integrable F volume) :
    ∀ᵐ L ∂(stiefelMeasure L₀),
      Integrable (fun b : F' =>
        ‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F') • F (L b)) volume := by
  set n := Module.finrank ℝ E - Module.finrank ℝ F' with hn
  have hA : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have hpoint : ∀ (L : F' →ₗᵢ[ℝ] E) (b : F'),
      ‖‖L b‖ ^ n • F (L b)‖ₑ = ENNReal.ofReal (‖L b‖ ^ n) * ‖F (L b)‖ₑ := by
    intro L b
    rw [enorm_smul, Real.enorm_eq_ofReal (by positivity)]
  have hkey := toSphere_mul_lintegral_stiefelMeasure L₀ (F := fun x : E => ‖F x‖ₑ) hFm.enorm
  have hRHS : ((volume : Measure F').toSphere univ) * (∫⁻ x : E, ‖F x‖ₑ) ≠ ∞ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
    have h := hF.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    exact h.ne
  have hX : (∫⁻ L, (∫⁻ b : F', ENNReal.ofReal (‖L b‖ ^ n) * ‖F (L b)‖ₑ)
      ∂(stiefelMeasure L₀)) ≠ ∞ := by
    intro hinf
    rw [← hkey, hinf, ENNReal.mul_top hA] at hRHS
    exact hRHS rfl
  have hjoint : Measurable fun p : (F' →ₗᵢ[ℝ] E) × F' =>
      ENNReal.ofReal (‖p.1 p.2‖ ^ n) * ‖F (p.1 p.2)‖ₑ :=
    (((continuous_frameApply.norm.pow n).measurable).ennreal_ofReal).mul
      ((hFm.comp_measurable continuous_frameApply.measurable).enorm)
  filter_upwards [ae_lt_top hjoint.lintegral_prod_right' hX] with L hL
  refine ⟨((continuous_frameApply.comp
      (continuous_const.prodMk continuous_id)).norm.pow n).stronglyMeasurable.smul
    (hFm.comp_measurable L.continuous.measurable) |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ b : F', ‖‖L b‖ ^ n • F (L b)‖ₑ
      = ∫⁻ b : F', ENNReal.ofReal (‖L b‖ ^ n) * ‖F (L b)‖ₑ := lintegral_congr (hpoint L)
    _ < ∞ := hL

omit [Nontrivial F'] [CompleteSpace G] in
/-- **The doubly iterated integrand of the matrix polar formula is integrable on the product.** This
is the second convergence hypothesis, derived from the unsigned direction average. -/
theorem integrable_prod_radialIntegral (L₀ : F' →ₗᵢ[ℝ] E) {F : E → G}
    (hFm : StronglyMeasurable F) (hF : Integrable F volume) :
    Integrable
      (fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 => radialIntegral F (frameDirection p.1 p.2))
      ((stiefelMeasure L₀).prod ((volume : Measure F').toSphere)) := by
  have hA : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (μ := (volume : Measure E)))
  have hgsm : StronglyMeasurable fun p : sphere (0 : E) 1 × ℝ =>
      p.2 ^ (Module.finrank ℝ E - 1) • F (p.2 • (p.1 : E)) :=
    ((continuous_snd.pow (Module.finrank ℝ E - 1)).stronglyMeasurable).smul
      (hFm.comp_measurable
        (continuous_snd.smul (continuous_subtype_val.comp continuous_fst)).measurable)
  have hHsm : StronglyMeasurable (radialIntegral F) :=
    hgsm.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  have hHint : Integrable (radialIntegral F) (volume : Measure E).toSphere :=
    integrable_toSphere_integral_Ioi (volume : Measure E) hF
  have hkey := toSphere_mul_lintegral_directionAverage L₀
    (H := fun v => ‖radialIntegral F v‖ₑ) hHsm.enorm
  have hRHS : ((volume : Measure F').toSphere univ) *
      (∫⁻ v, ‖radialIntegral F v‖ₑ ∂(volume : Measure E).toSphere) ≠ ∞ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
    have h := hHint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    exact h.ne
  have hX : (∫⁻ L, (∫⁻ ω : sphere (0 : F') 1, ‖radialIntegral F (frameDirection L ω)‖ₑ
      ∂(volume : Measure F').toSphere) ∂(stiefelMeasure L₀)) ≠ ∞ := by
    intro hinf
    rw [← hkey, hinf, ENNReal.mul_top hA] at hRHS
    exact hRHS rfl
  refine ⟨(hHsm.comp_measurable
    continuous_frameDirection_prod.measurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    lintegral_prod (fun p : (F' →ₗᵢ[ℝ] E) × sphere (0 : F') 1 =>
        ‖radialIntegral F (frameDirection p.1 p.2)‖ₑ)
      ((hHsm.comp_measurable continuous_frameDirection_prod.measurable).enorm.aemeasurable)]
  exact lt_of_le_of_ne le_top hX

/-- **The matrix polar integration formula for a strongly measurable integrand**, with no
convergence hypothesis beyond integrability. The measurability is what the left-hand side needs in
order to be determined at all: it reads the integrand only along the ranges of the frames, which are
null sets of `E` when `k < m`. -/
theorem toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable (L₀ : F' →ₗᵢ[ℝ] E)
    {F : E → G} (hFm : StronglyMeasurable F) (hF : Integrable F volume) :
    ((volume : Measure E).toSphere.real univ) •
        (∫ L, (∫ b : F',
            ‖L b‖ ^ (Module.finrank ℝ E - Module.finrank ℝ F') • F (L b)) ∂(stiefelMeasure L₀))
      = ((volume : Measure F').toSphere.real univ) • ∫ x : E, F x :=
  toSphere_real_smul_integral_stiefelMeasure L₀ hF
    (ae_integrable_weighted_frameSection L₀ hFm hF)
    (integrable_prod_radialIntegral L₀ hFm hF)

end MeasureTheory
