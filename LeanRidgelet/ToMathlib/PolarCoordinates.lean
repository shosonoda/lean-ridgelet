/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar coordinates for the Bochner integral

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib's `MeasureTheory.Measure.toSphere` and
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` provide the polar
decomposition of an additive Haar measure on a normed space, but the resulting integral formula is
recorded only for **radial** integrands (`MeasureTheory.integral_fun_norm_addHaar`). This file
proves the general formula
$$`\int_E F\,d\mu=\int_{\mathbb S}\int_0^\infty r^{d-1}F(r\,u)\,dr\,d\mu_{\mathbb S}(u),
\qquad d=\dim E,`
for an arbitrary integrand, following the same route as the radial case: restrict to `Eᶜ{0}`,
transport along the polar homeomorphism, and unwind the density of
`MeasureTheory.Measure.volumeIoiPow`.

## Main results

* `MeasureTheory.integral_eq_integral_prod_toSphere`: the product form, valid for every
  integrand (both sides are junk values simultaneously when the integrand is not integrable,
  since the polar map is measure preserving).
* `MeasureTheory.integrable_prod_toSphere_of_integrable`: integrability transports to polar
  coordinates.
* `MeasureTheory.integral_eq_integral_toSphere_integral_Ioi`: the iterated form
  `∫ F = ∫_{sphere} ∫_{r > 0} r^{d-1} F (r • u) dr du` for an integrable integrand, and
  `MeasureTheory.integrable_toSphere_integral_Ioi`: its inner integral is integrable on the
  sphere.
-/

@[expose] public section

noncomputable section

open Set Function Metric MeasurableSpace MeasureTheory
open scoped Pointwise ENNReal NNReal

local notation "dim" => Module.finrank ℝ

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [Nontrivial E] (μ : Measure E) [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- **Polar coordinates**, product form: the Bochner integral over a nontrivial
finite-dimensional normed space with an additive Haar measure equals the integral over
`sphere × (0, ∞)` of `F (r • u)` against `μ.toSphere.prod (volumeIoiPow (dim E - 1))`. -/
theorem integral_eq_integral_prod_toSphere (F : E → G) :
    ∫ x, F x ∂μ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      F ((p.2 : ℝ) • (p.1 : E)) ∂(μ.toSphere.prod (Measure.volumeIoiPow (dim E - 1))) := by
  calc ∫ x, F x ∂μ
      = ∫ x : ({(0 : E)}ᶜ : Set E), F (x : E) ∂(Measure.comap Subtype.val μ) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl F,
          restrict_compl_singleton]
    _ = _ := by
        have h := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
        rw [← h]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hx : (x : E) ≠ 0 := x.2
        simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
          smul_smul]
        rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- Integrability in polar coordinates. -/
theorem integrable_prod_toSphere_of_integrable {F : E → G} (hF : Integrable F μ) :
    Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
      (μ.toSphere.prod (Measure.volumeIoiPow (dim E - 1))) := by
  have hemb := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (g := fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
    (Homeomorph.measurableEmbedding _)
  rw [← hemb]
  have hsub : Integrable (fun x : ({(0 : E)}ᶜ : Set E) => F (x : E))
      (Measure.comap Subtype.val μ) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : E)).compl).mp
      hF.integrableOn
  refine hsub.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : (x : E) ≠ 0 := x.2
  simp only [Function.comp_apply, homeomorphUnitSphereProd_apply_fst_coe,
    homeomorphUnitSphereProd_apply_snd_coe, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- The integral against `volumeIoiPow n` is the integral against the density `r ^ n`. -/
theorem integral_volumeIoiPow (n : ℕ) (H : ℝ → G) :
    ∫ r : Ioi (0 : ℝ), H (r : ℝ) ∂(Measure.volumeIoiPow n) = ∫ r in Ioi (0 : ℝ), r ^ n • H r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by fun_prop) (fun r : Ioi (0 : ℝ) => H (r : ℝ)),
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r ^ n) • H r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _)]

/-- The inner polar integral is integrable on the sphere. -/
theorem integrable_toSphere_integral_Ioi {F : E → G} (hF : Integrable F μ) :
    Integrable (fun u : sphere (0 : E) 1 =>
      ∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • (u : E))) μ.toSphere := by
  have h := (integrable_prod_toSphere_of_integrable μ hF).integral_prod_left
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  exact integral_volumeIoiPow (dim E - 1) (fun r : ℝ => F (r • (u : E)))

/-- **Polar coordinates**, iterated form: `∫ F = ∫_{sphere} ∫_{r > 0} r^{d-1} F (r • u) dr du`. -/
theorem integral_eq_integral_toSphere_integral_Ioi {F : E → G} (hF : Integrable F μ) :
    ∫ x, F x ∂μ
      = ∫ u : sphere (0 : E) 1,
          (∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • (u : E))) ∂μ.toSphere := by
  rw [integral_eq_integral_prod_toSphere μ F,
    integral_prod _ (integrable_prod_toSphere_of_integrable μ hF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact integral_volumeIoiPow (dim E - 1) (fun r : ℝ => F (r • (u : E)))

end MeasureTheory
