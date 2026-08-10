/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

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
* `MeasureTheory.lintegral_eq_lintegral_prod_toSphere`,
  `MeasureTheory.lintegral_volumeIoiPow`,
  `MeasureTheory.lintegral_eq_lintegral_toSphere_lintegral_Ioi`: the same two forms for the lower
  Lebesgue integral, where the first needs no hypothesis and the second only measurability.
* `MeasureTheory.ae_integrable_radial_of_integrable`: at almost every direction the radial section
  `r ↦ |r|^{d-1} F (r • u)` is itself integrable on `ℝ`. This is the fibrewise counterpart of the
  statement above, and it is what keeps the iterated formulas free of any hypothesis beyond
  integrability of `F`.

The same formulas are proved for the **lower Lebesgue integral**,
`MeasureTheory.lintegral_eq_lintegral_prod_toSphere` and
`MeasureTheory.lintegral_eq_lintegral_toSphere_lintegral_Ioi`. There the product form needs no
hypothesis at all and the iterated form needs only measurability, both reductions being Tonelli; and
that is what an absolute convergence *statement* has to be proved with, since deciding whether a
product integrand is integrable means computing the integral of its norm.

The sphere measure is also shown to be invariant under the antipodal map,
`MeasureTheory.map_sphereNeg_toSphere`. Mathlib records how `Measure.toSphere` is computed but
none of its symmetries, and this one is what turns the polar formula above, whose radial variable
runs over `(0, ∞)`, into the two-sided form
`MeasureTheory.integral_eq_integral_toSphere_integral_two_sided` whose radial variable runs over
all of `ℝ` at the cost of a factor `2`. That two-sided form is the one that matches a scale
parameter ranging over a full Euclidean space.
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

omit [NormedSpace ℝ G] [Nontrivial E] in
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

/-- Integrability against `volumeIoiPow n` is integrability against the density `r ^ n`, the
integrability counterpart of `MeasureTheory.integral_volumeIoiPow`. -/
theorem integrable_volumeIoiPow_iff (n : ℕ) (H : ℝ → G) :
    Integrable (fun r : Ioi (0 : ℝ) => H (r : ℝ)) (Measure.volumeIoiPow n)
      ↔ IntegrableOn (fun r : ℝ => r ^ n • H r) (Ioi (0 : ℝ)) volume := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integrable_withDensity_iff_integrable_smul (by fun_prop)]
  refine integrable_congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply, NNReal.smul_def,
    Real.coe_toNNReal _ (pow_nonneg (le_of_lt r.2) n)]

omit [Nontrivial E] in
/-- **Almost every radial section of an integrable function is integrable on the positive
half-line.** The polar decomposition of an integrable function is integrable on the product
`sphere × (0, ∞)`, so almost every fibre over the sphere is integrable. -/
theorem ae_integrableOn_Ioi_of_integrable {F : E → G} (hF : Integrable F μ) :
    ∀ᵐ u : sphere (0 : E) 1 ∂μ.toSphere,
      IntegrableOn (fun r : ℝ => r ^ (dim E - 1) • F (r • (u : E))) (Ioi (0 : ℝ)) volume := by
  filter_upwards [(integrable_prod_toSphere_of_integrable μ hF).prod_right_ae] with u hu
  exact (integrable_volumeIoiPow_iff (dim E - 1) fun r : ℝ => F (r • (u : E))).1 hu

omit [Nontrivial E] in
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

/-! ## The lower Lebesgue integral

The unsigned forms carry no hypothesis beyond measurability, so they are what an absolute
convergence *statement* has to be proved with: to know that a product integrand is integrable one
computes the integral of its norm, and that computation is Tonelli, not Fubini.
-/

/-- **Polar coordinates for the lower Lebesgue integral**, product form. No hypothesis at all: the
polar map is a measurable equivalence and both sides of the change of variables are unsigned. -/
theorem lintegral_eq_lintegral_prod_toSphere (F : E → ℝ≥0∞) :
    ∫⁻ x, F x ∂μ = ∫⁻ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      F ((p.2 : ℝ) • (p.1 : E)) ∂(μ.toSphere.prod (Measure.volumeIoiPow (dim E - 1))) := by
  calc ∫⁻ x, F x ∂μ
      = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F (x : E) ∂(Measure.comap Subtype.val μ) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl F,
          restrict_compl_singleton]
    _ = _ := by
        rw [← μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F ((p.2 : ℝ) • (p.1 : E)))]
        refine lintegral_congr fun x => ?_
        have hx : (x : E) ≠ 0 := x.2
        simp only [homeomorphUnitSphereProd_apply_fst_coe,
          homeomorphUnitSphereProd_apply_snd_coe, smul_smul]
        rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

/-- The lower Lebesgue integral against `volumeIoiPow n` is the one against the density `r ^ n`,
the unsigned counterpart of `MeasureTheory.integral_volumeIoiPow`. -/
theorem lintegral_volumeIoiPow (n : ℕ) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ r : Ioi (0 : ℝ), H (r : ℝ) ∂(Measure.volumeIoiPow n)
      = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * H r := by
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (g := fun r : Ioi (0 : ℝ) => H (r : ℝ)) (by fun_prop),
    ← lintegral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r ^ n) * H r)]
  rfl

/-- **Polar coordinates for the lower Lebesgue integral**, iterated form:
`∫⁻ F = ∫⁻_{sphere} ∫⁻_{r > 0} r^{d-1} F (r • u) dr du`. Measurability of the integrand is the only
hypothesis; this is Tonelli, so there is nothing to assume about convergence. -/
theorem lintegral_eq_lintegral_toSphere_lintegral_Ioi {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂μ
      = ∫⁻ u : sphere (0 : E) 1,
          (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (dim E - 1)) * F (r • (u : E)))
        ∂μ.toSphere := by
  rw [lintegral_eq_lintegral_prod_toSphere μ F,
    lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun u => ?_
  exact lintegral_volumeIoiPow (dim E - 1) (H := fun r : ℝ => F (r • (u : E)))
    (hF.comp (measurable_id.smul_const (u : E)))

/-! ## The antipodal map -/

/-- The antipodal map on the unit sphere. -/
def sphereNeg (E : Type*) [NormedAddCommGroup E] : sphere (0 : E) 1 → sphere (0 : E) 1 :=
  fun u => ⟨-(u : E), by simp⟩

omit [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
@[simp] theorem coe_sphereNeg (u : sphere (0 : E) 1) : ((sphereNeg E u : sphere (0 : E) 1) : E)
    = -(u : E) := rfl

omit [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem continuous_sphereNeg : Continuous (sphereNeg E) :=
  Continuous.subtype_mk (continuous_subtype_val.neg) _

omit [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] in
theorem measurable_sphereNeg : Measurable (sphereNeg E) :=
  continuous_sphereNeg.measurable

omit [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem image_coe_preimage_sphereNeg (s : Set (sphere (0 : E) 1)) :
    ((↑) : sphere (0 : E) 1 → E) '' (sphereNeg E ⁻¹' s) = -(((↑) : sphere (0 : E) 1 → E) '' s) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨sphereNeg E u, hu, rfl⟩
  · rintro ⟨v, hv, hx⟩
    refine ⟨sphereNeg E v, ?_, ?_⟩
    · simpa [sphereNeg] using hv
    · simp only [coe_sphereNeg]
      rw [hx, neg_neg]

omit [MeasurableSpace E] [Nontrivial E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Scaling a reflected set by a set of scalars reflects the scaled set. -/
theorem smul_set_neg_set (S : Set ℝ) (A : Set E) : S • (-A) = -(S • A) := by
  ext x
  simp only [Set.mem_smul, Set.mem_neg]
  constructor
  · rintro ⟨s, hs, a, ha, rfl⟩
    exact ⟨s, hs, -a, by simpa using ha, by simp⟩
  · rintro ⟨s, hs, a, ha, hx⟩
    refine ⟨s, hs, -a, by simpa using ha, ?_⟩
    rw [smul_neg, hx, neg_neg]

omit [Nontrivial E] in
/-- **The sphere measure is invariant under the antipodal map.** Mathlib computes
`Measure.toSphere` but records none of its symmetries; this one follows from the invariance of an
additive Haar measure under negation, because the cone over the reflected set is the reflection of
the cone. -/
theorem map_sphereNeg_toSphere : Measure.map (sphereNeg E) μ.toSphere = μ.toSphere := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_sphereNeg hs,
    Measure.toSphere_apply' μ (measurable_sphereNeg hs), Measure.toSphere_apply' μ hs,
    image_coe_preimage_sphereNeg, smul_set_neg_set, Measure.measure_neg μ]

omit [Nontrivial E] [FiniteDimensional ℝ E] in
/-- The antipodal map as a measurable equivalence. -/
def sphereNegEquiv : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toFun := sphereNeg E
  invFun := sphereNeg E
  left_inv u := Subtype.ext (neg_neg (u : E))
  right_inv u := Subtype.ext (neg_neg (u : E))
  measurable_toFun := measurable_sphereNeg
  measurable_invFun := measurable_sphereNeg

omit [Nontrivial E] [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
theorem measurableEmbedding_sphereNeg : MeasurableEmbedding (sphereNeg E) := by
  exact (sphereNegEquiv (E := E)).measurableEmbedding

omit [Nontrivial E] in
theorem measurePreserving_sphereNeg :
    MeasurePreserving (sphereNeg E) μ.toSphere μ.toSphere :=
  ⟨measurable_sphereNeg, map_sphereNeg_toSphere μ⟩

omit [Nontrivial E] in
/-- Integration against the sphere measure is invariant under the antipodal map. -/
theorem integral_sphereNeg (F : sphere (0 : E) 1 → G) :
    ∫ u : sphere (0 : E) 1, F (sphereNeg E u) ∂μ.toSphere
      = ∫ u : sphere (0 : E) 1, F u ∂μ.toSphere :=
  (measurePreserving_sphereNeg μ).integral_comp measurableEmbedding_sphereNeg F

/-! ## The two-sided polar formula -/

omit [MeasurableSpace E] [Nontrivial E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Reflecting the radius is reflecting the direction. -/
theorem integral_Ioi_sphereNeg (F : E → G) (u : sphere (0 : E) 1) :
    (∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • ((sphereNeg E u : sphere (0 : E) 1) : E)))
      = ∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)) := by
  have hIic : (∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)))
      = ∫ r in Iic (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)) :=
    setIntegral_congr_set Iio_ae_eq_Iic
  have hneg := integral_comp_neg_Ioi (0 : ℝ) fun r => |r| ^ (dim E - 1) • F (r • (u : E))
  simp only [neg_zero] at hneg
  rw [hIic, ← hneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : (0 : ℝ) < r := hr
  simp [abs_neg, abs_of_pos hr0, coe_sphereNeg, neg_smul, smul_neg]

/-- The polar formula with the radial variable on the negative axis. The sphere measure does not
see the reflection, so the negative half-line contributes the whole integral again. -/
theorem integral_eq_integral_toSphere_integral_Iio {F : E → G} (hF : Integrable F μ) :
    ∫ x, F x ∂μ = ∫ u : sphere (0 : E) 1,
      (∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E))) ∂μ.toSphere := by
  calc ∫ x, F x ∂μ
      = ∫ u : sphere (0 : E) 1,
          (∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • (u : E))) ∂μ.toSphere :=
        integral_eq_integral_toSphere_integral_Ioi μ hF
    _ = ∫ u : sphere (0 : E) 1,
          (∫ r in Ioi (0 : ℝ),
            r ^ (dim E - 1) • F (r • ((sphereNeg E u : sphere (0 : E) 1) : E))) ∂μ.toSphere :=
        (integral_sphereNeg μ _).symm
    _ = ∫ u : sphere (0 : E) 1,
          (∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E))) ∂μ.toSphere :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => integral_Ioi_sphereNeg F u)

omit [Nontrivial E] in
/-- The negative-axis polar integral is integrable on the sphere. -/
theorem integrable_toSphere_integral_Iio {F : E → G} (hF : Integrable F μ) :
    Integrable (fun u : sphere (0 : E) 1 =>
      ∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E))) μ.toSphere := by
  have hcomp := ((measurePreserving_sphereNeg μ).integrable_comp_emb
    measurableEmbedding_sphereNeg).mpr (integrable_toSphere_integral_Ioi μ hF)
  refine hcomp.congr (Filter.Eventually.of_forall fun u => ?_)
  exact integral_Ioi_sphereNeg F u

omit [Nontrivial E] in
/-- Almost every radial section is integrable on the negative half-line too: the sphere measure
does not see the antipodal map, so the statement transports from the positive half-line by
`r ↦ -r`. -/
theorem ae_integrableOn_Iio_of_integrable {F : E → G} (hF : Integrable F μ) :
    ∀ᵐ u : sphere (0 : E) 1 ∂μ.toSphere,
      IntegrableOn (fun r : ℝ => |r| ^ (dim E - 1) • F (r • (u : E))) (Iio (0 : ℝ)) volume := by
  filter_upwards [(measurePreserving_sphereNeg μ).quasiMeasurePreserving.ae
    (ae_integrableOn_Ioi_of_integrable μ hF)] with u hu
  refine (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
    (Homeomorph.neg ℝ).measurableEmbedding).1 ?_
  rw [show (fun r : ℝ => -r) ⁻¹' (Iio (0 : ℝ)) = Ioi (0 : ℝ) by ext r; simp]
  refine hu.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0 : (0 : ℝ) < r := hr
  simp only [Function.comp_apply, coe_sphereNeg, abs_neg, abs_of_pos hr0, neg_smul, smul_neg]

omit [Nontrivial E] in
/-- **The radial section of an integrable function is integrable, at almost every direction.** Both
half-lines together, which is what the two-sided polar formula below needs. -/
theorem ae_integrable_radial_of_integrable {F : E → G} (hF : Integrable F μ) :
    ∀ᵐ u : sphere (0 : E) 1 ∂μ.toSphere,
      Integrable (fun r : ℝ => |r| ^ (dim E - 1) • F (r • (u : E))) (volume : Measure ℝ) := by
  filter_upwards [ae_integrableOn_Ioi_of_integrable μ hF,
    ae_integrableOn_Iio_of_integrable μ hF] with u hIoi hIio
  have hIoi' : IntegrableOn (fun r : ℝ => |r| ^ (dim E - 1) • F (r • (u : E)))
      (Ioi (0 : ℝ)) volume :=
    hIoi.congr_fun (fun r hr => by
      rw [abs_of_pos (show (0 : ℝ) < r from hr)]) measurableSet_Ioi
  have hunion := hIio.union hIoi'
  rw [Iio_union_Ioi] at hunion
  rwa [IntegrableOn, restrict_compl_singleton] at hunion

/-- **The two-sided polar formula.** With the radial variable running over all of `ℝ` against the
weight `|r|^{d-1}`, the polar integral computes twice the integral. This is the form that matches
a scale parameter ranging over a full Euclidean space rather than over a half-line, and the factor
`2` is exactly the double cover `(r, u) ↦ r • u` of `E ∖ {0}` by `ℝ ∖ {0} × 𝕊`. -/
theorem integral_eq_integral_toSphere_integral_two_sided {F : E → G} (hF : Integrable F μ) :
    (2 : ℝ) • ∫ x, F x ∂μ
      = ∫ u : sphere (0 : E) 1,
          (∫ r : ℝ, |r| ^ (dim E - 1) • F (r • (u : E)) ∂(volume : Measure ℝ)) ∂μ.toSphere := by
  have hint := ae_integrable_radial_of_integrable μ hF
  have hsplit : ∀ᵐ u : sphere (0 : E) 1 ∂μ.toSphere,
      (∫ r : ℝ, |r| ^ (dim E - 1) • F (r • (u : E)) ∂(volume : Measure ℝ))
        = (∫ r in Iio (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)))
          + ∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • (u : E)) := by
    filter_upwards [hint] with u hu
    have hIoi : (∫ r in Ioi (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)))
        = ∫ r in Ioi (0 : ℝ), r ^ (dim E - 1) • F (r • (u : E)) :=
      setIntegral_congr_fun measurableSet_Ioi fun r hr => by
        rw [abs_of_pos (show (0 : ℝ) < r from hr)]
    have hIci : (∫ r in Ici (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)))
        = ∫ r in Ioi (0 : ℝ), |r| ^ (dim E - 1) • F (r • (u : E)) :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    rw [← hIoi, ← hIci, ← integral_add_compl measurableSet_Iio hu, compl_Iio]
  have hIioInt := integrable_toSphere_integral_Iio μ hF
  have hIoiInt := integrable_toSphere_integral_Ioi μ hF
  rw [integral_congr_ae hsplit, integral_add hIioInt hIoiInt,
    ← integral_eq_integral_toSphere_integral_Iio μ hF,
    ← integral_eq_integral_toSphere_integral_Ioi μ hF, two_smul]

end MeasureTheory
