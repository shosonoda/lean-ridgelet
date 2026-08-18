/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.AffineGroupHaar
public import LeanRidgelet.HA.AffineMackeyInduction

/-!
# The equivariant lift of a quotient class to the affine group

Folland's proof of Lemma 6.29 realizes the induced representation on functions over the group that
transform by the inducing character, and smoothing is then an ordinary group convolution. This file
constructs that lift for the affine Mackey model: a function on the quotient is multiplied by the
inverse phase of the normalized section at the point itself,

`F x = (phase x (x H))⁻¹ * f (x H)`,

so that translating the argument produces exactly the phase factor of the induced action. The
resulting identity

`F (g⁻¹ x) = (phase x (x H))⁻¹ * (phase g (x H) * f (g⁻¹ • x H))`

is what turns the smoothed vector into a convolution: integrating it against a compactly supported
kernel reproduces the induced-action integrand up to the unimodular factor `(phase x (x H))⁻¹`,
which is continuous in `x` and therefore harmless.

## Main results

* `LeanRidgelet.affineMackeyLiftPhase`: the phase at a point and its own coset, continuous and
  unimodular.
* `LeanRidgelet.affineMackeyLiftPhase_mul`: its cocycle law.
* `LeanRidgelet.affineMackeyLiftFun`: the lift of a function on the quotient.
* `LeanRidgelet.affineMackeyLiftFun_inv_mul`: the translation identity above.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The section phase of a group element at its own coset.  It is the gauge that makes the lift of a
quotient function transform by the inducing character. -/
def affineMackeyLiftPhase {xi : E} (x : AffineEquiv.TopologicalSemidirectProduct E) : ℂ :=
  affineTopologicalMackeySectionPhase (xi := xi) x (QuotientGroup.mk x)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem affineMackeyLiftPhase_norm_one {xi : E} (hxi : xi ≠ 0)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    ‖affineMackeyLiftPhase (xi := xi) x‖ = 1 :=
  affineTopologicalMackeySectionPhase_norm_one hxi x _

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem affineMackeyLiftPhase_ne_zero {xi : E} (hxi : xi ≠ 0)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeyLiftPhase (xi := xi) x ≠ 0 := by
  rw [← norm_ne_zero_iff, affineMackeyLiftPhase_norm_one hxi x]
  exact one_ne_zero

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The lift phase is continuous: although the normalized section itself is only set-theoretic, its
character equals the explicit Fourier phase, which is jointly continuous. -/
theorem continuous_affineMackeyLiftPhase {xi : E} (hxi : xi ≠ 0) :
    Continuous (affineMackeyLiftPhase (xi := xi)) := by
  have hfun : (affineMackeyLiftPhase (xi := xi)) = fun x ↦
      affineFrequencyPhase (AffineEquiv.topologicalSemidirectProductEquiv E x)
        (affineTopologicalMackeyOrbitMap xi x) := by
    funext x
    rw [affineMackeyLiftPhase, affineTopologicalMackeySectionPhase_eq_quotientPhase hxi,
      affineTopologicalMackeyQuotientPhase]
    rfl
  rw [hfun]
  unfold affineFrequencyPhase
  have htranslation : Continuous fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      (AffineEquiv.topologicalSemidirectProductEquiv E x) 0 := by
    have hfun' : (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
        (AffineEquiv.topologicalSemidirectProductEquiv E x) 0) =
        fun x ↦ x.left.toAdd := by
      funext x
      simp
    rw [hfun']
    exact SemidirectProduct.continuous_left
      (φ := AffineEquiv.continuousLinearMultiplicativeActionHom E)
  have horbit : Continuous (affineTopologicalMackeyOrbitMap xi) :=
    continuous_affineTopologicalMackeyOrbitMap xi
  fun_prop

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The cocycle law of the lift phase: translating the argument by `g⁻¹` splits off exactly the
section phase of `g` at the coset. -/
theorem affineMackeyLiftPhase_mul {xi : E} (hxi : xi ≠ 0)
    (g x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeyLiftPhase (xi := xi) x =
      affineTopologicalMackeySectionPhase (xi := xi) g (QuotientGroup.mk x) *
        affineMackeyLiftPhase (xi := xi) (g⁻¹ * x) := by
  have hcocycle := affineTopologicalMackeySectionPhase_cocycle hxi g (g⁻¹ * x)
    (QuotientGroup.mk (s := (affineTopologicalMackeySubgroup xi).toSubgroup) x)
  rw [show g * (g⁻¹ * x) = x by group] at hcocycle
  rw [affineMackeyLiftPhase, hcocycle]
  congr 2

/-- The lift of a function on the affine homogeneous quotient to the affine group. -/
def affineMackeyLiftFun {xi : E} (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (x : AffineEquiv.TopologicalSemidirectProduct E) : ℂ :=
  (affineMackeyLiftPhase (xi := xi) x)⁻¹ * f (QuotientGroup.mk x)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem affineMackeyLiftFun_apply {xi : E} (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeyLiftFun f x = (affineMackeyLiftPhase (xi := xi) x)⁻¹ * f (QuotientGroup.mk x) :=
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The lift has the same absolute value as the function it lifts, because the gauge is
unimodular. -/
theorem norm_affineMackeyLiftFun {xi : E} (hxi : xi ≠ 0)
    (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    ‖affineMackeyLiftFun f x‖ = ‖f (QuotientGroup.mk x)‖ := by
  rw [affineMackeyLiftFun_apply, norm_mul, norm_inv,
    affineMackeyLiftPhase_norm_one hxi x, inv_one, one_mul]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The translation identity that turns smoothing into a convolution: the lift at `g⁻¹ x` is the
induced-action integrand at the coset of `x`, up to the gauge at `x`. -/
theorem affineMackeyLiftFun_inv_mul {xi : E} (hxi : xi ≠ 0)
    (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (g x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeyLiftFun f (g⁻¹ * x) =
      (affineMackeyLiftPhase (xi := xi) x)⁻¹ *
        (affineTopologicalMackeySectionPhase (xi := xi) g (QuotientGroup.mk x) *
          f (g⁻¹ • QuotientGroup.mk (s := (affineTopologicalMackeySubgroup xi).toSubgroup) x)) := by
  have hphase := affineMackeyLiftPhase_mul hxi g x
  have hcoset : QuotientGroup.mk (s := (affineTopologicalMackeySubgroup xi).toSubgroup)
      (g⁻¹ * x) =
      g⁻¹ • QuotientGroup.mk (s := (affineTopologicalMackeySubgroup xi).toSubgroup) x := rfl
  have hne : affineMackeyLiftPhase (xi := xi) (g⁻¹ * x) ≠ 0 :=
    affineMackeyLiftPhase_ne_zero hxi _
  have hgne : affineTopologicalMackeySectionPhase (xi := xi) g (QuotientGroup.mk x) ≠ 0 := by
    rw [← norm_ne_zero_iff, affineTopologicalMackeySectionPhase_norm_one hxi]
    exact one_ne_zero
  rw [affineMackeyLiftFun_apply, hcoset, hphase, mul_inv, ← mul_assoc]
  congr 1
  field_simp

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The lift of a measurable function is measurable: the gauge is continuous and the quotient map is
continuous. -/
theorem measurable_affineMackeyLiftFun {xi : E} (hxi : xi ≠ 0)
    {f : AffineTopologicalMackeyQuotient xi → ℂ} (hf : Measurable f) :
    Measurable (affineMackeyLiftFun f) := by
  have hcont : Continuous (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      (QuotientGroup.mk x : AffineTopologicalMackeyQuotient xi)) := continuous_quotient_mk'
  have hmk : Measurable (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      (QuotientGroup.mk x : AffineTopologicalMackeyQuotient xi)) :=
    Continuous.measurable (γ := AffineTopologicalMackeyQuotient xi) hcont
  exact ((continuous_affineMackeyLiftPhase hxi).measurable.inv).mul (hf.comp hmk)

/-- The image of a compactly restricted Haar measure of the affine group under the inverse coset
map is dominated by a finite multiple of the homogeneous-quotient measure, restricted to a set of
finite measure. -/
theorem affine_map_quotientMk_inv_haar_restrict_le {xi : E} (hxi : xi ≠ 0)
    {S : Set (AffineEquiv.TopologicalSemidirectProduct E)} (hS : IsCompact S) :
    ∃ (C : ℝ≥0∞) (B : Set (AffineTopologicalMackeyQuotient xi)), C ≠ ⊤ ∧
      affineTopologicalMackeyQuotientMeasure hxi B ≠ ⊤ ∧
      Measure.map (fun x ↦ (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi))
          ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) ≤
        C • (affineTopologicalMackeyQuotientMeasure hxi).restrict B := by
  classical
  set T : AffineTopologicalMackeyQuotient xi → E :=
    fun q ↦ (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi q).1 with hTdef
  have hTemb : MeasurableEmbedding T :=
    (MeasurableEmbedding.subtype_coe measurableSet_affineDualOrbit).comp
      (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi).measurableEmbedding
  have hTmk : ∀ p : AffineEquiv.TopologicalSemidirectProduct E,
      T (QuotientGroup.mk p) = affineTopologicalMackeyOrbitMap xi p := fun _ ↦ rfl
  have hTmap :
      Measure.map T (affineTopologicalMackeyQuotientMeasure hxi) = (volume : Measure E) := by
    have hcomp : T = (Subtype.val : affineDualOrbit (E := E) → E) ∘
        (affineTopologicalMackeyQuotientHomeomorphDualOrbit hxi) := rfl
    rw [hcomp, ← Measure.map_map measurable_subtype_coe
        (affineTopologicalMackeyQuotient_measurePreserving hxi).measurable,
      (affineTopologicalMackeyQuotient_measurePreserving hxi).map_eq,
      affineDualOrbitSubtypeMeasure_map_subtypeVal]
  obtain ⟨C, B₀, hCtop, hB₀compact, hbound⟩ := affine_map_adjointOrbitMap_haar_restrict_le hxi hS
  refine ⟨C, T ⁻¹' B₀, hCtop, ?_, ?_⟩
  · rw [← Measure.map_apply hTemb.measurable hB₀compact.measurableSet, hTmap]
    exact hB₀compact.measure_lt_top.ne
  · have hmkinv : Measurable fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
        (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi) :=
      QuotientGroup.measurable_coe.comp continuous_inv.measurable
    have horbitinv : Measurable fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
        affineTopologicalMackeyOrbitMap xi x⁻¹ :=
      ((continuous_affineTopologicalMackeyOrbitMap xi).comp continuous_inv).measurable
    rw [Measure.le_iff]
    intro A hA
    have himage : MeasurableSet (T '' A) := hTemb.measurableSet_image.mpr hA
    have hpre : (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
          (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi)) ⁻¹' A =
        (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
          affineTopologicalMackeyOrbitMap xi x⁻¹) ⁻¹' (T '' A) := by
      ext x
      simp only [Set.mem_preimage, ← hTmk x⁻¹, hTemb.injective.mem_set_image]
    calc
      Measure.map (fun x ↦ (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi))
            ((Measure.haar :
              Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) A =
          Measure.map (fun x ↦ affineTopologicalMackeyOrbitMap xi x⁻¹)
            ((Measure.haar :
              Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) (T '' A) := by
        rw [Measure.map_apply hmkinv hA, Measure.map_apply horbitinv himage, hpre]
      _ ≤ (C • (volume : Measure E).restrict B₀) (T '' A) := Measure.le_iff'.mp hbound _
      _ = C * (volume : Measure E) (T '' A ∩ B₀) := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply himage]
      _ = C * affineTopologicalMackeyQuotientMeasure hxi (A ∩ T ⁻¹' B₀) := by
        have hset : T ⁻¹' (T '' A ∩ B₀) = A ∩ T ⁻¹' B₀ := by
          rw [Set.preimage_inter, Set.preimage_image_eq A hTemb.injective]
        rw [← hTmap, Measure.map_apply hTemb.measurable
          (himage.inter hB₀compact.measurableSet), hset]
      _ = (C • (affineTopologicalMackeyQuotientMeasure hxi).restrict (T ⁻¹' B₀)) A := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]

omit [Nontrivial E] in
/-- The lift of an `L²` class on the affine homogeneous quotient, precomposed with inversion, is
locally integrable on the affine group, provided the image of every compactly restricted Haar
measure under `x ↦ x⁻¹ H` is dominated by a finite multiple of the homogeneous-space measure
restricted to a set of finite measure.

Local compactness reduces the claim to integrability on a compact set. The lift is measurable and
has the same absolute value as the class it lifts, so the lower integral of its norm transports to
the quotient along `x ↦ x⁻¹ H`; the domination hypothesis then bounds it by a finite multiple of
the lower integral of `‖f‖` over a set of finite measure, which is finite because an `L²` function
on a finite measure is integrable. -/
theorem locallyIntegrable_affineMackeyLiftFun_inv_of_bound {xi : E} (hxi : xi ≠ 0)
    {f : AffineTopologicalMackeyQuotient xi → ℂ} (hfmeas : Measurable f)
    (hf : MemLp f 2 (affineTopologicalMackeyQuotientMeasure hxi))
    (hbound : ∀ S : Set (AffineEquiv.TopologicalSemidirectProduct E), IsCompact S →
      ∃ (C : ℝ≥0∞) (B : Set (AffineTopologicalMackeyQuotient xi)), C ≠ ⊤ ∧
        affineTopologicalMackeyQuotientMeasure hxi B ≠ ⊤ ∧
        Measure.map (fun x ↦ (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi))
            ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) ≤
          C • (affineTopologicalMackeyQuotientMeasure hxi).restrict B) :
    LocallyIntegrable (fun y ↦ affineMackeyLiftFun f y⁻¹)
      (Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)) := by
  have hmk : Measurable (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi)) :=
    Continuous.measurable (γ := AffineTopologicalMackeyQuotient xi)
      (continuous_quotient_mk'.comp continuous_inv)
  have hlift : Measurable (fun y : AffineEquiv.TopologicalSemidirectProduct E ↦
      affineMackeyLiftFun f y⁻¹) :=
    (measurable_affineMackeyLiftFun hxi hfmeas).comp continuous_inv.measurable
  rw [locallyIntegrable_iff]
  intro S hS
  obtain ⟨C, B, hC, hB, hle⟩ := hbound S hS
  haveI : IsFiniteMeasure ((affineTopologicalMackeyQuotientMeasure hxi).restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hB.lt_top⟩
  have hintegrable : Integrable f ((affineTopologicalMackeyQuotientMeasure hxi).restrict B) :=
    (hf.restrict B).integrable one_le_two
  refine ⟨hlift.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  calc ∫⁻ y, ‖affineMackeyLiftFun f y⁻¹‖ₑ
        ∂((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S)
      = ∫⁻ y, ‖f (QuotientGroup.mk y⁻¹ : AffineTopologicalMackeyQuotient xi)‖ₑ
        ∂((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S) := by
        refine lintegral_congr fun y ↦ ?_
        rw [← ofReal_norm, ← ofReal_norm, norm_affineMackeyLiftFun hxi]
    _ = ∫⁻ q, ‖f q‖ₑ
        ∂(Measure.map (fun x ↦ (QuotientGroup.mk x⁻¹ : AffineTopologicalMackeyQuotient xi))
          ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).restrict S)) :=
        (lintegral_map hfmeas.enorm hmk).symm
    _ ≤ ∫⁻ q, ‖f q‖ₑ ∂(C • (affineTopologicalMackeyQuotientMeasure hxi).restrict B) :=
        lintegral_mono' hle le_rfl
    _ = C * ∫⁻ q, ‖f q‖ₑ ∂((affineTopologicalMackeyQuotientMeasure hxi).restrict B) :=
        lintegral_smul_measure _ _
    _ < ∞ := ENNReal.mul_lt_top hC.lt_top hintegrable.hasFiniteIntegral

/-- Local integrability of the lift composed with inversion, which is the hypothesis of the
compact-kernel group-convolution continuity theorem.  It combines the quotient-form Haar
pushforward bound with the Cauchy--Schwarz estimate on a finite-measure set. -/
theorem locallyIntegrable_affineMackeyLiftFun_inv {xi : E} (hxi : xi ≠ 0)
    {f : AffineTopologicalMackeyQuotient xi → ℂ} (hfmeas : Measurable f)
    (hf : MemLp f 2 (affineTopologicalMackeyQuotientMeasure hxi)) :
    LocallyIntegrable (fun y ↦ affineMackeyLiftFun f y⁻¹)
      (Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)) :=
  locallyIntegrable_affineMackeyLiftFun_inv_of_bound hxi hfmeas hf
    fun _ hS ↦ affine_map_quotientMk_inv_haar_restrict_le hxi hS

end LeanRidgelet
