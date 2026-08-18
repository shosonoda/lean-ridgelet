/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import LeanRidgelet.HA.AffineMackeyLift
public import LeanRidgelet.ToMathlib.BochnerIntegralL2
public import LeanRidgelet.ToMathlib.LieGroup.GroupConvolution

/-!
# Continuity of the smoothing integral on the affine homogeneous quotient

The Haar-smoothed vector of the normalized-section induced representation has, pointwise, the
integral

`q ↦ ∫ ψ g * (phase g q * (√(det g) * f (g⁻¹ • q))) dg`

as its candidate representative. This file proves that this integral is a continuous function of the
coset, given local integrability of the lift of `f` to the group.

The mechanism is the one Folland uses: along the quotient map the integral is a group convolution of
the compactly supported kernel `ψ · √(det ·)` with the lift, corrected by the continuous unimodular
gauge of the lift. Continuity of the convolution is the compact-kernel theorem
`MeasureTheory.continuous_integral_compact_mul_right`, and continuity descends to the quotient
because the quotient map of a topological group by a subgroup is a quotient map.

The same integrand is also shown to be integrable on the product of the group with any
finite-measure part of the quotient.  That is the slice hypothesis under which the integral is the
almost-everywhere representative of the Bochner-integrated vector, and it holds because each slice
is an `L²` class of fixed norm -- the induced action is unitary -- so Hölder's inequality bounds
the slice integrals uniformly and the compactly supported kernel dominates the group variable.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The kernel of the smoothing integral, with the Radon--Nikodym square root absorbed. -/
def affineMackeySmoothingKernel
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ)) :
    C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ) where
  toFun g := ψ g * ((affineTopologicalJacobian g).sqrt : ℂ)
  continuous_toFun := by
    refine ψ.continuous.mul ?_
    exact Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp
        (NNReal.continuous_sqrt.comp continuous_affineTopologicalJacobian))
  hasCompactSupport' := ψ.hasCompactSupport.mul_right

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem affineMackeySmoothingKernel_apply
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeySmoothingKernel ψ g = ψ g * ((affineTopologicalJacobian g).sqrt : ℂ) := rfl

/-- The integrand of the smoothing integral, as a function of the group element and of the point of
the homogeneous quotient.  Each slice in the group variable is the explicit almost-everywhere
representative of the induced action, scaled by the smoothing kernel. -/
def affineMackeySmoothingIntegrand {xi : E}
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (g : AffineEquiv.TopologicalSemidirectProduct E)
    (q : AffineTopologicalMackeyQuotient xi) : ℂ :=
  ψ g * (affineTopologicalMackeySectionPhase g q *
    (((affineTopologicalJacobian g).sqrt : ℂ) * f (g⁻¹ • q)))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The smoothing integrand is jointly measurable: every factor but `f` is jointly continuous, and
`f` is composed with the continuous group action on the homogeneous quotient. -/
theorem measurable_uncurry_affineMackeySmoothingIntegrand {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    {f : AffineTopologicalMackeyQuotient xi → ℂ} (hfmeas : Measurable f) :
    Measurable (Function.uncurry (affineMackeySmoothingIntegrand ψ f)) := by
  have hψ : Measurable fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦ ψ p.1 :=
    (ψ.continuous.comp continuous_fst).measurable
  have hphase : Measurable fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦ affineTopologicalMackeySectionPhase p.1 p.2 :=
    (continuous_uncurry_affineTopologicalMackeySectionPhase hxi).measurable
  have hjac : Measurable fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦ ((affineTopologicalJacobian p.1).sqrt : ℂ) :=
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (NNReal.continuous_sqrt.comp continuous_affineTopologicalJacobian))).comp
        continuous_fst).measurable
  have haction : Continuous fun p : AffineEquiv.TopologicalSemidirectProduct E ×
      AffineTopologicalMackeyQuotient xi ↦ p.1⁻¹ • p.2 :=
    continuous_smul.comp (continuous_fst.inv.prodMk continuous_snd)
  exact hψ.mul (hphase.mul (hjac.mul (hfmeas.comp haction.measurable)))

set_option maxHeartbeats 800000 in
-- Unfolding the fully instantiated induced action goes through a long chain of `Lp` isometries.
/-- Each slice of the smoothing integrand is almost everywhere the value of the kernel times the
normalized-section induced action applied to the `L²` class that `f` represents. -/
theorem affineMackeySmoothingIntegrand_ae_eq {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    {f : AffineTopologicalMackeyQuotient xi → ℂ}
    {F : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)}
    (hfF : f =ᵐ[affineTopologicalMackeyQuotientMeasure hxi] F)
    (g : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeySmoothingIntegrand ψ f g =ᵐ[affineTopologicalMackeyQuotientMeasure hxi]
      fun q ↦ ψ g • ((affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
        Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi) →L[ℂ]
          Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)) F :
            AffineTopologicalMackeyQuotient xi → ℂ) q := by
  have hrep := affineTopologicalMackeySectionInducedLpUnitaryRepresentation_apply_ae_explicit
    hxi g F
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity
    (affineTopologicalMackeyQuotientJacobian (xi := xi))
    measurable_affineTopologicalMackeyQuotient_smul
    (affineTopologicalMackeyQuotientMeasure_map_eq_withDensity hxi) g
  have hcoe := hqmp.ae_eq hfF.symm
  filter_upwards [hrep, hcoe] with q hq hcoeq
  simp only [Function.comp_apply] at hcoeq
  rw [affineMackeySmoothingIntegrand, hq, hcoeq, smul_eq_mul]

set_option maxHeartbeats 800000 in
-- The slice estimate instantiates the induced action and its `Lp` coercions at every group element.
/-- The smoothing integrand is integrable on the product of the affine group with a finite-measure
part of the homogeneous quotient.  Its slices are `L²` classes on the quotient, hence integrable on
a set of finite measure, and Hölder's inequality bounds their `L¹` norms uniformly in the group
variable because the induced action is unitary; the smoothing kernel then supplies a compactly
supported dominating function on the group. -/
theorem integrable_uncurry_affineMackeySmoothingIntegrand {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    {f : AffineTopologicalMackeyQuotient xi → ℂ} (hfmeas : Measurable f)
    {F : Lp ℂ 2 (affineTopologicalMackeyQuotientMeasure hxi)}
    (hfF : f =ᵐ[affineTopologicalMackeyQuotientMeasure hxi] F)
    {s : Set (AffineTopologicalMackeyQuotient xi)} (hs : MeasurableSet s)
    (hfin : affineTopologicalMackeyQuotientMeasure hxi s ≠ ⊤) :
    Integrable (Function.uncurry (affineMackeySmoothingIntegrand ψ f))
      ((Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)).prod
        ((affineTopologicalMackeyQuotientMeasure hxi).restrict s)) := by
  revert F hfF
  set μQ := affineTopologicalMackeyQuotientMeasure hxi
  intro F hfF
  have huniv : (μQ.restrict s) Set.univ = μQ s := by
    rw [Measure.restrict_apply' hs, Set.univ_inter]
  haveI : IsFiniteMeasure (μQ.restrict s) := ⟨by rw [huniv]; exact lt_top_iff_ne_top.mpr hfin⟩
  -- Every slice is, up to the kernel, an `L²` class of the same norm as `F`.
  have key : ∀ g : AffineEquiv.TopologicalSemidirectProduct E, ∃ w : Lp ℂ 2 μQ, ‖w‖ = ‖F‖ ∧
      affineMackeySmoothingIntegrand ψ f g =ᵐ[μQ]
        fun q ↦ ψ g • (w : AffineTopologicalMackeyQuotient xi → ℂ) q := fun g ↦
    ⟨(affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g :
        Lp ℂ 2 μQ →L[ℂ] Lp ℂ 2 μQ) F,
      Unitary.norm_map (affineTopologicalMackeySectionInducedLpUnitaryRepresentation hxi g) F,
      affineMackeySmoothingIntegrand_ae_eq hxi ψ hfF g⟩
  have haesm : AEStronglyMeasurable (Function.uncurry (affineMackeySmoothingIntegrand ψ f))
      (Measure.haar.prod (μQ.restrict s)) :=
    (measurable_uncurry_affineMackeySmoothingIntegrand hxi ψ hfmeas).aestronglyMeasurable
  rw [integrable_prod_iff haesm]
  constructor
  · refine Filter.Eventually.of_forall fun g ↦ ?_
    obtain ⟨w, -, hae⟩ := key g
    have hmem : MemLp (affineMackeySmoothingIntegrand ψ f g) 2 μQ :=
      MemLp.ae_eq hae.symm ((Lp.memLp w).const_smul (ψ g))
    exact (hmem.restrict s).integrable one_le_two
  · set K := ‖F‖ * (μQ s).toReal ^ (2 : ℝ)⁻¹
    refine Integrable.mono' (g := fun g ↦ ‖ψ g‖ * K) ?_ haesm.norm.integral_prod_right' ?_
    · exact Continuous.integrable_of_hasCompactSupport
        (ψ.continuous.norm.mul continuous_const) ψ.hasCompactSupport.norm.mul_right
    refine Filter.Eventually.of_forall fun g ↦ ?_
    obtain ⟨w, hwnorm, hae⟩ := key g
    have hsplit : ∫ q, ‖affineMackeySmoothingIntegrand ψ f g q‖ ∂(μQ.restrict s) =
        ‖ψ g‖ * ∫ q in s, ‖(w : AffineTopologicalMackeyQuotient xi → ℂ) q‖ ∂μQ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := s) hae] with q hq
      rw [hq, norm_smul]
    have hbound := integral_norm_restrict_le_norm_mul_rpow μQ hs hfin w
    rw [hwnorm] at hbound
    calc ‖∫ q, ‖affineMackeySmoothingIntegrand ψ f g q‖ ∂(μQ.restrict s)‖
        = ∫ q, ‖affineMackeySmoothingIntegrand ψ f g q‖ ∂(μQ.restrict s) :=
          Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
      _ = ‖ψ g‖ * ∫ q in s, ‖(w : AffineTopologicalMackeyQuotient xi → ℂ) q‖ ∂μQ := hsplit
      _ ≤ ‖ψ g‖ * K := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

/-- The pointwise smoothing integral on the homogeneous quotient. -/
def affineMackeySmoothingIntegral {xi : E}
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (q : AffineTopologicalMackeyQuotient xi) : ℂ :=
  ∫ g, affineMackeySmoothingIntegrand ψ f g q ∂Measure.haar

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The smoothing integral along the quotient map is the group convolution of the smoothing kernel
with the lift, corrected by the gauge.  This is the identity that makes the convolution continuity
theorem applicable. -/
theorem affineMackeySmoothingIntegral_quotientMk {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    (f : AffineTopologicalMackeyQuotient xi → ℂ)
    (x : AffineEquiv.TopologicalSemidirectProduct E) :
    affineMackeySmoothingIntegral ψ f (QuotientGroup.mk x) =
      affineMackeyLiftPhase (xi := xi) x *
        ∫ y, affineMackeyLiftFun f y⁻¹ * affineMackeySmoothingKernel ψ (x * y) ∂Measure.haar := by
  symm
  have hshift : ∀ y : AffineEquiv.TopologicalSemidirectProduct E,
      affineMackeyLiftFun f y⁻¹ * affineMackeySmoothingKernel ψ (x * y) =
        (fun g ↦ affineMackeyLiftFun f (g⁻¹ * x) * affineMackeySmoothingKernel ψ g) (x * y) := by
    intro y
    simp only []
    congr 2
    group
  calc
    affineMackeyLiftPhase (xi := xi) x *
        ∫ y, affineMackeyLiftFun f y⁻¹ * affineMackeySmoothingKernel ψ (x * y) ∂Measure.haar =
        affineMackeyLiftPhase (xi := xi) x *
          ∫ y, (fun g ↦ affineMackeyLiftFun f (g⁻¹ * x) *
            affineMackeySmoothingKernel ψ g) (x * y) ∂Measure.haar := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hshift)
    _ = affineMackeyLiftPhase (xi := xi) x *
          ∫ g, affineMackeyLiftFun f (g⁻¹ * x) *
            affineMackeySmoothingKernel ψ g ∂Measure.haar := by
      congr 1
      exact integral_mul_left_eq_self
        (μ := (Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E)))
        (E := ℂ)
        (fun g ↦ affineMackeyLiftFun f (g⁻¹ * x) * affineMackeySmoothingKernel ψ g) x
    _ = ∫ g, affineMackeyLiftPhase (xi := xi) x *
          (affineMackeyLiftFun f (g⁻¹ * x) *
            affineMackeySmoothingKernel ψ g) ∂Measure.haar := by
      rw [← integral_const_mul]
    _ = affineMackeySmoothingIntegral ψ f (QuotientGroup.mk x) := by
      rw [affineMackeySmoothingIntegral]
      simp only [affineMackeySmoothingIntegrand]
      apply integral_congr_ae
      filter_upwards with g
      rw [affineMackeyLiftFun_inv_mul hxi f g x, affineMackeySmoothingKernel_apply]
      have hne : affineMackeyLiftPhase (xi := xi) x ≠ 0 :=
        affineMackeyLiftPhase_ne_zero hxi x
      field_simp

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Continuity of the smoothing integral on the homogeneous quotient, given local integrability of
the lift.  The convolution is continuous by the compact-kernel group-convolution theorem, the gauge
is continuous, and the quotient map is a topological quotient map. -/
theorem continuous_affineMackeySmoothingIntegral {xi : E} (hxi : xi ≠ 0)
    (ψ : C_c(AffineEquiv.TopologicalSemidirectProduct E, ℂ))
    {f : AffineTopologicalMackeyQuotient xi → ℂ}
    (hloc : LocallyIntegrable (fun y ↦ affineMackeyLiftFun f y⁻¹)
      (Measure.haar : Measure (AffineEquiv.TopologicalSemidirectProduct E))) :
    Continuous (affineMackeySmoothingIntegral ψ f) := by
  have hconv : Continuous fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      ∫ y, ContinuousLinearMap.mul ℂ ℂ (affineMackeyLiftFun f y⁻¹)
        (affineMackeySmoothingKernel ψ (x * y)) ∂Measure.haar := by
    refine MeasureTheory.continuous_integral_compact_mul_right (ContinuousLinearMap.mul ℂ ℂ)
      ?_ (affineMackeySmoothingKernel ψ).continuous
      (affineMackeySmoothingKernel ψ).hasCompactSupport
    exact hloc
  have hcomp : Continuous fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
      affineMackeySmoothingIntegral ψ f (QuotientGroup.mk x) := by
    have hfun : (fun x : AffineEquiv.TopologicalSemidirectProduct E ↦
        affineMackeySmoothingIntegral ψ f (QuotientGroup.mk x)) =
        fun x ↦ affineMackeyLiftPhase (xi := xi) x *
          ∫ y, ContinuousLinearMap.mul ℂ ℂ (affineMackeyLiftFun f y⁻¹)
            (affineMackeySmoothingKernel ψ (x * y)) ∂Measure.haar := by
      funext x
      exact affineMackeySmoothingIntegral_quotientMk hxi ψ f x
    rw [hfun]
    exact (continuous_affineMackeyLiftPhase hxi).mul hconv
  have hquotient : Topology.IsQuotientMap
      (QuotientGroup.mk : AffineEquiv.TopologicalSemidirectProduct E →
        AffineTopologicalMackeyQuotient xi) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap
  exact hquotient.continuous_iff.mpr hcomp

end LeanRidgelet
