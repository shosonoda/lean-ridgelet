/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticBounded

/-!
# The quadratic-form network through its composite kernel

`LeanRidgelet.quadratic_reconstruction_of_memLp` assumes that the feature itself is square
integrable for the product of the data measure with the parameter measure — condition T2 of the
article's boundedness appendix.  For an unbounded activation that hypothesis is false, and not
marginally so: already for a fixed parameter the integral of the squared feature over the data space
diverges, so the hypothesis is empty for the rectified linear unit and every other activation of
polynomial growth.

This file carries the other route, condition T1 of the same appendix, which is what the L1 and L2
theories use: only the *composite* kernel

`k (x, y) = ∫ ψ y ξ * conj (σ-feature x ξ) dν ξ`

has to be square integrable, and then the reconstruction operator of the network is bounded even
though neither of the two integral operators need be.  The analysis feature `ψ` is free — it is the
ridgelet function of the article, not part of the network — so the burden of decay can be put there,
exactly as the L1 theory puts it on its admissible pairs and the L2 theory on its weighted
activation spaces.

The reconstruction argument only ever uses the composite, and the development already separates that
case: `LeanRidgelet.ha_reconstruction_of_intertwiner` takes a bounded intertwining endomorphism
directly.  So the endpoint here needs no boundedness of the machine or of the ridgelet transform.

## Main results

* `LeanRidgelet.quadraticCompositeKernel`: the composite kernel of a synthesis and an analysis
  feature over the relatively invariant parameter measure.
* `LeanRidgelet.quadraticCompositeOperator`: the bounded reconstruction operator it defines, with
  `LeanRidgelet.norm_quadraticCompositeOperator_le`.
* `LeanRidgelet.coeFn_quadraticCompositeOperator`: it is the pointwise composite of the Bochner
  synthesis with the Bochner ridgelet, by Fubini.
* `LeanRidgelet.quadraticComposite_reconstruction`: the Section 7 endpoint from square integrability
  of the composite kernel alone.

## What is assumed

Square integrability of the composite kernel, and the Fubini hypothesis that exchanges the order of
the two integrals.  Both are conditions on the pair of features rather than on the activation alone,
and unlike square integrability of the feature itself they are not automatically false for an
activation of polynomial growth.

## What this route cannot give, and why

It bounds the reconstruction operator, but it cannot produce a *nonzero* reconstruction constant. 
An
operator with a square-integrable kernel is Hilbert--Schmidt, hence compact, while the scalar
operator the Schur step produces is compact only when the scalar vanishes, the data space being
infinite dimensional.  So whenever the hypotheses here are met the constant is zero and the
normalized ridgelet transform is not a right inverse of anything.  The same applies to
`LeanRidgelet.quadratic_reconstruction_of_memLp`: square integrability of the feature makes each of
the two integral operators Hilbert--Schmidt, so their composite is too.

That is not a defect of the formalization but the shape of the problem, and it is why the L1 and L2
theories do something else.  They bound the analysis and the synthesis *separately*, through a
weighted intermediate space — a weighted parameter measure in the L1 theory, transported
coordinates with a weighted activation space in the L2 theory — and neither operator is
Hilbert--Schmidt there; the composite is bounded without being compact.  For the quadratic feature
that is the route to a nonzero constant, and it is new analysis: the weight cannot go on the
parameter measure, which the balance of `LeanRidgelet.HA.QuadraticRelativeMeasure` pins down, so it
has to go where the L2 theory puts it, on the coefficient space.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- The composite kernel of an analysis feature `ψ` against a synthesis feature `σ`, integrated over
the relatively invariant parameter measure.  This is the kernel of the reconstruction operator. -/
def quadraticCompositeKernel (lam : Measure (QuadraticParameter E)) (σ ψ : ℝ → ℂ) : E × E → ℂ :=
  fun p ↦ ∫ ξ, quadraticVectorFeature ψ p.2 ξ * conj (quadraticVectorFeature σ p.1 ξ)
    ∂quadraticRelativeMeasure lam

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The reconstruction operator of the quadratic-form network, as a bounded operator on data `L²`,
whenever its composite kernel is square integrable. -/
def quadraticCompositeOperator (lam : Measure (QuadraticParameter E)) {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E))) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  hilbertSchmidtKernelOperator hk

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The operator norm of the reconstruction operator is at most the `L²` norm of the composite
kernel.  This is condition T1 of the article's boundedness appendix. -/
theorem norm_quadraticCompositeOperator_le (lam : Measure (QuadraticParameter E)) {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E))) :
    ‖quadraticCompositeOperator lam hk‖ ≤
      (eLpNorm (quadraticCompositeKernel lam σ ψ) 2
        ((volume : Measure E).prod (volume : Measure E))).toReal :=
  norm_hilbertSchmidtKernelOperator_le hk

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The kernel operator of the composite kernel is the pointwise composite of the Bochner synthesis
with the Bochner ridgelet.  The exchange of the two integrals is the Fubini hypothesis. -/
theorem coeFn_quadraticCompositeOperator (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E)))
    (f : Lp ℂ 2 (volume : Measure E))
    (hfub : ∀ᵐ x ∂(volume : Measure E), Integrable
      (Function.uncurry fun (ξ : QuadraticParameter E) (y : E) ↦
        (f : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) * quadraticVectorFeature σ x ξ)
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    (quadraticCompositeOperator lam hk f : E → ℂ) =ᵐ[(volume : Measure E)]
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) := by
  refine (coeFn_hilbertSchmidtKernelOperator hk f).trans ?_
  filter_upwards [hfub] with x hx
  have hswap : ∫ ξ, (∫ y, (f : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) *
        quadraticVectorFeature σ x ξ ∂(volume : Measure E)) ∂quadraticRelativeMeasure lam =
      ∫ y, (∫ ξ, (f : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) *
        quadraticVectorFeature σ x ξ ∂quadraticRelativeMeasure lam) ∂(volume : Measure E) :=
    integral_integral_swap hx
  have hright : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
      (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ)) x =
      ∫ ξ, (∫ y, (f : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) *
        quadraticVectorFeature σ x ξ ∂(volume : Measure E)) ∂quadraticRelativeMeasure lam := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
    simp only [bochnerRidgelet, RCLike.inner_apply, smul_eq_mul]
    rw [← integral_mul_const]
  have hleft : ∫ y, (f : E → ℂ) y * conj (quadraticCompositeKernel lam σ ψ (x, y))
        ∂(volume : Measure E) =
      ∫ y, (∫ ξ, (f : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) *
        quadraticVectorFeature σ x ξ ∂quadraticRelativeMeasure lam) ∂(volume : Measure E) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [quadraticCompositeKernel, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hleft, ← hswap, ← hright]

omit [Nontrivial E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The Bochner ridgelet of the quadratic feature only depends on the data function up to almost
everywhere equality. -/
theorem bochnerRidgelet_quadraticVectorFeature_congr_ae (ψ : ℝ → ℂ) {F₁ F₂ : E → ℂ}
    (hF : F₁ =ᵐ[(volume : Measure E)] F₂) :
    bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) F₁ =
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) F₂ := by
  funext ξ
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx]

omit [Nontrivial E] in
/-- The reconstruction operator intertwines the affine data representation with itself.  The
identity holds in `L²`, and both pointwise Bochner identities enter through the almost-everywhere
formula for the data representation. -/
theorem quadraticCompositeOperator_intertwines (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E)))
    (hfub : ∀ h : Lp ℂ 2 (volume : Measure E), ∀ᵐ x ∂(volume : Measure E), Integrable
      (Function.uncurry fun (ξ : QuadraticParameter E) (y : E) ↦
        (h : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) * quadraticVectorFeature σ x ξ)
      ((quadraticRelativeMeasure lam).prod (volume : Measure E)))
    (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 (volume : Measure E)) :
    quadraticCompositeOperator lam hk
        ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f) =
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        (quadraticCompositeOperator lam hk f) := by
  refine Lp.ext_iff.2 ?_
  have hπD := affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g f
  have hpull : bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
      (fun x ↦ ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
        Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f : E → ℂ) x) =
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          fun x ↦ (f : E → ℂ) x) := by
    have hstep := bochnerRidgelet_quadraticVectorFeature_congr_ae (E := E) ψ
      (hπD.trans (Filter.EventuallyEq.of_eq
        (quasiUnitaryPullbackAction_one_eq affineDataJacobian g fun x ↦ (f : E → ℂ) x).symm))
    rw [hstep]
    funext ξ
    exact quadraticRelativeBochnerRidgelet_intertwines (volume : Measure E) ψ g
      (fun x ↦ (f : E → ℂ) x) ξ
  refine (coeFn_quadraticCompositeOperator lam hk _ (hfub _)).trans ?_
  rw [hpull]
  have hsyn : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
      (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          fun x ↦ (f : E → ℂ) x)) =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g
        (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
            fun x ↦ (f : E → ℂ) x)) := by
    funext x
    exact quadraticRelativeBochnerSynthesis_intertwines lam σ g _ x
  rw [hsyn]
  refine Filter.EventuallyEq.symm ?_
  refine (affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g _).trans ?_
  rw [← quasiUnitaryPullbackAction_one_eq affineDataJacobian g]
  exact affineData_quasiUnitaryPullbackAction_congr_ae g
    (coeFn_quadraticCompositeOperator lam hk f (hfub f))

/-- The reconstruction operator as a bundled intertwining endomorphism of the data
representation. -/
def quadraticCompositeIntertwiner (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E)))
    (hfub : ∀ h : Lp ℂ 2 (volume : Measure E), ∀ᵐ x ∂(volume : Measure E), Integrable
      (Function.uncurry fun (ξ : QuadraticParameter E) (y : E) ↦
        (h : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) * quadraticVectorFeature σ x ξ)
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    JointEquivariantMachine
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation where
  __ := quadraticCompositeOperator lam hk
  isIntertwining' g :=
    ContinuousLinearMap.ext fun f ↦ quadraticCompositeOperator_intertwines lam hk hfub g f

/-- **Section 7 for an unbounded activation.**  If the composite kernel of the pair of features is
square integrable and the two integrals may be exchanged, then the reconstruction operator of the
quadratic-form network is a scalar multiple of the identity.  Neither the machine nor the ridgelet
transform is assumed bounded, which is what makes the statement available for an activation of
polynomial growth such as the rectified linear unit. -/
theorem quadraticComposite_reconstruction (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ}
    (hk : MemLp (quadraticCompositeKernel lam σ ψ) 2
      ((volume : Measure E).prod (volume : Measure E)))
    (hfub : ∀ h : Lp ℂ 2 (volume : Measure E), ∀ᵐ x ∂(volume : Measure E), Integrable
      (Function.uncurry fun (ξ : QuadraticParameter E) (y : E) ↦
        (h : E → ℂ) y * conj (quadraticVectorFeature ψ y ξ) * quadraticVectorFeature σ x ξ)
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    ∃ c : ℂ, (quadraticCompositeIntertwiner lam hk hfub).toContinuousLinearMap =
      c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
  ha_reconstruction_of_intertwiner
    (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E))
    affineDataLpUnitaryRepresentation_isTopologicallyIrreducible
    (quadraticCompositeIntertwiner lam hk hfub)

end LeanRidgelet
