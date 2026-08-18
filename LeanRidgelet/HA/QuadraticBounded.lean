/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticReconstruction
public import LeanRidgelet.ToMathlib.HilbertSchmidtKernel

/-!
# The bounded machine and ridgelet transform of the quadratic-form network

The endpoint of `LeanRidgelet.HA.QuadraticReconstruction` takes a bounded machine and a bounded
ridgelet transform as hypotheses.  This file builds them, under the one analytic hypothesis of the
article's boundedness appendix: that the feature is square integrable for the product of the data
measure with the parameter measure.  With that, condition T1 of the appendix bundles each integral
into a continuous linear map on `L²` whose operator norm is at most the `L²` norm of the feature,
and the quasi-invariant Bochner identities upgrade them to intertwining maps.

The identification of the operators with the pointwise integrals is at the level of `L²` classes,
which is the honest level: a class is an almost-everywhere equivalence class of functions, and both
the representations and the operators are only defined that way.  So the intertwining is proved as
an equality in `L²`, not pointwise, and the pointwise Bochner identities enter through the
almost-everywhere formulas for the two representations.

## Main results

* `LeanRidgelet.quadraticMachine` and `LeanRidgelet.quadraticRidgelet`: the two bounded operators,
  with `LeanRidgelet.norm_quadraticMachine_le` and `LeanRidgelet.norm_quadraticRidgelet_le`.
* `LeanRidgelet.quadraticEquivariantMachine` and `LeanRidgelet.quadraticEquivariantRidgelet`: the
  same operators as intertwining maps between the quadratic parameter representation and the affine
  data representation.
* `LeanRidgelet.quadratic_reconstruction_of_memLp`: the Section 7 endpoint with no boundedness
  hypothesis left — only square integrability of the feature.

## What is assumed

Square integrability of the feature against the product measure.  For a general activation this is
false, so it cannot be proved; the article assumes it in the same place, as condition T2 of its
boundedness appendix.  Everything else here is unconditional.

Two warnings about that hypothesis.  It fails for every activation of polynomial growth, the
rectified linear unit included: already at a fixed parameter the integral of the squared feature
over
the data space diverges.  And where it does hold it forces the reconstruction constant to vanish,
because each of the two operators is then Hilbert--Schmidt, hence so is their composite, and a
scalar
operator on an infinite-dimensional space is compact only for the zero scalar.  So the right-inverse
branch of `LeanRidgelet.quadratic_reconstruction_of_memLp` is unreachable through this hypothesis.
`LeanRidgelet.HA.QuadraticComposite` records the same obstruction for the weaker composite-kernel
condition, and says what the L1 and L2 theories do instead.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal ComplexConjugate

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-! ### Almost-everywhere congruence of the two actions -/

omit [Nontrivial E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- The corrected affine data action respects almost-everywhere equality of representatives, because
the inverse action is quasi measure preserving for the data measure. -/
theorem affineData_quasiUnitaryPullbackAction_congr_ae (g : E ≃ᵃ[ℝ] E) {f₁ f₂ : E → ℂ}
    (hf : f₁ =ᵐ[(volume : Measure E)] f₂) :
    quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g f₁ =ᵐ[(volume : Measure E)]
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g f₂ := by
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity affineDataJacobian
    affineData_measurable (affineData_group_map_eq_withDensity (volume : Measure E)) g
  filter_upwards [hqmp.ae_eq hf] with x hx
  simp only [quasiUnitaryPullbackAction]
  rw [show f₁ (g⁻¹ • x) = f₂ (g⁻¹ • x) from hx]

omit [Nontrivial E] in
/-- The quadratic parameter action respects almost-everywhere equality of representatives. -/
theorem quadraticRelative_quasiRegularAction_congr_ae
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E)
    {γ₁ γ₂ : QuadraticParameter E → ℂ} (hγ : γ₁ =ᵐ[quadraticRelativeMeasure lam] γ₂) :
    quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g γ₁
        =ᵐ[quadraticRelativeMeasure lam]
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g γ₂ := by
  have hqmp := quasiMeasurePreserving_of_map_eq_withDensity
    quadraticRelativeParameterJacobian quadraticParameter_measurable
    (quadraticRelativeParameter_group_map_eq_withDensity lam) g
  filter_upwards [hqmp.ae_eq hγ] with ξ hξ
  simp only [quasiRegularAction]
  rw [show γ₁ (g⁻¹ • ξ) = γ₂ (g⁻¹ • ξ) from hξ]

/-! ### The two kernels -/

/-- The synthesis kernel of the quadratic feature: the conjugate feature, so that the kernel
operator integrates the coefficient against the feature itself. -/
def quadraticSynthesisKernel (σ : ℝ → ℂ) : E × QuadraticParameter E → ℂ :=
  fun p ↦ conj (quadraticVectorFeature σ p.1 p.2)

/-- The analysis kernel of the quadratic feature: the feature with its arguments exchanged, so that
the kernel operator pairs the data against the feature. -/
def quadraticAnalysisKernel (ψ : ℝ → ℂ) : QuadraticParameter E × E → ℂ :=
  fun p ↦ quadraticVectorFeature ψ p.2 p.1

/-! ### The two bounded operators -/

/-- The quadratic machine: the synthesis integral of the quadratic feature, as a bounded operator
from parameter `L²` to data `L²`. -/
def quadraticMachine (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] {σ : ℝ → ℂ}
    (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam))) :
    Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  hilbertSchmidtKernelOperator hσ

/-- The quadratic ridgelet transform: the analysis integral of the quadratic feature, as a bounded
operator from data `L²` to parameter `L²`. -/
def quadraticRidgelet (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] {ψ : ℝ → ℂ}
    (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam) :=
  hilbertSchmidtKernelOperator hψ

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The operator norm of the quadratic machine is at most the `L²` norm of the feature. -/
theorem norm_quadraticMachine_le (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {σ : ℝ → ℂ} (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam))) :
    ‖quadraticMachine lam hσ‖ ≤
      (eLpNorm (quadraticSynthesisKernel (E := E) σ) 2
        ((volume : Measure E).prod (quadraticRelativeMeasure lam))).toReal :=
  norm_hilbertSchmidtKernelOperator_le hσ

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The operator norm of the quadratic ridgelet transform is at most the `L²` norm of the
feature. -/
theorem norm_quadraticRidgelet_le (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {ψ : ℝ → ℂ} (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    ‖quadraticRidgelet lam hψ‖ ≤
      (eLpNorm (quadraticAnalysisKernel (E := E) ψ) 2
        ((quadraticRelativeMeasure lam).prod (volume : Measure E))).toReal :=
  norm_hilbertSchmidtKernelOperator_le hψ

/-! ### Identification with the pointwise Bochner formulas -/

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The machine is the pointwise Bochner synthesis of the quadratic feature, almost everywhere. -/
theorem coeFn_quadraticMachine (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {σ : ℝ → ℂ} (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam)))
    (γ : Lp ℂ 2 (quadraticRelativeMeasure lam)) :
    (quadraticMachine lam hσ γ : E → ℂ) =ᵐ[(volume : Measure E)]
      bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (γ : QuadraticParameter E → ℂ) := by
  refine (coeFn_hilbertSchmidtKernelOperator hσ γ).trans ?_
  filter_upwards with x
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  simp only [quadraticSynthesisKernel, smul_eq_mul, Complex.conj_conj]

omit [Nontrivial E] [BorelSpace (QuadraticSymmetric E)] in
/-- The ridgelet transform is the pointwise Bochner ridgelet of the quadratic feature, almost
everywhere. -/
theorem coeFn_quadraticRidgelet (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {ψ : ℝ → ℂ} (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E)))
    (f : Lp ℂ 2 (volume : Measure E)) :
    (quadraticRidgelet lam hψ f : QuadraticParameter E → ℂ)
        =ᵐ[quadraticRelativeMeasure lam]
      bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ) (f : E → ℂ) := by
  refine (coeFn_hilbertSchmidtKernelOperator hψ f).trans ?_
  filter_upwards with ξ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [quadraticAnalysisKernel, RCLike.inner_apply]

/-! ### The intertwining property -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)] in
/-- With the trivial output representation the corrected pullback action is the corrected regular
action. -/
theorem quasiUnitaryPullbackAction_one_eq (jac : (E ≃ᵃ[ℝ] E) → E → ℝ≥0) (g : E ≃ᵃ[ℝ] E)
    (f : E → ℂ) :
    quasiUnitaryPullbackAction jac (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g f =
      quasiRegularAction (radonNikodymWeight jac) g f := by
  funext x
  simp [quasiUnitaryPullbackAction, quasiRegularAction]

omit [Nontrivial E] in
/-- The almost-everywhere formula for the quadratic parameter representation. -/
theorem quadraticRelativeParameterLpUnitaryRepresentation_apply_ae
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E)
    (γ : Lp ℂ 2 (quadraticRelativeMeasure lam)) :
    ((quadraticRelativeParameterLpUnitaryRepresentation lam g :
        Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam)) γ)
        =ᵐ[quadraticRelativeMeasure lam]
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        fun ξ ↦ (γ : QuadraticParameter E → ℂ) ξ :=
  quasiInvariantLpUnitaryRepresentation_apply_ae quadraticRelativeParameterJacobian
    quadraticParameter_measurable (quadraticRelativeParameter_group_map_eq_withDensity lam)
    quadraticRelativeParameterJacobian_measurable quadraticRelativeParameterJacobian_ne_zero
    quadraticRelativeParameterJacobian_one quadraticRelativeParameterJacobian_cocycle g γ

omit [Nontrivial E] in
/-- The quadratic machine intertwines the quadratic parameter representation with the affine data
representation.  The identity holds in `L²`; the pointwise Bochner identity enters through the
almost-everywhere formulas for the two representations. -/
theorem quadraticMachine_intertwines (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ : ℝ → ℂ}
    (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam)))
    (g : E ≃ᵃ[ℝ] E) (γ : Lp ℂ 2 (quadraticRelativeMeasure lam)) :
    quadraticMachine lam hσ
        ((quadraticRelativeParameterLpUnitaryRepresentation lam g :
          Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam)) γ) =
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        (quadraticMachine lam hσ γ) := by
  refine Lp.ext_iff.2 ?_
  have hπP := quadraticRelativeParameterLpUnitaryRepresentation_apply_ae lam g γ
  have hstep : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
      (fun ξ ↦ ((quadraticRelativeParameterLpUnitaryRepresentation lam g :
        Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam)) γ :
          QuadraticParameter E → ℂ) ξ) =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g
        (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          fun ξ ↦ (γ : QuadraticParameter E → ℂ) ξ) := by
    have hcoef : bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (fun ξ ↦ ((quadraticRelativeParameterLpUnitaryRepresentation lam g :
          Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam)) γ :
            QuadraticParameter E → ℂ) ξ) =
        bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
          (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
            fun ξ ↦ (γ : QuadraticParameter E → ℂ) ξ) := by
      funext x
      refine integral_congr_ae ?_
      filter_upwards [hπP] with ξ hξ
      rw [hξ]
    rw [hcoef]
    funext x
    exact quadraticRelativeBochnerSynthesis_intertwines lam σ g
      (fun ξ ↦ (γ : QuadraticParameter E → ℂ) ξ) x
  refine (coeFn_quadraticMachine lam hσ _).trans ?_
  rw [hstep]
  refine Filter.EventuallyEq.symm ?_
  refine (affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g _).trans ?_
  rw [← quasiUnitaryPullbackAction_one_eq affineDataJacobian g]
  exact affineData_quasiUnitaryPullbackAction_congr_ae g (coeFn_quadraticMachine lam hσ γ)

omit [Nontrivial E] in
/-- The quadratic ridgelet transform intertwines the affine data representation with the quadratic
parameter representation. -/
theorem quadraticRidgelet_intertwines (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {ψ : ℝ → ℂ}
    (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E)))
    (g : E ≃ᵃ[ℝ] E) (f : Lp ℂ 2 (volume : Measure E)) :
    quadraticRidgelet lam hψ
        ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f) =
      (quadraticRelativeParameterLpUnitaryRepresentation lam g :
          Lp ℂ 2 (quadraticRelativeMeasure lam) →L[ℂ] Lp ℂ 2 (quadraticRelativeMeasure lam))
        (quadraticRidgelet lam hψ f) := by
  refine Lp.ext_iff.2 ?_
  have hπD := affineDataLpUnitaryRepresentation_apply_ae_vector (volume : Measure E) g f
  have hstep : bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
      (fun x ↦ ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
        Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f : E → ℂ) x) =
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          fun x ↦ (f : E → ℂ) x) := by
    have hdata : bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
        (fun x ↦ ((affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E) g :
          Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) f : E → ℂ) x) =
        bochnerRidgelet (volume : Measure E) (quadraticVectorFeature ψ)
          (quasiUnitaryPullbackAction affineDataJacobian
            (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) ℂ) g fun x ↦ (f : E → ℂ) x) := by
      funext ξ
      refine integral_congr_ae ?_
      rw [quasiUnitaryPullbackAction_one_eq]
      filter_upwards [hπD] with x hx
      rw [hx]
    rw [hdata]
    funext ξ
    exact quadraticRelativeBochnerRidgelet_intertwines (volume : Measure E) ψ g
      (fun x ↦ (f : E → ℂ) x) ξ
  refine (coeFn_quadraticRidgelet lam hψ _).trans ?_
  rw [hstep]
  refine Filter.EventuallyEq.symm ?_
  refine (quadraticRelativeParameterLpUnitaryRepresentation_apply_ae lam g _).trans ?_
  exact quadraticRelative_quasiRegularAction_congr_ae lam g (coeFn_quadraticRidgelet lam hψ f)

/-! ### The bundled intertwining maps and the endpoint -/

/-- The quadratic machine as an intertwining map, hence as a joint-equivariant machine in the sense
of the reconstruction theorem. -/
def quadraticEquivariantMachine (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {σ : ℝ → ℂ} (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam))) :
    JointEquivariantMachine
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation where
  __ := quadraticMachine lam hσ
  isIntertwining' g :=
    ContinuousLinearMap.ext fun γ ↦ quadraticMachine_intertwines lam hσ g γ

/-- The quadratic ridgelet transform as an intertwining map. -/
def quadraticEquivariantRidgelet (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    {ψ : ℝ → ℂ} (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    JointEquivariantRidgelet
      (affineDataLpUnitaryRepresentation (Y := ℂ) (volume : Measure E)).toContRepresentation
      (quadraticRelativeParameterLpUnitaryRepresentation lam).toContRepresentation where
  __ := quadraticRidgelet lam hψ
  isIntertwining' g :=
    ContinuousLinearMap.ext fun f ↦ quadraticRidgelet_intertwines lam hψ g f

/-- **Section 7 with no boundedness hypothesis left.**  If the quadratic feature is square
integrable for the product of the data measure with the relatively invariant parameter measure, then
the reconstruction operator of the quadratic-form network is a scalar multiple of the identity, and
a nonzero scalar makes the normalized quadratic ridgelet transform a right inverse of the quadratic
machine.  Square integrability of the feature is the analytic input of the article's boundedness
appendix; everything else is proved. -/
theorem quadratic_reconstruction_of_memLp (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] {σ ψ : ℝ → ℂ}
    (hσ : MemLp (quadraticSynthesisKernel (E := E) σ) 2
      ((volume : Measure E).prod (quadraticRelativeMeasure lam)))
    (hψ : MemLp (quadraticAnalysisKernel (E := E) ψ) 2
      ((quadraticRelativeMeasure lam).prod (volume : Measure E))) :
    ∃ c : ℂ, jointReconstructionOperator (quadraticEquivariantMachine lam hσ)
          (quadraticEquivariantRidgelet lam hψ) =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) ∧
      (c ≠ 0 → Function.RightInverse
        (⇑(c⁻¹ • (quadraticEquivariantRidgelet lam hψ).toContinuousLinearMap))
        (⇑(quadraticEquivariantMachine lam hσ))) :=
  quadratic_reconstruction lam (quadraticEquivariantMachine lam hσ)
    (quadraticEquivariantRidgelet lam hψ)

end LeanRidgelet
