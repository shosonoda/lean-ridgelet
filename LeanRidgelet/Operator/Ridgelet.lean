/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.GeneralSolution
public import LeanRidgelet.Operator.Synthesis

/-!
# Concrete coordinate operators and the general solution

This file specializes the abstract simple-tensor, adjoint, projection, and general-solution theory
to the activation, coefficient, and transported parameter Hilbert spaces. In the present
coordinate model `T = I`, so `ridgeletOperator h` represents `J_h`; after transport to the original
parameter space it represents the manuscript operator `R_h = T* J_h`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate InnerProduct

namespace LeanRidgelet

/-- The simple-tensor operator `J_h` in the transported unitary-coordinate model.

The name `ridgeletOperator` is retained for API compatibility; on the original parameter space
the corresponding operator is `R_h = T* J_h`. -/
def ridgeletOperator (m : ℕ) [NeZero m] (s t : ℝ) (h : FiberSpace m s t) :
    TargetSpace m →L[ℂ] ParameterSpace m s t :=
  fiberRidgelet volume h

/-- The concrete ridgelet operator is the abstract `R_h = T* J_h` specialized to the transported
coordinate model `T = I`. -/
theorem ridgeletOperator_eq_unitaryRidgelet (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) :
    ridgeletOperator m s t h =
      unitaryRidgelet volume (parameterCoordinateEquiv m s t) h := by
  ext f
  rfl

/-- In unitary coordinates, `J_h[f]` is the simple tensor `x ↦ f(x)h`. -/
theorem ridgeletOperator_apply_ae (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) (f : TargetSpace m) :
    ridgeletOperator m s t h f =ᵐ[volume] fun x ↦ f x • h :=
  fiberRidgelet_apply_ae volume h f

/-- The concrete form of `T[R_h[f]] = f ⊗ h`, corresponding to equation (34). -/
theorem fourierDilationTransform_ridgeletOperator_apply_ae
    (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) (f : TargetSpace m) :
    (fourierDilationTransform m s t (ridgeletOperator m s t h f) :
        InputSpace m → FiberSpace m s t) =ᵐ[volume]
      fun x ↦ f x • h := by
  simpa [fourierDilationTransform, parameterCoordinateEquiv_apply] using
    ridgeletOperator_apply_ae m s t h f

/-- Coordinate reconstruction `\widetilde L_σ J_h = L_σ[h] I`. -/
theorem networkSynthesis_comp_ridgeletOperator (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberSpace m s t) :
    networkSynthesis m s t σ ∘L ridgeletOperator m s t h =
      activationFiberFunctional m s t σ h •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  fiberSynthesis_comp_fiberRidgelet volume (activationFiberFunctional m s t σ) h

/-- The Riesz representer `h_σ` associated with an activation functional. -/
def activationRieszRepresenter (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) : FiberSpace m s t :=
  rieszRepresenter (activationFiberFunctional m s t σ)

@[simp]
theorem inner_activationRieszRepresenter (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberSpace m s t) :
    inner ℂ (activationRieszRepresenter m s t σ) h =
      activationFiberFunctional m s t σ h :=
  inner_rieszRepresenter (activationFiberFunctional m s t σ) h

/-- The normalization constant `cσ = ‖hσ‖²`. -/
def activationNormalization (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) : ℝ :=
  fiberNormalization (activationFiberFunctional m s t σ)

theorem activationNormalization_eq_norm_sq (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    activationNormalization m s t σ = ‖activationRieszRepresenter m s t σ‖ ^ 2 :=
  rfl

/-- A nonzero activation induces a nonzero coefficient functional. -/
theorem activationFiberFunctional_ne_zero (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    activationFiberFunctional m s t σ ≠ 0 := by
  intro hfunctional
  have hcoefficient : (2 * (Real.pi : ℂ)) ^ (m - 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hrange (h : FiberSpace m s t) :
      inner ℂ (star σ) (fiberDualCoordinate m s t h) = 0 := by
    have hvalue := congrArg (fun L : FiberSpace m s t →L[ℂ] ℂ ↦ L h) hfunctional
    have hproduct : (2 * (Real.pi : ℂ)) ^ (m - 1) *
        inner ℂ (star σ) (fiberDualCoordinate m s t h) = 0 := by
      simpa [activationFiberFunctional] using hvalue
    exact (mul_eq_zero.mp hproduct).resolve_left hcoefficient
  have hinner (y : L2 ℝ volume) : inner ℂ (star σ) y = 0 := by
    refine (denseRange_fiberDualCoordinate m s t).induction_on y ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact hrange
  have hstar : star σ = 0 := inner_self_eq_zero.mp (hinner (star σ))
  apply hσ
  have := congrArg star hstar
  have hstarZero : star (0 : L2 ℝ volume) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_star_L2]
    simp
  simpa only [star_star, hstarZero] using this

theorem activationNormalization_pos (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    0 < activationNormalization m s t σ :=
  fiberNormalization_pos (activationFiberFunctional_ne_zero m s t hσ)

/-- The adjoint synthesis operator is represented in coordinates by `J_{h_σ}`. -/
theorem adjoint_networkSynthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    (networkSynthesis m s t σ)† =
      ridgeletOperator m s t (activationRieszRepresenter m s t σ) :=
  adjoint_fiberSynthesis volume (activationFiberFunctional m s t σ)

/-- Synthesis composed with its adjoint is multiplication by `cσ`. -/
theorem networkSynthesis_comp_adjoint (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    networkSynthesis m s t σ ∘L (networkSynthesis m s t σ)† =
      (activationNormalization m s t σ : ℂ) •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  fiberSynthesis_comp_adjoint volume (activationFiberFunctional m s t σ)

/-- The normalized Hilbert adjoint `c_σ⁻¹ S*`, giving the Moore--Penrose right inverse. -/
def normalizedNetworkRightInverse (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) : TargetSpace m →L[ℂ] ParameterSpace m s t :=
  normalizedRightInverse volume (activationFiberFunctional m s t σ)

theorem normalizedNetworkRightInverse_rightInverse (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    Function.RightInverse (normalizedNetworkRightInverse m s t σ)
      (networkSynthesis m s t σ) :=
  normalizedRightInverse_rightInverse volume
    (activationFiberFunctional_ne_zero m s t hσ)

theorem surjective_networkSynthesis (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    Function.Surjective (networkSynthesis m s t σ) :=
  (normalizedNetworkRightInverse_rightInverse m s t hσ).surjective

/-- The canonical orthogonal parameter projection `P = S^\dagger S`.

The name `networkVisibleProjection` is retained for API compatibility. -/
def networkVisibleProjection (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) : ParameterSpace m s t →L[ℂ] ParameterSpace m s t :=
  visibleProjection volume (activationFiberFunctional m s t σ)

theorem isIdempotentElem_networkVisibleProjection (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    IsIdempotentElem (networkVisibleProjection m s t σ) :=
  isIdempotentElem_visibleProjection volume
    (activationFiberFunctional_ne_zero m s t hσ)

theorem isSelfAdjoint_networkVisibleProjection (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    IsSelfAdjoint (networkVisibleProjection m s t σ) :=
  isSelfAdjoint_visibleProjection volume

theorem ker_networkVisibleProjection (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    (networkVisibleProjection m s t σ).ker = (networkSynthesis m s t σ).ker :=
  ker_visibleProjection volume (activationFiberFunctional_ne_zero m s t hσ)

theorem range_networkVisibleProjection (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    (networkVisibleProjection m s t σ).range = (networkSynthesis m s t σ).kerᗮ :=
  range_visibleProjection volume (activationFiberFunctional_ne_zero m s t hσ)

/-- Pointwise characterization of the null space in unitary coordinates. -/
theorem mem_ker_networkSynthesis_iff (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    γ ∈ LinearMap.ker (networkSynthesis m s t σ).toLinearMap ↔
      ∀ᵐ x ∂volume, activationFiberFunctional m s t σ (γ x) = 0 :=
  mem_ker_fiberSynthesis_iff volume (activationFiberFunctional m s t σ) γ

/-- The null-space characterization with the manuscript unitary coordinate transform explicit. -/
theorem mem_ker_networkSynthesis_iff_fourierDilation
    (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    γ ∈ LinearMap.ker (networkSynthesis m s t σ).toLinearMap ↔
      ∀ᵐ x ∂volume,
        activationFiberFunctional m s t σ
          (fourierDilationTransform m s t γ x) = 0 := by
  rw [networkSynthesis_eq_unitarySynthesis]
  exact mem_ker_unitarySynthesis_iff volume
    (fourierDilationTransform m s t) (activationFiberFunctional m s t σ) γ

/-- Every solution is the normalized-adjoint solution plus a null component. -/
theorem networkSolution_iff_kernel_translate (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) (f : TargetSpace m)
    (γ : ParameterSpace m s t) :
    networkSynthesis m s t σ γ = f ↔
      γ - normalizedNetworkRightInverse m s t σ f ∈
        LinearMap.ker (networkSynthesis m s t σ).toLinearMap :=
  solution_iff_kernel_translate volume
    (activationFiberFunctional_ne_zero m s t hσ) f γ

/-- The normalized-adjoint solution is the unique minimum-norm parameter solution. -/
theorem normalizedNetworkRightInverse_unique_minimal (m : ℕ) [NeZero m] (s t : ℝ)
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) (f : TargetSpace m) :
    ∀ γ : ParameterSpace m s t,
      networkSynthesis m s t σ γ = f →
      ‖normalizedNetworkRightInverse m s t σ f‖ ≤ ‖γ‖ ∧
        (‖normalizedNetworkRightInverse m s t σ f‖ = ‖γ‖ →
          normalizedNetworkRightInverse m s t σ f = γ) :=
  normalizedRightInverse_unique_minimal volume
    (activationFiberFunctional_ne_zero m s t hσ) f

/-- The coefficient-vector series expansion of a parameter distribution. -/
theorem hasSum_ridgeletOperator_fiberCoefficient {ι : Type*}
    (m : ℕ) [NeZero m] (s t : ℝ) (b : HilbertBasis ι ℂ (TargetSpace m))
    (γ : ParameterSpace m s t) :
    HasSum
      (fun i ↦ ridgeletOperator m s t (fiberCoefficient volume (b i) γ) (b i)) γ :=
  hasSum_fiberRidgelet_coefficients volume b γ

/-- Every coefficient vector of a null parameter lies in the activation functional's kernel. -/
theorem activationFiberFunctional_fiberCoefficient_eq_zero_of_mem_ker {ι : Type*}
    (m : ℕ) [NeZero m] (s t : ℝ) (σ : ActivationSpace s t)
    (b : HilbertBasis ι ℂ (TargetSpace m)) (γ : ParameterSpace m s t)
    (hγ : γ ∈ LinearMap.ker (networkSynthesis m s t σ).toLinearMap) (i : ι) :
    activationFiberFunctional m s t σ (fiberCoefficient volume (b i) γ) = 0 :=
  apply_fiberCoefficient_eq_zero_of_mem_ker volume
    (activationFiberFunctional m s t σ) b γ hγ i

end LeanRidgelet
