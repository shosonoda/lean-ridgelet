/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.Ridgelet

/-!
# Compatibility wrappers for the previous L2 result order

This file retains wrappers named after the 2026-07-15 result order while the general-first
2026-07-18 manuscript structure is migrated. Results already available in the coordinate-based
formalization are exposed through thin wrapper theorems. The remaining results are stated as
ordinary propositions with named `sorry` proofs, so that Lean and the repository assumption audit
can track the exact formalization boundary.

The wrappers for Theorem 1 and Lemma 1 expose their currently formalized unitary-coordinate
content. They are not the final numbering of `ghost20260718.pdf`; the staged replacement is
recorded in `00note/plan.md`. Agreement with the original classical integrals remains future work.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal InnerProduct

namespace LeanRidgelet

/-- L2 Proposition 1: the activation coordinate map is an isometric isomorphism onto `L²(ℝ)`. -/
theorem l2_proposition_one_activation_hilbert_structure (s t : ℝ) :
    Nonempty (ActivationSpace s t ≃ₗᵢ[ℂ] L2 ℝ volume) :=
  ⟨activationCoordinateEquiv s t⟩

/-- Legacy L2 Theorem 1 wrapper: coordinate synthesis is pointwise evaluation and satisfies the
concrete bound. -/
theorem l2_theorem_one_bounded_synthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    (networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ (γ x)) ∧
    ‖networkSynthesis m s t σ γ‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ * ‖γ‖ :=
  ⟨networkSynthesis_apply_ae m s t σ γ, norm_networkSynthesis_apply_le m s t σ γ⟩

/-- Legacy L2 Lemma 1 wrapper: the formalized coordinate representation is a simple tensor. -/
theorem l2_lemma_one_ridgelet_fiber_representation (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberSpace m s t) (f : TargetSpace m) :
    ridgeletOperator m s t h f =ᵐ[volume] fun x ↦ f x • h :=
  ridgeletOperator_apply_ae m s t h f

/-- Legacy L2 Theorem 2 wrapper: synthesis after a prescribed coefficient is scalar
reconstruction. -/
theorem l2_theorem_two_reconstruction (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (h : FiberSpace m s t) :
    networkSynthesis m s t σ ∘L ridgeletOperator m s t h =
      activationFiberFunctional m s t σ h •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  networkSynthesis_comp_ridgeletOperator m s t σ h

/-- Legacy L2 Lemma 2 wrapper: the adjoint uses the Riesz representer and satisfies the scaled
coisometry identity. -/
theorem l2_lemma_two_adjoint (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    (networkSynthesis m s t σ)† =
      ridgeletOperator m s t (activationRieszRepresenter m s t σ) ∧
    networkSynthesis m s t σ ∘L (networkSynthesis m s t σ)† =
      (activationNormalization m s t σ : ℂ) •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  ⟨adjoint_networkSynthesis m s t σ, networkSynthesis_comp_adjoint m s t σ⟩

/--
Legacy L2 Theorem 3 wrapper: pointwise nullity, the unique basis expansion, the complete
solution set, and the minimum-norm solution, collected from the coordinate theorems.
-/
theorem l2_theorem_three_null_space_and_general_solution {ι : Type*}
    (m : ℕ) [NeZero m] (s t : ℝ) (b : HilbertBasis ι ℂ (TargetSpace m))
    {σ : ActivationSpace s t} (hσ : σ ≠ 0) (f : TargetSpace m)
    (γ : ParameterSpace m s t) :
    (γ ∈ LinearMap.ker (networkSynthesis m s t σ).toLinearMap ↔
      ∀ᵐ x ∂volume, activationFiberFunctional m s t σ (γ x) = 0) ∧
    HasSum
      (fun i ↦ ridgeletOperator m s t (fiberCoefficient volume (b i) γ) (b i)) γ ∧
    (γ ∈ LinearMap.ker (networkSynthesis m s t σ).toLinearMap →
      ∀ i, activationFiberFunctional m s t σ (fiberCoefficient volume (b i) γ) = 0) ∧
    (∀ h : ι → FiberSpace m s t,
      HasSum (fun i ↦ ridgeletOperator m s t (h i) (b i)) γ →
      ∀ i, h i = fiberCoefficient volume (b i) γ) ∧
    (networkSynthesis m s t σ γ = f ↔
      γ - normalizedNetworkRightInverse m s t σ f ∈
        LinearMap.ker (networkSynthesis m s t σ).toLinearMap) ∧
    ∀ δ : ParameterSpace m s t,
      networkSynthesis m s t σ δ = f →
      ‖normalizedNetworkRightInverse m s t σ f‖ ≤ ‖δ‖ ∧
        (‖normalizedNetworkRightInverse m s t σ f‖ = ‖δ‖ →
          normalizedNetworkRightInverse m s t σ f = δ) := by
  refine ⟨mem_ker_networkSynthesis_iff m s t σ γ,
    hasSum_ridgeletOperator_fiberCoefficient m s t b γ, ?_, ?_,
    networkSolution_iff_kernel_translate m s t hσ f γ,
    normalizedNetworkRightInverse_unique_minimal m s t hσ f⟩
  · intro hγ i
    exact activationFiberFunctional_fiberCoefficient_eq_zero_of_mem_ker
      m s t σ b γ hγ i
  · intro h hq i
    exact eq_fiberCoefficient_of_hasSum_fiberRidgelet volume b h γ hq i

/--
Legacy L2 Theorem 4: countably many null coefficient vectors admit dual readout activations,
giving stable encoding and perturbative readout without changing the null component.
-/
theorem l2_theorem_four_encoding_and_perturbative_readout
    (m : ℕ) [NeZero m] (s t : ℝ) {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    ∃ (h : ℕ → FiberSpace m s t) (τ : ℕ → ActivationSpace s t),
      Orthonormal ℂ h ∧
      (∀ i, activationFiberFunctional m s t σ (h i) = 0) ∧
      (∀ i j, activationFiberFunctional m s t (τ i) (h j) = if i = j then 1 else 0) ∧
      ∀ (f₀ : TargetSpace m) (f : ℕ → TargetSpace m),
        Summable (fun i ↦ ‖f i‖ ^ 2) →
        ∃ γenc : ParameterSpace m s t,
          HasSum (fun i ↦ ridgeletOperator m s t (h i) (f i))
            (γenc - normalizedNetworkRightInverse m s t σ f₀) ∧
          networkSynthesis m s t σ γenc = f₀ ∧
          ∀ i,
            networkSynthesis m s t (τ i) γenc = f i ∧
            let δγ := normalizedNetworkRightInverse m s t σ (f i - f₀)
            networkSynthesis m s t σ (γenc + δγ) = f i ∧
            (ContinuousLinearMap.id ℂ (ParameterSpace m s t) -
                networkVisibleProjection m s t σ) (γenc + δγ) =
              (ContinuousLinearMap.id ℂ (ParameterSpace m s t) -
                networkVisibleProjection m s t σ) γenc := by
  sorry

/--
Legacy L2 Theorem 5, in its Hilbert-valued sampling form: a centered normalized feature
distribution has an `N`-term realization with `N⁻¹ᐟ²` output error.
-/
theorem l2_theorem_five_normalized_finite_width_approximation
    {Θ H : Type*} [MeasurableSpace Θ] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (Φ : Θ → H) (u : Θ → ℂ)
    (hu : ∀ᵐ θ ∂μ, ‖u θ‖ = 1)
    (henergy : Integrable (fun θ ↦ ‖Φ θ‖ ^ 2) μ)
    (hnull : ∫ θ, u θ • Φ θ ∂μ = 0) :
    ∀ N : ℕ, 0 < N →
      ∃ θ : Fin N → Θ,
        ‖(N : ℂ)⁻¹ • ∑ j, u (θ j) • Φ (θ j)‖ ≤
          Real.sqrt ((∫ x, ‖Φ x‖ ^ 2 ∂μ) / N) := by
  sorry

/--
Legacy L2 Corollary 1, at the present coordinate level: a nonzero null ridgelet element exists
and is a candidate for the finite-width discretization theorem.
-/
theorem l2_corollary_one_discretizable_ridgelet_null_elements
    (m : ℕ) [NeZero m] (s t : ℝ) {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    ∃ (f : TargetSpace m) (h : FiberSpace m s t),
      f ≠ 0 ∧ h ≠ 0 ∧
      activationFiberFunctional m s t σ h = 0 ∧
      ridgeletOperator m s t h f ∈
        LinearMap.ker (networkSynthesis m s t σ).toLinearMap := by
  sorry

/-- Legacy L2 Proposition 2: parity and ReLU affine cancellation give exact finite null
relations. -/
theorem l2_proposition_two_exact_finite_null_relations (m : ℕ) :
    (∀ σ : ℝ → ℂ,
      (∀ z, σ (-z) = -σ z) →
      ∀ (a x : InputSpace m) (b : ℝ),
        σ (inner ℝ a x - b) + σ (inner ℝ (-a) x - (-b)) = 0) ∧
    (∀ σ : ℝ → ℂ,
      (∀ z, σ (-z) = σ z) →
      ∀ (a x : InputSpace m) (b : ℝ),
        σ (inner ℝ a x - b) - σ (inner ℝ (-a) x - (-b)) = 0) ∧
    ∀ (J : ℕ) (c : Fin J → ℝ) (a : Fin J → InputSpace m) (b : Fin J → ℝ),
      (∑ j, c j • a j) = 0 → (∑ j, c j * b j) = 0 →
      ∀ x : InputSpace m,
        ∑ j, c j *
          (max (inner ℝ (a j) x - b j) 0 -
            max (inner ℝ (-a j) x - (-b j)) 0) = 0 := by
  sorry

end LeanRidgelet
