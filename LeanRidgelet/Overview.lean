/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.Ridgelet

/-!
# Overview of the main L2 results

This file lists the numbered results of the L2 manuscript in publication order. Results already
available in the coordinate-based formalization are exposed through thin wrapper theorems. The
remaining results are stated as ordinary propositions with named `sorry` proofs, so that Lean and
the repository assumption audit can track the exact formalization boundary.

The wrappers for Theorem 1 and Lemma 1 expose their currently formalized Fourier--dilation
coordinate content. Agreement with the original classical integrals remains future work.
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

/-- L2 Theorem 1: coordinate synthesis is fiberwise evaluation and satisfies the paper bound. -/
theorem l2_theorem_one_bounded_synthesis (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (γ : ParameterSpace m s t) :
    (networkSynthesis m s t σ γ =ᵐ[volume]
      fun x ↦ activationFiberFunctional m s t σ (γ x)) ∧
    ‖networkSynthesis m s t σ γ‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ * ‖γ‖ :=
  ⟨networkSynthesis_apply_ae m s t σ γ, norm_networkSynthesis_apply_le m s t σ γ⟩

/-- L2 Lemma 1: the formalized fiber representation of a ridgelet is a simple tensor. -/
theorem l2_lemma_one_ridgelet_fiber_representation (m : ℕ) [NeZero m] (s t : ℝ)
    (q : FiberSpace m s t) (f : TargetSpace m) :
    ridgeletOperator m s t q f =ᵐ[volume] fun x ↦ f x • q :=
  ridgeletOperator_apply_ae m s t q f

/-- L2 Theorem 2: synthesis after a ridgelet is scalar reconstruction. -/
theorem l2_theorem_two_reconstruction (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) (q : FiberSpace m s t) :
    networkSynthesis m s t σ ∘L ridgeletOperator m s t q =
      activationFiberFunctional m s t σ q •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  networkSynthesis_comp_ridgeletOperator m s t σ q

/-- L2 Lemma 2: the adjoint is the Riesz ridgelet and satisfies the adjoint identity. -/
theorem l2_lemma_two_adjoint (m : ℕ) [NeZero m] (s t : ℝ)
    (σ : ActivationSpace s t) :
    (networkSynthesis m s t σ)† =
      ridgeletOperator m s t (activationRieszRepresenter m s t σ) ∧
    networkSynthesis m s t σ ∘L (networkSynthesis m s t σ)† =
      (activationNormalization m s t σ : ℂ) •
        ContinuousLinearMap.id ℂ (TargetSpace m) :=
  ⟨adjoint_networkSynthesis m s t σ, networkSynthesis_comp_adjoint m s t σ⟩

/--
L2 Theorem 3: fiberwise nullity, the unique basis expansion, the complete solution set, and the
minimum-norm solution, collected from the corresponding coordinate theorems.
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
    (∀ q : ι → FiberSpace m s t,
      HasSum (fun i ↦ ridgeletOperator m s t (q i) (b i)) γ →
      ∀ i, q i = fiberCoefficient volume (b i) γ) ∧
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
  · intro q hq i
    exact eq_fiberCoefficient_of_hasSum_fiberRidgelet volume b q γ hq i

/--
L2 Theorem 4: countably many null fibers admit dual readout activations, giving stable encoding and
perturbative readout without changing the null component.
-/
theorem l2_theorem_four_encoding_and_perturbative_readout
    (m : ℕ) [NeZero m] (s t : ℝ) {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    ∃ (q : ℕ → FiberSpace m s t) (τ : ℕ → ActivationSpace s t),
      Orthonormal ℂ q ∧
      (∀ i, activationFiberFunctional m s t σ (q i) = 0) ∧
      (∀ i j, activationFiberFunctional m s t (τ i) (q j) = if i = j then 1 else 0) ∧
      ∀ (f₀ : TargetSpace m) (f : ℕ → TargetSpace m),
        Summable (fun i ↦ ‖f i‖ ^ 2) →
        ∃ γenc : ParameterSpace m s t,
          HasSum (fun i ↦ ridgeletOperator m s t (q i) (f i))
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
L2 Theorem 5, in its Hilbert-valued sampling form: a centered normalized feature distribution has
an `N`-term realization with `N⁻¹ᐟ²` output error.
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
L2 Corollary 1, at the present coordinate level: a nonzero null ridgelet element exists and is a
candidate for the finite-width discretization theorem.
-/
theorem l2_corollary_one_discretizable_ridgelet_null_elements
    (m : ℕ) [NeZero m] (s t : ℝ) {σ : ActivationSpace s t} (hσ : σ ≠ 0) :
    ∃ (f : TargetSpace m) (q : FiberSpace m s t),
      f ≠ 0 ∧ q ≠ 0 ∧
      activationFiberFunctional m s t σ q = 0 ∧
      ridgeletOperator m s t q f ∈
        LinearMap.ker (networkSynthesis m s t σ).toLinearMap := by
  sorry

/-- L2 Proposition 2: parity and ReLU affine cancellation give exact finite null relations. -/
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
