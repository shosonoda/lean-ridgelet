/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Deep

/-!
# Finite-depth fully-connected features

This file formalizes the algebraic part of Section 5 of arXiv:2405.13682.  A layer has a linear
weight `A`, bias `b`, arbitrary activation `σ`, and linear readout `C`.  The affine input change is
absorbed entirely by the first layer, while an invertible linear output change is absorbed by the
last readout.  The endpoint identities propagate through an arbitrary heterogeneous finite
cascade.

The result is independent of measure theory and of boundedness.  For the scalar Euclidean
operators used later, boundedness is supplied by `HA.L2Bridge` from the existing L2 theory.

## Deviations from the article

Matrices are represented by linear maps and the activation is an arbitrary function.  The
article restricts the final readout to a sphere; this algebraic covariance calculation does not
use that normalization.
-/

@[expose] public section

namespace LeanRidgelet

/-- Parameters `(A,b,C)` of one heterogeneous fully-connected layer. -/
abbrev FullyConnectedParameter (X P Q Y : Type*) [AddCommGroup X] [Module ℝ X]
    [AddCommGroup P] [Module ℝ P] [AddCommGroup Q] [Module ℝ Q]
    [AddCommGroup Y] [Module ℝ Y] :=
  (X →ₗ[ℝ] P) × P × (Q →ₗ[ℝ] Y)

/-- A fully-connected feature `C[σ(Ax-b)]`. -/
def fullyConnectedFeature {X P Q Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup P] [Module ℝ P] [AddCommGroup Q] [Module ℝ Q]
    [AddCommGroup Y] [Module ℝ Y] (σ : P → Q)
    (x : X) (ξ : FullyConnectedParameter X P Q Y) : Y :=
  ξ.2.2 (σ (ξ.1 x - ξ.2.1))

/-- Change of first-layer parameters contragredient to `x ↦ L x + t`. -/
def fullyConnectedInputParameterTransform {X P Q Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup P] [Module ℝ P]
    [AddCommGroup Q] [Module ℝ Q] [AddCommGroup Y] [Module ℝ Y]
    (L : X ≃ₗ[ℝ] X) (t : X) (ξ : FullyConnectedParameter X P Q Y) :
    FullyConnectedParameter X P Q Y :=
  (ξ.1.comp L.symm.toLinearMap, ξ.2.1 + ξ.1 (L.symm t), ξ.2.2)

/-- The transformed first layer has exactly the same value on the transformed input. -/
theorem fullyConnectedFeature_input_invariant {X P Q Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup P] [Module ℝ P]
    [AddCommGroup Q] [Module ℝ Q] [AddCommGroup Y] [Module ℝ Y]
    (σ : P → Q) (L : X ≃ₗ[ℝ] X) (t x : X)
    (ξ : FullyConnectedParameter X P Q Y) :
    fullyConnectedFeature σ (L x + t) (fullyConnectedInputParameterTransform L t ξ) =
      fullyConnectedFeature σ x ξ := by
  simp [fullyConnectedFeature, fullyConnectedInputParameterTransform]

/-- Change of the last-layer readout by an invertible linear output map. -/
def fullyConnectedOutputParameterTransform {X P Q Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup P] [Module ℝ P]
    [AddCommGroup Q] [Module ℝ Q] [AddCommGroup Y] [Module ℝ Y]
    (R : Y ≃ₗ[ℝ] Y) (ξ : FullyConnectedParameter X P Q Y) :
    FullyConnectedParameter X P Q Y :=
  (ξ.1, ξ.2.1, R.toLinearMap.comp ξ.2.2)

/-- The transformed last readout applies the output representation to the layer value. -/
theorem fullyConnectedFeature_output_equivariant {X P Q Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup P] [Module ℝ P]
    [AddCommGroup Q] [Module ℝ Q] [AddCommGroup Y] [Module ℝ Y]
    (σ : P → Q) (R : Y ≃ₗ[ℝ] Y) (x : X)
    (ξ : FullyConnectedParameter X P Q Y) :
    fullyConnectedFeature σ x (fullyConnectedOutputParameterTransform R ξ) =
      R (fullyConnectedFeature σ x ξ) := rfl

namespace DeepParameters

/-- Apply a map only to the first entry of a nonempty heterogeneous tuple. -/
def mapFirst {Ξ : ℕ → Type*} (F : Ξ 0 → Ξ 0) :
    {n : ℕ} → DeepParameters Ξ (n + 1) → DeepParameters Ξ (n + 1)
  | 0, .snoc .nil ξ => .snoc .nil (F ξ)
  | _ + 1, .snoc ξ ξn => .snoc (mapFirst F ξ) ξn

/-- Apply a map only to the last entry of a nonempty heterogeneous tuple. -/
def mapLast {Ξ : ℕ → Type*} {n : ℕ} (F : Ξ n → Ξ n) :
    DeepParameters Ξ (n + 1) → DeepParameters Ξ (n + 1)
  | .snoc ξ ξn => .snoc ξ (F ξn)

end DeepParameters

/-- A change absorbed by the first layer does not affect the value of the full cascade. -/
theorem deepFeature_mapFirst {X Ξ : ℕ → Type*}
    (φ : ∀ i, X i → Ξ i → X (i + 1)) (F : Ξ 0 → Ξ 0) (S : X 0 → X 0)
    (hfirst : ∀ x ξ, φ 0 (S x) (F ξ) = φ 0 x ξ) :
    ∀ (n : ℕ) (x : X 0) (ξ : DeepParameters Ξ (n + 1)),
      deepFeature φ (n + 1) (S x) (DeepParameters.mapFirst F ξ) =
        deepFeature φ (n + 1) x ξ := by
  intro n
  induction n with
  | zero =>
      intro x ξ
      cases ξ with
      | snoc ξ ξ0 =>
          cases ξ
          exact hfirst x ξ0
  | succ n ih =>
      intro x ξ
      cases ξ with
      | snoc ξ ξn =>
          simp only [DeepParameters.mapFirst, deepFeature_succ]
          rw [ih x ξ]

/-- A change absorbed by the last layer acts on the output of the full cascade. -/
theorem deepFeature_mapLast {X Ξ : ℕ → Type*}
    (φ : ∀ i, X i → Ξ i → X (i + 1)) (n : ℕ) (F : Ξ n → Ξ n)
    (R : X (n + 1) → X (n + 1))
    (hlast : ∀ x ξ, φ n x (F ξ) = R (φ n x ξ))
    (x : X 0) (ξ : DeepParameters Ξ (n + 1)) :
    deepFeature φ (n + 1) x (DeepParameters.mapLast F ξ) =
      R (deepFeature φ (n + 1) x ξ) := by
  cases ξ with
  | snoc ξ ξn =>
      exact hlast (deepFeature φ n x ξ) ξn

/-- The depth-`n+1` fully-connected feature associated with heterogeneous activations. -/
def deepFullyConnectedFeature {X P Q : ℕ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℝ (P i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]
    (σ : ∀ i, P i → Q i) (n : ℕ) :
    X 0 → DeepParameters (fun i ↦ FullyConnectedParameter (X i) (P i) (Q i) (X (i + 1))) n →
      X n :=
  deepFeature (fun i ↦ fullyConnectedFeature (σ i)) n

/-- Section 5 joint-equivariance calculation: the affine input transformation is absorbed by the
first parameters and the output transformation by the final readout, for every finite depth and
every choice of activation functions. -/
theorem deepFullyConnectedFeature_endpoint_equivariant
    {X P Q : ℕ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℝ (P i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]
    (σ : ∀ i, P i → Q i) (n : ℕ) (L : X 0 ≃ₗ[ℝ] X 0) (t : X 0)
    (R : X (n + 1) ≃ₗ[ℝ] X (n + 1)) (x : X 0)
    (ξ : DeepParameters
      (fun i ↦ FullyConnectedParameter (X i) (P i) (Q i) (X (i + 1))) (n + 1)) :
    deepFullyConnectedFeature σ (n + 1) (L x + t)
        (DeepParameters.mapLast (fullyConnectedOutputParameterTransform R)
          (DeepParameters.mapFirst (fullyConnectedInputParameterTransform L t) ξ)) =
      R (deepFullyConnectedFeature σ (n + 1) x ξ) := by
  rw [deepFullyConnectedFeature, deepFeature_mapLast]
  · congr 1
    exact deepFeature_mapFirst
      (φ := fun i ↦ fullyConnectedFeature (σ i))
      (F := fullyConnectedInputParameterTransform L t)
      (S := fun y ↦ L y + t)
      (fullyConnectedFeature_input_invariant (σ 0) L t) n x ξ
  · exact fullyConnectedFeature_output_equivariant (σ n) R

end LeanRidgelet
