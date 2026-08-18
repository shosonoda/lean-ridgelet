/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.JointEquivariance
public import LeanRidgelet.HA.Reconstruction

/-!
# Finite-depth joint-equivariant machines

This file formalizes Lemma 3.5 and Corollary 4.1 of arXiv:2405.13682.

The binary cascade from the algebraic layer is iterated over a genuinely heterogeneous finite
family: data and parameter types may change at every layer. Once the resulting synthesis and
ridgelet integrals have been realized as bounded intertwining maps, the Schur reconstruction
theorem applies verbatim.

## Deviations from the article

Layer indices start at zero in Lean. The reconstruction statement is made at bounded-operator
level; the separate Bochner bridge records measurability, integral formulas, and change of
variables.
-/

@[expose] public section

noncomputable section

open scoped ContRepresentation

namespace LeanRidgelet

variable {G : Type*}

/-- A finite heterogeneous parameter tuple, built by appending the parameter of each layer. -/
inductive DeepParameters (Ξ : ℕ → Type*) : ℕ → Type _
  /-- The empty parameter tuple. -/
  | nil : DeepParameters Ξ 0
  /-- Append the parameter of layer `n` to a tuple for the preceding layers. -/
  | snoc {n : ℕ} : DeepParameters Ξ n → Ξ n → DeepParameters Ξ (n + 1)

namespace DeepParameters

/-- Componentwise scalar multiplication on a heterogeneous parameter tuple. -/
protected def smul {Ξ : ℕ → Type*} [∀ i, SMul G (Ξ i)] (g : G) :
    {n : ℕ} → DeepParameters Ξ n → DeepParameters Ξ n
  | 0, .nil => .nil
  | _ + 1, .snoc ξ ξn => .snoc (DeepParameters.smul g ξ) (g • ξn)

instance {Ξ : ℕ → Type*} [∀ i, SMul G (Ξ i)] {n : ℕ} :
    SMul G (DeepParameters Ξ n) :=
  ⟨fun g ξ => DeepParameters.smul (Ξ := Ξ) g ξ⟩

@[simp]
theorem smul_nil {Ξ : ℕ → Type*} [∀ i, SMul G (Ξ i)] (g : G) :
    g • (DeepParameters.nil : DeepParameters Ξ 0) = DeepParameters.nil := rfl

@[simp]
theorem smul_snoc {Ξ : ℕ → Type*} [∀ i, SMul G (Ξ i)]
    (g : G) {n : ℕ} (ξ : DeepParameters Ξ n) (ξn : Ξ n) :
    g • DeepParameters.snoc ξ ξn = DeepParameters.snoc (g • ξ) (g • ξn) := rfl

instance {Ξ : ℕ → Type*} [Monoid G] [∀ i, MulAction G (Ξ i)] {n : ℕ} :
    MulAction G (DeepParameters Ξ n) where
  one_smul ξ := by
    induction ξ with
    | nil => rfl
    | snoc ξ ξn ih => simp [ih]
  mul_smul g h ξ := by
    induction ξ with
    | nil => rfl
    | snoc ξ ξn ih => simp [ih, mul_smul]

end DeepParameters

/-- Composition of a finite heterogeneous family of parametrized layers. -/
def deepFeature {X Ξ : ℕ → Type*}
    (φ : ∀ i, X i → Ξ i → X (i + 1)) :
    (n : ℕ) → X 0 → DeepParameters Ξ n → X n
  | 0, x, .nil => x
  | n + 1, x, .snoc ξ ξn => φ n (deepFeature φ n x ξ) ξn

@[simp]
theorem deepFeature_zero {X Ξ : ℕ → Type*}
    (φ : ∀ i, X i → Ξ i → X (i + 1)) (x : X 0) :
    deepFeature φ 0 x .nil = x := rfl

@[simp]
theorem deepFeature_succ {X Ξ : ℕ → Type*}
    (φ : ∀ i, X i → Ξ i → X (i + 1)) (n : ℕ) (x : X 0)
    (ξ : DeepParameters Ξ n) (ξn : Ξ n) :
    deepFeature φ (n + 1) x (.snoc ξ ξn) = φ n (deepFeature φ n x ξ) ξn := rfl

/-- Lemma 3.5 in heterogeneous finite-depth form. -/
theorem isJointEquivariant_deepFeature {X Ξ : ℕ → Type*}
    [Monoid G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Ξ i)]
    (φ : ∀ i, X i → Ξ i → X (i + 1))
    (hφ : ∀ i, IsJointEquivariant (G := G) (φ i)) (n : ℕ) :
    IsJointEquivariant (G := G) (deepFeature φ n) := by
  intro g x ξ
  induction ξ with
  | nil => rfl
  | snoc ξ ξn ih =>
      rw [DeepParameters.smul_snoc, deepFeature_succ, deepFeature_succ, ih]
      exact hφ _ g (deepFeature φ _ x ξ) ξn

variable {H K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Corollary 4.1 at bounded-operator level. The finite-depth construction contributes joint
equivariance through `isJointEquivariant_deepFeature`; boundedness and the integral formulas are
supplied independently by the Bochner bridge or by the L2 operator theory. -/
theorem deepRidgelet_reconstruction_formula (πData : UnitaryRepresentation G H)
    (hirr : πData.IsTopologicallyIrreducible) (πParameter : ContRepresentation ℂ G K)
    (M : JointEquivariantMachine πParameter πData.toContRepresentation)
    (R : JointEquivariantRidgelet πData.toContRepresentation πParameter) :
    ∃ c : ℂ, jointReconstructionOperator M R = c • ContinuousLinearMap.id ℂ H :=
  ha_reconstruction_formula πData hirr πParameter M R

omit [CompleteSpace H] in
/-- A nonzero reconstruction scalar makes the normalized deep ridgelet a right inverse. -/
theorem deepRidgelet_normalized_rightInverse
    {πData : ContRepresentation ℂ G H} {πParameter : ContRepresentation ℂ G K}
    (M : JointEquivariantMachine πParameter πData)
    (R : JointEquivariantRidgelet πData πParameter) {c : ℂ}
    (hrec : jointReconstructionOperator M R = c • ContinuousLinearMap.id ℂ H) (hc : c ≠ 0) :
    Function.RightInverse (⇑(c⁻¹ • R.toContinuousLinearMap)) (⇑M) :=
  ha_normalizedRidgelet_rightInverse M R hrec hc

end LeanRidgelet
