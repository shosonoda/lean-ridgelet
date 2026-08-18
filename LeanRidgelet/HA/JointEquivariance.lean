/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Joint-equivariant feature maps

The algebraic core of joint equivariance from Sections 3.1--3.2 of

> S. Sonoda, Y. Hashimoto, I. Ishikawa and M. Ikeda, *Deep Ridgelet Transform and Unified
> Universality Theorem for Deep and Shallow Joint-Group-Equivariant Machines*
> (arXiv:2405.13682).

This file deliberately contains no integration or topology. It proves that ordinary equivariance
is a special case, constructs an equivariant orbit feature from an arbitrary seed, and proves that
joint-equivariant layers are closed under cascade composition.

## Deviations from the article

None. The article's depth-`n` statement is represented first by the binary cascade theorem below;
the heterogeneous finite-depth formulation will be obtained by induction in `HA.Deep`.
-/

@[expose] public section

namespace LeanRidgelet

variable {G X Ξ Y Ω Z : Type*}

/-- A feature map is joint-`G`-equivariant when simultaneous actions on its data and parameter
arguments agree with the action on its output. This is Definition 3.2. -/
def IsJointEquivariant [SMul G X] [SMul G Ξ] [SMul G Y] (φ : X → Ξ → Y) : Prop :=
  ∀ (g : G) (x : X) (ξ : Ξ), φ (g • x) (g • ξ) = g • φ x ξ

/-- Ordinary equivariance of a map between two `G`-spaces. -/
def IsEquivariant [SMul G X] [SMul G Y] (φ : X → Y) : Prop :=
  ∀ (g : G) (x : X), φ (g • x) = g • φ x

/-- Remark 3.3: ordinary equivariance is joint equivariance when the parameter action is trivial. -/
theorem IsEquivariant.isJointEquivariant_of_fixed [SMul G X] [SMul G Ξ] [SMul G Y]
    {φ : X → Ξ → Y} (hφ : ∀ ξ, IsEquivariant (G := G) fun x ↦ φ x ξ)
    (hfixed : ∀ (g : G) (ξ : Ξ), g • ξ = ξ) : IsJointEquivariant (G := G) φ := by
  intro g x ξ
  rw [hfixed g ξ]
  exact hφ ξ g x

/-- The orbit feature generated from an arbitrary seed map, as in Lemma 3.4. -/
def orbitFeature [Group G] [MulAction G X] [MulAction G Y] (φ₀ : X → Y) (x : X) (h : G) : Y :=
  h • φ₀ (h⁻¹ • x)

/-- Lemma 3.4: the orbit feature of any seed map is joint-equivariant. -/
theorem isJointEquivariant_orbitFeature [Group G] [MulAction G X] [MulAction G Y]
    (φ₀ : X → Y) :
    IsJointEquivariant (G := G) (Ξ := G) (orbitFeature (G := G) φ₀) := by
  intro g x h
  simp [orbitFeature, mul_smul]

/-- Cascade composition of two parametrized feature maps. -/
def jointCascade (φ : X → Ξ → Y) (ψ : Y → Ω → Z) (x : X) (p : Ξ × Ω) : Z :=
  ψ (φ x p.1) p.2

/-- The binary form of Lemma 3.5: a cascade of joint-equivariant layers is joint-equivariant. -/
theorem IsJointEquivariant.jointCascade [Monoid G] [MulAction G X] [MulAction G Ξ] [MulAction G Y]
    [MulAction G Ω] [MulAction G Z] {φ : X → Ξ → Y} {ψ : Y → Ω → Z}
    (hφ : IsJointEquivariant (G := G) φ) (hψ : IsJointEquivariant (G := G) ψ) :
    IsJointEquivariant (G := G) (jointCascade φ ψ) := by
  intro g x p
  change ψ (φ (g • x) (g • p.1)) (g • p.2) = g • ψ (φ x p.1) p.2
  rw [hφ g x p.1]
  exact hψ g (φ x p.1) p.2

end LeanRidgelet
