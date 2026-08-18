/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Schur

/-!
# Conjugating unitary representations

This file transports a unitary representation across a linear isometric equivalence of Hilbert
spaces. The equivalence becomes a continuous intertwining map, and topological irreducibility is
preserved. These elementary constructions are independent of ridgelet transforms and are intended
as Mathlib upstream candidates.
-/

@[expose] public section

noncomputable section

open scoped ContRepresentation

variable {G H K : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace UnitaryRepresentation

/-- Conjugation of linear isometric automorphisms by a linear isometric equivalence. -/
def conjugateLinearIsometryEquivMonoidHom (e : H ≃ₗᵢ[ℂ] K) :
    (H ≃ₗᵢ[ℂ] H) →* (K ≃ₗᵢ[ℂ] K) where
  toFun U := e.symm.trans (U.trans e)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    simp
  map_mul' U V := by
    apply LinearIsometryEquiv.ext
    intro x
    change e ((U * V) (e.symm x)) =
      e (U (e.symm (e (V (e.symm x)))))
    simp

/-- Transport a unitary representation across a linear isometric equivalence. -/
def conjugate (π : UnitaryRepresentation G H) (e : H ≃ₗᵢ[ℂ] K) :
    UnitaryRepresentation G K :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    ((conjugateLinearIsometryEquivMonoidHom e).comp
      (Unitary.linearIsometryEquiv.toMonoidHom.comp π))

@[simp]
theorem linearIsometryEquiv_conjugate_apply (π : UnitaryRepresentation G H)
    (e : H ≃ₗᵢ[ℂ] K) (g : G) (x : K) :
    Unitary.linearIsometryEquiv (π.conjugate e g) x =
      e (Unitary.linearIsometryEquiv (π g) (e.symm x)) := rfl

/-- Strong continuity is preserved when a unitary representation is transported across a linear
isometric equivalence. -/
theorem IsStronglyContinuous.conjugate [TopologicalSpace G]
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (e : H ≃ₗᵢ[ℂ] K) : (π.conjugate e).IsStronglyContinuous := by
  intro x
  have h := e.continuous.comp (hπ (e.symm x))
  convert h using 1
  funext g
  exact linearIsometryEquiv_conjugate_apply π e g x

/-- The equivalence used for conjugation is a continuous intertwining map. -/
def conjugateIntertwiningMap (π : UnitaryRepresentation G H) (e : H ≃ₗᵢ[ℂ] K) :
    π.toContRepresentation →ⁱL (π.conjugate e).toContRepresentation where
  __ := e.toContinuousLinearEquiv.toContinuousLinearMap
  isIntertwining' g := by
    ext x
    change e (Unitary.linearIsometryEquiv (π g) x) =
      Unitary.linearIsometryEquiv (π.conjugate e g) (e x)
    rw [linearIsometryEquiv_conjugate_apply, e.symm_apply_apply]

@[simp]
theorem conjugateIntertwiningMap_apply (π : UnitaryRepresentation G H)
    (e : H ≃ₗᵢ[ℂ] K) (x : H) :
    conjugateIntertwiningMap π e x = e x := rfl

/-- The inverse equivalence intertwines the conjugated representation back with the original
representation. -/
def conjugateInverseIntertwiningMap (π : UnitaryRepresentation G H) (e : H ≃ₗᵢ[ℂ] K) :
    (π.conjugate e).toContRepresentation →ⁱL π.toContRepresentation where
  __ := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  isIntertwining' g := by
    ext x
    change e.symm (Unitary.linearIsometryEquiv (π.conjugate e g) x) =
      Unitary.linearIsometryEquiv (π g) (e.symm x)
    rw [linearIsometryEquiv_conjugate_apply, e.symm_apply_apply]

@[simp]
theorem conjugateInverseIntertwiningMap_apply (π : UnitaryRepresentation G H)
    (e : H ≃ₗᵢ[ℂ] K) (x : K) :
    conjugateInverseIntertwiningMap π e x = e.symm x := rfl

@[simp]
theorem conjugate_symm (π : UnitaryRepresentation G H) (e : H ≃ₗᵢ[ℂ] K) :
    (π.conjugate e).conjugate e.symm = π := by
  apply MonoidHom.ext
  intro g
  apply Unitary.linearIsometryEquiv.injective
  apply LinearIsometryEquiv.ext
  intro x
  simp

/-- Topological irreducibility is preserved when a unitary representation is transported across
a linear isometric equivalence. -/
theorem conjugate_isTopologicallyIrreducible (π : UnitaryRepresentation G H)
    (e : H ≃ₗᵢ[ℂ] K) (hπ : π.IsTopologicallyIrreducible) :
    (π.conjugate e).IsTopologicallyIrreducible := by
  letI : Nontrivial H := hπ.1
  letI : Nontrivial K := e.symm.toEquiv.nontrivial
  refine ⟨inferInstance, ?_⟩
  intro W hW
  let V : ClosedSubmodule ℂ H := W.mapEquiv e.symm.toContinuousLinearEquiv
  have hV : π.IsInvariant V := by
    intro g x hx
    rw [show V = W.mapEquiv e.symm.toContinuousLinearEquiv from rfl,
      ClosedSubmodule.mem_mapEquiv_iff] at hx ⊢
    change e x ∈ W at hx
    change e (Unitary.linearIsometryEquiv (π g) x) ∈ W
    have hconj := hW g hx
    change Unitary.linearIsometryEquiv (π.conjugate e g) (e x) ∈ W at hconj
    rw [linearIsometryEquiv_conjugate_apply, e.symm_apply_apply] at hconj
    exact hconj
  rcases hπ.2 V hV with hbot | htop
  · left
    apply (ClosedSubmodule.mapEquiv e.symm.toContinuousLinearEquiv).injective
    simpa only [ClosedSubmodule.mapEquiv_bot_eq_bot] using hbot
  · right
    apply (ClosedSubmodule.mapEquiv e.symm.toContinuousLinearEquiv).injective
    simpa only [ClosedSubmodule.mapEquiv_top_eq_top] using htop

/-- Conjugate unitary representations are topologically irreducible simultaneously. -/
theorem conjugate_isTopologicallyIrreducible_iff (π : UnitaryRepresentation G H)
    (e : H ≃ₗᵢ[ℂ] K) :
    (π.conjugate e).IsTopologicallyIrreducible ↔ π.IsTopologicallyIrreducible := by
  constructor
  · intro h
    have h' := conjugate_isTopologicallyIrreducible (π.conjugate e) e.symm h
    simpa using h'
  · exact conjugate_isTopologicallyIrreducible π e

end UnitaryRepresentation
