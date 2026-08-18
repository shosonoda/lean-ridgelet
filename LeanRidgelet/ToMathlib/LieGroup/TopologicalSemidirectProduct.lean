/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Topological semidirect products

Mathlib's `SemidirectProduct` is algebraic.  This file equips it with the topology and Borel
structure transported from the product of its two factors.  A jointly continuous action makes the
resulting group a topological group, while second countability, Polishness, and local compactness
are inherited from the product.
-/

@[expose] public section

open Topology

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] (φ : G →* MulAut N)

/-- The product topology on a semidirect product. -/
instance instTopologicalSpace [TopologicalSpace N] [TopologicalSpace G] :
    TopologicalSpace (N ⋊[φ] G) :=
  TopologicalSpace.induced (equivProd (φ := φ)) inferInstance

/-- A semidirect product with its product topology is homeomorphic to the product of its
factors. -/
def homeomorphProd [TopologicalSpace N] [TopologicalSpace G] :
    N ⋊[φ] G ≃ₜ N × G where
  toEquiv := equivProd (φ := φ)
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

@[simp]
theorem homeomorphProd_apply [TopologicalSpace N] [TopologicalSpace G] (p : N ⋊[φ] G) :
    homeomorphProd φ p = (p.left, p.right) := rfl

@[simp]
theorem homeomorphProd_symm_apply [TopologicalSpace N] [TopologicalSpace G] (p : N × G) :
    (homeomorphProd φ).symm p = ⟨p.1, p.2⟩ := rfl

/-- The canonical measurable structure on a topological semidirect product is its Borel
structure. -/
instance instMeasurableSpace [TopologicalSpace N] [TopologicalSpace G] :
    MeasurableSpace (N ⋊[φ] G) :=
  borel (N ⋊[φ] G)

/-- The measurable structure installed above is the Borel structure. -/
instance instBorelSpace [TopologicalSpace N] [TopologicalSpace G] :
    BorelSpace (N ⋊[φ] G) := ⟨rfl⟩

variable [TopologicalSpace N] [TopologicalSpace G]

theorem continuous_left : Continuous (left : N ⋊[φ] G → N) :=
  by
    change Continuous (Prod.fst ∘ equivProd (φ := φ))
    exact continuous_fst.comp continuous_induced_dom

theorem continuous_right : Continuous (right : N ⋊[φ] G → G) :=
  by
    change Continuous (Prod.snd ∘ equivProd (φ := φ))
    exact continuous_snd.comp continuous_induced_dom

instance instT2Space [T2Space N] [T2Space G] : T2Space (N ⋊[φ] G) :=
  T2Space.of_injective_continuous (equivProd (φ := φ)).injective continuous_induced_dom

/-- Second countability of a semidirect product only depends on its product topology. -/
noncomputable instance instSecondCountableTopology [SecondCountableTopology N]
    [SecondCountableTopology G] : SecondCountableTopology (N ⋊[φ] G) :=
  (homeomorphProd φ).secondCountableTopology

/-- A semidirect product with its product topology is Polish when both factors are Polish. -/
noncomputable instance instPolishSpace [PolishSpace N] [PolishSpace G] :
    PolishSpace (N ⋊[φ] G) :=
  (equivProd (φ := φ)).polishSpace_induced

/-- Local compactness of a semidirect product only depends on its product topology. -/
instance instLocallyCompactSpace [LocallyCompactSpace N] [LocallyCompactSpace G] :
    LocallyCompactSpace (N ⋊[φ] G) :=
  (homeomorphProd φ).isClosedEmbedding.locallyCompactSpace

/-- A jointly continuous action makes the product-topology semidirect product a topological
group. -/
theorem isTopologicalGroupOfContinuous [IsTopologicalGroup N] [IsTopologicalGroup G]
    (hφ : Continuous fun p : G × N ↦ φ p.1 p.2) : IsTopologicalGroup (N ⋊[φ] G) where
  continuous_mul := continuous_induced_rng.mpr <| by
    apply Continuous.prodMk
    · exact (continuous_left (φ := φ)).comp continuous_fst |>.mul <|
        hφ.comp (((continuous_right (φ := φ)).comp continuous_fst).prodMk
          ((continuous_left (φ := φ)).comp continuous_snd))
    · exact ((continuous_right (φ := φ)).comp continuous_fst).mul
        ((continuous_right (φ := φ)).comp continuous_snd)
  continuous_inv := continuous_induced_rng.mpr <| by
    apply Continuous.prodMk
    · exact hφ.comp ((continuous_right (φ := φ)).inv.prodMk
        (continuous_left (φ := φ)).inv)
    · exact (continuous_right (φ := φ)).inv

end SemidirectProduct
