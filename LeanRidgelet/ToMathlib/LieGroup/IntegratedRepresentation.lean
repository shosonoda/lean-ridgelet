/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import LeanRidgelet.ToMathlib.LieGroup.Schur

/-!
# Integrated vectors of strongly continuous unitary representations

A compactly supported continuous scalar kernel can be integrated against an orbit of a strongly
continuous unitary representation.  The resulting Bochner integral remains in every closed
invariant subspace containing the original vector.  This is the abstract part of the smoothing
step in Folland Lemma 6.29; no choice of an approximate identity is made here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace UnitaryRepresentation

variable {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector obtained by integrating a compactly supported continuous scalar kernel against a
unitary orbit. -/
noncomputable def integratedVector (π : UnitaryRepresentation G H) (μ : Measure G)
    (ψ : C_c(G, ℂ)) (v : H) : H :=
  ∫ g, ψ g • (π g : H →L[ℂ] H) v ∂μ

/-- Strong continuity and compact support make the orbit-kernel integrand Bochner integrable. -/
theorem integratedVector_integrable
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (ψ : C_c(G, ℂ)) (v : H) :
    Integrable (fun g ↦ ψ g • (π g : H →L[ℂ] H) v) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ψ.continuous.smul (hπ v)
  · exact ψ.hasCompactSupport.smul_right

/-- Integrating a unitary orbit does not leave a closed invariant subspace. -/
theorem integratedVector_mem
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : ClosedSubmodule ℂ H) (hK : π.IsInvariant K)
    (ψ : C_c(G, ℂ)) {v : H} (hv : v ∈ K) :
    π.integratedVector μ ψ v ∈ K := by
  apply K.toSubmodule.starProjection_eq_self_iff.mp
  rw [integratedVector,
    ← K.toSubmodule.starProjection.integral_comp_comm
      (integratedVector_integrable hπ μ ψ v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g ↦
    K.toSubmodule.starProjection_eq_self_iff.mpr (K.smul_mem (ψ g) (hK g hv))

/-- Mathlib's peak-function convergence theorem applied to a strongly continuous unitary orbit.
This is the convergence mechanism for approximate-identity smoothing in Folland Lemma 6.29. -/
theorem tendsto_setIntegral_peak_smul_orbit
    [T2Space G] {ι : Type*} {l : Filter ι} {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ]
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (v : H) {s t : Set G} (hs : IsCompact s) (ht : MeasurableSet t)
    (hts : t ⊆ s) (h'ts : t ∈ 𝓝[s] (1 : G)) (h't : μ t ≠ ∞)
    {φ : ι → G → ℝ} (hnφ : ∀ᶠ i in l, ∀ g ∈ s, 0 ≤ φ i g)
    (hlφ : ∀ u : Set G, IsOpen u → 1 ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Filter.Tendsto (fun i ↦ ∫ g in t, φ i g ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s)) :
    Filter.Tendsto
      (fun i ↦ ∫ g in s, φ i g • (π g : H →L[ℂ] H) v ∂μ) l (𝓝 v) := by
  apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    hs.measurableSet ht hts h'ts h't hnφ hlφ hiφ h'iφ
  · exact (hπ v).continuousOn.integrableOn_compact hs
  · have hc : Filter.Tendsto (fun g : G ↦ (π g : H →L[ℂ] H) v)
        (𝓝 (1 : G)) (𝓝 v) := by
      have hone : (π (1 : G) : H →L[ℂ] H) v = v := by
        rw [show π (1 : G) = 1 from π.map_one]
        rfl
      have hc0 : Filter.Tendsto (fun g : G ↦ (π g : H →L[ℂ] H) v)
          (nhds (1 : G)) (nhds ((π (1 : G) : H →L[ℂ] H) v)) :=
        (hπ v).continuousAt
      rw [hone] at hc0
      exact hc0
    exact hc.mono_left inf_le_left

section Haar

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Integrated vector for Mathlib's chosen left Haar measure. -/
noncomputable def haarIntegratedVector (π : UnitaryRepresentation G H)
    (ψ : C_c(G, ℂ)) (v : H) : H :=
  π.integratedVector Measure.haar ψ v

/-- A compactly supported kernel times a strongly continuous unitary orbit is Haar integrable. -/
theorem haarIntegratedVector_integrable
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (ψ : C_c(G, ℂ)) (v : H) :
    Integrable (fun g ↦ ψ g • (π g : H →L[ℂ] H) v) Measure.haar :=
  integratedVector_integrable hπ Measure.haar ψ v

/-- Haar-integrated vectors remain in every closed invariant subspace containing the input. -/
theorem haarIntegratedVector_mem
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (K : ClosedSubmodule ℂ H) (hK : π.IsInvariant K)
    (ψ : C_c(G, ℂ)) {v : H} (hv : v ∈ K) :
    π.haarIntegratedVector ψ v ∈ K :=
  integratedVector_mem hπ Measure.haar K hK ψ hv

end Haar

end UnitaryRepresentation
