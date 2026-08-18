/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import LeanRidgelet.ToMathlib.LieGroup.IntegratedRepresentation

/-!
# Compactly supported approximate identities for Haar measure

This file constructs normalized nonnegative continuous bump functions supported in arbitrary
neighborhoods of the identity of a locally compact Hausdorff group.  A first-countable
specialization packages them into a sequential Haar approximate identity and connects that
sequence to integrated vectors of strongly continuous unitary representations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported ENNReal Topology

namespace UnitaryRepresentation

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Regard a real compactly supported kernel as a complex one. -/
def complexKernel (f : C_c(G, ℝ)) : C_c(G, ℂ) where
  toFun g := f g
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous
  hasCompactSupport' := by
    change HasCompactSupport (Complex.ofReal ∘ (f : G → ℝ))
    exact f.hasCompactSupport.comp_left Complex.ofReal_zero

omit [Group G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] in
@[simp]
theorem complexKernel_apply (f : C_c(G, ℝ)) (g : G) : complexKernel f g = f g := rfl

/-- Every neighborhood of the identity contains the support of a nonnegative continuous Haar
probability density. -/
theorem exists_haarProbabilityBump {U : Set G} (hU : IsOpen U) (h1U : 1 ∈ U) :
    ∃ ψ : C_c(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ tsupport ψ ⊆ U ∧
      ∫ g, ψ g ∂Measure.haar = 1 := by
  obtain ⟨f, hfone, hfcompact, hfsupport, hfrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      isCompact_singleton hU (Set.singleton_subset_iff.mpr h1U)
  have hfnonneg : 0 ≤ (f : G → ℝ) := fun g ↦ (hfrange g).1
  have hfone' : f 1 ≠ 0 := by
    rw [hfone (Set.mem_singleton 1)]
    exact one_ne_zero
  have hpos : 0 < ∫ g, f g ∂Measure.haar :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hfcompact hfnonneg hfone'
  let c : ℝ := (∫ g, f g ∂Measure.haar)⁻¹
  let fc : C_c(G, ℝ) := ⟨f, hfcompact⟩
  refine ⟨c • fc, ?_, ?_, ?_⟩
  · intro g
    change 0 ≤ c * f g
    exact mul_nonneg (le_of_lt (inv_pos.mpr hpos)) (hfnonneg g)
  · exact (tsupport_smul_subset_right (fun _ : G ↦ c) f).trans hfsupport
  · change ∫ g, c * f g ∂Measure.haar = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

/-- A first-countable locally compact group admits a sequence of compactly supported continuous
nonnegative Haar probability densities whose supports eventually lie in every neighborhood of the
identity.  The supports can moreover be chosen inside one fixed compact set. -/
theorem exists_haarApproximateIdentity [FirstCountableTopology G] :
    ∃ ψ : ℕ → C_c(G, ℝ),
      (∀ n g, 0 ≤ ψ n g) ∧
      (∀ n, ∫ g, ψ n g ∂Measure.haar = 1) ∧
      (∀ U ∈ nhds (1 : G), ∀ᶠ n in Filter.atTop, tsupport (ψ n) ⊆ U) ∧
      ∃ s : Set G, IsCompact s ∧ ∀ n, tsupport (ψ n) ⊆ s := by
  obtain ⟨U, hUopen, hUbasis⟩ :=
    (nhds_basis_opens (1 : G)).exists_antitone_subbasis
  obtain ⟨V, hVopen, h1V, hVcompact⟩ :=
    exists_isOpen_mem_isCompact_closure (1 : G)
  choose ψ hψ using fun n ↦ exists_haarProbabilityBump
    ((hUopen n).2.inter hVopen) ⟨(hUopen n).1, h1V⟩
  refine ⟨ψ, fun n g ↦ (hψ n).1 g, fun n ↦ (hψ n).2.2, ?_, ?_⟩
  · intro W hW
    obtain ⟨i, hi⟩ := hUbasis.mem_iff.mp hW
    exact Filter.eventually_atTop.2 ⟨i, fun n hn ↦
      (hψ n).2.1.trans
        ((Set.inter_subset_left : U n ∩ V ⊆ U n).trans ((hUbasis.2 hn).trans hi))⟩
  · exact ⟨closure V, hVcompact, fun n ↦
      (hψ n).2.1.trans
        ((Set.inter_subset_right : U n ∩ V ⊆ V).trans subset_closure)⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A compactly supported sequential Haar approximate identity can be chosen so that its
integrated unitary orbit converges to the original vector. -/
theorem exists_haarApproximateIdentity_tendsto_smul_orbit
    [FirstCountableTopology G] [T2Space G]
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous) (v : H) :
    ∃ ψ : ℕ → C_c(G, ℝ),
      (∀ n g, 0 ≤ ψ n g) ∧
      (∀ n, ∫ g, ψ n g ∂Measure.haar = 1) ∧
      (∀ U ∈ nhds (1 : G), ∀ᶠ n in Filter.atTop, tsupport (ψ n) ⊆ U) ∧
      Filter.Tendsto
        (fun n ↦ ∫ g, ψ n g • (π g : H →L[ℂ] H) v ∂Measure.haar)
        Filter.atTop (nhds v) := by
  obtain ⟨ψ, hnonneg, hintegral, hsupport, s, hs, hψs⟩ :=
    exists_haarApproximateIdentity (G := G)
  refine ⟨ψ, hnonneg, hintegral, hsupport, ?_⟩
  have hpeak : Filter.Tendsto
      (fun n ↦ ∫ g in s, ψ n g • (π g : H →L[ℂ] H) v ∂Measure.haar)
      Filter.atTop (nhds v) := by
    apply tendsto_setIntegral_peak_smul_orbit hπ v hs hs.measurableSet
      Set.Subset.rfl self_mem_nhdsWithin hs.measure_ne_top
    · exact Filter.Eventually.of_forall fun n g _ ↦ hnonneg n g
    · intro U hUopen h1U
      have heventualSupport := hsupport U (hUopen.mem_nhds h1U)
      have hzero : TendstoUniformlyOn (fun _ : ℕ ↦ (0 : G → ℝ)) 0
          Filter.atTop (s \ U) :=
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ))
          Filter.atTop (nhds 0)).tendstoUniformlyOn_const _
      apply hzero.congr
      filter_upwards [heventualSupport] with n hn
      intro g hg
      change 0 = ψ n g
      symm
      by_contra hgSupport
      exact hg.2 (hn (subset_closure hgSupport))
    · have hsetIntegral : ∀ n, ∫ g in s, ψ n g ∂Measure.haar = 1 := by
        intro n
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · exact hintegral n
        · intro g hg
          by_contra hgSupport
          exact hg (hψs n (subset_closure hgSupport))
      simpa only [hsetIntegral] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          Filter.atTop (nhds 1))
    · exact Filter.Eventually.of_forall fun n ↦
        (ψ n).continuous.aestronglyMeasurable.restrict
  apply hpeak.congr'
  exact Filter.Eventually.of_forall fun n ↦
    setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg ↦ by
      have hzero : ψ n g = 0 := by
        by_contra hgSupport
        exact hg (hψs n (subset_closure hgSupport))
      simp [hzero]

/-- The preceding convergence written using the bundled complex Haar-integrated vector. -/
theorem exists_haarApproximateIdentity_tendsto_integratedVector
    [FirstCountableTopology G] [T2Space G]
    {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous) (v : H) :
    ∃ ψ : ℕ → C_c(G, ℝ),
      (∀ n g, 0 ≤ ψ n g) ∧
      (∀ n, ∫ g, ψ n g ∂Measure.haar = 1) ∧
      (∀ U ∈ nhds (1 : G), ∀ᶠ n in Filter.atTop, tsupport (ψ n) ⊆ U) ∧
      Filter.Tendsto
        (fun n ↦ π.haarIntegratedVector (complexKernel (ψ n)) v)
        Filter.atTop (nhds v) := by
  obtain ⟨ψ, hnonneg, hintegral, hsupport, htendsto⟩ :=
    exists_haarApproximateIdentity_tendsto_smul_orbit hπ v
  refine ⟨ψ, hnonneg, hintegral, hsupport, ?_⟩
  apply htendsto.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    change (∫ g, ψ n g • (π g : H →L[ℂ] H) v ∂Measure.haar) =
      ∫ g, complexKernel (ψ n) g • (π g : H →L[ℂ] H) v ∂Measure.haar
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g ↦ by
      simp only
      rw [complexKernel_apply]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) (ψ n g) ((π g : H →L[ℂ] H) v)

end UnitaryRepresentation
