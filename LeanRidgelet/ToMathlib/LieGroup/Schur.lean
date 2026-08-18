/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Algebra.Star.Module
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Unitary representations and the infinite-dimensional Schur lemma

This file develops the part of Schur's lemma needed for unitary representations on complex
Hilbert spaces. It is independent of ridgelet transforms and is intended as a Mathlib upstream
candidate.

Mathlib provides algebraic irreducibility in `Representation.IsIrreducible` and Schur's lemma when
the relevant hom space is finite-dimensional. A unitary representation on an infinite-dimensional
Hilbert space instead uses *topological irreducibility*: only closed invariant subspaces are
required to be trivial. The corresponding infinite-dimensional Schur lemma is not currently in
Mathlib. The proof below follows the standard commutant argument: invariant closed subspaces
correspond to commuting orthogonal projections, the commutant is closed under adjoints, and a
non-scalar self-adjoint operator supplies a nontrivial spectral subspace. The last step is obtained
using Mathlib's continuous functional calculus: positive-part cutoff functions at a midpoint of two
distinct real spectral values give two nonzero self-adjoint operators with zero product, and the
closure of the range of either cutoff is the required closed subspace.
-/

@[expose] public section

noncomputable section

open scoped CStarAlgebra ContRepresentation ContinuousFunctionalCalculus

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A unitary representation of a group on a complex Hilbert space, expressed using the unitary
group of the C\*-algebra of bounded operators. No continuity in the group variable is imposed;
the Schur argument only uses the algebraic action and unitarity. -/
abbrev UnitaryRepresentation (G H : Type*) [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

/-- Forget that the operators in a unitary representation are unitary. -/
def toContRepresentation (π : UnitaryRepresentation G H) : ContRepresentation ℂ G H :=
  .ofMonoidHom
    { toFun := fun g ↦ (π g : H →L[ℂ] H)
      map_one' := by simp
      map_mul' := by
        intro g h
        simp }

@[simp]
theorem toContRepresentation_apply (π : UnitaryRepresentation G H) (g : G) :
    π.toContRepresentation g = (π g : H →L[ℂ] H) := rfl

/-- Restrict a unitary representation along a group homomorphism. -/
def restrict {G' : Type*} [Group G'] (π : UnitaryRepresentation G H) (φ : G' →* G) :
    UnitaryRepresentation G' H :=
  π.comp φ

@[simp]
theorem restrict_apply {G' : Type*} [Group G'] (π : UnitaryRepresentation G H) (φ : G' →* G)
    (g : G') : π.restrict φ g = π (φ g) := rfl

/-- Strong continuity of a unitary representation: every orbit map is continuous in the group
variable.  Mathlib's `ContRepresentation` only says that each represented operator is continuous;
it deliberately imposes no topology on the acting group. -/
def IsStronglyContinuous [TopologicalSpace G] (π : UnitaryRepresentation G H) : Prop :=
  ∀ x : H, Continuous fun g : G ↦ (π g : H →L[ℂ] H) x

theorem IsStronglyContinuous.restrict {G' : Type*} [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] {π : UnitaryRepresentation G H} (hπ : π.IsStronglyContinuous)
    (φ : G' →ₜ* G) : (π.restrict φ.toMonoidHom).IsStronglyContinuous := by
  intro x
  exact (hπ x).comp φ.continuous

/-- A closed subspace is invariant under a unitary representation when every group element maps
it into itself. Since inverses also occur in the representation, inclusion automatically upgrades
to equality; the inclusion form is more convenient for applications. -/
def IsInvariant (π : UnitaryRepresentation G H) (K : ClosedSubmodule ℂ H) : Prop :=
  ∀ (g : G) ⦃x : H⦄, x ∈ K → (π g : H →L[ℂ] H) x ∈ K

/-- Topological irreducibility for a unitary representation: the Hilbert space is nonzero and its
only closed invariant subspaces are zero and the whole space. -/
def IsTopologicallyIrreducible (π : UnitaryRepresentation G H) : Prop :=
  Nontrivial H ∧ ∀ K : ClosedSubmodule ℂ H, π.IsInvariant K → K = ⊥ ∨ K = ⊤

theorem restrict_isInvariant_iff_of_surjective {G' : Type*} [Group G']
    (π : UnitaryRepresentation G H) (φ : G' →* G) (hφ : Function.Surjective φ)
    (K : ClosedSubmodule ℂ H) :
    (π.restrict φ).IsInvariant K ↔ π.IsInvariant K := by
  constructor
  · intro h g x hx
    obtain ⟨g', rfl⟩ := hφ g
    exact h g' hx
  · intro h g' x hx
    exact h (φ g') hx

/-- Restriction along a surjective group homomorphism preserves and reflects topological
irreducibility. -/
theorem restrict_isTopologicallyIrreducible_iff_of_surjective {G' : Type*} [Group G']
    (π : UnitaryRepresentation G H) (φ : G' →* G) (hφ : Function.Surjective φ) :
    (π.restrict φ).IsTopologicallyIrreducible ↔ π.IsTopologicallyIrreducible := by
  constructor <;> rintro ⟨hH, h⟩ <;> refine ⟨hH, ?_⟩
  · intro K hK
    exact h K ((π.restrict_isInvariant_iff_of_surjective φ hφ K).mpr hK)
  · intro K hK
    exact h K ((π.restrict_isInvariant_iff_of_surjective φ hφ K).mp hK)

/-- Membership in the commutant of a unitary representation. -/
def Commutes (π : UnitaryRepresentation G H) (T : H →L[ℂ] H) : Prop :=
  ∀ g : G, T.comp (π g : H →L[ℂ] H) = (π g : H →L[ℂ] H).comp T

/-- The property asserted by the infinite-dimensional complex Schur lemma. Keeping it as a
predicate allows downstream theorems to accept the missing analytic result as an explicit
hypothesis rather than hiding it in a structure or typeclass field. -/
def HasSchurProperty (π : UnitaryRepresentation G H) : Prop :=
  ∀ T : H →L[ℂ] H, π.Commutes T → ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ H

theorem isInvariant_bot (π : UnitaryRepresentation G H) : π.IsInvariant ⊥ := by
  intro g x hx
  simp only [ClosedSubmodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

theorem isInvariant_top (π : UnitaryRepresentation G H) : π.IsInvariant ⊤ := by
  simp [IsInvariant]

/-- Every closed complex-linear subspace of the one-dimensional Hilbert space `ℂ` is zero or the
whole space.  This is the final fiberwise step in scalar instances of the Mackey correspondence. -/
theorem closedSubmodule_complex_eq_bot_or_top (K : ClosedSubmodule ℂ ℂ) :
    K = ⊥ ∨ K = ⊤ := by
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  right
  apply top_unique
  intro z hz
  have hsub : K.toSubmodule ≠ ⊥ := by
    intro h
    apply hbot
    apply ClosedSubmodule.toSubmodule_injective
    simpa using h
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsub
  have hzx : (z / x) • x ∈ K := K.smul_mem (z / x) hxK
  simpa only [smul_eq_mul, div_mul_cancel₀ z hx0] using hzx

/-- Every unitary representation on the one-dimensional complex Hilbert space is topologically
irreducible. This supplies the character representations used in scalar Mackey induction. -/
theorem complex_isTopologicallyIrreducible (π : UnitaryRepresentation G ℂ) :
    π.IsTopologicallyIrreducible := by
  refine ⟨inferInstance, ?_⟩
  intro K _hK
  exact closedSubmodule_complex_eq_bot_or_top K

/-- The trivial unitary representation on the one-dimensional complex Hilbert space is
topologically irreducible. -/
theorem one_complex_isTopologicallyIrreducible :
    (1 : UnitaryRepresentation G ℂ).IsTopologicallyIrreducible :=
  complex_isTopologicallyIrreducible 1

/-- The inverse group element acts by the inverse linear isometric equivalence. -/
theorem linearIsometryEquiv_inv (π : UnitaryRepresentation G H) (g : G) :
    (Unitary.linearIsometryEquiv (π g)).symm = Unitary.linearIsometryEquiv (π g⁻¹) := by
  change (Unitary.linearIsometryEquiv (π g))⁻¹ = _
  rw [← map_inv]
  simp

/-- A unitary action maps an invariant closed subspace onto itself, not merely into itself. -/
theorem map_eq_of_isInvariant (π : UnitaryRepresentation G H) (K : ClosedSubmodule ℂ H)
    (hK : π.IsInvariant K) (g : G) :
    K.toSubmodule.map (Unitary.linearIsometryEquiv (π g)).toLinearEquiv.toLinearMap =
      K.toSubmodule := by
  let U : H ≃ₗᵢ[ℂ] H := Unitary.linearIsometryEquiv (π g)
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hK g hx
  · intro y hy
    refine ⟨U.symm y, ?_, U.apply_symm_apply y⟩
    rw [show U.symm = Unitary.linearIsometryEquiv (π g⁻¹) from π.linearIsometryEquiv_inv g]
    exact hK g⁻¹ hy

/-- Folland Proposition 3.4: a closed subspace is invariant precisely when its orthogonal
projection belongs to the commutant. -/
theorem isInvariant_iff_starProjection_commutes (π : UnitaryRepresentation G H)
    (K : ClosedSubmodule ℂ H) :
    π.IsInvariant K ↔ π.Commutes K.toSubmodule.starProjection := by
  constructor
  · intro hK g
    let U : H ≃ₗᵢ[ℂ] H := Unitary.linearIsometryEquiv (π g)
    have hmap : K.toSubmodule.map U.toLinearEquiv.toLinearMap = K.toSubmodule :=
      π.map_eq_of_isInvariant K hK g
    ext x
    have hp := (Submodule.starProjection_map_apply U K.toSubmodule (U x)).symm
    rw [U.symm_apply_apply] at hp
    have hp' : U (K.toSubmodule.starProjection x) =
        K.toSubmodule.starProjection (U x) := by
      simpa only [hmap] using hp
    change K.toSubmodule.starProjection ((π g : H →L[ℂ] H) x) =
      (π g : H →L[ℂ] H) (K.toSubmodule.starProjection x)
    have hU (z : H) : U z = (π g : H →L[ℂ] H) z := rfl
    rw [← hU x, ← hU (K.toSubmodule.starProjection x)]
    exact hp'.symm
  · intro hP g x hx
    apply K.toSubmodule.starProjection_eq_self_iff.mp
    have hPx : K.toSubmodule.starProjection x = x :=
      K.toSubmodule.starProjection_eq_self_iff.mpr hx
    exact DFunLike.congr_fun (hP g) x |>.trans <| by
      simp only [ContinuousLinearMap.comp_apply, hPx]

/-- The commutant is a complex vector space. -/
theorem Commutes.add {π : UnitaryRepresentation G H} {S T : H →L[ℂ] H}
    (hS : π.Commutes S) (hT : π.Commutes T) : π.Commutes (S + T) := by
  intro g
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  have hSx := DFunLike.congr_fun (hS g) x
  have hTx := DFunLike.congr_fun (hT g) x
  simp only [ContinuousLinearMap.comp_apply] at hSx hTx
  rw [hSx, hTx]
  exact ((π g : H →L[ℂ] H).map_add (S x) (T x)).symm

/-- The commutant is closed under complex scalar multiplication. -/
theorem Commutes.smul {π : UnitaryRepresentation G H} {T : H →L[ℂ] H}
    (hT : π.Commutes T) (c : ℂ) : π.Commutes (c • T) := by
  intro g
  ext x
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  have hTx := DFunLike.congr_fun (hT g) x
  simp only [ContinuousLinearMap.comp_apply] at hTx
  rw [hTx]
  exact (π g : H →L[ℂ] H).map_smul c (T x) |>.symm

/-- The commutant is closed under real scalar multiplication through restriction of scalars. -/
theorem Commutes.real_smul {π : UnitaryRepresentation G H} {T : H →L[ℂ] H}
    (hT : π.Commutes T) (c : ℝ) : π.Commutes (c • T) := by
  intro g
  ext x
  simp only [smul_apply, ContinuousLinearMap.comp_apply]
  have hTx := DFunLike.congr_fun (hT g) x
  simp only [ContinuousLinearMap.comp_apply] at hTx
  rw [hTx]
  exact (π g : H →L[ℂ] H).map_smul_of_tower c (T x) |>.symm

/-- The commutant of a unitary representation is closed under adjoints. -/
theorem Commutes.adjoint {π : UnitaryRepresentation G H} {T : H →L[ℂ] H}
    (hT : π.Commutes T) : π.Commutes (ContinuousLinearMap.adjoint T) := by
  intro g
  have h := congrArg ContinuousLinearMap.adjoint (hT g⁻¹)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h
  have hunitary : ContinuousLinearMap.adjoint (π g⁻¹ : H →L[ℂ] H) =
      (π g : H →L[ℂ] H) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star, Unitary.star_eq_inv]
    simp
  simpa only [hunitary] using h.symm

/-- A non-scalar self-adjoint operator admits two nonzero orthogonal continuous-functional-calculus
cutoffs. Every operator commuting with the original operator also commutes with the first cutoff.

Choose two distinct points `lo < hi` in the real spectrum and put `r = (lo + hi) / 2`. The
positive parts of `x - r` and `r - x` are nonzero at `hi` and `lo`, respectively, and their product
vanishes everywhere. This continuous substitute for a characteristic function is sufficient for
the infinite-dimensional Schur argument; no Borel functional calculus is needed. -/
theorem exists_nonzero_orthogonal_cutoffs_of_isSelfAdjoint_not_scalar
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hscalar : ¬ ∃ c : ℂ, A = c • ContinuousLinearMap.id ℂ H) :
    ∃ B C : H →L[ℂ] H,
      B ≠ 0 ∧ C ≠ 0 ∧ IsSelfAdjoint B ∧ IsSelfAdjoint C ∧ B.comp C = 0 ∧
        ∀ T : H →L[ℂ] H, A.comp T = T.comp A → B.comp T = T.comp B := by
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp fun hH ↦ by
    apply hscalar
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨a, ha⟩ :=
    ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hnot : ¬ spectrum ℝ A ⊆ {a} := by
    intro hs
    apply hscalar
    refine ⟨(a : ℂ), ?_⟩
    have heq := CFC.eq_algebraMap_of_spectrum_subset_singleton A a hs hA
    simpa [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def] using heq
  obtain ⟨b, hb, hba⟩ := Set.not_subset.mp hnot
  have hba' : b ≠ a := by simpa using hba
  obtain ⟨lo, hlo, hi, hhi, hlohi⟩ :
      ∃ lo ∈ spectrum ℝ A, ∃ hi ∈ spectrum ℝ A, lo < hi := by
    rcases lt_or_gt_of_ne hba' with hlt | hgt
    · exact ⟨b, hb, a, ha, hlt⟩
    · exact ⟨a, ha, b, hb, hgt⟩
  let r : ℝ := (lo + hi) / 2
  let f : ℝ → ℝ := fun x ↦ max (x - r) 0
  let g : ℝ → ℝ := fun x ↦ max (r - x) 0
  have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
  have hg : Continuous g := (continuous_const.sub continuous_id).max continuous_const
  let B : H →L[ℂ] H := cfc f A
  let C : H →L[ℂ] H := cfc g A
  have hfhi : f hi ≠ 0 := by
    rw [show f hi = hi - r by
      simp only [f]
      rw [max_eq_left (by dsimp [r]; linarith)]]
    dsimp [r]
    linarith
  have hglo : g lo ≠ 0 := by
    rw [show g lo = r - lo by
      simp only [g]
      rw [max_eq_left (by dsimp [r]; linarith)]]
    dsimp [r]
    linarith
  have hB : B ≠ 0 := by
    intro hzero
    have hnorm := norm_apply_le_norm_cfc f A hhi hf.continuousOn hA
    rw [show cfc f A = B from rfl, hzero, norm_zero] at hnorm
    exact hfhi (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hC : C ≠ 0 := by
    intro hzero
    have hnorm := norm_apply_le_norm_cfc g A hlo hg.continuousOn hA
    rw [show cfc g A = C from rfl, hzero, norm_zero] at hnorm
    exact hglo (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hfg : (fun x : ℝ ↦ f x * g x) = fun _ ↦ 0 := by
    funext x
    dsimp only [f, g]
    by_cases hx : x ≤ r
    · rw [max_eq_right (sub_nonpos.mpr hx), zero_mul]
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hx)), mul_zero]
  have hBC : B.comp C = 0 := by
    rw [← ContinuousLinearMap.mul_def]
    rw [← cfc_mul f g A hf.continuousOn hg.continuousOn, hfg, cfc_const_zero]
  refine ⟨B, C, hB, hC, IsSelfAdjoint.cfc, IsSelfAdjoint.cfc, hBC, ?_⟩
  intro T hT
  have hc : Commute A T := hT
  exact (hc.cfc_real f).eq

/-- The continuous-functional-calculus step in the infinite-dimensional self-adjoint spectral
theorem, in the form needed by Schur's lemma.

For the first cutoff `B` supplied above, take the closure `K` of its range. Nonzeroness of `B`
makes `K` nonzero. A second nonzero self-adjoint cutoff `C` with `B C = 0` supplies a nonzero vector
orthogonal to the range of `B`, so `K` is proper. Commutation with `A` preserves both `K` and its
orthogonal complement; hence it commutes with the orthogonal projection onto `K`. -/
theorem exists_nontrivial_spectralSubspace_of_isSelfAdjoint_not_scalar
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hscalar : ¬ ∃ c : ℂ, A = c • ContinuousLinearMap.id ℂ H) :
    ∃ K : ClosedSubmodule ℂ H,
      K ≠ ⊥ ∧ K ≠ ⊤ ∧
        ∀ T : H →L[ℂ] H,
          A.comp T = T.comp A →
            K.toSubmodule.starProjection.comp T = T.comp K.toSubmodule.starProjection := by
  obtain ⟨B, C, hB, hC, hBself, _hCself, hBC, hBcomm⟩ :=
    exists_nonzero_orthogonal_cutoffs_of_isSelfAdjoint_not_scalar A hA hscalar
  let K : ClosedSubmodule ℂ H := B.range.closure
  have hKbot : K ≠ ⊥ := by
    intro hK
    apply hB
    ext x
    have hxK : B x ∈ K := by
      exact subset_closure ⟨x, rfl⟩
    have hxbot : B x ∈ (⊥ : ClosedSubmodule ℂ H) := hK ▸ hxK
    simpa using hxbot
  have hKtop : K ≠ ⊤ := by
    intro hK
    apply hC
    ext x
    have hxker : C x ∈ B.ker := by
      change B (C x) = 0
      have hx := DFunLike.congr_fun hBC x
      simpa only [ContinuousLinearMap.comp_apply, zero_apply] using hx
    have hxorth : C x ∈ B.rangeᗮ := by
      rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hBself.isStarNormal]
      exact hxker
    have hxKorth : C x ∈ Kᗮ := by
      rw [show Kᗮ = B.rangeᗮ.closure by
        dsimp only [K]
        exact ClosedSubmodule.orthogonal_closure'' B.range]
      exact subset_closure hxorth
    have hxtoporth : C x ∈ (⊤ : ClosedSubmodule ℂ H)ᗮ := hK ▸ hxKorth
    simpa using hxtoporth
  refine ⟨K, hKbot, hKtop, ?_⟩
  intro T hT
  have hAT : Commute A T := hT
  have hATadj : Commute A (ContinuousLinearMap.adjoint T) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    apply Commute.star_right
    simpa only [hA.star_eq] using hAT
  have range_invariant (S : H →L[ℂ] H) (hST : Commute B S) :
      B.range ∈ Module.End.invtSubmodule S.toLinearMap := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    rintro _ ⟨x, rfl⟩
    refine ⟨S x, ?_⟩
    change B (S x) = S (B x)
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun hST.eq x
  have hKinv : K.toSubmodule ∈ Module.End.invtSubmodule T.toLinearMap := by
    change B.range.topologicalClosure ∈ Module.End.invtSubmodule T.toLinearMap
    exact Submodule.topologicalClosure_mem_invtSubmodule
      (range_invariant T (hBcomm T hT))
  have hKadj : K.toSubmodule ∈
      Module.End.invtSubmodule (ContinuousLinearMap.adjoint T).toLinearMap := by
    change B.range.topologicalClosure ∈
      Module.End.invtSubmodule (ContinuousLinearMap.adjoint T).toLinearMap
    exact Submodule.topologicalClosure_mem_invtSubmodule
      (range_invariant (ContinuousLinearMap.adjoint T) (hBcomm _ hATadj.eq))
  have hKorth : K.toSubmoduleᗮ ∈ Module.End.invtSubmodule T.toLinearMap :=
    ContinuousLinearMap.mem_invtSubmodule_adjoint_iff.mp hKadj
  have hPidempotent : IsIdempotentElem K.toSubmodule.starProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    change K.toSubmodule.starProjection (K.toSubmodule.starProjection x) =
      K.toSubmodule.starProjection x
    exact DFunLike.congr_fun K.toSubmodule.isIdempotentElem_starProjection x
  have hP : Commute K.toSubmodule.starProjection.toLinearMap T.toLinearMap :=
    (LinearMap.IsIdempotentElem.commute_iff hPidempotent).mpr <| by
      simpa only [Submodule.range_starProjection, Submodule.ker_starProjection] using
        And.intro hKinv hKorth
  ext x
  exact DFunLike.congr_fun hP.eq x

/-- A self-adjoint member of the commutant of a topologically irreducible unitary representation
is scalar. This is the self-adjoint core of Schur's lemma. -/
theorem exists_scalar_of_isSelfAdjoint_of_commutes (π : UnitaryRepresentation G H)
    (hπ : π.IsTopologicallyIrreducible) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hcomm : π.Commutes A) :
    ∃ c : ℂ, A = c • ContinuousLinearMap.id ℂ H := by
  by_contra hscalar
  obtain ⟨K, hKbot, hKtop, hK⟩ :=
    exists_nontrivial_spectralSubspace_of_isSelfAdjoint_not_scalar A hA hscalar
  have hKinv : π.IsInvariant K :=
    (π.isInvariant_iff_starProjection_commutes K).mpr fun g ↦
      hK (π g : H →L[ℂ] H) (hcomm g)
  rcases hπ.2 K hKinv with h | h
  · exact hKbot h
  · exact hKtop h

/-- The infinite-dimensional unitary form of **Schur's lemma**. -/
theorem hasSchurProperty_of_isTopologicallyIrreducible (π : UnitaryRepresentation G H)
    (hπ : π.IsTopologicallyIrreducible) : π.HasSchurProperty := by
  intro T hT
  let A : H →L[ℂ] H := selfAdjointPart ℝ T
  let S : H →L[ℂ] H := skewAdjointPart ℝ T
  let B : H →L[ℂ] H := Complex.I • S
  have hstar : π.Commutes (star T) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hT.adjoint
  have hAcomm : π.Commutes A := by
    simpa [A, selfAdjointPart_apply_coe] using (hT.add hstar).real_smul (⅟2 : ℝ)
  have hScomm : π.Commutes S := by
    simpa [S, skewAdjointPart_apply_coe, sub_eq_add_neg] using
      (hT.add (hstar.smul (-1))).real_smul (⅟2 : ℝ)
  have hBcomm : π.Commutes B := hScomm.smul Complex.I
  have hAself : IsSelfAdjoint A := (selfAdjointPart ℝ T).prop
  have hBself : IsSelfAdjoint B := by
    rw [isSelfAdjoint_iff]
    dsimp only [B]
    rw [star_smul, RCLike.star_def, Complex.conj_I,
      show star S = -S from skewAdjoint.mem_iff.mp (skewAdjointPart ℝ T).prop]
    module
  obtain ⟨a, ha⟩ := π.exists_scalar_of_isSelfAdjoint_of_commutes hπ A hAself hAcomm
  obtain ⟨b, hb⟩ := π.exists_scalar_of_isSelfAdjoint_of_commutes hπ B hBself hBcomm
  refine ⟨a + (-Complex.I) * b, ?_⟩
  have hdecomp : A + S = T := StarModule.selfAdjointPart_add_skewAdjointPart ℝ T
  have hS : S = (-Complex.I) • B := by
    ext x
    simp [B, smul_smul]
  calc
    T = A + S := hdecomp.symm
    _ = (a • ContinuousLinearMap.id ℂ H) +
        (-Complex.I) • (b • ContinuousLinearMap.id ℂ H) := by rw [ha, hS, hb]
    _ = (a + (-Complex.I) * b) • ContinuousLinearMap.id ℂ H := by module

/-- The converse to the unitary Schur lemma: if every bounded operator in the commutant is
scalar, then the representation is topologically irreducible.  Indeed, the orthogonal projection
onto an invariant closed subspace is scalar; if the subspace is nonzero, evaluating that scalar
projection on a nonzero vector in the subspace forces the scalar to be one. -/
theorem isTopologicallyIrreducible_of_hasSchurProperty [Nontrivial H]
    (π : UnitaryRepresentation G H) (hπ : π.HasSchurProperty) :
    π.IsTopologicallyIrreducible := by
  refine ⟨inferInstance, ?_⟩
  intro K hK
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  right
  obtain ⟨c, hc⟩ := hπ K.toSubmodule.starProjection
    ((π.isInvariant_iff_starProjection_commutes K).mp hK)
  have hsub : K.toSubmodule ≠ ⊥ := by
    intro h
    apply hKbot
    apply ClosedSubmodule.toSubmodule_injective
    simpa using h
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsub
  have hcx : c • x = x := by
    calc
      c • x = (c • ContinuousLinearMap.id ℂ H) x := by simp
      _ = K.toSubmodule.starProjection x := DFunLike.congr_fun hc.symm x
      _ = x := K.toSubmodule.starProjection_eq_self_iff.mpr hxK
  have hc_one : c = 1 := by
    apply smul_left_injective ℂ hx0
    simpa only [one_smul] using hcx
  apply top_unique
  intro y _
  apply K.toSubmodule.starProjection_eq_self_iff.mp
  rw [hc, hc_one]
  simp

/-- For a nonzero complex Hilbert space, topological irreducibility is equivalent to the scalar
commutant property.  This is the commutant formulation used by Mackey's imprimitivity argument. -/
theorem isTopologicallyIrreducible_iff_hasSchurProperty [Nontrivial H]
    (π : UnitaryRepresentation G H) :
    π.IsTopologicallyIrreducible ↔ π.HasSchurProperty :=
  ⟨π.hasSchurProperty_of_isTopologicallyIrreducible,
    π.isTopologicallyIrreducible_of_hasSchurProperty⟩

end UnitaryRepresentation
