/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Schur
public import LeanRidgelet.ToMathlib.LpFunctor
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise unitary representations on Bochner `Lp`

A linear isometric equivalence of the value Hilbert space acts pointwise on a Bochner `Lp`
space.  This file bundles that action first as a linear isometric equivalence and then as a
unitary representation.  It also records the elementary construction which combines two
commuting unitary representations on the same Hilbert space into a representation of the
product group.

The constructions use Mathlib's `ContinuousLinearMap.compLp`; no representative is selected as
part of the definition.  The expected pointwise formulas are instead stated a.e.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnitaryRepresentation

variable {G G₁ G₂ X E H : Type*}
  [Group G] [Group G₁] [Group G₂]
  [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {p : ℝ≥0∞} {μ : Measure X} [Fact (1 ≤ p)]

/-- Pointwise application of a value-space linear isometric equivalence to a Bochner `Lp`
class. -/
def lpPointwiseLinearIsometry (U : E ≃ₗᵢ[ℂ] E) :
    Lp E p μ →ₗᵢ[ℂ] Lp E p μ where
  toFun f := U.toLinearIsometry.toContinuousLinearMap.compLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp (f + g),
      U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f,
      U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp g,
      Lp.coeFn_add f g,
      Lp.coeFn_add
        (U.toLinearIsometry.toContinuousLinearMap.compLp f)
        (U.toLinearIsometry.toContinuousLinearMap.compLp g)] with x hfg hf hg hadd hout
    rw [hfg, hadd, Pi.add_apply, map_add, hout, Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp (c • f),
      U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (U.toLinearIsometry.toContinuousLinearMap.compLp f)] with x hcf hf hin hout
    rw [hcf, hin, Pi.smul_apply, map_smul]
    change c • U.toLinearIsometry.toContinuousLinearMap (f x) =
      ((c • U.toLinearIsometry.toContinuousLinearMap.compLp f : Lp E p μ) : X → E) x
    rw [hout, Pi.smul_apply, hf]
  norm_map' f := by
    change ‖U.toLinearIsometry.toContinuousLinearMap.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_norm_ae
    filter_upwards [U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with x hx
    rw [hx]
    exact U.norm_map (f x)

omit [CompleteSpace E] in
/-- The pointwise `Lp` isometry has the expected a.e. representative. -/
theorem lpPointwiseLinearIsometry_apply_ae (U : E ≃ₗᵢ[ℂ] E) (f : Lp E p μ) :
    lpPointwiseLinearIsometry U f =ᵐ[μ] fun x ↦ U (f x) :=
  U.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f

omit [CompleteSpace E] in
/-- Pointwise application is onto; applying `U.symm` supplies an explicit preimage. -/
theorem lpPointwiseLinearIsometry_surjective (U : E ≃ₗᵢ[ℂ] E) :
    Function.Surjective (lpPointwiseLinearIsometry (p := p) (μ := μ) U) := by
  intro f
  refine ⟨lpPointwiseLinearIsometry U.symm f, ?_⟩
  apply Lp.ext
  filter_upwards [lpPointwiseLinearIsometry_apply_ae U
      (lpPointwiseLinearIsometry U.symm f),
    lpPointwiseLinearIsometry_apply_ae U.symm f] with x hout hin
  rw [hout, hin, U.apply_symm_apply]

/-- Pointwise application of a value-space unitary, as an equivalence of Bochner `Lp`. -/
def lpPointwiseLinearIsometryEquiv (U : E ≃ₗᵢ[ℂ] E) :
    Lp E p μ ≃ₗᵢ[ℂ] Lp E p μ :=
  LinearIsometryEquiv.ofSurjective (lpPointwiseLinearIsometry U)
    (lpPointwiseLinearIsometry_surjective U)

omit [CompleteSpace E] in
/-- The bundled pointwise equivalence has the expected a.e. representative. -/
theorem lpPointwiseLinearIsometryEquiv_apply_ae (U : E ≃ₗᵢ[ℂ] E)
    (f : Lp E p μ) :
    lpPointwiseLinearIsometryEquiv U f =ᵐ[μ] fun x ↦ U (f x) :=
  lpPointwiseLinearIsometry_apply_ae U f

omit [CompleteSpace E] in
/-- Pointwise application respects composition of value-space unitaries. -/
theorem lpPointwiseLinearIsometryEquiv_mul_apply (U V : E ≃ₗᵢ[ℂ] E)
    (f : Lp E p μ) :
    lpPointwiseLinearIsometryEquiv (U * V) f =
      lpPointwiseLinearIsometryEquiv U (lpPointwiseLinearIsometryEquiv V f) := by
  apply Lp.ext
  filter_upwards [lpPointwiseLinearIsometryEquiv_apply_ae (U * V) f,
    lpPointwiseLinearIsometryEquiv_apply_ae U (lpPointwiseLinearIsometryEquiv V f),
    lpPointwiseLinearIsometryEquiv_apply_ae V f] with x huv hu hv
  rw [huv, hu, hv]
  rfl

/-- Pointwise application is a homomorphism on the group of value-space unitaries. -/
def lpPointwiseLinearIsometryEquivMonoidHom :
    (E ≃ₗᵢ[ℂ] E) →* (Lp E p μ ≃ₗᵢ[ℂ] Lp E p μ) where
  toFun := lpPointwiseLinearIsometryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change lpPointwiseLinearIsometryEquiv (LinearIsometryEquiv.refl ℂ E) f = f
    apply Lp.ext
    filter_upwards [lpPointwiseLinearIsometryEquiv_apply_ae
      (LinearIsometryEquiv.refl ℂ E) f] with x hx
    simpa using hx
  map_mul' U V := by
    apply LinearIsometryEquiv.ext
    exact lpPointwiseLinearIsometryEquiv_mul_apply U V

section L2

/-- Lift a unitary representation on the value space to its pointwise representation on
Bochner `L²`. -/
def lpPointwise (π : UnitaryRepresentation G E) :
    UnitaryRepresentation G (Lp E 2 μ) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    ((lpPointwiseLinearIsometryEquivMonoidHom (p := 2) (μ := μ)).comp
      (Unitary.linearIsometryEquiv.toMonoidHom.comp π))

/-- The lifted representation applies the value-space unitary pointwise, a.e. -/
theorem lpPointwise_apply_ae (π : UnitaryRepresentation G E) (g : G)
    (f : Lp E 2 μ) :
    ((π.lpPointwise (μ := μ) g : unitary (Lp E 2 μ →L[ℂ] Lp E 2 μ)) :
        Lp E 2 μ →L[ℂ] Lp E 2 μ) f =ᵐ[μ]
      fun x ↦ (π g : E →L[ℂ] E) (f x) := by
  exact lpPointwiseLinearIsometryEquiv_apply_ae
    (Unitary.linearIsometryEquiv (π g)) f

end L2

/-- Two commuting unitary representations on one Hilbert space combine to a unitary
representation of the product group. -/
def prodOfCommute (π₁ : UnitaryRepresentation G₁ H)
    (π₂ : UnitaryRepresentation G₂ H)
    (hcomm : ∀ g₁ g₂, Commute (π₁ g₁) (π₂ g₂)) :
    UnitaryRepresentation (G₁ × G₂) H :=
  π₁.noncommCoprod π₂ hcomm

@[simp]
theorem prodOfCommute_apply (π₁ : UnitaryRepresentation G₁ H)
    (π₂ : UnitaryRepresentation G₂ H)
    (hcomm : ∀ g₁ g₂, Commute (π₁ g₁) (π₂ g₂)) (g : G₁ × G₂) :
    prodOfCommute π₁ π₂ hcomm g = π₁ g.1 * π₂ g.2 := rfl

section FiniteOutputIrreducibility

variable {A : Type*} [Group A] [FiniteDimensional ℂ E]

/-- A finite-dimensional form of irreducibility of an outer product, proved directly on Bochner
`L²` without a completed Hilbert tensor product.

The representation `ρ` on vector-valued `L²` must be natural with respect to the coordinate
embeddings and projections for its scalar counterpart `ρ₀`.  For an invariant closed subspace,
the matrix coefficients of its orthogonal projection then commute with `ρ₀`, so Schur's lemma
makes them scalar.  Finite coordinate reconstruction makes the projection the pointwise lift of
one value-space operator, and a second application of Schur to `π` makes that operator scalar.
Idempotence leaves only the zero and identity projections. -/
theorem prodOfCommute_isTopologicallyIrreducible_of_finiteDimensional
    (π : UnitaryRepresentation G E)
    (ρ : UnitaryRepresentation A (Lp E 2 μ))
    (ρ₀ : UnitaryRepresentation A (Lp ℂ 2 μ))
    (hEmbed : ∀ a v,
      (ρ a : Lp E 2 μ →L[ℂ] Lp E 2 μ) ∘L
          ContinuousLinearMap.lpCoordinateEmbedding (q := 2) (ν := μ) v =
        ContinuousLinearMap.lpCoordinateEmbedding (q := 2) (ν := μ) v ∘L
          (ρ₀ a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
    (hProject : ∀ a v,
      ContinuousLinearMap.lpCoordinateProjection (q := 2) (ν := μ) v ∘L
          (ρ a : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
        (ρ₀ a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ∘L
          ContinuousLinearMap.lpCoordinateProjection (q := 2) (ν := μ) v)
    (hcomm : ∀ g a, Commute (π.lpPointwise (μ := μ) g) (ρ a))
    (hπ : π.IsTopologicallyIrreducible)
    (hρ₀ : ρ₀.IsTopologicallyIrreducible) :
    (prodOfCommute (π.lpPointwise (μ := μ)) ρ hcomm).IsTopologicallyIrreducible := by
  let prodRep := prodOfCommute (π.lpPointwise (μ := μ)) ρ hcomm
  letI : Nontrivial E := hπ.1
  letI : Nontrivial (Lp ℂ 2 μ) := hρ₀.1
  have hnontrivial : Nontrivial (Lp E 2 μ) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    obtain ⟨v : E, hv⟩ := exists_ne (0 : E)
    have hvmap : ContinuousLinearMap.toSpanSingleton ℂ v ≠ 0 := by
      intro hzero
      have hone := DFunLike.congr_fun hzero (1 : ℂ)
      have : v = 0 := by simpa using hone
      exact hv this
    have hvlift : ContinuousLinearMap.lpCoordinateEmbedding
        (K := ℂ) (V := E) (q := 2) (ν := μ) v ≠ 0 := by
      intro hzero
      apply hvmap
      apply ContinuousLinearMap.compLpL_injective
        (K := ℂ) (V := ℂ) (W := E) (q := 2) (ν := μ)
      simpa [ContinuousLinearMap.lpCoordinateEmbedding] using hzero
    exact hvlift (Subsingleton.elim _ _)
  letI : Nontrivial (Lp E 2 μ) := hnontrivial
  refine ⟨hnontrivial, ?_⟩
  intro K hK
  let P : Lp E 2 μ →L[ℂ] Lp E 2 μ := K.toSubmodule.starProjection
  have hP : prodRep.Commutes P :=
    (prodRep.isInvariant_iff_starProjection_commutes K).mp hK
  have hPρ (a : A) :
      P ∘L (ρ a : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
        (ρ a : Lp E 2 μ →L[ℂ] Lp E 2 μ) ∘L P := by
    simpa [prodRep] using hP (1, a)
  have hPπ (g : G) :
      P ∘L (π.lpPointwise (μ := μ) g : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
        (π.lpPointwise (μ := μ) g : Lp E 2 μ →L[ℂ] Lp E 2 μ) ∘L P := by
    simpa [prodRep] using hP (g, 1)
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E := stdOrthonormalBasis ℂ E
  have hcoeff (i j : Fin (Module.finrank ℂ E)) : ∃ c : ℂ,
      ContinuousLinearMap.lpCoordinateProjection (q := 2) (ν := μ) (b i) ∘L P ∘L
          ContinuousLinearMap.lpCoordinateEmbedding (q := 2) (ν := μ) (b j) =
        c • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
    apply ρ₀.hasSchurProperty_of_isTopologicallyIrreducible hρ₀
    intro a
    apply ContinuousLinearMap.ext
    intro f
    change ContinuousLinearMap.lpCoordinateProjection (b i)
        (P (ContinuousLinearMap.lpCoordinateEmbedding (b j)
          ((ρ₀ a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) f))) =
      (ρ₀ a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
        (ContinuousLinearMap.lpCoordinateProjection (b i)
          (P (ContinuousLinearMap.lpCoordinateEmbedding (b j) f)))
    have hembed := DFunLike.congr_fun (hEmbed a (b j)) f
    have hproj := DFunLike.congr_fun (hProject a (b i))
      (P (ContinuousLinearMap.lpCoordinateEmbedding (b j) f))
    have hp := DFunLike.congr_fun (hPρ a)
      (ContinuousLinearMap.lpCoordinateEmbedding (b j) f)
    simp only [ContinuousLinearMap.comp_apply] at hembed hproj hp
    rw [← hembed, hp, hproj]
  obtain ⟨C, hPC⟩ :=
    ContinuousLinearMap.exists_eq_compLpL_of_matrixCoefficient_scalar b P hcoeff
  have hpointwise (g : G) :
      (π.lpPointwise (μ := μ) g : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
        (π g : E →L[ℂ] E).compLpL 2 μ := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [π.lpPointwise_apply_ae g f,
      (π g : E →L[ℂ] E).coeFn_compLpL f] with x hπx hgx
    exact hπx.trans hgx.symm
  have hCcomm : π.Commutes C := by
    intro g
    apply ContinuousLinearMap.compLpL_injective (q := 2) (ν := μ)
    change (C.comp (π g : E →L[ℂ] E)).compLpL 2 μ =
      ((π g : E →L[ℂ] E).comp C).compLpL 2 μ
    rw [ContinuousLinearMap.comp_compLpL, ContinuousLinearMap.comp_compLpL]
    rw [← hpointwise g, ← hPC]
    exact hPπ g
  obtain ⟨c, hC⟩ := π.hasSchurProperty_of_isTopologicallyIrreducible hπ C hCcomm
  have hPscalar : P = c • ContinuousLinearMap.id ℂ (Lp E 2 μ) := by
    rw [hPC, hC, ContinuousLinearMap.smul_compLpL,
      ContinuousLinearMap.id_compLpL]
  by_cases hc : c = 0
  · left
    apply le_antisymm
    · intro x hx
      have hxP : P x = x := K.toSubmodule.starProjection_eq_self_iff.mpr hx
      rw [hPscalar, hc] at hxP
      simpa using hxP.symm
    · exact bot_le
  · have hc1 : c = 1 := by
      obtain ⟨x : Lp E 2 μ, hx⟩ := exists_ne (0 : Lp E 2 μ)
      have hidem : P (P x) = P x := by
        exact DFunLike.congr_fun K.toSubmodule.isIdempotentElem_starProjection x
      rw [hPscalar] at hidem
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul] at hidem
      have hmul : c * c = c := by
        apply (smul_left_injective ℂ hx)
        exact hidem
      apply mul_left_cancel₀ hc
      simpa using hmul
    right
    apply top_unique
    intro x hx
    apply K.toSubmodule.starProjection_eq_self_iff.mp
    change P x = x
    rw [hPscalar, hc1]
    simp

end FiniteOutputIrreducibility

end UnitaryRepresentation
