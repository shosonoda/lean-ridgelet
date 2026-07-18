/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Operator.GeneralSolution

/-!
# Synthesis transported through unitary coordinates

This file is the abstract operator-theoretic layer of the L2 manuscript.  A unitary coordinate
map `T : G ≃ₗᵢ[ℂ] L²(X; H)` transports the pointwise lift `\widetilde L` from Bochner coordinates
to the parameter Hilbert space `G`.  No analytic realization of `T` is assumed or stored in a
structure; concrete transforms can instantiate the equivalence after their unitarity is proved.
-/

@[expose] public section

noncomputable section

open scoped InnerProduct ComplexConjugate lp
open MeasureTheory InnerProductSpace

namespace LeanRidgelet

variable {α H G : Type*} [MeasurableSpace α] (μ : Measure α)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The abstract synthesis operator `S = \widetilde L T`. -/
def unitarySynthesis (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    G →L[ℂ] L2 α μ :=
  fiberSynthesis μ L ∘L (T : G →L[ℂ] BochnerL2 α H μ)

/-- The abstract ridgelet map `R_h = T* J_h`.  For a unitary equivalence, `T* = T⁻¹`. -/
def unitaryRidgelet (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (h : H) :
    L2 α μ →L[ℂ] G :=
  (T.symm : BochnerL2 α H μ →L[ℂ] G) ∘L fiberRidgelet μ h

omit [CompleteSpace H] [CompleteSpace G] in
@[simp]
theorem unitarySynthesis_apply (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) (γ : G) :
    unitarySynthesis μ T L γ = fiberSynthesis μ L (T γ) :=
  rfl

omit [CompleteSpace H] [CompleteSpace G] in
@[simp]
theorem unitaryRidgelet_apply (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (h : H) (f : L2 α μ) :
    unitaryRidgelet μ T h f = T.symm (fiberRidgelet μ h f) :=
  rfl

/-- The Hilbert adjoint of a unitary coordinate map is its inverse. -/
theorem adjoint_unitaryCoordinate (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) :
    (T : G →L[ℂ] BochnerL2 α H μ)† =
      (T.symm : BochnerL2 α H μ →L[ℂ] G) :=
  T.adjoint_eq_symm

/-- The adjoint of synthesis is the ridgelet map associated with the Riesz representer. -/
theorem adjoint_unitarySynthesis (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) :
    (unitarySynthesis μ T L)† = unitaryRidgelet μ T (rieszRepresenter L) := by
  rw [unitarySynthesis, ContinuousLinearMap.adjoint_comp, T.adjoint_eq_symm,
    adjoint_fiberSynthesis]
  rfl

omit [CompleteSpace H] [CompleteSpace G] in
/-- Abstract reconstruction: `S R_h = L[h] I`. -/
theorem unitarySynthesis_comp_unitaryRidgelet
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) (h : H) :
    unitarySynthesis μ T L ∘L unitaryRidgelet μ T h =
      L h • ContinuousLinearMap.id ℂ (L2 α μ) := by
  apply ContinuousLinearMap.ext
  intro f
  change fiberSynthesis μ L (T (T.symm (fiberRidgelet μ h f))) = _
  rw [T.apply_symm_apply]
  exact congrArg (fun A : L2 α μ →L[ℂ] L2 α μ => A f)
    (fiberSynthesis_comp_fiberRidgelet μ L h)

/-- Synthesis composed with its adjoint is scalar multiplication by `c_L`. -/
theorem unitarySynthesis_comp_adjoint
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    unitarySynthesis μ T L ∘L (unitarySynthesis μ T L)† =
      (fiberNormalization L : ℂ) • ContinuousLinearMap.id ℂ (L2 α μ) := by
  rw [adjoint_unitarySynthesis, unitarySynthesis_comp_unitaryRidgelet,
    apply_rieszRepresenter]

/-- Exact norm identity for the abstract synthesis adjoint. -/
theorem norm_adjoint_unitarySynthesis_sq
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) (f : L2 α μ) :
    ‖((unitarySynthesis μ T L)†) f‖ ^ 2 = fiberNormalization L * ‖f‖ ^ 2 := by
  rw [adjoint_unitarySynthesis, unitaryRidgelet_apply, T.symm.norm_map,
    ← adjoint_fiberSynthesis]
  exact norm_adjoint_fiberSynthesis_sq μ L f

/-- The abstract Moore--Penrose inverse `S† = c_L⁻¹ S*` for nonzero `L`.

Here the name `moorePenroseInverse` distinguishes it from Lean's postfix `†`, which denotes only
the Hilbert adjoint. -/
def unitaryMoorePenroseInverse (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) : L2 α μ →L[ℂ] G :=
  ((fiberNormalization L : ℂ)⁻¹) • (unitarySynthesis μ T L)†

/-- The abstract Moore--Penrose inverse is the coordinate inverse transported by `T⁻¹`. -/
theorem unitaryMoorePenroseInverse_eq_transport
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    unitaryMoorePenroseInverse μ T L =
      (T.symm : BochnerL2 α H μ →L[ℂ] G) ∘L normalizedRightInverse μ L := by
  rw [unitaryMoorePenroseInverse, normalizedRightInverse, adjoint_unitarySynthesis,
    adjoint_fiberSynthesis]
  ext f
  simp

@[simp]
theorem unitaryCoordinate_moorePenroseInverse
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) (f : L2 α μ) :
    T (unitaryMoorePenroseInverse μ T L f) = normalizedRightInverse μ L f := by
  rw [unitaryMoorePenroseInverse_eq_transport]
  simp

/-- For nonzero `L`, the Moore--Penrose inverse is a right inverse of synthesis. -/
theorem unitaryMoorePenroseInverse_rightInverse
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    Function.RightInverse (unitaryMoorePenroseInverse μ T L)
      (unitarySynthesis μ T L) := by
  intro f
  rw [unitarySynthesis_apply, unitaryCoordinate_moorePenroseInverse]
  exact normalizedRightInverse_rightInverse μ hL f

/-- The canonical parameter projection `P = S† S`. -/
def unitaryParameterProjection (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) : G →L[ℂ] G :=
  unitaryMoorePenroseInverse μ T L ∘L unitarySynthesis μ T L

/-- The parameter projection is transported from the coordinate projection. -/
theorem unitaryCoordinate_parameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) (γ : G) :
    T (unitaryParameterProjection μ T L γ) = visibleProjection μ L (T γ) := by
  simp [unitaryParameterProjection, visibleProjection]

theorem isIdempotentElem_unitaryParameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    IsIdempotentElem (unitaryParameterProjection μ T L) := by
  change unitaryParameterProjection μ T L ∘L unitaryParameterProjection μ T L =
    unitaryParameterProjection μ T L
  apply ContinuousLinearMap.ext
  intro γ
  apply T.injective
  simp only [ContinuousLinearMap.comp_apply]
  rw [unitaryCoordinate_parameterProjection, unitaryCoordinate_parameterProjection]
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun A : BochnerL2 α H μ →L[ℂ] BochnerL2 α H μ => A (T γ))
      (show visibleProjection μ L ∘L visibleProjection μ L = visibleProjection μ L from
        isIdempotentElem_visibleProjection μ hL)

/-- The canonical parameter projection is self-adjoint. -/
theorem adjoint_unitaryParameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    (unitaryParameterProjection μ T L)† = unitaryParameterProjection μ T L := by
  rw [unitaryParameterProjection, unitaryMoorePenroseInverse,
    ContinuousLinearMap.adjoint_comp, map_smulₛₗ,
    ContinuousLinearMap.adjoint_adjoint]
  simp

theorem isSelfAdjoint_unitaryParameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    IsSelfAdjoint (unitaryParameterProjection μ T L) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact adjoint_unitaryParameterProjection μ T L

/-- The kernel of the canonical parameter projection is the synthesis kernel. -/
theorem ker_unitaryParameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    (unitaryParameterProjection μ T L).ker = (unitarySynthesis μ T L).ker := by
  ext γ
  constructor
  · intro hγ
    change unitaryParameterProjection μ T L γ = 0 at hγ
    change unitarySynthesis μ T L γ = 0
    calc
      unitarySynthesis μ T L γ = unitarySynthesis μ T L
          (unitaryMoorePenroseInverse μ T L (unitarySynthesis μ T L γ)) :=
        (unitaryMoorePenroseInverse_rightInverse μ T hL
          (unitarySynthesis μ T L γ)).symm
      _ = unitarySynthesis μ T L (unitaryParameterProjection μ T L γ) := rfl
      _ = 0 := by rw [hγ, map_zero]
  · intro hγ
    change unitarySynthesis μ T L γ = 0 at hγ
    change unitaryMoorePenroseInverse μ T L (unitarySynthesis μ T L γ) = 0
    rw [hγ, map_zero]

/-- The range of the canonical projection is the orthogonal complement of the synthesis kernel. -/
theorem range_unitaryParameterProjection
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0) :
    (unitaryParameterProjection μ T L).range = (unitarySynthesis μ T L).kerᗮ := by
  let P := unitaryParameterProjection μ T L
  have hP : IsIdempotentElem P := isIdempotentElem_unitaryParameterProjection μ T hL
  calc
    P.range = P.range.topologicalClosure := by
      apply SetLike.coe_injective
      simpa only [Submodule.topologicalClosure_coe] using
        (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP).closure_eq.symm
    _ = P.kerᗮ := by
      symm
      calc
        P.kerᗮ = (P†).range.topologicalClosure := P.orthogonal_ker
        _ = P.range.topologicalClosure := by
          rw [adjoint_unitaryParameterProjection]
    _ = (unitarySynthesis μ T L).kerᗮ := by
      rw [ker_unitaryParameterProjection μ T hL]

omit [CompleteSpace H] [CompleteSpace G] in
/-- Unitary coordinates identify the synthesis kernel with the coordinate-side pointwise kernel. -/
theorem map_ker_unitarySynthesis
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) :
    (unitarySynthesis μ T L).ker.map T.toLinearEquiv.toLinearMap =
      (fiberSynthesis μ L).ker := by
  ext u
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact hγ
  · intro hu
    refine ⟨T.symm u, ?_, ?_⟩
    · simpa [unitarySynthesis] using hu
    · simp

omit [CompleteSpace H] [CompleteSpace G] in
/-- Pointwise characterization of the transported null space. -/
theorem mem_ker_unitarySynthesis_iff
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ) (γ : G) :
    γ ∈ LinearMap.ker (unitarySynthesis μ T L).toLinearMap ↔
      ∀ᵐ x ∂μ, L ((T γ) x) = 0 := by
  exact mem_ker_fiberSynthesis_iff μ L (T γ)

/-- Every solution is the canonical solution plus an element of the synthesis kernel. -/
theorem unitarySolution_iff_kernel_translate
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0)
    (f : L2 α μ) (γ : G) :
    unitarySynthesis μ T L γ = f ↔
      γ - unitaryMoorePenroseInverse μ T L f ∈
        LinearMap.ker (unitarySynthesis μ T L).toLinearMap := by
  change unitarySynthesis μ T L γ = f ↔
    unitarySynthesis μ T L (γ - unitaryMoorePenroseInverse μ T L f) = 0
  rw [map_sub, unitaryMoorePenroseInverse_rightInverse μ T hL, sub_eq_zero]

/-- Pythagoras identity for the abstract parameter-space solution decomposition. -/
theorem unitaryMoorePenroseInverse_pythagorean
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0)
    (f : L2 α μ) (γ : G) (hγ : unitarySynthesis μ T L γ = f) :
    ‖γ‖ ^ 2 = ‖unitaryMoorePenroseInverse μ T L f‖ ^ 2 +
      ‖γ - unitaryMoorePenroseInverse μ T L f‖ ^ 2 := by
  have hcoordinate : fiberSynthesis μ L (T γ) = f := hγ
  have hp := normalizedRightInverse_pythagorean μ hL f (T γ) hcoordinate
  calc
    ‖γ‖ ^ 2 = ‖T γ‖ ^ 2 := by rw [T.norm_map]
    _ = ‖normalizedRightInverse μ L f‖ ^ 2 +
        ‖T γ - normalizedRightInverse μ L f‖ ^ 2 := hp
    _ = ‖unitaryMoorePenroseInverse μ T L f‖ ^ 2 +
        ‖γ - unitaryMoorePenroseInverse μ T L f‖ ^ 2 := by
      rw [← unitaryCoordinate_moorePenroseInverse μ T L f, ← map_sub,
        T.norm_map, T.norm_map]

/-- The abstract Moore--Penrose solution is the unique minimum-norm solution. -/
theorem unitaryMoorePenroseInverse_unique_minimal
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) {L : H →L[ℂ] ℂ} (hL : L ≠ 0)
    (f : L2 α μ) :
    ∀ γ : G,
      unitarySynthesis μ T L γ = f →
      ‖unitaryMoorePenroseInverse μ T L f‖ ≤ ‖γ‖ ∧
        (‖unitaryMoorePenroseInverse μ T L f‖ = ‖γ‖ →
          unitaryMoorePenroseInverse μ T L f = γ) := by
  intro γ hγ
  have hcoordinate : fiberSynthesis μ L (T γ) = f := hγ
  obtain ⟨hle, hunique⟩ := normalizedRightInverse_unique_minimal μ hL f (T γ) hcoordinate
  constructor
  · simpa only [← unitaryCoordinate_moorePenroseInverse μ T L f, T.norm_map] using hle
  · intro heq
    apply T.injective
    rw [unitaryCoordinate_moorePenroseInverse]
    apply hunique
    simpa only [← unitaryCoordinate_moorePenroseInverse μ T L f, T.norm_map] using heq

section Series

variable {ι : Type*}

/-- Coefficient vectors of an abstract parameter are the coordinate-side fiber coefficients. -/
def unitaryCoefficient (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (e : L2 α μ) (γ : G) : H :=
  fiberCoefficient μ e (T γ)

omit [CompleteSpace G] in
/-- Hilbert-basis expansion in the abstract parameter space. -/
theorem hasSum_unitaryRidgelet_coefficients
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (b : HilbertBasis ι ℂ (L2 α μ)) (γ : G) :
    HasSum (fun i => unitaryRidgelet μ T (unitaryCoefficient μ T (b i) γ) (b i)) γ := by
  have hsum := (T.symm : BochnerL2 α H μ →L[ℂ] G).hasSum
    (hasSum_fiberRidgelet_coefficients μ b (T γ))
  simpa [unitaryCoefficient, unitaryRidgelet] using hsum

omit [CompleteSpace G] in
/-- Parseval identity for coefficient vectors in the abstract parameter space. -/
theorem hasSum_norm_sq_unitaryCoefficient
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (b : HilbertBasis ι ℂ (L2 α μ)) (γ : G) :
    HasSum (fun i => ‖unitaryCoefficient μ T (b i) γ‖ ^ 2) (‖γ‖ ^ 2) := by
  simpa [unitaryCoefficient, T.norm_map] using
    hasSum_norm_sq_fiberCoefficient μ b (T γ)

omit [CompleteSpace G] in
/-- Coefficient vectors in the unitary ridgelet expansion are unique. -/
theorem eq_unitaryCoefficient_of_hasSum_unitaryRidgelet
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (b : HilbertBasis ι ℂ (L2 α μ))
    (h : ι → H) (γ : G)
    (hq : HasSum (fun i => unitaryRidgelet μ T (h i) (b i)) γ) (i : ι) :
    h i = unitaryCoefficient μ T (b i) γ := by
  have hmap := (T : G →L[ℂ] BochnerL2 α H μ).hasSum hq
  apply eq_fiberCoefficient_of_hasSum_fiberRidgelet μ b h (T γ)
  simpa [unitaryRidgelet] using hmap

omit [CompleteSpace G] in
/-- Coefficients of an abstract null element lie in `ker L`. -/
theorem apply_unitaryCoefficient_eq_zero_of_mem_ker
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ)
    (b : HilbertBasis ι ℂ (L2 α μ)) (γ : G)
    (hγ : γ ∈ LinearMap.ker (unitarySynthesis μ T L).toLinearMap) (i : ι) :
    L (unitaryCoefficient μ T (b i) γ) = 0 := by
  exact apply_fiberCoefficient_eq_zero_of_mem_ker μ L b (T γ) hγ i

omit [CompleteSpace G] in
/-- A parameter is null exactly when every Hilbert-basis coefficient lies in `ker L`. -/
theorem mem_ker_unitarySynthesis_iff_coefficients
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ)
    (b : HilbertBasis ι ℂ (L2 α μ)) (γ : G) :
    γ ∈ LinearMap.ker (unitarySynthesis μ T L).toLinearMap ↔
      ∀ i, L (unitaryCoefficient μ T (b i) γ) = 0 := by
  constructor
  · intro hγ i
    exact apply_unitaryCoefficient_eq_zero_of_mem_ker μ T L b γ hγ i
  · intro hcoeff
    change unitarySynthesis μ T L γ = 0
    have hmap := (unitarySynthesis μ T L).hasSum
      (hasSum_unitaryRidgelet_coefficients μ T b γ)
    have hterms :
        (fun i => unitarySynthesis μ T L
          (unitaryRidgelet μ T (unitaryCoefficient μ T (b i) γ) (b i))) =
        fun _ : ι => (0 : L2 α μ) := by
      funext i
      change (unitarySynthesis μ T L ∘L
        unitaryRidgelet μ T (unitaryCoefficient μ T (b i) γ)) (b i) = 0
      rw [unitarySynthesis_comp_unitaryRidgelet]
      simp [hcoeff i]
    rw [hterms] at hmap
    exact (hasSum_zero : HasSum (fun _ : ι => (0 : L2 α μ)) 0).unique hmap |>.symm

section NullSeries

variable {κ : Type*}

/-- The `i`th coefficient vector of an abstract null parameter, bundled in `ker L`. -/
def unitaryKernelCoefficient (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) (b : HilbertBasis ι ℂ (L2 α μ))
    (γ : G) (hγ : γ ∈ (unitarySynthesis μ T L).ker) (i : ι) : L.ker :=
  kernelFiberCoefficient μ L b (T γ) (by
    change fiberSynthesis μ L (T γ) = 0
    exact hγ) i

/-- The flattened null coefficients of an abstract parameter as an element of `ℓ²(I × J)`. -/
def unitaryNullDoubleCoefficients (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ)
    (L : H →L[ℂ] ℂ) (b : HilbertBasis ι ℂ (L2 α μ))
    (d : HilbertBasis κ ℂ L.ker) (γ : G)
    (hγ : γ ∈ (unitarySynthesis μ T L).ker) : ℓ²(ι × κ, ℂ) :=
  fiberNullDoubleCoefficients μ L b d (T γ) (by
    change fiberSynthesis μ L (T γ) = 0
    exact hγ)

omit [CompleteSpace G] in
@[simp]
theorem unitaryNullDoubleCoefficients_apply
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ)
    (b : HilbertBasis ι ℂ (L2 α μ)) (d : HilbertBasis κ ℂ L.ker)
    (γ : G) (hγ : γ ∈ (unitarySynthesis μ T L).ker) (p : ι × κ) :
    unitaryNullDoubleCoefficients μ T L b d γ hγ p =
      d.repr (unitaryKernelCoefficient μ T L b γ hγ p.1) p.2 := by
  rfl

omit [CompleteSpace G] in
/-- Every abstract null parameter has the unconditional `I × J` ridgelet expansion associated
with Hilbert bases of `L²(X)` and `ker L`. -/
theorem hasSum_unitaryRidgelet_kernelBasis
    (T : G ≃ₗᵢ[ℂ] BochnerL2 α H μ) (L : H →L[ℂ] ℂ)
    (b : HilbertBasis ι ℂ (L2 α μ)) (d : HilbertBasis κ ℂ L.ker)
    (γ : G) (hγ : γ ∈ (unitarySynthesis μ T L).ker) :
    HasSum (fun p : ι × κ =>
      unitaryNullDoubleCoefficients μ T L b d γ hγ p •
        unitaryRidgelet μ T ((d p.2 : L.ker) : H) (b p.1)) γ := by
  have hcoordinate : T γ ∈ (fiberSynthesis μ L).ker := by
    change fiberSynthesis μ L (T γ) = 0
    exact hγ
  have hsum := (T.symm : BochnerL2 α H μ →L[ℂ] G).hasSum
    (hasSum_fiberRidgelet_kernelBasis μ L b d (T γ) hcoordinate)
  simpa [unitaryNullDoubleCoefficients, unitaryRidgelet] using hsum

end NullSeries

end Series

end LeanRidgelet
