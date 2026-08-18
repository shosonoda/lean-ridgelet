/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.HA.QuadraticMeasure
public import LeanRidgelet.ToMathlib.RelativelyInvariantDensity
public import LeanRidgelet.ToMathlib.SymmetricCongruenceDet

/-!
# A relatively invariant parameter measure for the quadratic-form example

`LeanRidgelet.HA.QuadraticMeasure` equips the quadratic parameter space of Section 7 of
arXiv:2405.13682 with an additive Haar measure, whose Radon--Nikodym density under the parameter
action is the absolute determinant of that action.  By
`LeanRidgelet.det_quadraticParameterLinearEquiv` this determinant carries the extra congruence
factor of the symmetric block, so it is *not* the reciprocal of the data density
`LeanRidgelet.affineDataJacobian`, and the quasi-invariant Bochner identities of
`LeanRidgelet.HA.BochnerIntertwining` only apply in their character-twisted form.  This file
repairs the balance by replacing the Haar measure by a relatively invariant one.

Write `m` for `Module.finrank ℝ E`.  The determinant of the symmetric coefficient is a relative
invariant of the parameter action: congruence by `M` multiplies it by `(det M) ^ 2`, so the linear
part `L` of an affine `g` multiplies it by `(det L)⁻¹ ^ 2`
(`LeanRidgelet.quadraticSymmetricDet_smul`).  Weighting an additive Haar measure by
`|det A| ^ (-(m + 1) / 2)` therefore multiplies the measure by a determinant character which
cancels the congruence factor exactly: the pushforward of the weighted measure under the inverse
parameter action has the constant density `‖det L‖₊⁻¹`, the reciprocal of the data density.  With
the balance restored, the *untwisted* synthesis and ridgelet intertwining identities apply to the
quadratic feature.

## Main results

* `LeanRidgelet.quadraticSymmetricDet_smul`: the relative invariance of the symmetric determinant.
* `LeanRidgelet.quadraticRelativeWeight_smul`: the transformation law of the weight.
* `LeanRidgelet.quadraticRelativeMeasure`: the relatively invariant parameter measure, together
  with its σ-finiteness and the invariance
  (`LeanRidgelet.preimage_smul_quadraticNondegenerate`) of the locus it is supported on.
* `LeanRidgelet.quadraticRelativeParameter_group_map_eq_withDensity`: the balance, in the shape the
  generic quasi-invariant constructions consume.
* `LeanRidgelet.quadraticRelativeParameterLpUnitaryRepresentation`: the corrected unitary
  representation of the affine group on parameter `L²`.
* `LeanRidgelet.quadraticRelativeBochnerSynthesis_intertwines` and
  `LeanRidgelet.quadraticRelativeBochnerRidgelet_intertwines`: the untwisted quasi-invariant
  Bochner identities for the quadratic feature.

## The congruence determinant

The computation rests on `det (quadraticCongr M) = (det M) ^ (m + 1)`, the determinant of
congruence on the symmetric block.  That is `LeanRidgelet.det_quadraticCongr`, transported here
from the basis-free form `ContinuousLinearMap.det_congrSelfAdjoint` of
`LeanRidgelet.ToMathlib.SymmetricCongruenceDet`, which in turn comes from the matrix computation
over a basis of the symmetric matrices.  Nothing in this file is conditional.

## The measure is not locally finite, and that is harmless

The weight `|det A| ^ (-(m + 1) / 2)` blows up along the degenerate locus `det A = 0`.  Transverse
to a smooth point of that hypersurface it behaves like `|t| ^ (-(m + 1) / 2)`, which is integrable
near `t = 0` only when `(m + 1) / 2 < 1`, that is `m = 0`.  So for `m ≥ 1` every neighbourhood of a
degenerate parameter has infinite measure and `LeanRidgelet.quadraticRelativeMeasure` is not
locally finite, hence not an additive Haar measure.  That is unavoidable rather than an artefact:
an additive Haar measure is rescaled by a linear map by the absolute determinant of that map, and
`LeanRidgelet.quadraticParameterJacobian_eq_blocks` says that this is not the character the balance
asks for.  (The failure of local finiteness is a remark here; it is not formalized.)

Local finiteness is never used downstream.  The `L²` construction
`LeanRidgelet.quasiInvariantLpUnitaryRepresentation` needs only `MeasureTheory.SigmaFinite`, and
the Bochner intertwining theorems need only the pushforward identity; both are supplied here.
σ-finiteness holds because a weighted σ-finite measure with an everywhere finite density is
σ-finite, and `ENNReal.ofReal` is finite by construction.

## No case split is needed

Neither the dimension `m = 0` nor the degenerate locus forces a case distinction.  The weight law
`LeanRidgelet.quadraticRelativeWeight_smul` holds at every parameter, degenerate ones included,
because there both of its sides vanish: the real `rpow` of `0` at the negative exponent
`-(m + 1) / 2` is `0`.  And that exponent is negative for every `m`, `m = 0` included, so the
zero-dimensional case needs no separate argument either.

## Deviations from the article

The article writes the parameter measure through the explicit Jacobian of the coordinate change.
Here the degenerate locus `det A = 0` is deleted before the weight is applied.  This is not a loss:
the locus is invariant under the parameter action, so the restriction is compatible with the group
action, and on its complement the weight is finite and strictly positive, so the support of the
measure is exactly the nondegenerate locus.  Deleting it also avoids having to prove that a
determinant hypersurface is Haar-null, which is true but not needed.

As in `LeanRidgelet.HA.QuadraticMeasure`, the quadratic parameter space gets no global measurable
structure here: the measurable and Borel structures of the data space and of the symmetric block
are instance hypotheses, and the product structure follows from `Prod.instMeasurableSpace` and
`Prod.borelSpace`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `ENNReal.ofReal` of an absolute value is the coercion of the nonnegative norm.  This is the
bridge between the `ENNReal.ofReal` form produced by the Haar rescaling lemmas and the `‖·‖₊` form
used by the Radon--Nikodym cocycles. -/
theorem ofReal_abs_eq_coe_nnnorm (r : ℝ) : ENNReal.ofReal |r| = (‖r‖₊ : ℝ≥0∞) := by
  rw [← Real.norm_eq_abs, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

/-! ### The symmetric determinant as a relative invariant -/

/-- The star operation on continuous endomorphisms of a real inner product space preserves
determinants: it is the adjoint, whose matrix is a transpose. -/
theorem det_star_continuousLinearMap (N : E →L[ℝ] E) : (star N).det = N.det := by
  change LinearMap.det ((star N : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.det_adjoint]
  simp

/-- Rebundling a linear equivalence as a continuous endomorphism preserves determinants. -/
theorem det_quadraticCongrEndo (M : E ≃ₗ[ℝ] E) :
    (quadraticCongrEndo M).det = LinearMap.det (M : E →ₗ[ℝ] E) := by
  rw [quadraticCongrEndo]
  change LinearMap.det
    ((LinearMap.toContinuousLinearMap (M : E →ₗ[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
  simp

/-- **The relative invariant.**  Congruence by `M` multiplies the determinant of a symmetric
coefficient by `(det M) ^ 2`, because the two outer factors are adjoint to each other and an
adjoint has the same determinant. -/
theorem det_quadraticCongr_apply (M : E ≃ₗ[ℝ] E) (A : QuadraticSymmetric E) :
    ((quadraticCongr M A : QuadraticSymmetric E) : E →L[ℝ] E).det =
      LinearMap.det (M : E →ₗ[ℝ] E) ^ 2 * (A : E →L[ℝ] E).det := by
  have hmul : ∀ N P : E →L[ℝ] E, (N * P).det = N.det * P.det := by
    intro N P
    change LinearMap.det ((N * P : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
    rw [ContinuousLinearMap.toLinearMap_mul, map_mul]
  rw [quadraticCongr_coe, hmul, hmul, det_star_continuousLinearMap, det_quadraticCongrEndo]
  ring

/-- The determinant of the symmetric coefficient of a quadratic parameter. -/
def quadraticSymmetricDet (ξ : QuadraticParameter E) : ℝ := (ξ.1 : E →L[ℝ] E).det

/-- **Relative invariance of the symmetric determinant.**  The parameter action of `g` acts on the
symmetric block by congruence with `g.linear.symm`, so it multiplies the symmetric determinant by
the square of the reciprocal determinant of the linear part. -/
theorem quadraticSymmetricDet_smul (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticSymmetricDet (g • ξ) =
      (LinearMap.det (g.linear : E →ₗ[ℝ] E))⁻¹ ^ 2 * quadraticSymmetricDet ξ := by
  change ((quadraticCongr g.linear.symm ξ.1 : QuadraticSymmetric E) : E →L[ℝ] E).det = _
  rw [det_quadraticCongr_apply, LinearEquiv.det_coe_symm]
  rfl

/-- The nondegenerate locus of quadratic parameters, that is, those whose symmetric coefficient is
invertible.  This is the support of the relatively invariant measure below. -/
def quadraticNondegenerate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Set (QuadraticParameter E) :=
  {ξ | quadraticSymmetricDet ξ ≠ 0}

/-- Membership in the nondegenerate locus is unchanged by the parameter action, since the action
multiplies the symmetric determinant by a nonzero factor. -/
theorem mem_quadraticNondegenerate_smul_iff (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    g • ξ ∈ quadraticNondegenerate E ↔ ξ ∈ quadraticNondegenerate E := by
  have hg : (LinearMap.det (g.linear : E →ₗ[ℝ] E))⁻¹ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (inv_ne_zero g.linear.isUnit_det'.ne_zero)
  change quadraticSymmetricDet (g • ξ) ≠ 0 ↔ quadraticSymmetricDet ξ ≠ 0
  rw [quadraticSymmetricDet_smul]
  exact ⟨fun h h0 ↦ h (by rw [h0, mul_zero]), fun h ↦ mul_ne_zero hg h⟩

/-- **Invariance of the degenerate locus.**  The nondegenerate locus is exactly its own preimage
under the parameter action, so restricting a measure to it is compatible with the action. -/
theorem preimage_smul_quadraticNondegenerate (g : E ≃ᵃ[ℝ] E) :
    (fun ξ : QuadraticParameter E ↦ g • ξ) ⁻¹' quadraticNondegenerate E =
      quadraticNondegenerate E :=
  Set.ext fun ξ ↦ mem_quadraticNondegenerate_smul_iff g ξ

/-! ### The relatively invariant weight -/

/-- The weight defining the relatively invariant parameter measure: the power
`-(m + 1) / 2` of the absolute symmetric determinant, where `m = Module.finrank ℝ E`.  The
exponent is chosen so that the weight transforms by `‖det L‖₊ ^ (m + 1)`, which is exactly what
cancels the congruence factor in the parameter Jacobian. -/
def quadraticRelativeWeight (ξ : QuadraticParameter E) : ℝ≥0∞ :=
  ENNReal.ofReal (|quadraticSymmetricDet ξ| ^ (-(Module.finrank ℝ E + 1 : ℝ) / 2))

/-- **The weight law.**  The parameter action of `g` multiplies the weight by
`‖det L‖₊ ^ (m + 1)`, where `L` is the linear part of `g`.  No nondegeneracy is needed: on the
degenerate locus both sides vanish. -/
theorem quadraticRelativeWeight_smul (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticRelativeWeight (g • ξ) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) ^ (Module.finrank ℝ E + 1) *
        quadraticRelativeWeight ξ := by
  set d : ℝ := LinearMap.det (g.linear : E →ₗ[ℝ] E) with hd
  have hd0 : d ≠ 0 := g.linear.isUnit_det'.ne_zero
  have hdpos : (0 : ℝ) < |d| := abs_pos.mpr hd0
  set p : ℝ := -(Module.finrank ℝ E + 1 : ℝ) / 2 with hp
  have habs : |quadraticSymmetricDet (g • ξ)| = (|d| ^ 2)⁻¹ * |quadraticSymmetricDet ξ| := by
    rw [quadraticSymmetricDet_smul, abs_mul, abs_pow, abs_inv, ← hd, inv_pow]
  have hsq : (|d| ^ 2 : ℝ) = |d| ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfac : ((|d| ^ 2)⁻¹ : ℝ) ^ p = |d| ^ (Module.finrank ℝ E + 1) := by
    rw [hsq, ← Real.rpow_neg (abs_nonneg d), ← Real.rpow_mul (abs_nonneg d)]
    rw [show -(2 : ℝ) * p = ((Module.finrank ℝ E + 1 : ℕ) : ℝ) by rw [hp]; push_cast; ring]
    rw [Real.rpow_natCast]
  rw [quadraticRelativeWeight, quadraticRelativeWeight, ← hp, habs,
    Real.mul_rpow (by positivity) (abs_nonneg _), hfac,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (abs_nonneg d),
    ofReal_abs_eq_coe_nnnorm]

/-! ### The parameter Jacobian and the balance -/

/-- The constant Radon--Nikodym density of the inverse quadratic parameter action for the
relatively invariant measure.  Unlike `LeanRidgelet.quadraticParameterJacobian`, it is the exact
reciprocal of the data density `LeanRidgelet.affineDataJacobian`; it is literally the ridge
parameter Jacobian `LeanRidgelet.affineParameterJacobian` read on quadratic parameters. -/
def quadraticRelativeParameterJacobian (g : E ≃ᵃ[ℝ] E) : QuadraticParameter E → ℝ≥0 :=
  fun _ ↦ ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹

/-- The relative parameter Jacobian is normalized at the identity. -/
@[simp]
theorem quadraticRelativeParameterJacobian_one (ξ : QuadraticParameter E) :
    quadraticRelativeParameterJacobian (1 : E ≃ᵃ[ℝ] E) ξ = 1 := by
  simp only [quadraticRelativeParameterJacobian]
  rw [show (1 : E ≃ᵃ[ℝ] E).linear = LinearEquiv.refl ℝ E by rfl]
  simp

/-- The relative parameter Jacobian obeys the Radon--Nikodym cocycle law. -/
theorem quadraticRelativeParameterJacobian_cocycle (g h : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticRelativeParameterJacobian (g * h) ξ =
      quadraticRelativeParameterJacobian g (h • ξ) *
        quadraticRelativeParameterJacobian h ξ := by
  change ‖LinearMap.det ((g * h).linear : E →ₗ[ℝ] E)‖₊⁻¹ =
    ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ * ‖LinearMap.det (h.linear : E →ₗ[ℝ] E)‖₊⁻¹
  rw [show (g * h).linear = g.linear * h.linear by
    exact (AffineEquiv.linearHom (k := ℝ) (P₁ := E)).map_mul g h]
  change ‖LinearMap.det ((g.linear : E →ₗ[ℝ] E).comp (h.linear : E →ₗ[ℝ] E))‖₊⁻¹ = _
  rw [LinearMap.det_comp, nnnorm_mul, mul_inv_rev]
  exact mul_comm _ _

/-- The relative parameter Jacobian is everywhere nonzero. -/
theorem quadraticRelativeParameterJacobian_ne_zero (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticRelativeParameterJacobian g ξ ≠ 0 := by
  simp only [quadraticRelativeParameterJacobian, ne_eq, inv_eq_zero, nnnorm_eq_zero]
  exact g.linear.isUnit_det'.ne_zero

/-- The parameter density square root is the data-side inverse square-root multiplier: this is the
balance that the Haar parameter measure of `LeanRidgelet.HA.QuadraticMeasure` failed. -/
theorem quadraticRelative_synthesis_balance (g : E ≃ᵃ[ℝ] E) (x : E) (ξ : QuadraticParameter E) :
    ((quadraticRelativeParameterJacobian g ξ).sqrt : ℂ) =
      ((affineDataJacobian g (g.symm x)).sqrt : ℂ)⁻¹ := by
  simp [quadraticRelativeParameterJacobian, affineDataJacobian, NNReal.sqrt_inv]

/-- The data density square root is the parameter-side inverse square-root multiplier. -/
theorem quadraticRelative_ridgelet_balance (g : E ≃ᵃ[ℝ] E) (x : E) (ξ : QuadraticParameter E) :
    ((affineDataJacobian g x).sqrt : ℂ) =
      ((quadraticRelativeParameterJacobian g
        ((quadraticParameterLinearEquiv g).symm ξ)).sqrt : ℂ)⁻¹ := by
  simp [quadraticRelativeParameterJacobian, affineDataJacobian, NNReal.sqrt_inv]

/-- The synthesis balance in the form expected by the generic quasi-invariant theorem. -/
theorem quadraticRelative_synthesis_radonNikodym_balance (g : E ≃ᵃ[ℝ] E) (x : E)
    (ξ : QuadraticParameter E) :
    ((quadraticRelativeParameterJacobian g ξ).sqrt : ℂ) =
      radonNikodymWeight affineDataJacobian g x :=
  quadraticRelative_synthesis_balance g x ξ

/-- The ridgelet balance in the form expected by the generic quasi-invariant theorem. -/
theorem quadraticRelative_ridgelet_radonNikodym_balance (g : E ≃ᵃ[ℝ] E) (x : E)
    (ξ : QuadraticParameter E) :
    ((affineDataJacobian g x).sqrt : ℂ) =
      radonNikodymWeight quadraticRelativeParameterJacobian g ξ :=
  quadraticRelative_ridgelet_balance g x ξ

/-- The symmetric coefficients of a quadratic parameter are the self-adjoint continuous
endomorphisms.  The two are the same subtype with the same module structure, but the instances are
found by different paths, so the identity is bundled here once. -/
def quadraticSymmetricEquivSelfAdjoint :
    QuadraticSymmetric E ≃ₗ[ℝ] selfAdjoint (E →L[ℝ] E) where
  toFun A := ⟨(A : E →L[ℝ] E), A.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun A := ⟨(A : E →L[ℝ] E), A.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The determinant of the congruence on symmetric coefficients is the power `m + 1` of the
determinant of the conjugating map.  This is the congruence-determinant input of the relative
measure, discharged by the general matrix computation of
`Matrix.det_congrMap`: the symmetric coefficients of a quadratic parameter are exactly the
self-adjoint continuous endomorphisms, with the same module structure, so the two congruence maps
agree on the nose. -/
theorem det_quadraticCongr (M : E ≃ₗ[ℝ] E) :
    LinearMap.det
        ((quadraticCongr M : QuadraticSymmetric E ≃ₗ[ℝ] QuadraticSymmetric E) :
          QuadraticSymmetric E →ₗ[ℝ] QuadraticSymmetric E) =
      LinearMap.det (M : E →ₗ[ℝ] E) ^ (Module.finrank ℝ E + 1) := by
  have hmap : ((quadraticCongr M : QuadraticSymmetric E ≃ₗ[ℝ] QuadraticSymmetric E) :
      QuadraticSymmetric E →ₗ[ℝ] QuadraticSymmetric E) =
      (quadraticSymmetricEquivSelfAdjoint (E := E)).symm.toLinearMap ∘ₗ
        ContinuousLinearMap.congrSelfAdjoint (quadraticCongrEndo M) ∘ₗ
          (quadraticSymmetricEquivSelfAdjoint (E := E)).symm.symm.toLinearMap :=
    LinearMap.ext fun A ↦ Subtype.ext rfl
  rw [hmap, LinearMap.det_conj, ContinuousLinearMap.det_congrSelfAdjoint, det_quadraticCongrEndo]

/-- The absolute determinant of the quadratic parameter action: it is the reciprocal of
`‖det L‖₊ ^ (m + 2)`, where `L` is the linear part. -/
theorem nnnorm_det_quadraticParameterLinearEquiv
    (g : E ≃ᵃ[ℝ] E) :
    ‖LinearMap.det
        (quadraticParameterLinearEquiv g : QuadraticParameter E →ₗ[ℝ] QuadraticParameter E)‖₊ =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 2))⁻¹ := by
  rw [det_quadraticParameterLinearEquiv, det_quadraticCongr, LinearEquiv.det_coe_symm, nnnorm_mul,
    nnnorm_pow, nnnorm_inv, ← pow_succ, inv_pow]

omit [FiniteDimensional ℝ E] in
/-- The determinant of the linear part of an inverse affine equivalence is the reciprocal
determinant of the linear part. -/
theorem det_linear_inv (g : E ≃ᵃ[ℝ] E) :
    LinearMap.det ((g⁻¹).linear : E →ₗ[ℝ] E) =
      (LinearMap.det (g.linear : E →ₗ[ℝ] E))⁻¹ := by
  rw [show (g⁻¹).linear = (g.linear)⁻¹ from
    map_inv (AffineEquiv.linearHom (k := ℝ) (P₁ := E)) g]
  exact LinearEquiv.det_coe_symm g.linear

/-! ### The relatively invariant measure -/

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

omit [BorelSpace E] in
/-- The symmetric determinant is measurable, being continuous in the symmetric coefficient. -/
theorem measurable_quadraticSymmetricDet :
    Measurable (quadraticSymmetricDet : QuadraticParameter E → ℝ) :=
  (ContinuousLinearMap.continuous_det.comp continuous_subtype_val).measurable.comp measurable_fst

omit [BorelSpace E] in
/-- The nondegenerate locus is measurable. -/
theorem measurableSet_quadraticNondegenerate :
    MeasurableSet (quadraticNondegenerate E) :=
  (measurable_quadraticSymmetricDet (measurableSet_singleton (0 : ℝ))).compl

omit [BorelSpace E] in
/-- The relatively invariant weight is measurable. -/
theorem measurable_quadraticRelativeWeight :
    Measurable (quadraticRelativeWeight : QuadraticParameter E → ℝ≥0∞) := by
  have habs : Measurable fun ξ : QuadraticParameter E ↦ |quadraticSymmetricDet ξ| :=
    continuous_abs.measurable.comp measurable_quadraticSymmetricDet
  exact ENNReal.measurable_ofReal.comp (habs.pow_const _)

/-- **The relatively invariant parameter measure.**  An additive Haar measure `lam` on the
quadratic parameter space, restricted to the nondegenerate locus and weighted by
`LeanRidgelet.quadraticRelativeWeight`.  It is σ-finite but, for `m ≥ 1`, not locally finite; see
the module docstring. -/
def quadraticRelativeMeasure (lam : Measure (QuadraticParameter E)) :
    Measure (QuadraticParameter E) :=
  (lam.restrict (quadraticNondegenerate E)).withDensity quadraticRelativeWeight

/-- The relatively invariant parameter measure is σ-finite: it is a σ-finite measure weighted by an
everywhere finite density. -/
instance quadraticRelativeMeasure_sigmaFinite (lam : Measure (QuadraticParameter E))
    [SigmaFinite lam] : SigmaFinite (quadraticRelativeMeasure lam) := by
  unfold quadraticRelativeMeasure quadraticRelativeWeight
  infer_instance

/-- The restricted Haar measure is rescaled by the inverse parameter action, the rescaling being
the reciprocal absolute determinant of that action.  This is where the invariance of the
nondegenerate locus is used. -/
theorem quadraticRelative_map_restrict (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    (lam.restrict (quadraticNondegenerate E)).map (fun ξ ↦ g⁻¹ • ξ) =
      ENNReal.ofReal |(LinearMap.det (quadraticParameterLinearEquiv g⁻¹ :
          QuadraticParameter E →ₗ[ℝ] QuadraticParameter E))⁻¹| •
        lam.restrict (quadraticNondegenerate E) := by
  refine Measure.map_restrict_of_map_eq_smul (quadraticParameter_measurable g⁻¹) ?_
    measurableSet_quadraticNondegenerate (preimage_smul_quadraticNondegenerate g⁻¹)
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar lam
    (quadraticParameterLinearEquiv g⁻¹).isUnit_det'.ne_zero

omit [BorelSpace E] [BorelSpace (QuadraticSymmetric E)] in
/-- The constant relative parameter Jacobian is measurable. -/
theorem quadraticRelativeParameterJacobian_measurable (g : E ≃ᵃ[ℝ] E) :
    Measurable (quadraticRelativeParameterJacobian g) := measurable_const

/-- **The balance.**  The relatively invariant parameter measure is strongly quasi-invariant with
the constant Radon--Nikodym density `‖det L‖₊⁻¹`, which is the exact reciprocal of the data density
`LeanRidgelet.affineDataJacobian`.  The congruence factor of
`LeanRidgelet.quadraticParameterJacobian_eq_blocks` is cancelled by the weight, whose
transformation law contributes `‖det L‖₊ ^ (m + 1)` against the `‖det L‖₊ ^ (m + 2)` of the Haar
Jacobian.  Compare `LeanRidgelet.affineParameter_group_map_eq_withDensity`. -/
theorem quadraticRelativeParameter_group_map_eq_withDensity
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) :
    (quadraticRelativeMeasure lam).map (fun ξ ↦ g⁻¹ • ξ) =
      (quadraticRelativeMeasure lam).withDensity
        (fun ξ ↦ (quadraticRelativeParameterJacobian g ξ : ℝ≥0∞)) := by
  have hq0 : ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ≠ 0 := by
    simpa using g.linear.isUnit_det'.ne_zero
  have hqinv : ‖LinearMap.det ((g⁻¹).linear : E →ₗ[ℝ] E)‖₊ =
      ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ := by
    rw [det_linear_inv, nnnorm_inv]
  have hweight : ∀ ξ : QuadraticParameter E,
      quadraticRelativeWeight (g⁻¹ • ξ) =
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ ^ (Module.finrank ℝ E + 1) : ℝ≥0) : ℝ≥0∞) *
          quadraticRelativeWeight ξ := by
    intro ξ
    rw [quadraticRelativeWeight_smul g⁻¹ ξ, hqinv, ENNReal.coe_pow]
  have hdet : ‖LinearMap.det (quadraticParameterLinearEquiv g⁻¹ :
        QuadraticParameter E →ₗ[ℝ] QuadraticParameter E)‖₊ =
      ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 2) := by
    rw [nnnorm_det_quadraticParameterLinearEquiv g⁻¹, hqinv, inv_pow, inv_inv]
  have hmap : (lam.restrict (quadraticNondegenerate E)).map (fun ξ ↦ g⁻¹ • ξ) =
      (((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 2))⁻¹ : ℝ≥0) : ℝ≥0∞) •
        lam.restrict (quadraticNondegenerate E) := by
    rw [quadraticRelative_map_restrict lam g, ofReal_abs_eq_coe_nnnorm, nnnorm_inv, hdet]
  have hpow0 : (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ ^ (Module.finrank ℝ E + 1) : ℝ≥0) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero hq0)
  have hjac : (fun ξ : QuadraticParameter E ↦
        ((quadraticRelativeParameterJacobian g ξ : ℝ≥0) : ℝ≥0∞)) =
      fun _ : QuadraticParameter E ↦
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ : ℝ≥0) : ℝ≥0∞) := rfl
  have hsucc : ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 2) =
      ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 1) *
        ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ := pow_succ _ _
  have hkey : (quadraticRelativeMeasure lam).map (fun ξ ↦ g⁻¹ • ξ) =
      (((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ ^ (Module.finrank ℝ E + 1) : ℝ≥0) :
            ℝ≥0∞)⁻¹ *
          (((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ ^ (Module.finrank ℝ E + 2))⁻¹ : ℝ≥0) :
            ℝ≥0∞)) • quadraticRelativeMeasure lam :=
    Measure.map_withDensity_of_map_eq_smul (quadraticParameter_measurable g⁻¹)
      measurable_quadraticRelativeWeight hmap hweight (ENNReal.coe_ne_zero.mpr hpow0)
      ENNReal.coe_ne_top
  rw [hkey, hjac, withDensity_const]
  congr 1
  rw [← ENNReal.coe_inv hpow0, ← ENNReal.coe_mul, ENNReal.coe_inj, inv_pow, inv_inv, hsucc,
    mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), one_mul]

/-- The Radon--Nikodym-corrected quadratic parameter representation on scalar `L²`, built from the
relatively invariant measure.  Compare `LeanRidgelet.quadraticParameterLpUnitaryRepresentation`,
which uses the Haar measure and therefore a different, unbalanced, cocycle. -/
noncomputable def quadraticRelativeParameterLpUnitaryRepresentation
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] :
    UnitaryRepresentation (E ≃ᵃ[ℝ] E) (Lp ℂ 2 (quadraticRelativeMeasure lam)) :=
  quasiInvariantLpUnitaryRepresentation quadraticRelativeParameterJacobian
    quadraticParameter_measurable
    (quadraticRelativeParameter_group_map_eq_withDensity lam)
    quadraticRelativeParameterJacobian_measurable quadraticRelativeParameterJacobian_ne_zero
    quadraticRelativeParameterJacobian_one quadraticRelativeParameterJacobian_cocycle

/-! ### The quasi-invariant Bochner identities for the quadratic feature -/

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- `LeanRidgelet.quadraticFeature_invariant` restated through the two group actions, which is the
form the generic joint-invariance hypotheses are phrased in. -/
theorem quadraticFeature_smul_invariant (σ : ℝ → ℝ) (g : E ≃ᵃ[ℝ] E) (x : E)
    (ξ : QuadraticParameter E) :
    quadraticFeature σ (g • x) (g • ξ) = quadraticFeature σ x ξ :=
  quadraticFeature_invariant σ g x ξ

/-- A vector-valued quadratic-form feature, the analogue of `LeanRidgelet.affineFeature` for the
quadratic argument.  The Bochner synthesis and ridgelet transforms take values in a complex inner
product space, so the scalar `LeanRidgelet.quadraticFeature` is not directly usable there. -/
def quadraticVectorFeature (σ : ℝ → Y) (x : E) (ξ : QuadraticParameter E) : Y :=
  σ (quadraticArgument x ξ)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (QuadraticSymmetric E)]
  [BorelSpace (QuadraticSymmetric E)] in
/-- A vector-valued quadratic feature is jointly invariant; equivalently, it is jointly
equivariant for the trivial output representation. -/
theorem quadraticVectorFeature_jointInvariant (σ : ℝ → Y) (g : E ≃ᵃ[ℝ] E) (x : E)
    (ξ : QuadraticParameter E) :
    quadraticVectorFeature σ (g • x) (g • ξ) =
      ((1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g : Y →L[ℂ] Y)
        (quadraticVectorFeature σ x ξ) := by
  change σ (quadraticArgument (g x) (quadraticParameterLinearEquiv g ξ)) =
    σ (quadraticArgument x ξ)
  rw [quadraticArgument_invariant]

/-- **The payoff, synthesis half.**  The untwisted quasi-invariant Bochner synthesis identity for
the quadratic feature, available because the relatively invariant parameter measure balances the
data measure exactly.  Compare `LeanRidgelet.affineBochnerSynthesis_intertwines`. -/
theorem quadraticRelativeBochnerSynthesis_intertwines
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (σ : ℝ → Y)
    (g : E ≃ᵃ[ℝ] E) (γ : QuadraticParameter E → ℂ) (x : E) :
    bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ)
        (quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g γ) x =
      quasiUnitaryPullbackAction affineDataJacobian
        (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g
        (bochnerSynthesis (quadraticRelativeMeasure lam) (quadraticVectorFeature σ) γ) x :=
  bochnerSynthesis_quasi_intertwines (quadraticRelativeMeasure lam)
    (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) (quadraticVectorFeature σ)
    affineDataJacobian quadraticRelativeParameterJacobian quadraticParameter_measurable
    (quadraticRelativeParameter_group_map_eq_withDensity lam)
    quadraticRelativeParameterJacobian_measurable quadraticRelativeParameterJacobian_ne_zero
    (quadraticVectorFeature_jointInvariant σ)
    quadraticRelative_synthesis_radonNikodym_balance g γ x

omit [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)] in
/-- **The payoff, ridgelet half.**  The untwisted quasi-invariant Bochner ridgelet identity for the
quadratic feature.  Only the data measure enters, so this half needs neither the parameter measure
nor the congruence-determinant hypothesis; what it needs is the parameter Jacobian of the
relatively invariant measure, through the balance
`LeanRidgelet.quadraticRelative_ridgelet_radonNikodym_balance`.  Compare
`LeanRidgelet.affineBochnerRidgelet_intertwines`. -/
theorem quadraticRelativeBochnerRidgelet_intertwines
    (μ : Measure E) [μ.IsAddHaarMeasure] (ψ : ℝ → Y)
    (g : E ≃ᵃ[ℝ] E) (f : E → Y) (ξ : QuadraticParameter E) :
    bochnerRidgelet μ (quadraticVectorFeature ψ)
        (quasiUnitaryPullbackAction affineDataJacobian
          (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) g f) ξ =
      quasiRegularAction (radonNikodymWeight quadraticRelativeParameterJacobian) g
        (bochnerRidgelet μ (quadraticVectorFeature ψ) f) ξ :=
  bochnerRidgelet_quasi_intertwines μ
    (1 : UnitaryRepresentation (E ≃ᵃ[ℝ] E) Y) (quadraticVectorFeature ψ)
    affineDataJacobian quadraticRelativeParameterJacobian affineData_measurable
    (affineData_group_map_eq_withDensity μ) affineDataJacobian_measurable
    affineDataJacobian_ne_zero (quadraticVectorFeature_jointInvariant ψ)
    quadraticRelative_ridgelet_radonNikodym_balance g f ξ

end Measure

end LeanRidgelet
