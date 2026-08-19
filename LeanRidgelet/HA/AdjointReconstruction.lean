/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanRidgelet.HA.Reconstruction

/-!
# Reconstruction from the adjoint: the coorbit route to a nonzero constant

`LeanRidgelet.HA.QuadraticComposite` records an obstruction: a synthesis and an analysis operator
given by square-integrable kernels are Hilbert--Schmidt, so their composite is compact, so the
scalar Schur produces is zero.  That obstruction is an artifact of treating the two operators as
*independent* integral operators.  Coorbit theory and the theory of generalized wavelet transforms
avoid it in one move, and this file formalizes that move.

*Take the machine to be the adjoint of the ridgelet transform.*  Then the composite is `R† R`, which
is positive, and Schur makes it a scalar: `⟪R† R f, f⟫ = ‖R f‖²`, so the scalar is
`‖R f‖² / ‖f‖²` -- **real, nonnegative, and nonzero as soon as `R` is**.  Nothing has to be assumed
about the synthesis side at all, because there is no independent synthesis side: the only hypothesis
is that the ridgelet transform is bounded and does not annihilate everything.  And no compactness
obstruction arises, because an operator with `R† R = c · id`, `c ≠ 0`, is a multiple of an isometry,
which in infinite dimensions is never compact -- the hypothesis that produced compactness before,
square integrability of a kernel, is simply absent.

This is the standard argument of the field.  In the notation of Berge, *A Primer on Coorbit Theory*
(arXiv:2101.05232), the analysis operator is the wavelet transform `W_g f (x) = ⟪f, π(x) g⟫` of a
square-integrable representation, its adjoint is the weak integral `W_g^*(F) = ∫ F(x) π(x) g dx`
(Proposition 2.33 there), admissibility of `g` makes `W_g` an isometry, and the reconstruction
formula `f = W_g^*(W_g f)` is Corollary 2.34.  The constant comes from the orthogonality relation
of the Duflo--Moore theorem there; here Schur's lemma gives it instead, so neither square
integrability of the representation nor a Duflo--Moore operator is needed -- only irreducibility of
the data representation, which `LeanRidgelet.HA.AffineMackey` proves for the affine action.

## What this costs

The machine is then the adjoint of the analysis operator rather than an independently chosen
synthesis integral.  For the Bochner pair of this development that is the *common feature* case: the
adjoint of the ridgelet transform against a feature is the synthesis integral against the same
feature, so this route reconstructs with the network whose activation is the analysis feature, not
with an activation fixed in advance.  Fixing the activation and choosing the analysis feature to
match it is a separate problem, and it is the one the article's boundedness appendix is about.

## Main results

* `LeanRidgelet.adjointIntertwiner`: the adjoint of an intertwiner of unitary representations is an
  intertwiner, the other way.
* `LeanRidgelet.adjointReconstructionOperator`: the composite `R† R`, as an intertwining
  endomorphism, with `LeanRidgelet.inner_adjointReconstructionOperator`: pairing it with a vector
  gives the squared norm of the transform.
* `LeanRidgelet.ha_adjoint_reconstruction`: Schur makes it a scalar, and the scalar satisfies the
  **orthogonality relation** `⟪R f, R f⟫ = c ⟪f, f⟫` -- which exhibits it as `‖R f‖² / ‖f‖²`, hence
  real and nonnegative.
* `LeanRidgelet.ha_adjoint_reconstruction_of_ne_zero`: **the nonzero reconstruction formula.**  One
  datum with nonzero transform makes the constant nonzero, and then the normalized adjoint of the
  ridgelet transform inverts it on every datum.  No placeholder anywhere in the chain.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ContRepresentation InnerProductSpace

namespace LeanRidgelet

variable {G H K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### The adjoint of an intertwiner -/

/-- The adjoint of a unitary representation's operator is the operator at the inverse group element.
This is `star = adjoint` for continuous linear endomorphisms together with `star = inverse` in the
unitary group. -/
theorem UnitaryRepresentation.adjoint_coe (π : UnitaryRepresentation G H) (g : G) :
    ContinuousLinearMap.adjoint ((π g : H →L[ℂ] H)) = ((π g⁻¹ : H →L[ℂ] H)) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star, map_inv]
  rfl

/-- **The adjoint of an intertwiner is an intertwiner.**  Taking adjoints in the intertwining law
exchanges the two representations and replaces the group element by its inverse, and a group element
ranges over the whole group with its inverse. -/
def adjointIntertwiner {π₁ : UnitaryRepresentation G H} {π₂ : UnitaryRepresentation G K}
    (R : π₁.toContRepresentation →ⁱL π₂.toContRepresentation) :
    π₂.toContRepresentation →ⁱL π₁.toContRepresentation where
  __ := ContinuousLinearMap.adjoint R.toContinuousLinearMap
  isIntertwining' g := by
    have h := congrArg ContinuousLinearMap.adjoint (R.isIntertwining' g⁻¹)
    simp only [UnitaryRepresentation.toContRepresentation_apply, ContinuousLinearMap.adjoint_comp,
      UnitaryRepresentation.adjoint_coe, inv_inv] at h
    simpa only [UnitaryRepresentation.toContRepresentation_apply] using h.symm

@[simp]
theorem adjointIntertwiner_toContinuousLinearMap {π₁ : UnitaryRepresentation G H}
    {π₂ : UnitaryRepresentation G K}
    (R : π₁.toContRepresentation →ⁱL π₂.toContRepresentation) :
    (adjointIntertwiner R).toContinuousLinearMap =
      ContinuousLinearMap.adjoint R.toContinuousLinearMap := rfl

/-! ### The reconstruction operator of the adjoint pair -/

/-- **The reconstruction operator of the coorbit route.**  The composite of a bounded intertwiner
with
its own adjoint, as an intertwining endomorphism of the data representation. -/
def adjointReconstructionOperator {π₁ : UnitaryRepresentation G H} {π₂ : UnitaryRepresentation G K}
    (R : π₁.toContRepresentation →ⁱL π₂.toContRepresentation) :
    π₁.toContRepresentation →ⁱL π₁.toContRepresentation :=
  (adjointIntertwiner R).comp R

/-- The reconstruction operator applied to a datum is the adjoint of the transform of the datum. -/
theorem adjointReconstructionOperator_apply {π₁ : UnitaryRepresentation G H}
    {π₂ : UnitaryRepresentation G K}
    (R : π₁.toContRepresentation →ⁱL π₂.toContRepresentation) (f : H) :
    adjointReconstructionOperator R f =
      ContinuousLinearMap.adjoint R.toContinuousLinearMap (R f) := by
  rw [← ContIntertwiningMap.toContinuousLinearMap_apply]
  rfl

/-- **Positivity.**  Pairing the reconstruction operator with a datum gives the squared norm of the
datum's transform.  This is what makes the reconstruction constant real, nonnegative, and nonzero
exactly when the transform is. -/
theorem inner_adjointReconstructionOperator {π₁ : UnitaryRepresentation G H}
    {π₂ : UnitaryRepresentation G K}
    (R : π₁.toContRepresentation →ⁱL π₂.toContRepresentation) (f : H) :
    ⟪adjointReconstructionOperator R f, f⟫_ℂ = ⟪R f, R f⟫_ℂ := by
  rw [adjointReconstructionOperator_apply, ContinuousLinearMap.adjoint_inner_left,
    ContIntertwiningMap.toContinuousLinearMap_apply]

/-! ### The reconstruction formula -/

/-- **The orthogonality relation from Schur's lemma.**  For a bounded intertwiner into any unitary
representation of the same group, the composite with its adjoint is a scalar multiple of the
identity,
and the scalar satisfies `⟪R f, R f⟫ = c ⟪f, f⟫` for every datum.  The second statement exhibits the
scalar as `‖R f‖² / ‖f‖²`: it is real and nonnegative, with no positivity argument beyond that
identity.

In coorbit theory this relation is supplied by the Duflo--Moore theorem for a square-integrable
representation; here it comes from irreducibility of the data representation alone, so neither
square
integrability nor an admissible vector is assumed. -/
theorem ha_adjoint_reconstruction (πData : UnitaryRepresentation G H)
    (hirr : πData.IsTopologicallyIrreducible) {πParam : UnitaryRepresentation G K}
    (R : πData.toContRepresentation →ⁱL πParam.toContRepresentation) :
    ∃ c : ℂ, (adjointReconstructionOperator R).toContinuousLinearMap =
        c • ContinuousLinearMap.id ℂ H ∧
      ∀ f : H, ⟪R f, R f⟫_ℂ = c * ⟪f, f⟫_ℂ := by
  obtain ⟨c, hc⟩ := ha_reconstruction_of_intertwiner πData hirr (adjointReconstructionOperator R)
  refine ⟨c, hc, fun f ↦ ?_⟩
  have hf : adjointReconstructionOperator R f = c • f :=
    (ContIntertwiningMap.toContinuousLinearMap_apply _ f).symm.trans
      (by simpa using congr($(hc) f))
  have h1 : ⟪f, adjointReconstructionOperator R f⟫_ℂ = c * ⟪f, f⟫_ℂ := by
    rw [hf, inner_smul_right]
  have h2 : ⟪f, adjointReconstructionOperator R f⟫_ℂ = ⟪R f, R f⟫_ℂ := by
    rw [← inner_conj_symm, inner_adjointReconstructionOperator, inner_self_conj]
  exact h2.symm.trans h1

/-- **A nonzero reconstruction constant, and the reconstruction formula.**  If one datum has nonzero
transform then the constant is nonzero, and the normalized adjoint of the ridgelet transform returns
every datum.  This is the reconstruction formula of coorbit theory -- Corollary 2.34 of Berge's
primer
-- with Schur's lemma in place of the Duflo--Moore orthogonality relation.

The only hypotheses are that the ridgelet transform is a bounded intertwiner and that it does not
annihilate everything.  Nothing is assumed about the synthesis operator, which is the adjoint;
nothing
is assumed about kernels or their square integrability, which is why the compactness obstruction of
`LeanRidgelet.HA.QuadraticComposite` does not arise. -/
theorem ha_adjoint_reconstruction_of_ne_zero (πData : UnitaryRepresentation G H)
    (hirr : πData.IsTopologicallyIrreducible) {πParam : UnitaryRepresentation G K}
    (R : πData.toContRepresentation →ⁱL πParam.toContRepresentation) (f₀ : H) (hf₀ : R f₀ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (adjointReconstructionOperator R).toContinuousLinearMap =
        c • ContinuousLinearMap.id ℂ H ∧
      (∀ f : H, ⟪R f, R f⟫_ℂ = c * ⟪f, f⟫_ℂ) ∧
      ∀ f : H, c⁻¹ • ContinuousLinearMap.adjoint R.toContinuousLinearMap (R f) = f := by
  obtain ⟨c, hscalar, horth⟩ := ha_adjoint_reconstruction πData hirr R
  have hc : c ≠ 0 := by
    intro hc0
    refine hf₀ ?_
    have h := horth f₀
    rw [hc0, zero_mul] at h
    exact inner_self_eq_zero.1 h
  refine ⟨c, hc, hscalar, horth, fun f ↦ ?_⟩
  have hf : adjointReconstructionOperator R f = c • f :=
    (ContIntertwiningMap.toContinuousLinearMap_apply _ f).symm.trans
      (by simpa using congr($(hscalar) f))
  rw [adjointReconstructionOperator_apply] at hf
  rw [hf, smul_smul, inv_mul_cancel₀ hc, one_smul]

end LeanRidgelet
