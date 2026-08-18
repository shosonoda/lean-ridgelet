/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Affine

/-!
# The quadratic-form feature and its affine parameter action

This file formalizes the algebraic part of Section 7 of arXiv:2405.13682.  The feature is a
quadratic form in the data followed by an arbitrary activation,

`φ(x, (A, b, c)) = σ(⟪x, A x⟫ + ⟪x, b⟫ + c)`,

with a symmetric coefficient `A`, a linear coefficient `b`, and a constant `c`.  The affine group
acts on the data by `x ↦ L x + t` and on the parameters by

`(A, b, c) ↦ (L⁻ᵀ A L⁻¹, L⁻ᵀ b - 2 L⁻ᵀ A L⁻¹ t, c + tᵀ L⁻ᵀ A L⁻¹ t - tᵀ L⁻ᵀ b)`,

and the scalar argument of the activation is invariant under the two actions together.  Since the
data representation of the affine group on `L²` is irreducible, the general reconstruction theorem
then applies to this feature.

## Main results

* `LeanRidgelet.quadraticArgument_invariant`: joint invariance of the scalar argument, hence
  `LeanRidgelet.quadraticFeature_invariant` for any activation.
* `LeanRidgelet.quadraticParameterMulAction`: the parameter action is a group action.  It is
  obtained from the invariance itself, because a quadratic parameter is determined by its scalar
  functional (`LeanRidgelet.quadraticArgument_parameter_injective`).
* `LeanRidgelet.det_quadraticParameterLinearEquiv`: the parameter action is linear with
  determinant the product of its symmetric congruence block and the reciprocal determinant of the
  linear part.

## Deviations from the article

Symmetric matrices are represented by self-adjoint *continuous* endomorphisms of a
finite-dimensional real inner product space, so no basis is chosen and the transpose is the
adjoint.  They are collected in the real subspace `LeanRidgelet.symmetricSubmodule` of
`E →L[ℝ] E`, whose coercion to a type is again a finite-dimensional real normed space; this is
what lets a later file put a measure on the parameter space.  The determinant of the congruence
`A ↦ Mᵀ A M` on symmetric coefficients is left as the abstract determinant of that congruence: the
parameter measure only needs it to be a nonzero constant, and the explicit value `(det M)^(m+1)`
is not used anywhere below.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The self-adjoint continuous endomorphisms, as a real subspace. -/
def symmetricSubmodule (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Submodule ℝ (E →L[ℝ] E) where
  carrier := {A | IsSelfAdjoint A}
  add_mem' ha hb := IsSelfAdjoint.add ha hb
  zero_mem' := IsSelfAdjoint.zero _
  smul_mem' r _ ha := (IsSelfAdjoint.all r).smul ha

/-- The symmetric coefficient of a quadratic-form feature. -/
abbrev QuadraticSymmetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] := ↥(symmetricSubmodule E)

/-- The parameter space `(A, b, c)` of a quadratic-form feature. -/
abbrev QuadraticParameter (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] := QuadraticSymmetric E × E × ℝ

/-- A linear equivalence of a finite-dimensional space, viewed as a continuous endomorphism.  In
finite dimensions every linear map is continuous, so this is only a change of bundling. -/
def quadraticCongrEndo (M : E ≃ₗ[ℝ] E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (M : E →ₗ[ℝ] E)

/-- Evaluation of a continuous endomorphism at a fixed vector, as a linear map. -/
def quadraticEval (t : E) : (E →L[ℝ] E) →ₗ[ℝ] E where
  toFun A := A t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Congruence `A ↦ Mᵀ A M` preserves self-adjointness. -/
theorem isSelfAdjoint_congr (M : E →L[ℝ] E) {A : E →L[ℝ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (star M * A * M) := by
  have : star (star M * A * M) = star M * A * M := by
    rw [star_mul, star_mul, star_star, hA.star_eq, mul_assoc]
  exact this

/-- Congruence `A ↦ Mᵀ A M` on symmetric coefficients. -/
def quadraticCongrMap (M : E →L[ℝ] E) : QuadraticSymmetric E →ₗ[ℝ] QuadraticSymmetric E where
  toFun A := ⟨star M * (A : E →L[ℝ] E) * M, isSelfAdjoint_congr M A.2⟩
  map_add' A B := by
    refine Subtype.ext ?_
    change star M * ((A : E →L[ℝ] E) + B) * M = star M * (A : E →L[ℝ] E) * M + star M * B * M
    rw [mul_add, add_mul]
  map_smul' r A := by
    refine Subtype.ext ?_
    change star M * (r • (A : E →L[ℝ] E)) * M = r • (star M * (A : E →L[ℝ] E) * M)
    rw [mul_smul_comm, smul_mul_assoc]

@[simp]
theorem quadraticCongrMap_coe (M : E →L[ℝ] E) (A : QuadraticSymmetric E) :
    ((quadraticCongrMap M A : QuadraticSymmetric E) : E →L[ℝ] E) =
      star M * (A : E →L[ℝ] E) * M := rfl

/-- Congruence by an invertible map is invertible, with inverse the congruence by the inverse. -/
def quadraticCongr (M : E ≃ₗ[ℝ] E) : QuadraticSymmetric E ≃ₗ[ℝ] QuadraticSymmetric E :=
  LinearEquiv.ofLinear (quadraticCongrMap (quadraticCongrEndo M))
    (quadraticCongrMap (quadraticCongrEndo M.symm))
    (by
      have hinv : quadraticCongrEndo M.symm * quadraticCongrEndo M = 1 :=
        ContinuousLinearMap.ext fun x ↦ by simp [quadraticCongrEndo]
      refine LinearMap.ext fun A ↦ Subtype.ext ?_
      set N := quadraticCongrEndo M
      set N' := quadraticCongrEndo M.symm
      change star N * (star N' * (A : E →L[ℝ] E) * N') * N = (A : E →L[ℝ] E)
      calc star N * (star N' * (A : E →L[ℝ] E) * N') * N
          = star (N' * N) * (A : E →L[ℝ] E) * (N' * N) := by
            rw [star_mul]; simp only [mul_assoc]
        _ = (A : E →L[ℝ] E) := by rw [hinv]; simp)
    (by
      have hinv : quadraticCongrEndo M * quadraticCongrEndo M.symm = 1 :=
        ContinuousLinearMap.ext fun x ↦ by simp [quadraticCongrEndo]
      refine LinearMap.ext fun A ↦ Subtype.ext ?_
      set N := quadraticCongrEndo M
      set N' := quadraticCongrEndo M.symm
      change star N' * (star N * (A : E →L[ℝ] E) * N) * N' = (A : E →L[ℝ] E)
      calc star N' * (star N * (A : E →L[ℝ] E) * N) * N'
          = star (N * N') * (A : E →L[ℝ] E) * (N * N') := by
            rw [star_mul]; simp only [mul_assoc]
        _ = (A : E →L[ℝ] E) := by rw [hinv]; simp)

@[simp]
theorem quadraticCongr_coe (M : E ≃ₗ[ℝ] E) (A : QuadraticSymmetric E) :
    ((quadraticCongr M A : QuadraticSymmetric E) : E →L[ℝ] E) =
      star (quadraticCongrEndo M) * (A : E →L[ℝ] E) * quadraticCongrEndo M := rfl

/-- Congruence in an inner product: `⟪u, Mᵀ A M v⟫ = ⟪M u, A (M v)⟫`. -/
theorem inner_quadraticCongr (M : E ≃ₗ[ℝ] E) (A : QuadraticSymmetric E) (u v : E) :
    ⟪u, ((quadraticCongr M A : QuadraticSymmetric E) : E →L[ℝ] E) v⟫_ℝ =
      ⟪M u, (A : E →L[ℝ] E) (M v)⟫_ℝ := by
  rw [quadraticCongr_coe]
  change ⟪u, star (quadraticCongrEndo M) ((A : E →L[ℝ] E) (quadraticCongrEndo M v))⟫_ℝ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The scalar functional `xᵀ A x + xᵀ b + c` computed by a quadratic-form feature. -/
def quadraticArgument (x : E) (ξ : QuadraticParameter E) : ℝ :=
  ⟪x, (ξ.1 : E →L[ℝ] E) x⟫_ℝ + ⟪x, ξ.2.1⟫_ℝ + ξ.2.2

/-- The quadratic-form feature `σ(xᵀ A x + xᵀ b + c)` of Section 7. -/
def quadraticFeature (σ : ℝ → ℝ) (x : E) (ξ : QuadraticParameter E) : ℝ :=
  σ (quadraticArgument x ξ)

/-- The transformed symmetric coefficient applied to the translation of `g`. -/
def quadraticShearVector (g : E ≃ᵃ[ℝ] E) : QuadraticSymmetric E →ₗ[ℝ] E :=
  (quadraticEval (g 0)).comp
    ((symmetricSubmodule E).subtype.comp (quadraticCongr g.linear.symm).toLinearMap)

@[simp]
theorem quadraticShearVector_apply (g : E ≃ᵃ[ℝ] E) (A : QuadraticSymmetric E) :
    quadraticShearVector g A =
      ((quadraticCongr g.linear.symm A : QuadraticSymmetric E) : E →L[ℝ] E) (g 0) := rfl

/-- The translation-dependent block acting on the linear coefficient of a quadratic parameter. -/
def quadraticLinearShear (g : E ≃ᵃ[ℝ] E) : E →ₗ[ℝ] ℝ :=
  -(innerSL ℝ (g 0)).toLinearMap.comp (g.linear.symm.adjoint : E →ₗ[ℝ] E)

/-- The action on the linear and constant coefficients alone. -/
def quadraticLinearEquiv (g : E ≃ᵃ[ℝ] E) : (E × ℝ) ≃ₗ[ℝ] (E × ℝ) :=
  g.linear.symm.adjoint.skewProd (LinearEquiv.refl ℝ ℝ) (quadraticLinearShear g)

/-- The translation-dependent block below the symmetric coefficient. -/
def quadraticSymmetricShear (g : E ≃ᵃ[ℝ] E) : QuadraticSymmetric E →ₗ[ℝ] (E × ℝ) :=
  ((-2 : ℝ) • quadraticShearVector g).prod
    ((innerSL ℝ (g 0)).toLinearMap.comp (quadraticShearVector g))

/-- The parameter action of the affine group on quadratic parameters.  If `g x = L x + t`, it
sends `(A, b, c)` to `(L⁻ᵀ A L⁻¹, L⁻ᵀ b - 2 L⁻ᵀ A L⁻¹ t, c + tᵀ L⁻ᵀ A L⁻¹ t - tᵀ L⁻ᵀ b)`. -/
def quadraticParameterLinearEquiv (g : E ≃ᵃ[ℝ] E) :
    QuadraticParameter E ≃ₗ[ℝ] QuadraticParameter E :=
  (quadraticCongr g.linear.symm).skewProd (quadraticLinearEquiv g) (quadraticSymmetricShear g)

@[simp]
theorem quadraticParameterLinearEquiv_apply (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticParameterLinearEquiv g ξ =
      (quadraticCongr g.linear.symm ξ.1,
        g.linear.symm.adjoint ξ.2.1 + (-2 : ℝ) • quadraticShearVector g ξ.1,
        ξ.2.2 + quadraticLinearShear g ξ.2.1 + ⟪g 0, quadraticShearVector g ξ.1⟫_ℝ) := rfl

/-- The quadratic functional is invariant under the joint affine data/parameter action.  This is
the computation of Section 7 and Appendix F of the article. -/
theorem quadraticArgument_invariant (g : E ≃ᵃ[ℝ] E) (x : E) (ξ : QuadraticParameter E) :
    quadraticArgument (g x) (quadraticParameterLinearEquiv g ξ) = quadraticArgument x ξ := by
  obtain ⟨A, b, c⟩ := ξ
  have hdecomp : g x = g.linear x + g 0 := congrFun g.toAffineMap.decomp x
  have hgx : g.linear.symm (g x) = x + g.linear.symm (g 0) := by
    rw [hdecomp, map_add]
    simp
  set s := g.linear.symm (g 0) with hsdef
  have hsym : ⟪s, (A : E →L[ℝ] E) x⟫_ℝ = ⟪x, (A : E →L[ℝ] E) s⟫_ℝ := by
    have hA : ⟪(A : E →L[ℝ] E) s, x⟫_ℝ = ⟪s, (A : E →L[ℝ] E) x⟫_ℝ :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 A.2 s x
    rw [← hA, real_inner_comm]
  have hquad : ⟪g x,
      ((quadraticCongr g.linear.symm A : QuadraticSymmetric E) : E →L[ℝ] E) (g x)⟫_ℝ =
      ⟪x + s, (A : E →L[ℝ] E) (x + s)⟫_ℝ := by
    rw [inner_quadraticCongr, hgx]
  have hcross : ⟪g x, quadraticShearVector g A⟫_ℝ = ⟪x + s, (A : E →L[ℝ] E) s⟫_ℝ := by
    rw [quadraticShearVector_apply, inner_quadraticCongr, hgx]
  have hconst : ⟪g 0, quadraticShearVector g A⟫_ℝ = ⟪s, (A : E →L[ℝ] E) s⟫_ℝ := by
    rw [quadraticShearVector_apply, inner_quadraticCongr]
  have hlin : ⟪g x, (g.linear.symm.adjoint : E ≃ₗ[ℝ] E) b⟫_ℝ = ⟪x + s, b⟫_ℝ := by
    change ⟪g x, LinearMap.adjoint (g.linear.symm : E →ₗ[ℝ] E) b⟫_ℝ = _
    rw [LinearMap.adjoint_inner_right]
    exact congrArg (fun u ↦ ⟪u, b⟫_ℝ) hgx
  have hshearlin : quadraticLinearShear g b = -⟪s, b⟫_ℝ := by
    change -⟪g 0, LinearMap.adjoint (g.linear.symm : E →ₗ[ℝ] E) b⟫_ℝ = _
    rw [LinearMap.adjoint_inner_right]
    rfl
  have hexpand1 : ⟪x + s, (A : E →L[ℝ] E) (x + s)⟫_ℝ =
      ⟪x, (A : E →L[ℝ] E) x⟫_ℝ + 2 * ⟪x, (A : E →L[ℝ] E) s⟫_ℝ +
        ⟪s, (A : E →L[ℝ] E) s⟫_ℝ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym]
    ring
  have hexpand2 : ⟪x + s, (A : E →L[ℝ] E) s⟫_ℝ =
      ⟪x, (A : E →L[ℝ] E) s⟫_ℝ + ⟪s, (A : E →L[ℝ] E) s⟫_ℝ := inner_add_left _ _ _
  have hexpand3 : ⟪x + s, b⟫_ℝ = ⟪x, b⟫_ℝ + ⟪s, b⟫_ℝ := inner_add_left _ _ _
  rw [quadraticArgument, quadraticArgument, quadraticParameterLinearEquiv_apply]
  rw [hquad, inner_add_right, hlin, real_inner_smul_right, hcross, hshearlin, hconst,
    hexpand1, hexpand2, hexpand3]
  ring

/-- The quadratic feature is invariant under the joint affine data/parameter action. -/
theorem quadraticFeature_invariant (σ : ℝ → ℝ) (g : E ≃ᵃ[ℝ] E) (x : E)
    (ξ : QuadraticParameter E) :
    quadraticFeature σ (g x) (quadraticParameterLinearEquiv g ξ) = quadraticFeature σ x ξ := by
  rw [quadraticFeature, quadraticFeature, quadraticArgument_invariant]

/-- Quadratic parameters are determined by their scalar functional: the constant is the value at
the origin, the odd part determines the linear coefficient, and the even part determines the
quadratic form, hence the symmetric coefficient by polarization. -/
theorem quadraticArgument_parameter_injective :
    Function.Injective (fun ξ : QuadraticParameter E ↦ fun x : E ↦ quadraticArgument x ξ) := by
  rintro ⟨A₁, b₁, c₁⟩ ⟨A₂, b₂, c₂⟩ hpq
  have hc : c₁ = c₂ := by
    have h0 := congrFun hpq 0
    simpa [quadraticArgument] using h0
  have hplus : ∀ x : E, ⟪x, (A₁ : E →L[ℝ] E) x⟫_ℝ = ⟪x, (A₂ : E →L[ℝ] E) x⟫_ℝ := by
    intro x
    have hx := congrFun hpq x
    have hnx := congrFun hpq (-x)
    simp only [quadraticArgument, inner_neg_left, inner_neg_right, map_neg, neg_neg] at hx hnx
    linarith [hx, hnx, hc]
  have hminus : ∀ x : E, ⟪x, b₁⟫_ℝ = ⟪x, b₂⟫_ℝ := by
    intro x
    have hx := congrFun hpq x
    have hnx := congrFun hpq (-x)
    simp only [quadraticArgument, inner_neg_left, inner_neg_right, map_neg, neg_neg] at hx hnx
    linarith [hx, hnx, hplus x]
  have hb : b₁ = b₂ := by
    have hinner : innerSL ℝ b₁ = innerSL ℝ b₂ := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      change ⟪b₁, x⟫_ℝ = ⟪b₂, x⟫_ℝ
      rw [← real_inner_comm b₁ x, ← real_inner_comm b₂ x]
      exact hminus x
    exact innerSL_inj.mp hinner
  have hA : A₁ = A₂ := by
    have h₁ : IsSelfAdjoint (A₁ : E →L[ℝ] E) := A₁.2
    have h₂ : IsSelfAdjoint (A₂ : E →L[ℝ] E) := A₂.2
    have hsub : IsSelfAdjoint ((A₁ : E →L[ℝ] E) - (A₂ : E →L[ℝ] E)) := h₁.sub h₂
    have hsym : (((A₁ : E →L[ℝ] E) - (A₂ : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsub
    have hzero : (((A₁ : E →L[ℝ] E) - (A₂ : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 := by
      refine hsym.inner_map_self_eq_zero.1 fun x ↦ ?_
      have h1 : ⟪(((A₁ : E →L[ℝ] E) - (A₂ : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E) x, x⟫_ℝ =
          ⟪(A₁ : E →L[ℝ] E) x, x⟫_ℝ - ⟪(A₂ : E →L[ℝ] E) x, x⟫_ℝ := by
        rw [ContinuousLinearMap.coe_coe, sub_apply, inner_sub_left]
      have h2 : ⟪(A₁ : E →L[ℝ] E) x, x⟫_ℝ = ⟪x, (A₁ : E →L[ℝ] E) x⟫_ℝ := real_inner_comm _ _
      have h3 : ⟪(A₂ : E →L[ℝ] E) x, x⟫_ℝ = ⟪x, (A₂ : E →L[ℝ] E) x⟫_ℝ := real_inner_comm _ _
      rw [h1]
      linarith [hplus x, h2, h3]
    have hzero' : (A₁ : E →L[ℝ] E) - (A₂ : E →L[ℝ] E) = 0 := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have hx := congrArg (fun T : E →ₗ[ℝ] E ↦ T x) hzero
      simpa using hx
    exact Subtype.ext (sub_eq_zero.mp hzero')
  simp [hA, hb, hc]

/-- The joint affine action on quadratic parameters.  The priority keeps the componentwise
product action, which does not exist here, from being searched first. -/
instance (priority := 2000) quadraticParameterSMul :
    SMul (E ≃ᵃ[ℝ] E) (QuadraticParameter E) :=
  ⟨fun g ξ ↦ quadraticParameterLinearEquiv g ξ⟩

/-- The joint affine action on quadratic parameters. -/
instance quadraticParameterMulAction : MulAction (E ≃ᵃ[ℝ] E) (QuadraticParameter E) where
  one_smul ξ := by
    apply quadraticArgument_parameter_injective
    funext x
    change quadraticArgument x (quadraticParameterLinearEquiv (AffineEquiv.refl ℝ E) ξ) =
      quadraticArgument x ξ
    simpa using quadraticArgument_invariant (AffineEquiv.refl ℝ E) x ξ
  mul_smul g h ξ := by
    apply quadraticArgument_parameter_injective
    funext x
    have hgh := quadraticArgument_invariant (g * h) ((g * h).symm x) ξ
    have hg := quadraticArgument_invariant g (g.symm x) (quadraticParameterLinearEquiv h ξ)
    have hh := quadraticArgument_invariant h (h.symm (g.symm x)) ξ
    have hgh' : quadraticArgument x (quadraticParameterLinearEquiv (g * h) ξ) =
        quadraticArgument ((g * h).symm x) ξ := by simpa using hgh
    have hg' : quadraticArgument x
          (quadraticParameterLinearEquiv g (quadraticParameterLinearEquiv h ξ)) =
        quadraticArgument (g.symm x) (quadraticParameterLinearEquiv h ξ) := by
      simpa using hg
    have hh' : quadraticArgument (g.symm x) (quadraticParameterLinearEquiv h ξ) =
        quadraticArgument (h.symm (g.symm x)) ξ := by simpa using hh
    exact hgh'.trans <| by
      rw [show (g * h).symm x = h.symm (g.symm x) by rfl]
      exact (hg'.trans hh').symm

@[simp]
theorem quadraticParameter_smul_def (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    g • ξ = quadraticParameterLinearEquiv g ξ := rfl

/-- The determinant of the quadratic parameter action is the determinant of its symmetric
congruence block times the reciprocal determinant of the linear part. -/
theorem det_quadraticParameterLinearEquiv (g : E ≃ᵃ[ℝ] E) :
    LinearMap.det
        (quadraticParameterLinearEquiv g : QuadraticParameter E →ₗ[ℝ] QuadraticParameter E) =
      LinearMap.det
          ((quadraticCongr g.linear.symm) : QuadraticSymmetric E →ₗ[ℝ] QuadraticSymmetric E) *
        (LinearMap.det (g.linear : E →ₗ[ℝ] E))⁻¹ := by
  rw [quadraticParameterLinearEquiv, LinearEquiv.det_skewProd, quadraticLinearEquiv,
    LinearEquiv.det_skewProd, LinearEquiv.det_adjoint]
  simp [LinearEquiv.det_coe_symm]

end LeanRidgelet
