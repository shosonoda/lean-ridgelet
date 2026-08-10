/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.DiagonalScaling
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Singular value decomposition of an injective linear map

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

Mathlib has singular *values* — `LinearMap.singularValues`, the square roots of the eigenvalues of
`Tᵀ T` — but not the decomposition they are the values of. This file supplies it in the case that
matters for integration over a matrix space: an injective linear map `A : ℝ^k → E` factors as
$$`A = U D V^\top,`
with `U : ℝ^k →ₗᵢ E` an orthonormal `k`-frame, `V` a rotation of `ℝ^k`, and `D` the coordinatewise
scaling by `k` *positive* numbers.

The proof is the spectral theorem and nothing else. `T = Aᵀ A` is symmetric and, `A` being
injective, positive definite; its orthonormal eigenbasis `(bᵢ)` has eigenvalues `μᵢ = ‖A bᵢ‖² > 0`;
the vectors `uᵢ = A bᵢ / √μᵢ` are orthonormal in `E` because `⟪A bᵢ, A bⱼ⟫ = ⟪T bᵢ, bⱼ⟫ = μᵢ δᵢⱼ`;
and reading `A` in the two bases gives the factorization with `dᵢ = √μᵢ` and `V` the basis change.

## What this is and is not

This is the *existence* of the decomposition. The measure-theoretic half — the Jacobian
`dA = δ(D) dD dU dV` with `δ(D) = 2^{-k}|det D|^{m-k}∏_{i<j}(dᵢ² - dⱼ²)`, which is what turns an
integral over the matrix space into one over the singular value coordinates — is not here. Its
published proofs go through exterior differential forms, or through the Jacobian of the matrix polar
decomposition together with Weyl's integration formula for real symmetric matrices, and Mathlib has
none of those.

## Main results

* `MeasureTheory.exists_svd`: **the singular value decomposition**, in the form
  `A ω = U (D (V⁻¹ ω))` with `D` the coordinatewise scaling of `MeasureTheory.diagScale` by a vector
  of positive entries.
* `MeasureTheory.isometryOfOrthonormalFamily`: the auxiliary construction it is built from — an
  orthonormal family indexed by `Fin k` is a linear isometry out of `ℝ^k`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MeasureTheory

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear map out of `ℝ^k` sending the standard basis to a given family. -/
def linearMapOfFamily (u : Fin k → E) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E where
  toFun ω := ∑ i, ω i • u i
  map_add' ω η := by
    simp only [PiLp.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c ω := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact Finset.smul_sum.symm

@[simp] theorem linearMapOfFamily_apply (u : Fin k → E) (ω : EuclideanSpace ℝ (Fin k)) :
    linearMapOfFamily u ω = ∑ i, ω i • u i := rfl

/-- **An orthonormal family indexed by `Fin k` is a linear isometry out of `ℝ^k`**, sending the
standard basis to the family. -/
def isometryOfOrthonormalFamily {u : Fin k → E} (hu : Orthonormal ℝ u) :
    EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E where
  toLinearMap := linearMapOfFamily u
  norm_map' ω := by
    rw [linearMapOfFamily_apply]
    have hinner : (inner ℝ (∑ i, ω i • u i) (∑ i, ω i • u i) : ℝ) = ∑ i, ω i * ω i := by
      rw [hu.inner_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [norm_eq_sqrt_real_inner, hinner, EuclideanSpace.norm_eq]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]

@[simp] theorem isometryOfOrthonormalFamily_apply {u : Fin k → E} (hu : Orthonormal ℝ u)
    (ω : EuclideanSpace ℝ (Fin k)) :
    isometryOfOrthonormalFamily hu ω = ∑ i, ω i • u i := rfl

@[simp] theorem isometryOfOrthonormalFamily_single {u : Fin k → E} (hu : Orthonormal ℝ u)
    (i : Fin k) :
    isometryOfOrthonormalFamily hu (EuclideanSpace.single i (1 : ℝ)) = u i := by
  rw [isometryOfOrthonormalFamily_apply,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hji => by simp [hji])]
  simp

variable [FiniteDimensional ℝ E]

/-- **Singular value decomposition.** An injective linear map `A : ℝ^k → E` is an orthonormal
`k`-frame composed with a coordinatewise scaling by positive numbers composed with a rotation of
`ℝ^k`. Only the existence is proved here; the Jacobian of the decomposition is not. -/
theorem exists_svd (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) (hA : Function.Injective A) :
    ∃ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (d : EuclideanSpace ℝ (Fin k))
      (V : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)),
      (∀ i, 0 < d i) ∧
        ∀ ω : EuclideanSpace ℝ (Fin k), A ω = U (diagScale (WithLp.ofLp d) (V.symm ω)) := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  -- `T = Aᵀ A` is symmetric
  set T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    LinearMap.adjoint A ∘ₗ A with hTdef
  have hTinner : ∀ ω η : EuclideanSpace ℝ (Fin k),
      (inner ℝ (T ω) η : ℝ) = inner ℝ (A ω) (A η) := by
    intro ω η
    rw [hTdef]
    simp [LinearMap.adjoint_inner_left]
  have hT : T.IsSymmetric := by
    intro ω η
    rw [hTinner ω η, show (inner ℝ ω (T η) : ℝ) = inner ℝ (T η) ω from real_inner_comm _ _,
      hTinner η ω]
    exact real_inner_comm _ _
  -- its orthonormal eigenbasis, with positive eigenvalues
  set b := hT.eigenvectorBasis hn with hbdef
  set μ := hT.eigenvalues hn with hmudef
  have heig : ∀ i, T (b i) = μ i • b i := fun i =>
    (hT.hasEigenvector_eigenvectorBasis hn i).apply_eq_smul
  have hbnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hmupos : ∀ i, 0 < μ i := by
    intro i
    have h1 : (inner ℝ (T (b i)) (b i) : ℝ) = μ i := by
      rw [heig i, real_inner_smul_left, real_inner_self_eq_norm_sq, hbnorm i]
      ring
    have h2 : (inner ℝ (T (b i)) (b i) : ℝ) = ‖A (b i)‖ ^ 2 := by
      rw [hTinner, real_inner_self_eq_norm_sq]
    have h3 : A (b i) ≠ 0 := by
      intro h
      have hb0 : b i = 0 := hA (by rw [h, map_zero])
      have hb1 := hbnorm i
      rw [hb0, norm_zero] at hb1
      exact zero_ne_one hb1
    rw [← h1, h2]
    positivity
  -- the singular values, and the frame they normalize
  set d : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => Real.sqrt (μ i) with hddef
  have hdpos : ∀ i, 0 < d i := fun i => Real.sqrt_pos.2 (hmupos i)
  have hd2 : ∀ i, d i * d i = μ i := fun i => by
    rw [hddef]
    simpa using Real.mul_self_sqrt (hmupos i).le
  set u : Fin k → E := fun i => (d i)⁻¹ • A (b i) with hudef
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    have hAinner : (inner ℝ (A (b i)) (A (b j)) : ℝ) = if i = j then μ i else 0 := by
      rw [← hTinner, heig i, real_inner_smul_left]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, real_inner_self_eq_norm_sq, hbnorm i]
        ring
      · rw [if_neg hij, b.orthonormal.2 hij, mul_zero]
    rw [hudef]
    simp only [real_inner_smul_left, real_inner_smul_right, hAinner]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, ← hd2 i]
      field_simp [(hdpos i).ne']
    · rw [if_neg hij, if_neg hij, mul_zero, mul_zero]
  refine ⟨isometryOfOrthonormalFamily hu, d, b.repr.symm, hdpos, fun ω => ?_⟩
  simp only [LinearIsometryEquiv.symm_symm]
  -- both sides are linear, so it is enough to check them on the eigenbasis
  have hstep : ∀ j : Fin k, A (b j)
      = isometryOfOrthonormalFamily hu (diagScale (WithLp.ofLp d) (b.repr (b j))) := by
    intro j
    have hdiag : diagScale (WithLp.ofLp d) (b.repr (b j))
        = d j • EuclideanSpace.single j (1 : ℝ) := by
      rw [b.repr_self]
      ext i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [hdiag, map_smul, isometryOfOrthonormalFamily_single, hudef]
    simp only [smul_smul]
    rw [mul_inv_cancel₀ (hdpos j).ne', one_smul]
  have hlin : A = (isometryOfOrthonormalFamily hu).toLinearMap ∘ₗ
      (diagScale (WithLp.ofLp d) ∘ₗ b.repr.toLinearIsometry.toLinearMap) := by
    refine b.toBasis.ext fun j => ?_
    rw [OrthonormalBasis.coe_toBasis]
    exact hstep j
  exact LinearMap.congr_fun hlin ω

end MeasureTheory
