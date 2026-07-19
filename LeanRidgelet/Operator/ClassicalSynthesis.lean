/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Operator.Synthesis
public import LeanRidgelet.Space.ActivationRealization
public import LeanRidgelet.Transform.ClassicalSection

/-!
# Agreement of the Hilbert-space synthesis with the classical network integral

This file proves the classical part of the manuscript's boundedness theorem `thm:bdd.S`: on the
Schwartz compatibility domain, and for an activation coordinate whose realized classical
activation acts by integration against a function `σcl`, the Hilbert-space synthesis operator is
represented almost everywhere by the classical integral

`S[γ](x) = ∫ γ(a,b) σcl(⟨a,x⟩ - b) da db`

whenever the classical integral is defined.  The proof follows `sec:proof.bddS`: the pointwise
factorization `S[γ](x) = L_σ[T[γ](x,·)]`, the distributional pairing `L_σ[h] = (2π)^{m-1}σ♯[h]`,
Fourier inversion in the preactivation variable, and the measure-preserving preactivation shear.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform InnerProductSpace SchwartzMap

namespace LeanRidgelet

open LeanRidgelet.Fourier

/-- The classical network synthesis integral `x ↦ ∫ γ(a,b) σcl(⟨a,x⟩-b) da db`. -/
def classicalSynthesisIntegral {m : ℕ} (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (σcl : ℝ → ℂ) (x : InputSpace m) : ℂ :=
  ∫ p : InputSpace m × ℝ, γ p * σcl (inner ℝ p.1 x - p.2)

/-- Fubini and the preactivation shear evaluate the classical synthesis integral against the
classical section integral. -/
theorem classicalSynthesisIntegral_eq_sheared {m : ℕ}
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ) (σcl : ℝ → ℂ) (x : InputSpace m)
    (hint : Integrable (fun p : InputSpace m × ℝ ↦ γ p * σcl (inner ℝ p.1 x - p.2))) :
    classicalSynthesisIntegral γ σcl x =
      ∫ z : ℝ, shearedParameterIntegral γ x z * σcl z := by
  set G : InputSpace m × ℝ → ℂ :=
    fun p ↦ γ (p.1, inner ℝ p.1 x - p.2) * σcl p.2 with hG_def
  have hpoint : ∀ p : InputSpace m × ℝ,
      (fun q : InputSpace m × ℝ ↦ γ q * σcl (inner ℝ q.1 x - q.2))
        (p.1, inner ℝ p.1 x - p.2) = G p := by
    intro p
    rw [hG_def]
    change γ (p.1, inner ℝ p.1 x - p.2) * σcl (inner ℝ p.1 x - (inner ℝ p.1 x - p.2)) = _
    rw [show inner ℝ p.1 x - (inner ℝ p.1 x - p.2) = p.2 by ring]
  have hGint : Integrable G := by
    refine (integrable_comp_preactivationShear x hint).congr ?_
    filter_upwards with p
    exact hpoint p
  have hstep1 : classicalSynthesisIntegral γ σcl x = ∫ p, G p := by
    rw [classicalSynthesisIntegral,
      ← integral_comp_preactivationShear x
        (fun q : InputSpace m × ℝ ↦ γ q * σcl (inner ℝ q.1 x - q.2))]
    apply integral_congr_ae
    filter_upwards with p
    exact hpoint p
  have hstep2 : (∫ p, G p) = ∫ z : ℝ, ∫ a : InputSpace m, G (a, z) := by
    rw [Measure.volume_eq_prod] at hGint ⊢
    exact integral_prod_symm G hGint
  rw [hstep1, hstep2]
  apply integral_congr_ae
  filter_upwards with z
  rw [shearedParameterIntegral, ← integral_mul_const]

/--
**Agreement with the classical synthesis integral** (manuscript Theorem 14, `thm:bdd.S`,
classical part).  Let `σ` be an activation coordinate whose realized classical activation
`σ = 𝓕⁻¹_paper[σ♯]` acts on test functions by integration against `σcl`, and let `γ` be a
Schwartz parameter distribution in the compatibility domain.  If the classical integral is
defined at every input, then the Hilbert-space synthesis operator is represented almost
everywhere by the classical network integral `∫ γ(a,b) σcl(⟨a,x⟩-b) da db`.
-/
theorem networkSynthesis_parameterSchwartzRealization_classical_ae
    {m : ℕ} [NeZero m] (s t : ℝ) (σ : ActivationSpace s t) {σcl : ℝ → ℂ}
    (hσcl : ∀ φ : SchwartzMap ℝ ℂ,
      activationRealization s t σ φ = ∫ z : ℝ, φ z * σcl z)
    (γ : SchwartzMap (InputSpace m × ℝ) ℂ)
    (hγ : MemLp (fourierDilationTransformFiber s t γ) 2 volume)
    (hint : ∀ x : InputSpace m,
      Integrable (fun p : InputSpace m × ℝ ↦ γ p * σcl (inner ℝ p.1 x - p.2))) :
    networkSynthesis m s t σ (parameterSchwartzRealization s t γ hγ) =ᵐ[volume]
      classicalSynthesisIntegral γ σcl := by
  filter_upwards [networkSynthesis_parameterSchwartzRealization_apply_ae s t σ γ hγ]
    with x hx
  rw [hx]
  rw [show fourierDilationTransformFiber s t γ x =
      ((fourierDilationTransformFiberCore s t γ x : FiberCore m s t) :
        FiberSpace m s t) from rfl]
  rw [activationFiberFunctional_eq_realization m s t σ
    (fourierDilationTransformFiberCore s t γ x)]
  rw [hσcl]
  calc
    (2 * Real.pi : ℂ) ^ (m - 1) *
        ∫ z : ℝ, paperFourierSchwartz
          (FiberCore.toSchwartz (fourierDilationTransformFiberCore s t γ x)) z * σcl z =
        ∫ z : ℝ, shearedParameterIntegral γ x z * σcl z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [← mul_assoc, ← shearedParameterIntegral_eq_paperFourierSchwartz s t γ x z]
    _ = classicalSynthesisIntegral γ σcl x :=
      (classicalSynthesisIntegral_eq_sheared γ σcl x (hint x)).symm

end LeanRidgelet
