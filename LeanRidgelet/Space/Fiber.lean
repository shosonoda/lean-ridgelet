/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.Space.Activation
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Fiber Hilbert space

This file formalizes the norm on the dense Schwartz core of the fiber space from Section 2.2 of
the L2 manuscript and constructs the fiber Hilbert space by completing that core.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace SchwartzMap

namespace LeanRidgelet

/-- The Bessel potential `⟨∂⟩^t` acting on a Schwartz function. -/
def schwartzBesselPotential (t : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (paperBesselSymbol t)

/-- The first, dilation-Jacobian term of the fiber norm in Section 2.2. -/
def fiberBaseNormSq (m : ℕ) (h : SchwartzMap ℝ ℂ) : ℝ :=
  (2 * Real.pi) ^ (m - 1) * ∫ ω : ℝ, ‖h ω‖ ^ 2 * |ω| ^ m

/-- The weighted Bessel-potential term of the fiber norm in Section 2.2. -/
def fiberSobolevNormSq (s t : ℝ) (h : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ ω : ℝ, ‖schwartzBesselPotential t h ω‖ ^ 2 * japaneseBracketPow (-2 * s) ω

/-- The squared norm on the Schwartz core of `H_{s,t}`, before Hilbert completion. -/
def fiberNormSq (m : ℕ) (s t : ℝ) (h : SchwartzMap ℝ ℂ) : ℝ :=
  fiberBaseNormSq m h + fiberSobolevNormSq s t h

theorem fiberBaseNormSq_nonneg (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    0 ≤ fiberBaseNormSq m h := by
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply integral_nonneg
  intro ω
  positivity

theorem fiberSobolevNormSq_nonneg (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    0 ≤ fiberSobolevNormSq s t h := by
  apply integral_nonneg
  intro ω
  exact mul_nonneg (sq_nonneg _) (le_of_lt (japaneseBracketPow_pos (-2 * s) ω))

theorem fiberNormSq_nonneg (m : ℕ) (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    0 ≤ fiberNormSq m s t h := by
  exact add_nonneg (fiberBaseNormSq_nonneg m h) (fiberSobolevNormSq_nonneg s t h)

/-- Polynomially weighted pointwise inner products of Schwartz functions are integrable. -/
theorem integrable_inner_mul_abs_pow (m : ℕ) (h r : SchwartzMap ℝ ℂ) :
    Integrable (fun ω : ℝ ↦ ⟪h ω, r ω⟫_ℂ * (|ω| ^ m : ℝ)) := by
  let C := SchwartzMap.seminorm ℂ 0 0 h
  have hmajor : Integrable (fun ω : ℝ ↦ C * (‖ω‖ ^ m * ‖r ω‖)) :=
    (r.integrable_pow_mul volume m).const_mul C
  apply hmajor.mono
  · fun_prop
  · filter_upwards with ω
    have hC : 0 ≤ C := apply_nonneg _ h
    have hq : ‖h ω‖ ≤ C := SchwartzMap.norm_le_seminorm ℂ h ω
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg (norm_nonneg ω) m)
      (norm_nonneg (r ω))))]
    calc
      ‖⟪h ω, r ω⟫_ℂ * (|ω| ^ m : ℝ)‖
          ≤ (‖h ω‖ * ‖r ω‖) * |ω| ^ m := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (abs_nonneg ω) m)]
            gcongr
            exact norm_inner_le_norm _ _
      _ ≤ C * (‖ω‖ ^ m * ‖r ω‖) := by
        rw [Real.norm_eq_abs]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_right hq
            (mul_nonneg (pow_nonneg (abs_nonneg ω) m) (norm_nonneg (r ω)))

/-- Japanese-bracket weighted pointwise inner products of Schwartz functions are integrable. -/
theorem integrable_inner_mul_japaneseBracketPow (u : ℝ) (h r : SchwartzMap ℝ ℂ) :
    Integrable (fun ω : ℝ ↦ ⟪h ω, r ω⟫_ℂ * japaneseBracketPow u ω) := by
  let wr : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (temperedWeight u) r
  have hInt := integrable_inner_mul_abs_pow 0 h wr
  convert hInt using 1
  funext ω
  simp only [pow_zero, wr,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_temperedWeight u), temperedWeight]
  rw [inner_smul_right]
  norm_num
  ring

/-- The polynomially weighted squared norm of a Schwartz function is integrable. -/
theorem integrable_norm_sq_mul_abs_pow (m : ℕ) (h : SchwartzMap ℝ ℂ) :
    Integrable (fun ω : ℝ ↦ ‖h ω‖ ^ 2 * |ω| ^ m) := by
  refine (integrable_inner_mul_abs_pow m h h).re.congr ?_
  filter_upwards with ω
  rw [RCLike.mul_re, inner_self_eq_norm_sq, inner_self_im, zero_mul, sub_zero]
  congr 1

/-- Definiteness of the fiber norm on the Schwartz core. -/
theorem fiberNormSq_eq_zero_iff (m : ℕ) (_hm : 0 < m) (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    fiberNormSq m s t h = 0 ↔ h = 0 := by
  constructor
  · intro hnorm
    have hbase : fiberBaseNormSq m h = 0 := by
      have hb := fiberBaseNormSq_nonneg m h
      have hs := fiberSobolevNormSq_nonneg s t h
      unfold fiberNormSq at hnorm
      nlinarith
    have hcoefficient : (2 * Real.pi) ^ (m - 1) ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have hintegral : ∫ ω : ℝ, ‖h ω‖ ^ 2 * |ω| ^ m = 0 := by
      unfold fiberBaseNormSq at hbase
      exact (mul_eq_zero.mp hbase).resolve_left hcoefficient
    have hae : (fun ω : ℝ ↦ ‖h ω‖ ^ 2 * |ω| ^ m) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun ω ↦ mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg ω) m))
        (integrable_norm_sq_mul_abs_pow m h)).mp hintegral
    have hqae : (h : ℝ → ℂ) =ᵐ[volume] 0 := by
      filter_upwards [hae, volume.ae_ne (0 : ℝ)] with ω hω hω0
      have habs : |ω| ^ m ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hω0)
      have hnormSq : ‖h ω‖ ^ 2 = 0 := (mul_eq_zero.mp hω).resolve_right habs
      have hnormZero : ‖h ω‖ = 0 := by
        simpa only [sq_eq_zero_iff] using hnormSq
      exact norm_eq_zero.mp hnormZero
    have hqfun : (h : ℝ → ℂ) = 0 :=
      volume.eq_of_ae_eq hqae h.continuous continuous_zero
    ext ω
    exact congrFun hqfun ω
  · rintro rfl
    simp [fiberNormSq, fiberBaseNormSq, fiberSobolevNormSq]

/-- The sesquilinear form whose diagonal is the fiber norm from Section 2.2. -/
def fiberInner (m : ℕ) (s t : ℝ) (h r : SchwartzMap ℝ ℂ) : ℂ :=
  (2 * Real.pi : ℂ) ^ (m - 1) *
      (∫ ω : ℝ, ⟪h ω, r ω⟫_ℂ * (|ω| ^ m : ℝ)) +
    (∫ ω : ℝ, ⟪schwartzBesselPotential t h ω, schwartzBesselPotential t r ω⟫_ℂ *
      japaneseBracketPow (-2 * s) ω)

theorem fiberInner_conj_symm (m : ℕ) (s t : ℝ) (h r : SchwartzMap ℝ ℂ) :
    conj (fiberInner m s t r h) = fiberInner m s t h r := by
  have hbase :
      conj (∫ ω : ℝ, ⟪r ω, h ω⟫_ℂ * (|ω| ^ m : ℝ)) =
        ∫ ω : ℝ, ⟪h ω, r ω⟫_ℂ * (|ω| ^ m : ℝ) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with ω
    rw [map_mul, inner_conj_symm]
    norm_num
  have hsobolev :
      conj (∫ ω : ℝ,
        ⟪schwartzBesselPotential t r ω, schwartzBesselPotential t h ω⟫_ℂ *
          japaneseBracketPow (-2 * s) ω) =
        ∫ ω : ℝ,
          ⟪schwartzBesselPotential t h ω, schwartzBesselPotential t r ω⟫_ℂ *
            japaneseBracketPow (-2 * s) ω := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with ω
    rw [map_mul, inner_conj_symm]
    norm_num
  have hcoefficient :
      (starRingEnd ℂ) ((2 * (Real.pi : ℂ)) ^ (m - 1)) =
        (2 * (Real.pi : ℂ)) ^ (m - 1) := by
    rw [starRingEnd_apply, Complex.star_def, map_pow, map_mul, Complex.conj_ofNat,
      Complex.conj_ofReal]
  unfold fiberInner
  rw [map_add, map_mul, hbase, hsobolev, hcoefficient]

theorem fiberInner_add_left (m : ℕ) (s t : ℝ) (h r u : SchwartzMap ℝ ℂ) :
    fiberInner m s t (h + r) u = fiberInner m s t h u + fiberInner m s t r u := by
  unfold fiberInner
  simp only [add_apply, map_add, inner_add_left, add_mul]
  rw [integral_add (integrable_inner_mul_abs_pow m h u)
    (integrable_inner_mul_abs_pow m r u)]
  rw [integral_add
    (integrable_inner_mul_japaneseBracketPow (-2 * s) (schwartzBesselPotential t h)
      (schwartzBesselPotential t u))
    (integrable_inner_mul_japaneseBracketPow (-2 * s) (schwartzBesselPotential t r)
      (schwartzBesselPotential t u))]
  ring

theorem fiberInner_smul_left (m : ℕ) (s t : ℝ) (h r : SchwartzMap ℝ ℂ) (c : ℂ) :
    fiberInner m s t (c • h) r = conj c * fiberInner m s t h r := by
  unfold fiberInner
  simp only [smul_apply, map_smul, inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  ring

theorem fiberInner_self_re (m : ℕ) (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    (fiberInner m s t h h).re = fiberNormSq m s t h := by
  have hbase :
      (∫ ω : ℝ, ⟪h ω, h ω⟫_ℂ * (|ω| ^ m : ℝ)).re =
        ∫ ω : ℝ, ‖h ω‖ ^ 2 * |ω| ^ m := by
    calc
      _ = ∫ ω : ℝ, RCLike.re (⟪h ω, h ω⟫_ℂ * (|ω| ^ m : ℝ)) :=
        (integral_re (integrable_inner_mul_abs_pow m h h)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [RCLike.mul_re, inner_self_eq_norm_sq, inner_self_im, zero_mul, sub_zero]
        congr 1
  have hsobolev :
      (∫ ω : ℝ,
        ⟪schwartzBesselPotential t h ω, schwartzBesselPotential t h ω⟫_ℂ *
          japaneseBracketPow (-2 * s) ω).re =
        ∫ ω : ℝ, ‖schwartzBesselPotential t h ω‖ ^ 2 *
          japaneseBracketPow (-2 * s) ω := by
    calc
      _ = ∫ ω : ℝ, RCLike.re
          (⟪schwartzBesselPotential t h ω, schwartzBesselPotential t h ω⟫_ℂ *
            japaneseBracketPow (-2 * s) ω) :=
        (integral_re (integrable_inner_mul_japaneseBracketPow (-2 * s)
          (schwartzBesselPotential t h) (schwartzBesselPotential t h))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [RCLike.mul_re, inner_self_eq_norm_sq, inner_self_im, zero_mul, sub_zero]
        congr 1
  have hcoefficient :
      (2 * (Real.pi : ℂ)) ^ (m - 1) = ((2 * Real.pi) ^ (m - 1) : ℝ) := by
    push_cast
    rfl
  have hcoefficient_re :
      ((2 * (Real.pi : ℂ)) ^ (m - 1)).re = (2 * Real.pi) ^ (m - 1) := by
    calc
      _ = (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ).re := congrArg Complex.re hcoefficient
      _ = _ := Complex.ofReal_re _
  have hcoefficient_im : ((2 * (Real.pi : ℂ)) ^ (m - 1)).im = 0 := by
    calc
      _ = (((2 * Real.pi) ^ (m - 1) : ℝ) : ℂ).im := congrArg Complex.im hcoefficient
      _ = _ := Complex.ofReal_im _
  rw [fiberNormSq, fiberBaseNormSq, fiberSobolevNormSq]
  unfold fiberInner
  rw [Complex.add_re, Complex.mul_re, hbase, hsobolev, hcoefficient_re, hcoefficient_im]
  norm_num

theorem fiberInner_self_re_nonneg (m : ℕ) (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    0 ≤ (fiberInner m s t h h).re := by
  rw [fiberInner_self_re]
  exact fiberNormSq_nonneg m s t h

theorem fiberInner_self_eq_zero (m : ℕ) (hm : 0 < m) (s t : ℝ) (h : SchwartzMap ℝ ℂ) :
    fiberInner m s t h h = 0 → h = 0 := by
  intro hq
  apply (fiberNormSq_eq_zero_iff m hm s t h).1
  rw [← fiberInner_self_re, hq]
  rfl

/-- A type synonym for the Schwartz fiber core equipped with the paper's inner product. -/
def FiberCore (_m : ℕ) (_s _t : ℝ) := SchwartzMap ℝ ℂ

namespace FiberCore

/-- Forget the fiber-core norm and recover the underlying Schwartz function. -/
def toSchwartz {m : ℕ} {s t : ℝ} (h : FiberCore m s t) : SchwartzMap ℝ ℂ :=
  h

instance instAddCommGroup (m : ℕ) (s t : ℝ) : AddCommGroup (FiberCore m s t) :=
  inferInstanceAs (AddCommGroup (SchwartzMap ℝ ℂ))

instance instModule (m : ℕ) (s t : ℝ) : Module ℂ (FiberCore m s t) :=
  inferInstanceAs (Module ℂ (SchwartzMap ℝ ℂ))

/-- The inner-product core induced by the two terms of the fiber norm. -/
@[reducible]
def innerProductCore (m : ℕ) (hm : 0 < m) (s t : ℝ) :
    InnerProductSpace.Core ℂ (FiberCore m s t) where
  inner := fiberInner m s t
  conj_inner_symm := fiberInner_conj_symm m s t
  re_inner_nonneg := fiberInner_self_re_nonneg m s t
  add_left := fiberInner_add_left m s t
  smul_left := fiberInner_smul_left m s t
  definite := fiberInner_self_eq_zero m hm s t

noncomputable instance instNormedAddCommGroup (m : ℕ) [NeZero m] (s t : ℝ) :
    NormedAddCommGroup (FiberCore m s t) :=
  (innerProductCore m (NeZero.pos m) s t).toNormedAddCommGroup

instance instInnerProductSpace (m : ℕ) [NeZero m] (s t : ℝ) :
    InnerProductSpace ℂ (FiberCore m s t) := .ofCore _

theorem norm_sq_eq_fiberNormSq (m : ℕ) [NeZero m] (s t : ℝ)
    (h : FiberCore m s t) :
    ‖h‖ ^ 2 = fiberNormSq m s t (toSchwartz h) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  exact fiberInner_self_re m s t (toSchwartz h)

end FiberCore

/-- The fiber Hilbert space `H_{s,t}`, defined as the completion of its Schwartz core. -/
abbrev FiberSpace (m : ℕ) [NeZero m] (s t : ℝ) :=
  UniformSpace.Completion (FiberCore m s t)

/-- The Schwartz core has dense image in the completed fiber Hilbert space. -/
theorem denseRange_fiberCore_coe (m : ℕ) [NeZero m] (s t : ℝ) :
    DenseRange (fun h : FiberCore m s t ↦ (h : FiberSpace m s t)) :=
  UniformSpace.Completion.denseRange_coe

end LeanRidgelet
