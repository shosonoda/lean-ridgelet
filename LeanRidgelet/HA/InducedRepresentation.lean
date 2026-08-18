/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Schur
public import LeanRidgelet.ToMathlib.LpUnimodular
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Induced `L²` representations

This file separates the algebra of a quasi-regular action from its realization on an `L²`
quotient. For a left action of `G` on `X`, a multiplier `w` satisfying

`w (g * h) x = w g x * w h (g⁻¹ • x)`

acts pointwise by `f ↦ (fun x ↦ w g x • f (g⁻¹ • x))`. The group law is proved without
measure-theoretic assumptions. The Radon--Nikodym square-root multiplier from a strongly
quasi-invariant measure is recorded separately.

For an invariant measure, Mathlib's `Lp.compMeasurePreserving` supplies the isometric pullback on
the `Lp` quotient. For a strongly quasi-invariant measure, the `withDensity` integral formula and
`Measure.QuasiMeasurePreserving` give norm preservation, a.e. well-definedness, and the unitary
`L²` representation. A final general layer composes this corrected pullback with any measurable
unimodular multiplier cocycle. Mathlib's pointwise `Lp` multiplier isometry supplies the operator,
and a.e. representative identities prove the monoid law without hiding an induction theorem in a
structure field.

## Deviations from the article

Definition 3.1 of the article is stated for invariant measures, while its affine examples require
a Jacobian correction. We retain the invariant construction and add the strongly quasi-invariant
extension. The selected Radon--Nikodym cocycle is assumed explicitly measurable: equality of its
`withDensity` measure with a pushforward measure does not by itself make an arbitrary chosen
representative measurable.
-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace LeanRidgelet

variable {G X E : Type*} [Group G] [MulAction G X]

/-- The pointwise weighted pullback associated with a multiplier `weight`. -/
def quasiRegularAction (weight : G → X → ℂ) (g : G) (f : X → E)
    [SMul ℂ E] : X → E :=
  fun x ↦ weight g x • f (g⁻¹ • x)

@[simp]
theorem quasiRegularAction_apply (weight : G → X → ℂ) (g : G) (f : X → E)
    [SMul ℂ E] (x : X) :
    quasiRegularAction weight g f x = weight g x • f (g⁻¹ • x) := rfl

/-- The identity cocycle law gives the identity weighted pullback. -/
theorem quasiRegularAction_one [AddMonoid E] [DistribMulAction ℂ E]
    (weight : G → X → ℂ) (h_one : ∀ x, weight 1 x = 1) (f : X → E) :
    quasiRegularAction weight 1 f = f := by
  funext x
  simp [quasiRegularAction, h_one]

/-- The cocycle law is exactly the group law for weighted pullbacks. -/
theorem quasiRegularAction_mul [AddMonoid E] [DistribMulAction ℂ E]
    (weight : G → X → ℂ)
    (h_mul : ∀ g h x, weight (g * h) x = weight g x * weight h (g⁻¹ • x))
    (g h : G) (f : X → E) :
    quasiRegularAction weight (g * h) f =
      quasiRegularAction weight g (quasiRegularAction weight h f) := by
  funext x
  simp only [quasiRegularAction, h_mul, mul_inv_rev, mul_smul]

/-- Folland's square-root Radon--Nikodym multiplier
`φ(g, g⁻¹ • x)⁻¹/²`, with a positive cocycle represented in `ℝ≥0`. -/
def radonNikodymWeight (jacobian : G → X → ℝ≥0) (g : G) (x : X) : ℂ :=
  ((jacobian g (g⁻¹ • x)).sqrt : ℂ)⁻¹

@[simp]
theorem radonNikodymWeight_apply (jacobian : G → X → ℝ≥0) (g : G) (x : X) :
    radonNikodymWeight jacobian g x = ((jacobian g (g⁻¹ • x)).sqrt : ℂ)⁻¹ := rfl

/-- The Radon--Nikodym chain rule gives the multiplier cocycle used by the pointwise action. -/
theorem radonNikodymWeight_mul (jacobian : G → X → ℝ≥0)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (g h : G) (x : X) :
    radonNikodymWeight jacobian (g * h) x =
      radonNikodymWeight jacobian g x * radonNikodymWeight jacobian h (g⁻¹ • x) := by
  simp only [radonNikodymWeight, mul_inv_rev, mul_smul]
  rw [h_cocycle, NNReal.sqrt_mul]
  push_cast
  rw [mul_inv]
  simp [← mul_smul]

/-- The unit value of the Radon--Nikodym cocycle gives the unit multiplier. -/
theorem radonNikodymWeight_one (jacobian : G → X → ℝ≥0)
    (h_one : ∀ x, jacobian 1 x = 1) (x : X) :
    radonNikodymWeight jacobian 1 x = 1 := by
  simp [radonNikodymWeight, h_one]

section InvariantMeasure

open MeasureTheory

variable [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {μ : Measure X} [SMulInvariantMeasure G X μ] [MeasurableConstSMul G X]

/-- Pullback by an invariant action, bundled as a linear isometric equivalence of `Lp`. -/
def invariantLpLinearIsometryEquiv (c : Gᵈᵐᵃ) :
    Lp E (2 : ℝ≥0∞) μ ≃ₗᵢ[ℂ] Lp E (2 : ℝ≥0∞) μ where
  __ := DistribMulAction.toLinearEquiv ℂ (Lp E (2 : ℝ≥0∞) μ) c
  norm_map' := DomMulAct.norm_smul_Lp c

omit [CompleteSpace E] in
@[simp]
theorem invariantLpLinearIsometryEquiv_apply (c : Gᵈᵐᵃ)
    (f : Lp E (2 : ℝ≥0∞) μ) :
    invariantLpLinearIsometryEquiv c f = c • f := rfl

/-- The homomorphism `g ↦ op(g⁻¹)` converts the domain action into the usual pullback by
`g⁻¹`. -/
def toDomMulActInv : G →* Gᵈᵐᵃ where
  toFun g := DomMulAct.mk g⁻¹
  map_one' := by
    change MulOpposite.op (1 : G)⁻¹ = 1
    simp
  map_mul' g h := by
    change MulOpposite.op (g * h)⁻¹ = MulOpposite.op g⁻¹ * MulOpposite.op h⁻¹
    rw [mul_inv_rev]
    rfl

/-- An invariant measurable action induces a unitary representation on Bochner `L²`. -/
def invariantLpUnitaryRepresentation :
    UnitaryRepresentation G (Lp E (2 : ℝ≥0∞) μ) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    { toFun := fun g ↦ invariantLpLinearIsometryEquiv (toDomMulActInv g)
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro f
        simp [toDomMulActInv]
      map_mul' := by
        intro g h
        apply LinearIsometryEquiv.ext
        intro f
        simp [toDomMulActInv, mul_smul] }

/-- The invariant-measure representation is represented a.e. by `f(g⁻¹ • x)`. -/
theorem invariantLpUnitaryRepresentation_apply_ae (g : G)
    (f : Lp E (2 : ℝ≥0∞) μ) :
    ((↑(invariantLpUnitaryRepresentation (G := G) (X := X) (E := E) (μ := μ) g) :
      Lp E (2 : ℝ≥0∞) μ →L[ℂ] Lp E (2 : ℝ≥0∞) μ) f) =ᵐ[μ]
        fun x ↦ f (g⁻¹ • x) := by
  exact DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g⁻¹) f

end InvariantMeasure

section QuasiInvariantMeasure

open MeasureTheory

variable [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {μ : Measure X} [SigmaFinite μ]

omit [CompleteSpace E] in
/-- The square of Folland's inverse square-root multiplier cancels its positive density. -/
theorem radonNikodymWeight_enorm_sq_cancel (j : ℝ≥0) (hj : j ≠ 0) (v : E) :
    (j : ℝ≥0∞) * ‖((j.sqrt : ℂ)⁻¹ • v)‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  have hsj : j.sqrt ≠ 0 := by simpa using hj
  have hs : ‖(j.sqrt : ℂ)‖₊ = j.sqrt := by
    ext
    simp
  have hj_coe : (j : ℝ≥0∞) = (j.sqrt : ℝ≥0∞) ^ 2 := by
    rw [← ENNReal.coe_pow, NNReal.sq_sqrt]
  simp only [enorm_eq_nnnorm, nnnorm_smul, nnnorm_inv, hs, ENNReal.coe_mul,
    ENNReal.coe_inv hsj, mul_pow]
  rw [hj_coe]
  have hs0 : (j.sqrt : ℝ≥0∞) ≠ 0 := by exact_mod_cast hsj
  rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hs0 ENNReal.coe_ne_top]
  simp

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The `withDensity` change-of-variables identity gives preservation of the squared extended norm
by the Radon--Nikodym-corrected pullback. No measurability of the vector-valued representative is
needed at this stage: the action is a measurable equivalence, and the density is finite. -/
theorem quasiRegularAction_lintegral_enorm_sq (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (g : G) (f : X → E) :
    (∫⁻ x, ‖quasiRegularAction (radonNikodymWeight jacobian) g f x‖ₑ ^ 2 ∂μ) =
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  let e : X ≃ᵐ X :=
    { toEquiv :=
        { toFun := fun x ↦ g⁻¹ • x
          invFun := fun x ↦ g • x
          left_inv := fun x ↦ smul_inv_smul g x
          right_inv := fun x ↦ inv_smul_smul g x }
      measurable_toFun := h_measurable g⁻¹
      measurable_invFun := h_measurable g }
  let F : X → ℝ≥0∞ := fun x ↦ ‖((jacobian g x).sqrt : ℂ)⁻¹ • f x‖ₑ ^ 2
  calc
    (∫⁻ x, ‖quasiRegularAction (radonNikodymWeight jacobian) g f x‖ₑ ^ 2 ∂μ) =
        ∫⁻ x, F (e x) ∂μ := rfl
    _ = ∫⁻ x, F x ∂μ.map e := (e.measurableEmbedding.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ.withDensity (fun x ↦ (jacobian g x : ℝ≥0∞)) := by
      rw [show μ.map e = μ.withDensity (fun x ↦ (jacobian g x : ℝ≥0∞)) by
        simpa [e] using h_map g]
    _ = ∫⁻ x, (jacobian g x : ℝ≥0∞) * F x ∂μ := by
      simpa only [Pi.mul_apply] using
        lintegral_withDensity_eq_lintegral_mul_non_measurable μ
          (h_jacobian g).coe_nnreal_ennreal
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.coe_lt_top) F
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
      apply lintegral_congr
      intro x
      exact radonNikodymWeight_enorm_sq_cancel (jacobian g x) (h_ne_zero g x) (f x)

omit [SigmaFinite μ] [CompleteSpace E] in
/-- Folland's corrected pullback preserves the `L²` extended seminorm. -/
theorem quasiRegularAction_eLpNorm_two (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (g : G) (f : X → E) :
    eLpNorm (quasiRegularAction (radonNikodymWeight jacobian) g f) 2 μ =
      eLpNorm f 2 μ := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  change
    (∫⁻ x, ‖quasiRegularAction (radonNikodymWeight jacobian) g f x‖ₑ ^ (2 : ℝ) ∂μ) ^
        (1 / (2 : ℝ)) =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
  simp only [ENNReal.rpow_two]
  rw [quasiRegularAction_lintegral_enorm_sq jacobian h_measurable h_map h_jacobian
    h_ne_zero g f]

omit [SigmaFinite μ] in
/-- The translated map is quasi-measure-preserving whenever its pushforward has a density with
respect to the original measure. -/
theorem quasiMeasurePreserving_of_map_eq_withDensity (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (g : G) : Measure.QuasiMeasurePreserving (fun x : X ↦ g⁻¹ • x) μ μ where
  measurable := h_measurable g⁻¹
  absolutelyContinuous := by
    rw [h_map g]
    exact withDensity_absolutelyContinuous μ _

/-- A measurable Radon--Nikodym cocycle gives a measurable square-root multiplier. -/
theorem radonNikodymWeight_measurable (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_jacobian : ∀ g : G, Measurable (jacobian g)) (g : G) :
    Measurable (radonNikodymWeight jacobian g) := by
  unfold radonNikodymWeight
  fun_prop

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The corrected pullback of an a.e. strongly measurable representative remains a.e. strongly
measurable. Positivity of the density is not needed for this direction. -/
theorem quasiRegularAction_aestronglyMeasurable (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g)) (g : G) (f : X → E)
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (quasiRegularAction (radonNikodymWeight jacobian) g f) μ := by
  have hw := (radonNikodymWeight_measurable jacobian h_measurable h_jacobian g)
    |>.aestronglyMeasurable (μ := μ)
  have hcomp := hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_of_map_eq_withDensity jacobian h_measurable h_map g)
  change AEStronglyMeasurable
    (radonNikodymWeight jacobian g • fun x ↦ f (g⁻¹ • x)) μ
  exact hw.smul hcomp

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The corrected pullback sends square-integrable representatives to square-integrable
representatives. -/
theorem quasiRegularAction_memLp_two (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (g : G) (f : X → E)
    (hf : MemLp f 2 μ) :
    MemLp (quasiRegularAction (radonNikodymWeight jacobian) g f) 2 μ := by
  refine ⟨quasiRegularAction_aestronglyMeasurable jacobian h_measurable h_map h_jacobian
    g f hf.1, ?_⟩
  rw [quasiRegularAction_eLpNorm_two jacobian h_measurable h_map h_jacobian h_ne_zero g f]
  exact hf.2

/-- Folland's corrected pullback, bundled as a linear isometry of the `L²` quotient. -/
noncomputable def quasiInvariantLpLinearIsometry (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (g : G) :
    Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 μ where
  toFun f := (quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
    h_ne_zero g f (Lp.memLp f)).toLp _
  map_add' f k := by
    let hsum := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ (f + k) x) (Lp.memLp (f + k))
    let hf := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ f x) (Lp.memLp f)
    let hk := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ k x) (Lp.memLp k)
    change hsum.toLp _ = hf.toLp _ + hk.toLp _
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have hq := quasiMeasurePreserving_of_map_eq_withDensity jacobian h_measurable h_map g
    filter_upwards [hq.ae_eq (Lp.coeFn_add f k)] with x hx
    simp only [Function.comp_apply, Pi.add_apply] at hx
    simp only [quasiRegularAction, Pi.add_apply]
    rw [hx, smul_add]
  map_smul' c f := by
    let hcf := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ (c • f) x) (Lp.memLp (c • f))
    let hf := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ f x) (Lp.memLp f)
    change hcf.toLp _ = c • hf.toLp _
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have hq := quasiMeasurePreserving_of_map_eq_withDensity jacobian h_measurable h_map g
    filter_upwards [hq.ae_eq (Lp.coeFn_smul c f)] with x hx
    simp only [Function.comp_apply, Pi.smul_apply] at hx
    simp only [quasiRegularAction, Pi.smul_apply]
    rw [hx]
    simp only [smul_smul]
    rw [mul_comm]
  norm_map' f := by
    let hf := quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
      h_ne_zero g (fun x ↦ f x) (Lp.memLp f)
    change ‖hf.toLp _‖ = ‖f‖
    calc
      ‖hf.toLp _‖ = ENNReal.toReal
          (eLpNorm (quasiRegularAction (radonNikodymWeight jacobian) g fun x ↦ f x) 2 μ) :=
        Lp.norm_toLp _ hf
      _ = ENNReal.toReal (eLpNorm (fun x ↦ f x) 2 μ) := congrArg ENNReal.toReal
        (quasiRegularAction_eLpNorm_two jacobian h_measurable h_map h_jacobian
          h_ne_zero g fun x ↦ f x)
      _ = ‖f‖ := (Lp.norm_def f).symm

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The `L²` linear isometry has Folland's corrected pullback as an a.e. representative. -/
theorem quasiInvariantLpLinearIsometry_apply_ae (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (g : G) (f : Lp E 2 μ) :
    quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero g f
        =ᵐ[μ] quasiRegularAction (radonNikodymWeight jacobian) g fun x ↦ f x :=
  MemLp.coeFn_toLp (quasiRegularAction_memLp_two jacobian h_measurable h_map h_jacobian
    h_ne_zero g (fun x ↦ f x) (Lp.memLp f))

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The cocycle law descends from representatives to composition of the `L²` isometries. -/
theorem quasiInvariantLpLinearIsometry_mul_apply (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (g h : G) (f : Lp E 2 μ) :
    quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero
        (g * h) f =
      quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero g
        (quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero h f) :=
    by
  apply Lp.ext
  have hgh := quasiInvariantLpLinearIsometry_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero (g * h) f
  have hg := quasiInvariantLpLinearIsometry_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero g
      (quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero h f)
  have hh := quasiInvariantLpLinearIsometry_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero h f
  have hcomp := (quasiMeasurePreserving_of_map_eq_withDensity jacobian h_measurable h_map g)
    |>.ae_eq hh
  filter_upwards [hgh, hg, hcomp] with x hghx hgx hhx
  simp only [Function.comp_apply] at hhx
  rw [hghx, hgx]
  calc
    quasiRegularAction (radonNikodymWeight jacobian) (g * h) (fun x ↦ f x) x =
      quasiRegularAction (radonNikodymWeight jacobian) g
        (quasiRegularAction (radonNikodymWeight jacobian) h fun x ↦ f x) x := congrFun
          (quasiRegularAction_mul _ (radonNikodymWeight_mul jacobian h_cocycle)
            g h fun x ↦ f x) x
    _ = quasiRegularAction (radonNikodymWeight jacobian) g
        (fun x ↦ quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian
          h_ne_zero h f x) x := by
      simp only [quasiRegularAction]
      rw [hhx]
      rfl

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The identity cocycle descends to the identity isometry of `L²`. -/
theorem quasiInvariantLpLinearIsometry_one_apply (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (f : Lp E 2 μ) :
    quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero 1 f =
      f := by
  apply Lp.ext
  have hU := quasiInvariantLpLinearIsometry_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero 1 f
  filter_upwards [hU] with x hx
  rw [hx]
  exact congrFun
    (quasiRegularAction_one _ (radonNikodymWeight_one jacobian h_one) fun x ↦ f x) x

omit [SigmaFinite μ] [CompleteSpace E] in
/-- The inverse group element supplies a preimage for the corrected pullback isometry. -/
theorem quasiInvariantLpLinearIsometry_surjective (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (g : G) : Function.Surjective
      (quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero g :
        Lp E 2 μ → Lp E 2 μ) := by
  intro f
  refine ⟨quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian
    h_ne_zero g⁻¹ f, ?_⟩
  have hmul := quasiInvariantLpLinearIsometry_mul_apply jacobian h_measurable h_map
    h_jacobian h_ne_zero h_cocycle g g⁻¹ f
  rw [mul_inv_cancel, quasiInvariantLpLinearIsometry_one_apply jacobian h_measurable h_map
    h_jacobian h_ne_zero h_one] at hmul
  exact hmul.symm

/-- Folland's corrected pullback, bundled as a linear isometric equivalence of `L²`. -/
noncomputable def quasiInvariantLpLinearIsometryEquiv (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (g : G) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective
    (quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero g)
    (quasiInvariantLpLinearIsometry_surjective jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one h_cocycle g)

/-- The corrected `L²` isometries form a group representation. -/
noncomputable def quasiInvariantLpLinearIsometryEquivMonoidHom (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x) :
    G →* (Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ) where
  toFun g := quasiInvariantLpLinearIsometryEquiv jacobian h_measurable h_map h_jacobian
    h_ne_zero h_one h_cocycle g
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian
      h_ne_zero 1 f = f
    exact quasiInvariantLpLinearIsometry_one_apply jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one f
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    change quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian h_ne_zero
      (g * h) f = quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian
        h_ne_zero g (quasiInvariantLpLinearIsometry jacobian h_measurable h_map h_jacobian
          h_ne_zero h f)
    exact quasiInvariantLpLinearIsometry_mul_apply jacobian h_measurable h_map h_jacobian
      h_ne_zero h_cocycle g h f

/-- A strongly quasi-invariant measure with a measurable positive Radon--Nikodym cocycle induces
Folland's unitary representation on Bochner `L²`. -/
noncomputable def quasiInvariantLpUnitaryRepresentation (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x) :
    UnitaryRepresentation G (Lp E 2 μ) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (quasiInvariantLpLinearIsometryEquivMonoidHom jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one h_cocycle)

omit [SigmaFinite μ] in
/-- The quasi-invariant `L²` representation is represented a.e. by Folland's corrected pullback. -/
theorem quasiInvariantLpUnitaryRepresentation_apply_ae (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (g : G) (f : Lp E 2 μ) :
    ((↑(quasiInvariantLpUnitaryRepresentation (E := E) jacobian h_measurable h_map
      h_jacobian h_ne_zero h_one h_cocycle g) : Lp E 2 μ →L[ℂ] Lp E 2 μ) f) =ᵐ[μ]
        quasiRegularAction (radonNikodymWeight jacobian) g fun x ↦ f x := by
  exact quasiInvariantLpLinearIsometry_apply_ae jacobian h_measurable h_map h_jacobian
    h_ne_zero g f

/-- Compose the Radon--Nikodym-corrected pullback with a measurable unimodular multiplier.  This
is the operator underlying a character-twisted quasi-regular representation. -/
noncomputable def twistedQuasiInvariantLpLinearIsometryEquiv (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (phase : G → X → ℂ) (h_phase_measurable : ∀ g, AEStronglyMeasurable (phase g) μ)
    (h_phase_norm : ∀ g, ∀ᵐ x ∂μ, ‖phase g x‖ = 1) (g : G) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  (Unitary.linearIsometryEquiv
    (quasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one h_cocycle g)).trans
    (unimodularMultiplierLinearIsometryEquiv (phase g)
      (h_phase_measurable g) (h_phase_norm g))

omit [SigmaFinite μ] in
/-- The twisted isometry is represented by the product of the phase, the Radon--Nikodym weight,
and inverse pullback. -/
theorem twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae
    (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (phase : G → X → ℂ) (h_phase_measurable : ∀ g, AEStronglyMeasurable (phase g) μ)
    (h_phase_norm : ∀ g, ∀ᵐ x ∂μ, ‖phase g x‖ = 1) (g : G) (f : Lp ℂ 2 μ) :
    twistedQuasiInvariantLpLinearIsometryEquiv jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm g f =ᵐ[μ]
      fun x ↦ phase g x * (radonNikodymWeight jacobian g x * f (g⁻¹ • x)) := by
  change
    (unimodularMultiplierLinearIsometryEquiv (phase g)
      (h_phase_measurable g) (h_phase_norm g)
      (Unitary.linearIsometryEquiv
        (quasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map h_jacobian
          h_ne_zero h_one h_cocycle g) f)) =ᵐ[μ] _
  have hb := quasiInvariantLpUnitaryRepresentation_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero h_one h_cocycle g f
  have hb' :
      (Unitary.linearIsometryEquiv
        (quasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map h_jacobian
          h_ne_zero h_one h_cocycle g) f : Lp ℂ 2 μ) =ᵐ[μ]
        quasiRegularAction (radonNikodymWeight jacobian) g fun x ↦ f x := by
    exact hb
  have hp := unimodularMultiplierLinearIsometryEquiv_apply_ae (phase g)
    (h_phase_measurable g) (h_phase_norm g)
    (Unitary.linearIsometryEquiv
      (quasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map h_jacobian
        h_ne_zero h_one h_cocycle g) f)
  filter_upwards [hb', hp] with x hbx hpx
  rw [hpx, hbx]
  rfl

/-- A unimodular multiplier cocycle upgrades the quasi-invariant isometries to a monoid
homomorphism. -/
noncomputable def twistedQuasiInvariantLpLinearIsometryEquivMonoidHom
    (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (phase : G → X → ℂ) (h_phase_measurable : ∀ g, AEStronglyMeasurable (phase g) μ)
    (h_phase_norm : ∀ g, ∀ᵐ x ∂μ, ‖phase g x‖ = 1)
    (h_phase_one : ∀ x, phase 1 x = 1)
    (h_phase_cocycle : ∀ g h x, phase (g * h) x = phase g x * phase h (g⁻¹ • x)) :
    G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun := twistedQuasiInvariantLpLinearIsometryEquiv jacobian h_measurable h_map
    h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Lp.ext
    have h := twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae jacobian h_measurable
      h_map h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm 1 f
    filter_upwards [h] with x hx
    rw [hx]
    simp [h_phase_one, radonNikodymWeight, h_one]
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Lp.ext
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    have hgh := twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae jacobian h_measurable
      h_map h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm
      (g * h) f
    have hh := twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae jacobian h_measurable
      h_map h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm h f
    have hg := twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae jacobian h_measurable
      h_map h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm g
      (twistedQuasiInvariantLpLinearIsometryEquiv jacobian h_measurable h_map h_jacobian
        h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm h f)
    have hqmp := quasiMeasurePreserving_of_map_eq_withDensity jacobian h_measurable h_map g
    have hhp := hqmp.ae_eq hh
    filter_upwards [hgh, hg, hhp] with x hghx hgx hhx
    rw [hghx, hgx]
    simp only [Function.comp_apply] at hhx
    rw [hhx]
    rw [h_phase_cocycle, radonNikodymWeight_mul jacobian h_cocycle]
    simp only [mul_inv_rev, mul_smul]
    ring

/-- A strongly quasi-invariant measure together with a measurable unimodular multiplier cocycle
gives the character-twisted quasi-regular unitary representation on scalar `L²`. -/
noncomputable def twistedQuasiInvariantLpUnitaryRepresentation
    (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (phase : G → X → ℂ) (h_phase_measurable : ∀ g, AEStronglyMeasurable (phase g) μ)
    (h_phase_norm : ∀ g, ∀ᵐ x ∂μ, ‖phase g x‖ = 1)
    (h_phase_one : ∀ x, phase 1 x = 1)
    (h_phase_cocycle : ∀ g h x, phase (g * h) x = phase g x * phase h (g⁻¹ • x)) :
    UnitaryRepresentation G (Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp
    (twistedQuasiInvariantLpLinearIsometryEquivMonoidHom jacobian h_measurable h_map
      h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm
      h_phase_one h_phase_cocycle)

omit [SigmaFinite μ] in
/-- The character-twisted representation has the expected phase-times-corrected-pullback
representative. -/
theorem twistedQuasiInvariantLpUnitaryRepresentation_apply_ae
    (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x)
    (phase : G → X → ℂ) (h_phase_measurable : ∀ g, AEStronglyMeasurable (phase g) μ)
    (h_phase_norm : ∀ g, ∀ᵐ x ∂μ, ‖phase g x‖ = 1)
    (h_phase_one : ∀ x, phase 1 x = 1)
    (h_phase_cocycle : ∀ g h x, phase (g * h) x = phase g x * phase h (g⁻¹ • x))
    (g : G) (f : Lp ℂ 2 μ) :
    ((↑(twistedQuasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map
      h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm
      h_phase_one h_phase_cocycle g) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) f) =ᵐ[μ]
      fun x ↦ phase g x * (radonNikodymWeight jacobian g x * f (g⁻¹ • x)) := by
  exact twistedQuasiInvariantLpLinearIsometryEquiv_apply_ae jacobian h_measurable h_map
    h_jacobian h_ne_zero h_one h_cocycle phase h_phase_measurable h_phase_norm g f

omit [SigmaFinite μ] in
/-- Existence form of `quasiInvariantLpUnitaryRepresentation`, retained for theorem-level uses. -/
theorem exists_quasiInvariantLpUnitaryRepresentation (jacobian : G → X → ℝ≥0)
    (h_measurable : ∀ g : G, Measurable fun x : X ↦ g • x)
    (h_map : ∀ g : G,
      μ.map (fun x ↦ g⁻¹ • x) = μ.withDensity fun x ↦ (jacobian g x : ℝ≥0∞))
    (h_jacobian : ∀ g : G, Measurable (jacobian g))
    (h_ne_zero : ∀ g x, jacobian g x ≠ 0) (h_one : ∀ x, jacobian 1 x = 1)
    (h_cocycle : ∀ g h x, jacobian (g * h) x = jacobian g (h • x) * jacobian h x) :
    ∃ π : UnitaryRepresentation G (Lp E 2 μ),
      ∀ (g : G) (f : Lp E 2 μ),
        ((↑(π g) : Lp E 2 μ →L[ℂ] Lp E 2 μ) f) =ᵐ[μ]
          quasiRegularAction (radonNikodymWeight jacobian) g fun x ↦ f x := by
  exact ⟨quasiInvariantLpUnitaryRepresentation jacobian h_measurable h_map h_jacobian
    h_ne_zero h_one h_cocycle,
    quasiInvariantLpUnitaryRepresentation_apply_ae jacobian h_measurable h_map h_jacobian
      h_ne_zero h_one h_cocycle⟩

end QuasiInvariantMeasure

end LeanRidgelet
