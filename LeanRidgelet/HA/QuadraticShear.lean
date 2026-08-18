/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import LeanRidgelet.HA.QuadraticParameterFactor

/-!
# The quadratic parameter action is a shear in the constant coefficient

`LeanRidgelet.HA.QuadraticTransfer` moves a derivative in the constant coefficient of a quadratic
parameter onto the analysis feature, and `LeanRidgelet.HA.QuadraticWeighted` turns that into a
frequency-weighted `L²` identity for each slice in that coefficient.  The intermediate coefficient
space those two results point at is a Sobolev structure in the *last* coordinate of the parameter
space, informally `Γ^k = L²(base; H^k(ℝ))` with the base the first two coefficients.  Whether such a
space is usable depends on how the group acts on it, and that is what this file settles.

Reading `LeanRidgelet.quadraticParameterLinearEquiv_apply`, the parameter action of `g` sends
`(A, b, c)` to `(A', b', c + s)` where `A'`, `b'` and `s` depend on `A` and `b` only.  So the action
is a **shear** in the constant coefficient: a linear automorphism of the base parameter, together
with a base-dependent *translation* of the last coordinate.  Two consequences follow with no
analysis at all.  Differentiation in the last coordinate commutes with the pull-back along the
action on the nose — no Jacobian factor, because a translation has derivative one — and the `L²`
norm in the last coordinate is unchanged by the pull-back, because Lebesgue measure on the line is
translation invariant.  Neither statement needs the Fourier transform, which is why the Sobolev
structure is put in this coordinate rather than transported to the Fourier side.

## Main results

* `LeanRidgelet.quadraticParameterLinearEquiv_apply_shear`: the shear form of the parameter action,
  with `A'` and `b'` the two components of the linear automorphism
  `LeanRidgelet.quadraticBaseLinearEquiv` of the base parameter and `s` the linear functional
  `LeanRidgelet.quadraticConstShift` of it.  Against
  `LeanRidgelet.quadraticParameterLinearEquiv_apply` the first two components hold by `rfl` and the
  third needs one reassociation of addition; the shear is definitional.
* `LeanRidgelet.hasDerivAt_quadraticConstSlice_comp_smul` and
  `LeanRidgelet.iteratedDeriv_quadraticConstSlice_comp_smul`: differentiating the pull-back in the
  constant coefficient is the pull-back of the derivative, at a point and iterated.  Both are
  unconditional; the iterated form needs no differentiability hypothesis at all.
* `LeanRidgelet.quadraticConstIteratedDeriv_comp_smul`: the same identity read as equivariance of
  the derivative in the constant coefficient, as a function on the whole parameter space.
* `LeanRidgelet.eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul`: slice-wise invariance of the
  `Lᵖ` norm in the constant coefficient of the `j`-th derivative, with constant exactly `1`.
* `LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul`: the same integrated over the
  whole parameter space against `LeanRidgelet.quadraticRelativeMeasure`, where the constant is the
  one the quasi-invariance of that measure contributes, namely `‖det L‖₊`.
* `LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul`: the previous result
  pushed through the factorization of `LeanRidgelet.HA.QuadraticParameterFactor`, so that it reads
  as an identity of iterated integrals over the base parameter and the constant coefficient — the
  shape of the `Γ^k` seminorm.

## What is established and what is not

Established: the shear, the commutation of the last-coordinate derivative with the action, and the
invariance of the last-coordinate `L²` seminorm of each derivative, both slice-wise (constant `1`)
and globally against the relatively invariant parameter measure (constant `‖det L‖₊`, exactly the
reciprocal of the Radon--Nikodym constant of
`LeanRidgelet.quadraticRelativeParameter_group_map_eq_withDensity`, so that the same square-root
normalization that makes the parameter representation unitary makes the seminorms invariant on the
nose).

**Not** established, and deliberately not attempted: there is no type `Γ^k` here.  This file defines
no space, no norm on a space, and therefore claims invariance of no space.  A subsequent file that
wants `Γ^k` still has to choose a carrier (a subtype of `L²` of the parameter measure cut out by
finiteness of the seminorms below, or an `Lp`-valued `Lp` space through the factorization), prove it
complete, promote the seminorm identities below into an isometry or a bounded action on that
carrier, and only then can the analysis and synthesis bounds be stated through it.  What is settled
here is that no obstruction lives in the group action: the action does not differentiate, does not
rescale the last coordinate, and contributes only the constant that the parameter measure
contributes anyway.

One measurability hypothesis is genuinely needed and is left explicit rather than discharged: the
derivative in the constant coefficient, as a function on the parameter space, is assumed measurable
in the two integrated statements.  There is no measurability of `iteratedDeriv` in a parameter
anywhere in this development, and the honest thing is to carry it as a hypothesis; compare the
corresponding remark in `LeanRidgelet.HA.QuadraticWeighted`.  The additive Haar measure `lam`
appears as a hypothesis of
`LeanRidgelet.lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul` without appearing in its
conclusion: it is only a witness, used to route the base-level statement through the
quasi-invariance that is proved on the full parameter space, since no quasi-invariance of the base
parameter measure is available.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LeanRidgelet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The shear -/

/-- **The action on the base parameter.**  The first two coefficients of `g • (A, b, c)`, as a
linear automorphism of the base parameter `(A, b)`: congruence by the inverse linear part on the
symmetric coefficient, and the adjoint of the inverse linear part on the linear coefficient, skewed
by the translation block `LeanRidgelet.quadraticShearVector`.  The constant coefficient does not
enter, which is the first half of the shear. -/
def quadraticBaseLinearEquiv (g : E ≃ᵃ[ℝ] E) :
    (QuadraticSymmetric E × E) ≃ₗ[ℝ] (QuadraticSymmetric E × E) :=
  (quadraticCongr g.linear.symm).skewProd g.linear.symm.adjoint
    ((-2 : ℝ) • quadraticShearVector g)

/-- The two components of the base action, read off the skew product. -/
@[simp]
theorem quadraticBaseLinearEquiv_apply (g : E ≃ᵃ[ℝ] E) (A : QuadraticSymmetric E) (b : E) :
    quadraticBaseLinearEquiv g (A, b) =
      (quadraticCongr g.linear.symm A,
        g.linear.symm.adjoint b + (-2 : ℝ) • quadraticShearVector g A) := rfl

/-- **The shift of the constant coefficient.**  The amount by which the parameter action of `g`
displaces the constant coefficient.  It is a linear functional of the base parameter alone, which is
the second half of the shear. -/
def quadraticConstShift (g : E ≃ᵃ[ℝ] E) : (QuadraticSymmetric E × E) →ₗ[ℝ] ℝ :=
  (quadraticLinearShear g).comp (LinearMap.snd ℝ (QuadraticSymmetric E) E) +
    ((innerSL ℝ (g 0)).toLinearMap.comp (quadraticShearVector g)).comp
      (LinearMap.fst ℝ (QuadraticSymmetric E) E)

/-- The shift of the constant coefficient, as the sum of its linear and symmetric blocks. -/
@[simp]
theorem quadraticConstShift_apply (g : E ≃ᵃ[ℝ] E) (A : QuadraticSymmetric E) (b : E) :
    quadraticConstShift g (A, b) =
      quadraticLinearShear g b + ⟪g 0, quadraticShearVector g A⟫_ℝ := rfl

/-- **The parameter action is a shear in the constant coefficient.**  For every affine `g` the
parameter action sends `(A, b, c)` to `(A' (A, b), b' (A, b), c + s (A, b))`: the first two
components are a function of the first two components alone, and the third is the old constant
coefficient plus a quantity independent of it.  The shear is definitional: against
`LeanRidgelet.quadraticParameterLinearEquiv_apply` the first two components hold by `rfl` and the
third needs exactly one reassociation of addition, as the proof shows. -/
theorem quadraticParameterLinearEquiv_apply_shear (g : E ≃ᵃ[ℝ] E) (A : QuadraticSymmetric E)
    (b : E) (c : ℝ) :
    quadraticParameterLinearEquiv g (A, b, c) =
      ((quadraticBaseLinearEquiv g (A, b)).1, (quadraticBaseLinearEquiv g (A, b)).2,
        c + quadraticConstShift g (A, b)) :=
  Prod.ext rfl (Prod.ext rfl (add_assoc _ _ _))

/-- The shear form of the parameter action at an unsplit parameter. -/
theorem quadraticParameterLinearEquiv_eq_shear (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticParameterLinearEquiv g ξ =
      ((quadraticBaseLinearEquiv g (ξ.1, ξ.2.1)).1, (quadraticBaseLinearEquiv g (ξ.1, ξ.2.1)).2,
        ξ.2.2 + quadraticConstShift g (ξ.1, ξ.2.1)) :=
  quadraticParameterLinearEquiv_apply_shear g ξ.1 ξ.2.1 ξ.2.2

/-- **The shear, in existential form.**  For every affine `g` there is a linear automorphism `F` of
the base parameter and a linear functional `s` on it such that the parameter action of `g` is
`(A, b, c) ↦ ((F (A, b)).1, (F (A, b)).2, c + s (A, b))`, uniformly in `c`. -/
theorem exists_quadraticParameterLinearEquiv_shear (g : E ≃ᵃ[ℝ] E) :
    ∃ (F : (QuadraticSymmetric E × E) ≃ₗ[ℝ] (QuadraticSymmetric E × E))
      (s : (QuadraticSymmetric E × E) →ₗ[ℝ] ℝ),
      ∀ (A : QuadraticSymmetric E) (b : E) (c : ℝ),
        quadraticParameterLinearEquiv g (A, b, c) =
          ((F (A, b)).1, (F (A, b)).2, c + s (A, b)) :=
  ⟨quadraticBaseLinearEquiv g, quadraticConstShift g,
    quadraticParameterLinearEquiv_apply_shear g⟩

/-- **The shear, in difference form.**  Changing the constant coefficient of the argument leaves the
first two components of the transformed parameter alone and moves its constant coefficient by
exactly the same amount.  No reference to the explicit blocks is made. -/
theorem quadraticParameterLinearEquiv_apply_const_add (g : E ≃ᵃ[ℝ] E) (A : QuadraticSymmetric E)
    (b : E) (c d : ℝ) :
    quadraticParameterLinearEquiv g (A, b, c + d) =
      ((quadraticParameterLinearEquiv g (A, b, c)).1,
        (quadraticParameterLinearEquiv g (A, b, c)).2.1,
        (quadraticParameterLinearEquiv g (A, b, c)).2.2 + d) := by
  simp only [quadraticParameterLinearEquiv_apply_shear, Prod.mk.injEq, true_and]
  ring

/-! ### Commutation with differentiation in the constant coefficient -/

/-- The slice of a function on the quadratic parameter space in the constant coefficient, at a
frozen base parameter.  This is the object `LeanRidgelet.HA.QuadraticWeighted` estimates. -/
def quadraticConstSlice (T : QuadraticParameter E → ℂ) (p : QuadraticSymmetric E × E) : ℝ → ℂ :=
  fun t ↦ T (p.1, p.2, t)

/-- **The pull-back is a translated slice.**  Pulling back along the parameter action and then
slicing in the constant coefficient gives the slice at the transformed base parameter, translated by
the shift.  Nothing else happens: in particular the last coordinate is not rescaled. -/
theorem quadraticConstSlice_comp_smul (T : QuadraticParameter E → ℂ) (g : E ≃ᵃ[ℝ] E)
    (p : QuadraticSymmetric E × E) :
    quadraticConstSlice (fun η ↦ T (g • η)) p =
      fun t ↦ quadraticConstSlice T (quadraticBaseLinearEquiv g p)
        (t + quadraticConstShift g p) := by
  funext t
  change T (quadraticParameterLinearEquiv g (p.1, p.2, t)) = _
  rw [quadraticParameterLinearEquiv_apply_shear]
  rfl

/-- **Commutation with differentiation, at a point.**  If the slice of `T` at the transformed base
parameter has derivative `T'` at the shifted point, then the slice of the pull-back of `T` has the
*same* derivative `T'` at the unshifted point.  No factor appears, because the shear translates the
constant coefficient instead of rescaling it. -/
theorem hasDerivAt_quadraticConstSlice_comp_smul {T : QuadraticParameter E → ℂ} {T' : ℂ}
    (g : E ≃ᵃ[ℝ] E) (p : QuadraticSymmetric E × E) (c : ℝ)
    (h : HasDerivAt (quadraticConstSlice T (quadraticBaseLinearEquiv g p)) T'
      (c + quadraticConstShift g p)) :
    HasDerivAt (quadraticConstSlice (fun η ↦ T (g • η)) p) T' c := by
  rw [quadraticConstSlice_comp_smul]
  exact HasDerivAt.comp_add_const c (quadraticConstShift g p) h

/-- **Iterating the commutation.**  The `j`-th derivative in the constant coefficient of the slice
of the pull-back is the `j`-th derivative of the slice at the transformed base parameter, evaluated
at the shifted point.  Compare
`LeanRidgelet.iteratedDeriv_bochnerRidgelet_quadraticVectorFeature`, which is stated the same way,
as an equality of functions of the constant coefficient.  Unlike that result this one needs no
hypotheses: translation invariance of `iteratedDeriv` holds for every function. -/
theorem iteratedDeriv_quadraticConstSlice_comp_smul (j : ℕ) (T : QuadraticParameter E → ℂ)
    (g : E ≃ᵃ[ℝ] E) (p : QuadraticSymmetric E × E) :
    iteratedDeriv j (quadraticConstSlice (fun η ↦ T (g • η)) p) =
      fun c ↦ iteratedDeriv j (quadraticConstSlice T (quadraticBaseLinearEquiv g p))
        (c + quadraticConstShift g p) := by
  rw [quadraticConstSlice_comp_smul, iteratedDeriv_comp_add_const]

/-- The `j`-th derivative in the constant coefficient of a function on the quadratic parameter
space, again as a function on the parameter space.  This is the object whose `L²` norm is the `j`-th
`Γ`-seminorm. -/
def quadraticConstIteratedDeriv (j : ℕ) (T : QuadraticParameter E → ℂ) :
    QuadraticParameter E → ℂ :=
  fun ξ ↦ iteratedDeriv j (quadraticConstSlice T (ξ.1, ξ.2.1)) ξ.2.2

/-- **Equivariance of the derivative in the constant coefficient.**  The `j`-th derivative in the
constant coefficient of a pull-back is the pull-back of the `j`-th derivative, with no factor and at
every parameter.  This is `LeanRidgelet.iteratedDeriv_quadraticConstSlice_comp_smul` read on the
whole parameter space, and it is what makes the `Γ`-seminorms below transform like the parameter
measure. -/
theorem quadraticConstIteratedDeriv_comp_smul (j : ℕ) (T : QuadraticParameter E → ℂ)
    (g : E ≃ᵃ[ℝ] E) (ξ : QuadraticParameter E) :
    quadraticConstIteratedDeriv j (fun η ↦ T (g • η)) ξ =
      quadraticConstIteratedDeriv j T (g • ξ) := by
  have h := iteratedDeriv_quadraticConstSlice_comp_smul j T g (ξ.1, ξ.2.1)
  change iteratedDeriv j (quadraticConstSlice (fun η ↦ T (g • η)) (ξ.1, ξ.2.1)) ξ.2.2 = _
  rw [h]
  change _ = iteratedDeriv j (quadraticConstSlice T
    ((quadraticParameterLinearEquiv g ξ).1, (quadraticParameterLinearEquiv g ξ).2.1))
      (quadraticParameterLinearEquiv g ξ).2.2
  rw [quadraticParameterLinearEquiv_eq_shear]

/-- The pull-back of the derivative in the constant coefficient, as a composition.  This is the form
the measure-theoretic statements consume. -/
theorem quadraticConstIteratedDeriv_comp_smul_eq (j : ℕ) (T : QuadraticParameter E → ℂ)
    (g : E ≃ᵃ[ℝ] E) :
    quadraticConstIteratedDeriv j (fun η ↦ T (g • η)) =
      fun ξ ↦ quadraticConstIteratedDeriv j T (g • ξ) :=
  funext (quadraticConstIteratedDeriv_comp_smul j T g)

/-! ### Invariance of the Sobolev seminorms in the constant coefficient -/

/-- **Slice-wise invariance of the Sobolev seminorm.**  For a frozen base parameter, the `Lᵖ` norm
in the constant coefficient of the `j`-th derivative of the slice of a pull-back equals the `Lᵖ`
norm of the `j`-th derivative of the slice at the transformed base parameter, with constant exactly
`1`.  Only two inputs are used: the shear translates the constant coefficient, and Lebesgue measure
on the line is translation invariant.

This is the honest slice-wise form.  The constant `1` is not a normalization choice: the shift
enters only as a translation, and the modulus of the group appears not here but in the base
direction, where it is supplied by the quasi-invariance of the parameter measure; see
`LeanRidgelet.lintegral_enorm_quadraticConstIteratedDeriv_comp_smul`. -/
theorem eLpNorm_iteratedDeriv_quadraticConstSlice_comp_smul (j : ℕ) (T : QuadraticParameter E → ℂ)
    (g : E ≃ᵃ[ℝ] E) (p : QuadraticSymmetric E × E) (r : ℝ≥0∞)
    (hmeas : AEStronglyMeasurable
      (iteratedDeriv j (quadraticConstSlice T (quadraticBaseLinearEquiv g p)))
      (volume : Measure ℝ)) :
    eLpNorm (iteratedDeriv j (quadraticConstSlice (fun η ↦ T (g • η)) p)) r volume =
      eLpNorm (iteratedDeriv j (quadraticConstSlice T (quadraticBaseLinearEquiv g p))) r
        volume := by
  have hcomp : iteratedDeriv j (quadraticConstSlice (fun η ↦ T (g • η)) p) =
      iteratedDeriv j (quadraticConstSlice T (quadraticBaseLinearEquiv g p)) ∘
        (· + quadraticConstShift g p) :=
    iteratedDeriv_quadraticConstSlice_comp_smul j T g p
  rw [hcomp]
  exact eLpNorm_comp_measurePreserving hmeas
    (measurePreserving_add_right (volume : Measure ℝ) (quadraticConstShift g p))

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (QuadraticSymmetric E)] [BorelSpace (QuadraticSymmetric E)]

/-- **The parameter measure spent on a pull-back.**  A lower Lebesgue integral against the
relatively invariant parameter measure of a function pulled back along the parameter action of `g`
is `‖det L‖₊` times the integral of the function.  This is
`LeanRidgelet.quadraticRelativeParameter_group_map_eq_withDensity` at `g⁻¹`, whose constant density
inverts to `‖det L‖₊`.  Nothing about the shear is used here; it is the measure's own
quasi-invariance. -/
theorem lintegral_comp_smul_quadraticRelativeMeasure (lam : Measure (QuadraticParameter E))
    [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) {F : QuadraticParameter E → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ξ, F (g • ξ) ∂(quadraticRelativeMeasure lam) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) *
        ∫⁻ ξ, F ξ ∂(quadraticRelativeMeasure lam) := by
  have hinv : ‖LinearMap.det ((g⁻¹).linear : E →ₗ[ℝ] E)‖₊ =
      ‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊⁻¹ := by
    rw [det_linear_inv, nnnorm_inv]
  have hjac : (fun ξ : QuadraticParameter E ↦
        ((quadraticRelativeParameterJacobian g⁻¹ ξ : ℝ≥0) : ℝ≥0∞)) =
      fun _ : QuadraticParameter E ↦
        ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0) : ℝ≥0∞) := by
    funext ξ
    simp only [quadraticRelativeParameterJacobian, hinv, inv_inv]
  have hmap : (quadraticRelativeMeasure lam).map (fun ξ ↦ g • ξ) =
      ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0) : ℝ≥0∞) • quadraticRelativeMeasure lam := by
    have h := quadraticRelativeParameter_group_map_eq_withDensity lam g⁻¹
    rw [inv_inv] at h
    rw [h, hjac, withDensity_const]
  rw [← lintegral_map hF (quadraticParameter_measurable g), hmap, lintegral_smul_measure,
    smul_eq_mul]

/-- **Global invariance of the Sobolev seminorm, up to the quasi-invariance constant.**  The `L²`
norm in the constant coefficient of the `j`-th derivative, integrated over the whole parameter space
against the relatively invariant parameter measure, is multiplied by exactly `‖det L‖₊` when the
argument is pulled back along the parameter action of `g`.  That constant is the one the parameter
measure contributes on its own, so these seminorms become invariant under exactly the same
square-root normalization of the pull-back that makes
`LeanRidgelet.quadraticRelativeParameterLpUnitaryRepresentation` unitary.

The measurability hypothesis is on the derivative in the constant coefficient as a function of the
parameter; it is not available anywhere in this development and is carried as a hypothesis. -/
theorem lintegral_enorm_quadraticConstIteratedDeriv_comp_smul
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) (j : ℕ)
    {T : QuadraticParameter E → ℂ} (hT : Measurable (quadraticConstIteratedDeriv j T)) :
    ∫⁻ ξ, ‖quadraticConstIteratedDeriv j (fun η ↦ T (g • η)) ξ‖ₑ ^ 2
        ∂(quadraticRelativeMeasure lam) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) *
        ∫⁻ ξ, ‖quadraticConstIteratedDeriv j T ξ‖ₑ ^ 2 ∂(quadraticRelativeMeasure lam) := by
  have hcongr : ∫⁻ ξ, ‖quadraticConstIteratedDeriv j (fun η ↦ T (g • η)) ξ‖ₑ ^ 2
        ∂(quadraticRelativeMeasure lam) =
      ∫⁻ ξ, (fun η ↦ ‖quadraticConstIteratedDeriv j T η‖ₑ ^ 2) (g • ξ)
        ∂(quadraticRelativeMeasure lam) := by
    refine lintegral_congr fun ξ ↦ ?_
    rw [quadraticConstIteratedDeriv_comp_smul]
  rw [hcongr]
  exact lintegral_comp_smul_quadraticRelativeMeasure lam g (hT.enorm.pow_const 2)

/-- **The `Γ`-seminorm identity through the factorization.**  Combining the previous result with
`LeanRidgelet.exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul`, the iterated integral
over the base parameter of the squared `L²` norm in the constant coefficient of the `j`-th
derivative — that is, the `j`-th seminorm of the informal space `L²(base; H^j(ℝ))` — is multiplied
by exactly `‖det L‖₊` under the pull-back.  The undetermined constant of the factorization cancels
between the two sides.

The additive Haar measure `lam` on the full parameter space does not appear in the conclusion.  It
is only a witness: the base parameter measure has no quasi-invariance of its own in this
development, so the statement is routed through the one that is proved upstairs. -/
theorem lintegral_base_enorm_quadraticConstIteratedDeriv_comp_smul
    (lam : Measure (QuadraticParameter E)) [lam.IsAddHaarMeasure]
    (κ : Measure (QuadraticSymmetric E × E)) [κ.IsAddHaarMeasure] (g : E ≃ᵃ[ℝ] E) (j : ℕ)
    {T : QuadraticParameter E → ℂ} (hT : Measurable (quadraticConstIteratedDeriv j T)) :
    ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t,
          ‖iteratedDeriv j (quadraticConstSlice (fun η ↦ T (g • η)) p) t‖ₑ ^ 2
          ∂(volume : Measure ℝ) ∂(quadraticBaseRelativeMeasure κ) =
      (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) *
        ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t,
          ‖iteratedDeriv j (quadraticConstSlice T p) t‖ₑ ^ 2
          ∂(volume : Measure ℝ) ∂(quadraticBaseRelativeMeasure κ) := by
  obtain ⟨c, hc0, hctop, hmap⟩ :=
    exists_map_prodAssoc_symm_quadraticRelativeMeasure_eq_smul lam κ
  have hmeasR : Measurable fun ξ ↦ ‖quadraticConstIteratedDeriv j T ξ‖ₑ ^ 2 :=
    hT.enorm.pow_const 2
  have hmeasL : Measurable fun ξ ↦
      ‖quadraticConstIteratedDeriv j (fun η ↦ T (g • η)) ξ‖ₑ ^ 2 := by
    rw [quadraticConstIteratedDeriv_comp_smul_eq]
    exact (hT.comp (quadraticParameter_measurable g)).enorm.pow_const 2
  have hkey := lintegral_enorm_quadraticConstIteratedDeriv_comp_smul lam g j hT
  rw [lintegral_quadraticRelativeMeasure_of_map_eq_smul hmap hmeasL,
    lintegral_quadraticRelativeMeasure_of_map_eq_smul hmap hmeasR] at hkey
  rw [show (‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) *
      (c * ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t,
        ‖quadraticConstIteratedDeriv j T (p.1, p.2, t)‖ₑ ^ 2
        ∂(volume : Measure ℝ) ∂(quadraticBaseRelativeMeasure κ)) =
      c * ((‖LinearMap.det (g.linear : E →ₗ[ℝ] E)‖₊ : ℝ≥0∞) *
        ∫⁻ p : QuadraticSymmetric E × E, ∫⁻ t,
          ‖quadraticConstIteratedDeriv j T (p.1, p.2, t)‖ₑ ^ 2
          ∂(volume : Measure ℝ) ∂(quadraticBaseRelativeMeasure κ)) from by ring] at hkey
  exact (ENNReal.mul_right_inj hc0 hctop).1 hkey

end Measure

end LeanRidgelet
