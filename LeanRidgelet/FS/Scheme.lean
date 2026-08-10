/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Defs
public import LeanRidgelet.ToMathlib.IteratedFubini
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier slice method: the three steps as one conditional theorem

Section 2 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984),

in the generality the article's later sections use it in.

The article derives a ridgelet transform by three steps: turn the network into its *Fourier
expression* by convolving in the bias, *change variables* in the scale parameter so that the
feature map splits into a principal and an auxiliary factor, and close with a
*separation-of-variables* ansatz for the unknown coefficient function. What varies between the
article's four cases is the input domain and its inversion formula; the three steps do not vary.
This file carries them once.

## The data

* `V`, the scale and frequency space, a finite-dimensional real inner product space with an
  additive Haar measure. Its dimension is the exponent `r` of the article.
* `U` with a measure `ν`, the direction space: the sphere in Euclidean polar coordinates, the
  boundary `∂X` on a symmetric space, a point when the weight is a plain vector.
* `X`, the input domain, which needs no structure at all — only the composite distance
  `π : X → U → V` and the weight `w : X → U → ℂ` see it.
* `F` and `κ`, the Fourier data of the target and the density of its inversion formula.

The *only* hypothesis of the reconstruction theorem is that inversion formula. Neither Mathlib's
absence of a Helgason--Fourier theory nor any integrability condition enters as a structure field,
a typeclass field, or an axiom.

## Main definitions and results

* `fourierExpressionSynthesis`: the network after Step 1, `S[γ](x) = (2π)⁻¹ ∫∫∫ γ♯(a,u,ω) σ♯(ω)
  e^{iω⟪a, π(x,u)⟫} w(x,u)`.
* `separationOfVariables`: the ansatz `γ♯(a,u,ω) = F(ωa,u) κ(ωa) conj (ρ♯(ω))` of Step 3.
* `inversionIntegral`: the integral the inversion formula on the input domain evaluates.
* `fs_changeOfVariables`: Step 2, the change of variables `ξ = ω a` with Jacobian `|ω|^{-r}`.
* `fs_slice_of_inversion`: where Steps 2 and 3 meet — at each bias frequency the weight integral of
  the ansatz is `|ω|^{-r} f(x)`.
* `fs_reconstruction_of_inversion`: the reconstruction formula `S[γ_{f,ρ}] = ⦅σ,ρ⦆_r f`.

## Why no integrability hypotheses appear

Substituting the ansatz makes the bias frequency factor out of the two inner integrals as a
constant, so the proof pulls it out with `MeasureTheory.integral_const_mul` and never exchanges an
order of integration. The change of variables is `MeasureTheory.Measure.integral_comp_smul`, which
holds for every integrand because both sides degenerate together. Fubini enters the method only in
Step 1, which is not proved here — see below.

## Step 1

Step 1, the passage from the network as an integral against `σ(⟪a, π(x,u)⟫ - b)` to its Fourier
expression, splits into two parts, and `fs_fourierExpression_of_bias` puts them together.

The analytic part is one-dimensional: for fixed `a` and `u` it is the convolution theorem in the
bias followed by Fourier inversion, and it enters as the hypothesis `hbias`, since which form of
it is available depends on the class the activation is taken from. Over a finite field it is a
finite-sum identity and is proved outright; see `fs_finiteField_fourierExpression`.

The rest is bookkeeping: the bias frequency produced inside has to be moved outside the weight and
direction integrals. That is Fubini, and the article states it as the standing assumption that the
resulting triple integral converges absolutely "so that we can change the order of integrations
freely". Here it is the hypothesis `hint`, and the rearrangement itself is
`MeasureTheory.integral_integral_integral_swap_left`.

## Deviations from the article

The scalar is `fourierSlicePairing`, which is the article's `⦅σ,ρ⦆` with the domain-dependent
normalization moved out of it and into the ansatz — the coefficient function here carries the
inversion density `κ`, whereas the article's does not. So for the Euclidean network with an
`m`-dimensional weight this scalar is `(2π)^{-m}` times the article's; see `FS.Euclidean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LeanRidgelet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {U : Type*} [MeasurableSpace U] {X : Type*}

/-- The plane wave `e^{i t}`, the inverse-transform phase of the article's convention. -/
def fourierSlicePhase (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

@[simp] theorem fourierSlicePhase_zero : fourierSlicePhase 0 = 1 := by
  simp [fourierSlicePhase]

/-- The plane wave is unimodular, which is what makes multiplication by it preserve
integrability. -/
@[simp] theorem norm_fourierSlicePhase (t : ℝ) : ‖fourierSlicePhase t‖ = 1 := by
  rw [fourierSlicePhase, Complex.norm_exp]
  simp

theorem continuous_fourierSlicePhase : Continuous fourierSlicePhase := by
  unfold fourierSlicePhase
  fun_prop

/-- The network in Fourier expression form, the output of Step 1:
`S[γ](x) = (2π)⁻¹ ∫∫∫ γ♯(a,u,ω) σ♯(ω) e^{iω⟪a, π(x,u)⟫} w(x,u) dν du dω`,
with the bias frequency outermost. -/
def fourierExpressionSynthesis (μ : Measure V) (ν : Measure U) (Fσ : ℝ → ℂ)
    (Γ : V → U → ℝ → ℂ) (π : X → U → V) (w : X → U → ℂ) (x : X) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ ω : ℝ, ∫ a : V, ∫ u : U,
      Γ a u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u ∂ν ∂μ

/-- The separation-of-variables ansatz of Step 3: a principal factor carrying the Fourier data of
the target function and the density of its inversion formula, and an auxiliary factor carrying the
ridgelet spectrum, coupled through `ξ = ω a`. -/
def separationOfVariables (F : V → U → ℂ) (κ : V → ℝ) (Fρ : ℝ → ℂ) : V → U → ℝ → ℂ :=
  fun a u ω => F (ω • a) u * ((κ (ω • a) : ℝ) : ℂ) * conj (Fρ ω)

/-- The integral evaluated by the inversion formula on the input domain:
`∫∫ F(λ,u) κ(λ) e^{i⟪λ, π(x,u)⟫} w(x,u) dν dλ`. On a Euclidean space with `U` a point this is the
Fourier inversion integral; on a symmetric space it is the Helgason--Fourier inversion integral,
with `κ = |W|⁻¹|c(λ)|⁻²`. -/
def inversionIntegral (μ : Measure V) (ν : Measure U) (F : V → U → ℂ) (κ : V → ℝ)
    (π : X → U → V) (w : X → U → ℂ) (x : X) : ℂ :=
  ∫ lam : V, ∫ u : U,
    F lam u * ((κ lam : ℝ) : ℂ) * fourierSlicePhase (inner ℝ lam (π x u)) * w x u ∂ν ∂μ

/-! ## Step 1: the Fourier expression -/

/-- The network as the article writes it, an integral of `γ(a,u,b) σ(⟪a, π(x,u)⟫ - b) w(x,u)`
over weights, directions and biases. -/
def sliceSynthesis (μ : Measure V) (ν : Measure U) (σ : ℝ → ℂ) (γ : V → U → ℝ → ℂ)
    (π : X → U → V) (w : X → U → ℂ) (x : X) : ℂ :=
  ∫ a : V, (∫ u : U, (∫ b : ℝ, γ a u b * σ (inner ℝ a (π x u) - b) * w x u) ∂ν) ∂μ

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Step 1**: the network equals its Fourier expression.

The analytic input is one-dimensional and is the hypothesis `hbias`: at a fixed weight and
direction, convolving in the bias and inverting turns the bias integral into an integral against
the bias frequency. Everything else is Fubini, moving that frequency outside the weight and
direction integrals, which is the hypothesis `hint` — the article's standing assumption that the
triple integral converges absolutely so that the order of integration may be changed freely. -/
theorem fs_fourierExpression_of_bias (μ : Measure V) (ν : Measure U) [SFinite μ] [SFinite ν]
    (σ Fσ : ℝ → ℂ) (γ : V → U → ℝ → ℂ) (Γ : V → U → ℝ → ℂ) (π : X → U → V) (w : X → U → ℂ)
    (x : X)
    (hbias : ∀ (a : V) (u : U), (∫ b : ℝ, γ a u b * σ (inner ℝ a (π x u) - b) * w x u)
      = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ ω : ℝ, Γ a u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u)
    (hint : Integrable (fun p : ℝ × V × U =>
      Γ p.2.1 p.2.2 p.1 * Fσ p.1 * fourierSlicePhase (p.1 * inner ℝ p.2.1 (π x p.2.2)) *
        w x p.2.2) ((volume : Measure ℝ).prod (μ.prod ν))) :
    sliceSynthesis μ ν σ γ π w x = fourierExpressionSynthesis μ ν Fσ Γ π w x := by
  have hswap := integral_integral_integral_swap_left (volume : Measure ℝ) μ ν
    (fun (ω : ℝ) (a : V) (u : U) =>
      Γ a u ω * Fσ ω * fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u) hint
  rw [sliceSynthesis, fourierExpressionSynthesis]
  calc (∫ a : V, (∫ u : U, (∫ b : ℝ, γ a u b * σ (inner ℝ a (π x u) - b) * w x u) ∂ν) ∂μ)
      = ∫ a : V, (∫ u : U, ((2 * (Real.pi : ℂ))⁻¹ *
          ∫ ω : ℝ, Γ a u ω * Fσ ω *
            fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u) ∂ν) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => hbias a u)
    _ = (2 * (Real.pi : ℂ))⁻¹ *
          ∫ a : V, (∫ u : U, (∫ ω : ℝ, Γ a u ω * Fσ ω *
            fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u) ∂ν) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        exact integral_const_mul _ _
    _ = (2 * (Real.pi : ℂ))⁻¹ *
          ∫ ω : ℝ, (∫ a : V, (∫ u : U, Γ a u ω * Fσ ω *
            fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u ∂ν) ∂μ) := by
        rw [← hswap]

/-! ## Step 2: the change of variables -/

/-- **Step 2**: the change of variables `ξ = ω a` on the scale space, with Jacobian `|ω|^{-r}`
where `r` is the dimension. It holds for every integrand and every `ω`, including `ω = 0`, since
both sides degenerate together. -/
theorem fs_changeOfVariables (μ : Measure V) [μ.IsAddHaarMeasure] (G : V → ℂ) (ω : ℝ) :
    ∫ a : V, G (ω • a) ∂μ
      = ((|ω| ^ (Module.finrank ℝ V : ℝ))⁻¹ : ℝ) • ∫ lam : V, G lam ∂μ := by
  rw [Measure.integral_comp_smul]
  congr 1
  rw [abs_inv, abs_pow, Real.rpow_natCast]

/-! ## Steps 2 and 3 together -/

/-- Where Steps 2 and 3 meet. Substituting the ansatz, the weight integral at a fixed bias
frequency is the inversion integral rescaled by the Jacobian, hence `|ω|^{-r} f(x)`. The bias
frequency leaves the two inner integrals as a constant, which is why no integrability hypothesis
is needed. -/
theorem fs_slice_of_inversion (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure U)
    (Fσ Fρ : ℝ → ℂ) (F : V → U → ℂ) (κ : V → ℝ) (π : X → U → V) (w : X → U → ℂ)
    (f : X → ℂ) (hinv : ∀ y, inversionIntegral μ ν F κ π w y = f y) (x : X) (ω : ℝ) :
    (∫ a : V, ∫ u : U, separationOfVariables F κ Fρ a u ω * Fσ ω *
        fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u ∂ν ∂μ)
      = Fσ ω * conj (Fρ ω) * (((|ω| ^ (Module.finrank ℝ V : ℝ))⁻¹ : ℝ) : ℂ) * f x := by
  set G : V → ℂ := fun lam =>
    ∫ u : U, F lam u * ((κ lam : ℝ) : ℂ) * fourierSlicePhase (inner ℝ lam (π x u)) * w x u ∂ν
    with hG
  have hfactor : ∀ a : V, (∫ u : U, separationOfVariables F κ Fρ a u ω * Fσ ω *
      fourierSlicePhase (ω * inner ℝ a (π x u)) * w x u ∂ν)
      = Fσ ω * conj (Fρ ω) * G (ω • a) := by
    intro a
    have hpull : Fσ ω * conj (Fρ ω) * G (ω • a)
        = ∫ u : U, Fσ ω * conj (Fρ ω) * (F (ω • a) u * ((κ (ω • a) : ℝ) : ℂ) *
            fourierSlicePhase (inner ℝ (ω • a) (π x u)) * w x u) ∂ν := by
      rw [hG, integral_const_mul]
    rw [hpull]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [separationOfVariables]
    rw [real_inner_smul_left]
    ring
  simp only [hfactor]
  rw [integral_const_mul, fs_changeOfVariables, hG]
  have : (∫ lam : V, ∫ u : U, F lam u * ((κ lam : ℝ) : ℂ) *
      fourierSlicePhase (inner ℝ lam (π x u)) * w x u ∂ν ∂μ) = f x := hinv x
  rw [this, Complex.real_smul, ← mul_assoc]

/-! ## The reconstruction formula -/

/-- **The reconstruction formula of the Fourier slice method.** Given an inversion formula on the
input domain, the network built from the separation-of-variables ansatz reproduces the target
function up to the Fourier slice pairing of the activation spectrum against the ridgelet spectrum.

The inversion formula is the only hypothesis. Each of the article's cases is an instance: the
input domain and its inversion formula change, the three steps do not. -/
theorem fs_reconstruction_of_inversion (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure U)
    (Fσ Fρ : ℝ → ℂ) (F : V → U → ℂ) (κ : V → ℝ) (π : X → U → V) (w : X → U → ℂ)
    (f : X → ℂ) (hinv : ∀ y, inversionIntegral μ ν F κ π w y = f y) (x : X) :
    fourierExpressionSynthesis μ ν Fσ (separationOfVariables F κ Fρ) π w x
      = fourierSlicePairing (Module.finrank ℝ V : ℝ) Fσ Fρ * f x := by
  rw [fourierExpressionSynthesis]
  simp only [fs_slice_of_inversion μ ν Fσ Fρ F κ π w f hinv x]
  have hpull : (∫ ω : ℝ, Fσ ω * conj (Fρ ω) *
        (((|ω| ^ (Module.finrank ℝ V : ℝ))⁻¹ : ℝ) : ℂ) * f x)
      = (∫ ω : ℝ, Fσ ω * conj (Fρ ω) *
        (((|ω| ^ (Module.finrank ℝ V : ℝ))⁻¹ : ℝ) : ℂ)) * f x := by
    rw [integral_mul_const]
  have hrestrict : (∫ ω in {(0 : ℝ)}ᶜ, Fσ ω * conj (Fρ ω) /
        ((|ω| ^ (Module.finrank ℝ V : ℝ) : ℝ) : ℂ))
      = ∫ ω : ℝ, Fσ ω * conj (Fρ ω) *
        (((|ω| ^ (Module.finrank ℝ V : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [MeasureTheory.restrict_compl_singleton]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv]
  rw [hpull, fourierSlicePairing, hrestrict, mul_assoc]

end LeanRidgelet
