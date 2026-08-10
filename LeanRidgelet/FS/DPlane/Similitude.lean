/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.Stiefel

/-!
# Fourier slice method, Case IV: the similitude group

Section 6 of `arXiv:2402.15984` over the similitude group `GV_{m,k}`, the article's
`thm:similitude`. The weight matrix is `A = aU` with `a > 0` a scale and `U` an orthonormal frame.

This is the one case where the scale genuinely interacts with the frequency: the two couple through
`y = a r`, so the similitude network is **not** a scale mixture of Stiefel networks — at a fixed
scale no power of `σ♯ conj(ρ♯)` satisfies the Stiefel separation-of-variables condition. The Fubini
exchange that handles the coupling goes into Step 1, where the article puts it, after which the
assembly is polar coordinates in the frequency, the substitution `y = a r`, and the direction
average of `ToMathlib.LieGroup.MatrixPolar`.

## Main definitions and results

* `rpow_similitude_split`, `rpow_similitude_radial`: the two exponent identities that make the
  scale--frequency substitution come out.
* `similitudeSynthesis`, `similitudeFourierExpression`, `fs_similitude_fourierExpression_of_bias`:
  the layer and Step 1, the latter carrying the Fubini exchange.
* `fs_similitude_reconstruction_of_inversion`: **the reconstruction formula**, for an arbitrary real
  homogeneity `s`. What has to be constant is not the product of the two spectra, as in the Stiefel
  case, but its *radial* integral against `r^{-(d-s+1)}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


section GeneralCodim

open Metric

variable [Nontrivial E] [Nontrivial (EuclideanSpace ℝ (Fin k))]

/-! ### The similitude group

The weight matrix is now `A = aU` with `a > 0` a scale and `U` an orthonormal frame, against the
parameter measure `α(a) da dU db`. Unlike the Stiefel case this one has a scale, and the scale is
not a passenger: it couples to the radial variable of the bias frequency through `y = a r`, which is
what makes the separation-of-variables condition satisfiable for a whole family of exponents `s`. In
particular the similitude network is **not** a scale mixture of Stiefel networks — at a fixed scale
no power of `σ♯ conj(ρ♯)` satisfies the Stiefel condition, and that coupling is the substance of
this case.

The derivation is: polar coordinates in the bias frequency, the one-dimensional substitution `y = a
r` in the scale, and then the direction average of `ToMathlib.LieGroup.MatrixPolar`, whose weight
`y^{m-1}` is exactly what the substitution produces. The Fubini exchange that moves the bias
frequency outside the scale integral is in Step 1, where the article puts it. The two exponent
identities that make the substitution come out are `rpow_similitude_split` and
`rpow_similitude_radial`.
-/

/-- **The scale–frequency exponent identity of the similitude case.** At a positive scale and
radius, the parameter density `a^{m-s-1}` and the ansatz factor `(a r)^s` combine, in the product
variable `y = a r`, into the Jacobian `y^{m-1}` of polar coordinates on the input space, times a
power of the radius alone. This is why the ansatz closes for every real `s`: the exponent `s`
cancels out of the `y`-dependence. -/
theorem rpow_similitude_split {M s a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    a ^ (M - s - 1) * (a * r) ^ s = r ^ (-(M - s - 1)) * (a * r) ^ (M - 1) := by
  have e1 : a ^ (M - s - 1) * (a * r) ^ s = a ^ (M - 1) * r ^ s := by
    rw [Real.mul_rpow ha.le hr.le, ← mul_assoc, ← Real.rpow_add ha]
    congr 2
    ring
  have e2 : r ^ (-(M - s - 1)) * (a * r) ^ (M - 1) = a ^ (M - 1) * r ^ s := by
    rw [Real.mul_rpow ha.le hr.le,
      show r ^ (-(M - s - 1)) * (a ^ (M - 1) * r ^ (M - 1))
        = a ^ (M - 1) * (r ^ (-(M - s - 1)) * r ^ (M - 1)) from by ring,
      ← Real.rpow_add hr]
    congr 2
    ring
  rw [e1, e2]

/-- **The radial weight the similitude case leaves behind.** The Jacobian `r^{k-1}` of polar
coordinates on the frequency space, the factor `r^{-(m-s-1)}` left by the scale density, and the
Jacobian `r⁻¹` of the substitution `y = a r` combine into `r^{s-m+k-1} = r^{-(d-s+1)}`, `d = m - k`.
That is the weight the article's scalar `⦅σ,ρ⦆_s` integrates the two spectra against. -/
theorem rpow_similitude_radial {kk M s r : ℝ} (hr : 0 < r) :
    r ^ (kk - 1) * r ^ (-(M - s - 1)) * r⁻¹ = r ^ (s - M + kk - 1) := by
  rw [← Real.rpow_neg_one r, ← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1
  ring

/-- The `d`-plane layer over the similitude group,
`S[γ](x) = ∫ γ(a,U,b) σ(a Uᵀx - b) α(a) da dU db`. -/
def similitudeSynthesis (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)) (α : ℝ → ℝ)
    (σ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ : ℝ → (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ∫ L, (∫ a in Set.Ioi (0 : ℝ), ((α a : ℝ) : ℂ) *
    ∫ b : EuclideanSpace ℝ (Fin k), γ a L b * σ (a • dPlaneCoord L x - b)) ∂ν

/-- The Fourier expression of the similitude layer, the output of Step 1. The bias frequency sits
outside the scale integral, which is where the derivation needs it, and moving it there is the
article's standing assumption on exchanging the order of integration. -/
def similitudeFourierExpression (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)) (α : ℝ → ℝ)
    (Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (Γ : ℝ → (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
    ∫ L, (∫ ω : EuclideanSpace ℝ (Fin k), ∫ a in Set.Ioi (0 : ℝ), ((α a : ℝ) : ℂ) *
      (Γ a L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (a • dPlaneCoord L x)))) ∂ν

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [Nontrivial (EuclideanSpace ℝ (Fin k))] in
/-- **Step 1 over the similitude group**: the layer equals its Fourier expression. The analytic
input is the `k`-dimensional bias identity at each scale and frame, and — unlike the Stiefel case —
one Fubini exchange, moving the bias frequency outside the scale integral. That exchange is the
article's standing assumption that the iterated integral converges absolutely. -/
theorem fs_similitude_fourierExpression_of_bias
    (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)) (α : ℝ → ℝ)
    (σ Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ Γ : ℝ → (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) → ℂ) (x : E)
    (hbias : ∀ a : ℝ, 0 < a → ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ b : EuclideanSpace ℝ (Fin k), γ a L b * σ (a • dPlaneCoord L x - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k),
            Γ a L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (a • dPlaneCoord L x)))
    (hswap : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin k) => ((α p.1 : ℝ) : ℂ) *
          (Γ p.1 L p.2 * Fσ p.2 *
            fourierSlicePhase (inner ℝ p.2 (p.1 • dPlaneCoord L x))))
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume)) :
    similitudeSynthesis ν α σ γ x = similitudeFourierExpression ν α Fσ Γ x := by
  rw [similitudeSynthesis, similitudeFourierExpression, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  simp only []
  have hstep : ∀ a ∈ Set.Ioi (0 : ℝ),
      ((α a : ℝ) : ℂ) * (∫ b : EuclideanSpace ℝ (Fin k), γ a L b * σ (a • dPlaneCoord L x - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k), ((α a : ℝ) : ℂ) *
            (Γ a L ω * Fσ ω * fourierSlicePhase (inner ℝ ω (a • dPlaneCoord L x))) := by
    intro a ha
    rw [hbias a ha L, integral_const_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hstep, integral_const_mul,
    integral_integral_swap (hswap L)]

/-- **The reconstruction formula over the similitude group** — the article's `thm:similitude`. The
separation-of-variables ansatz is `γ♯(aU,ω) = f̂(aUω)(a‖ω‖)^s conj(ρ♯(ω))` with parameter density
`α(a) = a^{m-s-1}`, for an arbitrary real `s`. What has to be constant is not the product of the two
spectra, as in the Stiefel case, but its *radial* integral against `r^{-(d-s+1)}`; that is the
hypothesis `hradial`, and the constant is the article's `⦅σ,ρ⦆_s` up to normalization.

The scale and the radial variable of the bias frequency couple through `y = a r`. After polar
coordinates in the frequency, the substitution `y = a r` turns `a^{m-s-1}(ar)^s` into `y^{m-1}`, the
Jacobian of polar coordinates on the input space, and leaves behind exactly the radial weight
`r^{-(d-s+1)}` — these are `rpow_similitude_split` and `rpow_similitude_radial`. What is left is the
direction average, so the conclusion has the same shape as the Stiefel one with the radial constant
in place of the auxiliary factor. -/
theorem fs_similitude_reconstruction_of_inversion
    (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (s : ℝ) (cphi : ℂ)
    (Fσ Fρbar : EuclideanSpace ℝ (Fin k) → ℂ) (Ff f : E → ℂ) (x : E)
    (hradial : ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
      (∫ r in Set.Ioi (0 : ℝ),
          ((r ^ (s - (Module.finrank ℝ E : ℝ) + (k : ℝ) - 1) : ℝ) : ℂ) *
            (Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
              Fρbar (r • (v : EuclideanSpace ℝ (Fin k))))) = cphi)
    (hpolar : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      Integrable (fun ω : EuclideanSpace ℝ (Fin k) => ∫ a in Set.Ioi (0 : ℝ),
        ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
          ((Ff (a • L ω) * (((a * ‖ω‖) ^ s : ℝ) : ℂ) * Fρbar ω) * Fσ ω *
            fourierSlicePhase (inner ℝ ω (a • dPlaneCoord L x)))) volume)
    (hFfm : StronglyMeasurable Ff)
    (hF : Integrable (fun ξ : E => Ff ξ * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hinv : (∫ ξ : E, Ff ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ Module.finrank ℝ E : ℝ) : ℂ) * f x) :
    ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        similitudeFourierExpression (ContinuousLinearMap.stiefelMeasure L₀)
          (fun a => a ^ ((Module.finrank ℝ E : ℝ) - s - 1)) Fσ
          (fun a L ω => Ff (a • L ω) * (((a * ‖ω‖) ^ s : ℝ) : ℂ) * Fρbar ω) x
      = cphi * (((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere.real Set.univ : ℝ) : ℂ) *
          ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) * f x := by
  have hkE : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hk : 0 < k := hkE ▸ Module.finrank_pos
  have hm : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hkm : k ≤ Module.finrank ℝ E := by
    have := LinearMap.finrank_le_finrank_of_injective (f := L₀.toLinearMap) L₀.injective
    rwa [hkE] at this
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  have hmcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  set F : E → ℂ := fun ξ => Ff ξ * fourierSlicePhase (inner ℝ ξ x) with hFdef
  set H : Metric.sphere (0 : E) 1 → ℂ := fun w =>
    ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • F (y • (w : E)) with hHdef
  have hHint : Integrable H (volume : Measure E).toSphere :=
    MeasureTheory.integrable_toSphere_integral_Ioi (volume : Measure E) hF
  have hHpolar : (∫ w, H w ∂(volume : Measure E).toSphere) = ∫ ξ : E, F ξ :=
    (MeasureTheory.integral_eq_integral_toSphere_integral_Ioi (volume : Measure E) hF).symm
  -- the per-frame reduction: polar coordinates in the frequency, then the substitution `y = a r`
  have hframe : ∀ L : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ ω : EuclideanSpace ℝ (Fin k), ∫ a in Set.Ioi (0 : ℝ),
          ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
            ((Ff (a • L ω) * (((a * ‖ω‖) ^ s : ℝ) : ℂ) * Fρbar ω) * Fσ ω *
              fourierSlicePhase (inner ℝ ω (a • dPlaneCoord L x))))
        = cphi * ∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
            H (MeasureTheory.frameDirection L v)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere := by
    intro L
    rw [MeasureTheory.integral_eq_integral_toSphere_integral_Ioi
      (volume : Measure (EuclideanSpace ℝ (Fin k))) (hpolar L), hkE, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    have hv : ‖(v : EuclideanSpace ℝ (Fin k))‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
    have hw : ((MeasureTheory.frameDirection L v : Metric.sphere (0 : E) 1) : E) = L v := rfl
    have hrad : ∀ r ∈ Set.Ioi (0 : ℝ),
        r ^ (k - 1) • (∫ a in Set.Ioi (0 : ℝ),
            ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
              ((Ff (a • L (r • (v : EuclideanSpace ℝ (Fin k)))) *
                  (((a * ‖r • (v : EuclideanSpace ℝ (Fin k))‖) ^ s : ℝ) : ℂ) *
                  Fρbar (r • (v : EuclideanSpace ℝ (Fin k)))) *
                Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                fourierSlicePhase
                  (inner ℝ (r • (v : EuclideanSpace ℝ (Fin k))) (a • dPlaneCoord L x))))
          = ((r ^ (s - (Module.finrank ℝ E : ℝ) + (k : ℝ) - 1) : ℝ) : ℂ) *
              (Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                Fρbar (r • (v : EuclideanSpace ℝ (Fin k)))) *
              H (MeasureTheory.frameDirection L v) := by
      intro r hr
      have hr0 : (0 : ℝ) < r := hr
      have hnorm : ‖r • (v : EuclideanSpace ℝ (Fin k))‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hv, mul_one]
      -- rewrite the integrand as a constant in `r` times a function of `y = a * r`
      have hpt : ∀ a ∈ Set.Ioi (0 : ℝ),
          ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
              ((Ff (a • L (r • (v : EuclideanSpace ℝ (Fin k)))) *
                  (((a * ‖r • (v : EuclideanSpace ℝ (Fin k))‖) ^ s : ℝ) : ℂ) *
                  Fρbar (r • (v : EuclideanSpace ℝ (Fin k)))) *
                Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                fourierSlicePhase
                  (inner ℝ (r • (v : EuclideanSpace ℝ (Fin k))) (a • dPlaneCoord L x)))
            = (((r ^ (-((Module.finrank ℝ E : ℝ) - s - 1)) : ℝ) : ℂ) *
                (Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                  Fρbar (r • (v : EuclideanSpace ℝ (Fin k))))) *
                ((((a * r) ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) *
                  F ((a * r) • (MeasureTheory.frameDirection L v : E))) := by
        intro a ha
        have ha0 : (0 : ℝ) < a := ha
        have hval : a • L (r • (v : EuclideanSpace ℝ (Fin k)))
            = (a * r) • (MeasureTheory.frameDirection L v : E) := by
          rw [L.map_smul, smul_smul, hw]
        have hphase : inner ℝ (r • (v : EuclideanSpace ℝ (Fin k))) (a • dPlaneCoord L x)
            = inner ℝ ((a * r) • (MeasureTheory.frameDirection L v : E)) x := by
          rw [real_inner_smul_left, real_inner_smul_right, inner_dPlaneCoord,
            real_inner_smul_left, hw]
          ring
        have hsplit : ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
              (((a * r) ^ s : ℝ) : ℂ)
            = ((r ^ (-((Module.finrank ℝ E : ℝ) - s - 1)) : ℝ) : ℂ) *
              (((a * r) ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, rpow_similitude_split ha0 hr0]
        rw [hval, hphase, hnorm, hFdef]
        rw [show ((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) *
              ((Ff ((a * r) • (MeasureTheory.frameDirection L v : E)) *
                  (((a * r) ^ s : ℝ) : ℂ) *
                  Fρbar (r • (v : EuclideanSpace ℝ (Fin k)))) *
                Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                fourierSlicePhase
                  (inner ℝ ((a * r) • (MeasureTheory.frameDirection L v : E)) x))
            = (((a ^ ((Module.finrank ℝ E : ℝ) - s - 1) : ℝ) : ℂ) * (((a * r) ^ s : ℝ) : ℂ)) *
              ((Fσ (r • (v : EuclideanSpace ℝ (Fin k))) *
                Fρbar (r • (v : EuclideanSpace ℝ (Fin k)))) *
                (Ff ((a * r) • (MeasureTheory.frameDirection L v : E)) *
                  fourierSlicePhase
                    (inner ℝ ((a * r) • (MeasureTheory.frameDirection L v : E)) x))) from by
          ring, hsplit]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
      -- the substitution `y = a r`, and the identification of the `y`-integral with `H`
      have hsub : (∫ a in Set.Ioi (0 : ℝ),
            (((a * r) ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) *
              F ((a * r) • (MeasureTheory.frameDirection L v : E)))
          = r⁻¹ • ∫ y in Set.Ioi (0 : ℝ),
              ((y ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) *
                F (y • (MeasureTheory.frameDirection L v : E)) := by
        simpa using integral_comp_mul_right_Ioi
          (fun y : ℝ => ((y ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) *
            F (y • (MeasureTheory.frameDirection L v : E))) 0 hr0
      have hH : (∫ y in Set.Ioi (0 : ℝ),
            ((y ^ ((Module.finrank ℝ E : ℝ) - 1) : ℝ) : ℂ) *
              F (y • (MeasureTheory.frameDirection L v : E)))
          = H (MeasureTheory.frameDirection L v) := by
        rw [hHdef]
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy0 : (0 : ℝ) < y := hy
        rw [← hmcast, Real.rpow_natCast, Complex.real_smul]
      rw [hsub, hH]
      -- collect the powers of `r`
      have hcoef : ((r ^ (k - 1) : ℝ) : ℂ) *
            (((r ^ (-((Module.finrank ℝ E : ℝ) - s - 1)) : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ))
          = ((r ^ (s - (Module.finrank ℝ E : ℝ) + (k : ℝ) - 1) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        congr 1
        rw [← Real.rpow_natCast r (k - 1), hkcast, ← mul_assoc]
        exact rpow_similitude_radial hr0
      rw [Complex.real_smul, Complex.real_smul, ← hcoef]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hrad, integral_mul_const, hradial v]
  -- assemble: the direction average, polar coordinates on `E`, and inversion
  have hpow : ((2 * (Real.pi : ℂ)) ^ Module.finrank ℝ E)
      = ((2 * (Real.pi : ℂ)) ^ k) * ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) := by
    rw [← pow_add]
    congr 1
    omega
  have hpi : ((2 * (Real.pi : ℂ)) ^ k) ≠ 0 := pow_ne_zero _ Fourier.two_mul_pi_complex_ne_zero
  have hFsm : StronglyMeasurable F :=
    hFfm.mul (continuous_fourierSlicePhase.comp
      (Continuous.inner continuous_id continuous_const)).stronglyMeasurable
  have hdir := MeasureTheory.toSphere_real_smul_integral_directionAverage L₀ hHint
    (MeasureTheory.integrable_prod_radialIntegral L₀ hFsm hF)
  rw [similitudeFourierExpression, integral_congr_ae (Filter.Eventually.of_forall hframe),
    integral_const_mul]
  have hcollect : ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        (((2 * (Real.pi : ℂ)) ^ k)⁻¹ * (cphi * ∫ L,
          (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
            H (MeasureTheory.frameDirection L v)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere)
          ∂(ContinuousLinearMap.stiefelMeasure L₀)))
      = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ * cphi *
        ((((volume : Measure E).toSphere.real Set.univ : ℝ)) • ∫ L,
          (∫ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1,
            H (MeasureTheory.frameDirection L v)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere)
          ∂(ContinuousLinearMap.stiefelMeasure L₀)) := by
    rw [Complex.real_smul]
    ring
  rw [hcollect, hdir, hHpolar, hFdef, hinv, Complex.real_smul]
  push_cast
  rw [hpow]
  field_simp

end GeneralCodim
end LeanRidgelet
