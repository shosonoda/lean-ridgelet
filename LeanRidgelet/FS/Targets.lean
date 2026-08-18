/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.Affine
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite
public import LeanRidgelet.ToMathlib.TemperateGrowth

/-!
# Fourier slice method: the remaining targets

The results of `arXiv:2402.15984` that were not yet proved, stated so that the goals are Lean
propositions rather than prose. What is still open carries a `sorry` registered in
`permittedSorryDeclarations` of `audit/Assumptions.lean`, exactly as the four outstanding results of
the L2 manuscript are in `OverviewL2`; **three targets are left: the Jacobian of the singular value
decomposition, and the Helgason--Fourier inversion formula on each of the two spaces Section 5
instantiates at.**

The last two became statable only once the models existed. Section 5 takes the geometry of `G/K` as
data, and with the data free the inversion formula is not a proposition at all; the Poincaré ball
model of `LeanRidgelet.ToMathlib.LieGroup.Hyperbolic` and the chart model of
`LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite` fix it, so both formulas are now definite claims
about definite spaces.

The fractional derivative is now proved; it is a statement about the Fourier transform on a
finite-dimensional inner product space and will move to `ToMathlib`. The Jacobian is a statement
about invariant measures and will move to `ToMathlib/LieGroup/`. They are gathered here for now so
that the `sorry` surface of the project stays in two files.

## What is proved here

* `fs_exists_angularFourier_eq`: the angular Fourier transform is onto the Schwartz space. Mathlib's
  transform is invertible there and the two conventions differ by a dilation.
* `angularFourierSchwartz`: the angular Fourier transform of a Schwartz function, as a Schwartz
  function.
* `fs_exists_fractionalDerivative_of_compactSupport`: **the fractional derivative exists for a
  band-limited target.** If the Fourier transform of `φ` is compactly supported and vanishes on a
  ball about the origin, multiplying it by `‖ξ‖^s` again comes from a Schwartz function. This case
  needs no multiplier theory at all: the product is smooth by gluing — smooth away from the origin,
  identically zero on the ball — it inherits the compact support, and a smooth compactly supported
  function is Schwartz.
* `fs_exists_hasTemperateGrowth_eq_norm_rpow`: a function of temperate growth agreeing with `‖ξ‖^s`
  outside a ball. The multiplier is corrected inside the ball rather than outside it: a bump added
  to `‖ξ‖²` keeps it bounded away from zero without changing it where it matters, and a real power
  of a temperate function bounded away from zero is temperate, which is
  `Function.HasTemperateGrowth.rpow_of_le` of `ToMathlib.TemperateGrowth`.
* `fs_exists_fractionalDerivative`: **the general case**, for any Schwartz `φ` whose transform
  vanishes near the origin. Proved.

## What is open

* `fs_svdJacobian`: the article's Lemma C.3, the Jacobian of the singular value decomposition. The
  reconstruction formula over full-column-rank matrices does not depend on it — see
  `LeanRidgelet.FS.DPlane.Affine` — so this is what relates the two parameter *measures*, and
  settling it settles the two open questions about the article's constants.

## What is stated elsewhere, and what cannot be stated yet

The classical results of Section 7 are proved, not targets: the Radon formula of Carroll--Dickinson
and Ito is `fs_radon_reconstruction_codim_one` and the Fourier formula of Irie and Funahashi is
`fs_fourierFormula_irieFunahashi`. The inversion formula for the `d`-plane transform, the article's
Lemma 6.2, is `fs_dPlaneInversion`.

Three results of the article are *not* stated at all, deliberately.

* The inversion formula of Section 5, the Helgason--Fourier inversion on a noncompact symmetric
  space, together with the two examples that instantiate it — the horospherical hyperbolic network
  and the horospherical SPD network. `FS.Symmetric` takes the geometry as data, so with the data
  free the inversion formula is not a true proposition; stating it needs the geometry constructed
  first — the Poincaré ball model and then the symmetric positive definite matrices — which is a
  project of its own. The Blueprint records all three as nodes with no Lean declaration.
* Rubin's continuous `d`-plane ridgelet transform, `thm:dplane.rubin`, which Section 7 quotes from
  the literature. The article gives it as a citation and asserts it is the case of
  `thm:similitude` with radial `σ` and `ρ`; its normalization cannot be checked against the source,
  which is not among the reference texts here, so no statement is committed to.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## The fractional derivative -/

/-- The dilation of `E` by a nonzero scalar, as a continuous linear equivalence. This is what
carries the angular Fourier convention to Mathlib's: the two differ by the rescaling
`ξ ↦ (2π)⁻¹ ξ`. -/
def dilateCLE {c : ℝ} (hc : c ≠ 0) : E ≃L[ℝ] E :=
  { LinearEquiv.smulOfNeZero ℝ E c hc with
    continuous_toFun := continuous_const_smul c
    continuous_invFun := continuous_const_smul c⁻¹ }

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem dilateCLE_apply {c : ℝ} (hc : c ≠ 0) (x : E) : dilateCLE hc x = c • x := rfl

/-- **The angular Fourier transform is onto the Schwartz space.** Every Schwartz function is the
angular Fourier transform of one, because Mathlib's transform is invertible there and the two
conventions differ by a dilation, which the Schwartz space is invariant under. -/
theorem fs_exists_angularFourier_eq (Ψ : SchwartzMap E ℂ) :
    ∃ ψ : SchwartzMap E ℂ, ∀ ξ : E, Fourier.angularFourierIntegralInner ψ ξ = Ψ ξ := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  set Ψ' : SchwartzMap E ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilateCLE (E := E) h2π) Ψ with hΨ'
  refine ⟨𝓕⁻ Ψ', fun ξ => ?_⟩
  have hcoe : ((𝓕 (𝓕⁻ Ψ') : SchwartzMap E ℂ) : E → ℂ) = (Ψ' : E → ℂ) := by
    rw [FourierInvPair.fourier_fourierInv_eq Ψ']
  rw [Fourier.angularFourierIntegralInner_eq_fourier, ← SchwartzMap.fourier_coe, hcoe, hΨ']
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    dilateCLE_apply, smul_smul]
  rw [mul_inv_cancel₀ h2π, one_smul]

/-- The angular Fourier transform of a Schwartz function, as a Schwartz function. -/
def angularFourierSchwartz (φ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilateCLE (E := E) (c := (2 * Real.pi)⁻¹) (by positivity))
    (𝓕 φ)

@[simp] theorem angularFourierSchwartz_apply (φ : SchwartzMap E ℂ) (ξ : E) :
    angularFourierSchwartz φ ξ = Fourier.angularFourierIntegralInner φ ξ := by
  rw [Fourier.angularFourierIntegralInner_eq_fourier, angularFourierSchwartz,
    ← SchwartzMap.fourier_coe]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The multiplier `‖ξ‖^s` is smooth away from the origin. -/
theorem contDiffAt_norm_rpow (s : ℝ) {ξ : E} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : E => ((‖η‖ ^ s : ℝ) : ℂ)) ξ :=
  (Complex.ofRealCLM.contDiff.contDiffAt).comp ξ
    ((Real.contDiffAt_rpow_const_of_ne (p := s) (norm_ne_zero_iff.mpr hξ)).comp ξ
      (contDiffAt_norm ℝ hξ))

/-- **The fractional derivative of a band-limited Schwartz function exists.** If the angular Fourier
transform of `φ` has compact support and vanishes on a ball about the origin — that is, if `φ` is
band-limited to an annulus — then multiplying that transform by `‖ξ‖^s` again comes from a Schwartz
function.

This is the elementary case, and it needs no multiplier theory: away from the origin `‖ξ‖^s` is
smooth, on the ball the transform vanishes, so the product is smooth by gluing, it inherits the
compact support, and a smooth compactly supported function is Schwartz. The general case is
`fs_exists_fractionalDerivative`, where the support hypothesis is dropped and the growth of the
multiplier has to be controlled instead. -/
theorem fs_exists_fractionalDerivative_of_compactSupport (s : ℝ) (φ : SchwartzMap E ℂ)
    (hsupp : HasCompactSupport (Fourier.angularFourierIntegralInner φ))
    (hband : ∃ r > 0, ∀ ξ : E, ‖ξ‖ < r → Fourier.angularFourierIntegralInner φ ξ = 0) :
    ∃ ψ : SchwartzMap E ℂ, ∀ ξ : E,
      Fourier.angularFourierIntegralInner ψ ξ
        = ((‖ξ‖ ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner φ ξ := by
  obtain ⟨r, hr, hzero⟩ := hband
  set Φ : E → ℂ := Fourier.angularFourierIntegralInner φ with hΦ
  set Ψ : E → ℂ := fun ξ => ((‖ξ‖ ^ s : ℝ) : ℂ) * Φ ξ with hΨ
  -- `Ψ` vanishes on the ball, which is what makes it smooth at the origin
  have hΨzero : ∀ ξ : E, ‖ξ‖ < r → Ψ ξ = 0 := fun ξ hξ => by
    rw [hΨ]
    simp [hzero ξ hξ]
  have hΦsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    rw [hΦ]
    have : (Fourier.angularFourierIntegralInner (φ : E → ℂ)) = (angularFourierSchwartz φ : E → ℂ) :=
      funext fun ξ => (angularFourierSchwartz_apply φ ξ).symm
    rw [this]
    exact (angularFourierSchwartz φ).smooth'
  have hΨsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) ?_
      filter_upwards [Metric.ball_mem_nhds ξ hr] with η hη
      rw [hΨzero η (by simpa [hξ] using hη)]
    · exact (contDiffAt_norm_rpow s hξ).mul (hΦsmooth.contDiffAt)
  have hΨsupp : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro hsupp.isCompact ?_
    intro ξ hξ
    have : Φ ξ = 0 := image_eq_zero_of_notMem_tsupport hξ
    rw [hΨ]
    simp only []
    rw [this, mul_zero]
  obtain ⟨ψ, hψ⟩ := fs_exists_angularFourier_eq (hΨsupp.toSchwartzMap hΨsmooth)
  exact ⟨ψ, fun ξ => by rw [hψ ξ]; rfl⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A smooth cut-off of `‖ξ‖^s` has temperate growth.** For every `s` and every `r > 0` there is a
function of temperate growth agreeing with `‖ξ‖^s` outside the ball of radius `r`. That is all the
general fractional derivative needs.

`‖ξ‖^s` itself is not of temperate growth: for non-even `s` it is not smooth at the origin, and for
negative `s` it is not even bounded there. Away from the origin it is harmless, so what is needed is
a smooth modification inside the ball, and the modification is put on `‖ξ‖²` rather than on `‖ξ‖^s`:
with `β` a bump equal to `1` on the ball of radius `r/2` and supported in the ball of radius `r`,
the function
`q ξ = ‖ξ‖² + r² β ξ`
is of temperate growth — a sum of `‖ξ‖²` and a smooth compactly supported function — is bounded
below, and equals `‖ξ‖²` outside the ball. So `(q ξ)^{s/2}` is what is wanted, by
`Function.HasTemperateGrowth.rpow_of_le`.

That last step is where the Japanese bracket comes in. It is *not* a substitute for `‖ξ‖^s` — the
bracket `(1 + ‖ξ‖²)^{s/2}` is the Bessel potential multiplier `(1 - △)^{s/2}` whereas `‖ξ‖^s` is the
Riesz one `(-△)^{s/2}`, and Section 6 needs the homogeneous one, since the separation-of-variables
condition asks the product `γ♯σ♯` to be `f̂(Uω)|Uω|^d` and it is exactly that homogeneity which
matches the weight `|Ub|^{m-k}` of the matrix polar formula. But Mathlib's temperate growth of the
bracket is the right *proof*, because there the inner function `1 + ‖ξ‖²` already avoids the origin;
`ToMathlib.TemperateGrowth` generalizes it to an arbitrary inner function bounded away from zero,
which is what lets the inner function be chosen as above. -/
theorem fs_exists_hasTemperateGrowth_eq_norm_rpow (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ h : E → ℝ, Function.HasTemperateGrowth h ∧ ∀ ξ : E, r ≤ ‖ξ‖ → h ξ = ‖ξ‖ ^ s := by
  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump (0 : E), β.rIn = r / 2 ∧ β.rOut = r :=
    ⟨⟨r / 2, r, by positivity, by linarith⟩, rfl, rfl⟩
  -- the bump correction is smooth with compact support, hence of temperate growth
  have hbsupp : HasCompactSupport (fun ξ : E => r ^ 2 * β ξ) := by
    refine HasCompactSupport.intro β.hasCompactSupport.isCompact fun ξ hξ => ?_
    rw [image_eq_zero_of_notMem_tsupport hξ, mul_zero]
  have hbtg : Function.HasTemperateGrowth (fun ξ : E => r ^ 2 * β ξ) :=
    hbsupp.hasTemperateGrowth (contDiff_const.mul β.contDiff)
  have hqtg : Function.HasTemperateGrowth (fun ξ : E => ‖ξ‖ ^ 2 + r ^ 2 * β ξ) :=
    (Function.hasTemperateGrowth_norm_sq E).add hbtg
  -- and the corrected norm square is bounded below by `r²/4`
  have hqlb : ∀ ξ : E, r ^ 2 / 4 ≤ ‖ξ‖ ^ 2 + r ^ 2 * β ξ := by
    intro ξ
    by_cases hξ : ‖ξ‖ ≤ r / 2
    · have hβ1 : β ξ = 1 := by
        refine β.one_of_mem_closedBall ?_
        simpa [hβin, mem_closedBall_zero_iff] using hξ
      rw [hβ1]
      nlinarith [norm_nonneg ξ]
    · have hlt : r / 2 < ‖ξ‖ := not_le.mp hξ
      have hβ0 : (0 : ℝ) ≤ β ξ := β.nonneg
      nlinarith [norm_nonneg ξ]
  -- outside the ball the bump vanishes
  have hqout : ∀ ξ : E, r ≤ ‖ξ‖ → ‖ξ‖ ^ 2 + r ^ 2 * β ξ = ‖ξ‖ ^ 2 := by
    intro ξ hξ
    have hβ0 : β ξ = 0 := by
      refine β.zero_of_le_dist ?_
      simpa [hβout, dist_zero_right] using hξ
    rw [hβ0, mul_zero, add_zero]
  refine ⟨fun ξ => (‖ξ‖ ^ 2 + r ^ 2 * β ξ) ^ (s / 2), hqtg.rpow_of_le (by positivity) hqlb (s / 2),
    fun ξ hξ => ?_⟩
  have hnpos : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg ξ
  simp only []
  rw [hqout ξ hξ, ← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul hnpos]
  congr 1
  push_cast
  ring

/-- **The fractional derivative of order `s` exists.** For a Schwartz function whose Fourier
transform vanishes on a neighbourhood of the origin, multiplying that transform by `‖ξ‖^s` again
comes from a Schwartz function. That is the article's `△^{s/2}`, read through its multiplier, and it
is what discharges the hypothesis `hfrac` of `fs_stiefel_reconstruction`.

The hypothesis on the support is what makes `‖ξ‖^s` harmless: it is smooth away from the origin with
polynomially bounded derivatives there, so the product is Schwartz, but at the origin it is not
smooth for non-even `s`. Extending to the natural classes — the Lizorkin space, or the Sobolev space
`H^d` the article works in — is the follow-on, and is what a Riesz potential in `ToMathlib` would
provide.

The proof multiplies inside the Schwartz space, by
`SchwartzMap.smulLeftCLM` applied to a smooth cut-off of the multiplier; that cut-off is
`fs_exists_hasTemperateGrowth_eq_norm_rpow`, which is where the remaining `sorry` sits. Nothing else
about this theorem is open, and the band-limited case
`fs_exists_fractionalDerivative_of_compactSupport` is proved outright. -/
theorem fs_exists_fractionalDerivative (s : ℝ) (φ : SchwartzMap E ℂ)
    (hband : ∃ r > 0, ∀ ξ : E, ‖ξ‖ < r → Fourier.angularFourierIntegralInner φ ξ = 0) :
    ∃ ψ : SchwartzMap E ℂ, ∀ ξ : E,
      Fourier.angularFourierIntegralInner ψ ξ
        = ((‖ξ‖ ^ s : ℝ) : ℂ) * Fourier.angularFourierIntegralInner φ ξ := by
  obtain ⟨r, hr, hzero⟩ := hband
  obtain ⟨h, hhtg, hheq⟩ := fs_exists_hasTemperateGrowth_eq_norm_rpow (E := E) s hr
  have hctg : Function.HasTemperateGrowth (fun ξ : E => ((h ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hhtg
  set Ψ : SchwartzMap E ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun ξ : E => ((h ξ : ℝ) : ℂ)) (angularFourierSchwartz φ) with hΨ
  obtain ⟨ψ, hψ⟩ := fs_exists_angularFourier_eq Ψ
  refine ⟨ψ, fun ξ => ?_⟩
  rw [hψ ξ, hΨ, SchwartzMap.smulLeftCLM_apply_apply hctg, angularFourierSchwartz_apply,
    smul_eq_mul]
  by_cases hξ : r ≤ ‖ξ‖
  · rw [hheq ξ hξ]
  · rw [hzero ξ (lt_of_not_ge hξ)]
    ring

/-! ## The Jacobian of the singular value decomposition -/

section SVD

variable {m : ℕ}

/-- The chart of the singular value decomposition: strictly decreasing positive singular values. -/
def svdChart (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {d | (∀ i, 0 < d i) ∧ ∀ i j : Fin k, i < j → d j < d i}

/-- The matrix `U D Vᵀ` of a point of the singular value chart, as its tuple of columns. -/
def svdMatrix (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] InputSpace m) (d : EuclideanSpace ℝ (Fin k))
    (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) :
    Fin k → InputSpace m :=
  fun i => U (svdDiag d ((Unitary.linearIsometryEquiv V).symm (EuclideanSpace.single i (1 : ℝ))))

/-- The article's `δ(D) = 2^{-k}|det D|^{m-k}∏_{i<j}(dᵢ² - dⱼ²)`, the density of the singular value
decomposition. The first product runs to `k`, the number of singular values; the statement of
`thm:affine` writes `d` there, which its own appendix contradicts. -/
def svdJacobian (m k : ℕ) (d : EuclideanSpace ℝ (Fin k)) : ℝ :=
  (2 : ℝ) ^ (-(k : ℤ)) * (∏ i, d i) ^ (m - k) *
    ∏ i : Fin k, ∏ j ∈ Finset.univ.filter fun j => i < j, (d i ^ 2 - d j ^ 2)

/-- **The Jacobian of the singular value decomposition**, the article's Lemma C.3: Lebesgue measure
on the space of `m × k` matrices, read in the coordinates `A = U D Vᵀ`, has density `δ(D)` against
the invariant measures of the Stiefel manifold and the orthogonal group and Lebesgue measure on the
singular values.

Stated for the lower Lebesgue integral, so that no convergence hypothesis is needed, and with the
constant left existential: `stiefelMeasure` and `orthogonalHaar` are normalized to probability
measures whereas the article's `dU` and `dV` are the classical invariant measures, so the constant
depends on a normalization the statement should not fix. Determining it is what would settle the two
open questions about the article's constants — whether `c_{m,k}` is a Stiefel manifold of the
orthogonal complement, and whether dropping the ordering of the singular values costs a `k!`.

The decomposition itself is `MeasureTheory.exists_svd`; what is missing is only this measure
identity. Of the routes to it, the one that avoids differential forms reduces it to Weyl's
integration formula for real symmetric matrices, which Mathlib also lacks. -/
theorem fs_svdJacobian [Nontrivial (EuclideanSpace ℝ (Fin k))]
    (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] InputSpace m) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ G : (Fin k → InputSpace m) → ENNReal, Measurable G →
        (∫⁻ A : Fin k → InputSpace m, G A)
          = c * ∫⁻ U, (∫⁻ V, (∫⁻ d in svdChart k,
                ENNReal.ofReal (svdJacobian m k d) * G (svdMatrix U d V))
              ∂ContinuousLinearMap.orthogonalHaar) ∂(ContinuousLinearMap.stiefelMeasure L₀) := by
  sorry

end SVD

/-! ## The Helgason--Fourier inversion formula on real hyperbolic space -/

/-- **The Helgason--Fourier inversion formula on `ℍ^m`**, the input the reconstruction formula of
Section 5 needs at the article's first example:

`f(x) = |W|^{-1} ∫_ℝ ∫_{𝕊^{m-1}} f̂(λ,u) e^{(iλ+ϱ)⟨x,u⟩} |c(λ)|^{-2} du dλ`

in the Poincaré ball model, with `dλ` Lebesgue measure on `ℝ`, `du` the uniform probability measure
on the boundary sphere, and `dμ` the invariant measure `(2/(1-‖x‖²))^m dx`.

Every piece of that statement is now constructed, which is what makes this a proposition rather
than a schema: `fs_symmetric_reconstruction_of_inversion` receives the geometry as free data, and
with free data the formula has no truth value. Feeding the ball model to the abstract layer fixes
it,
and `fs_hyperbolic_reconstruction_of_inversion` turns this target into the article's reconstruction
formula on `ℍ^m` with nothing else assumed.

The order of the Weyl group and the `c`-function are existential rather than fixed, for the same
reason as in `fs_svdJacobian`: the triple `(|W|, c, dλ)` is only meaningful jointly. S. Helgason
normalizes `c` by `c(-iϱ) = 1` in *Groups and Geometric Analysis* but writes the inversion formula
of
*Geometric Analysis on Symmetric Spaces* against a normalization of `dλ` that is not Lebesgue
measure, and read with Lebesgue `dλ` the two differ by a power of `π`; the article's appendix mixes
the two. Producing the constant is part of proving this, not of stating it — the same discipline
that
made the constant of the matrix polar integration formula come out as a ratio of sphere areas.

No nonvanishing of `c` is asserted: the rank-one `c`-function is a ratio of Gamma factors with a
pole
at the origin, and correspondingly `|c(λ)|^{-2}` vanishes there.

The test functions are the smooth ones compactly supported inside the ball, which is `𝒟(X)` for the
ball model; that is the class Helgason's Theorem 1.3, Ch. III states the formula for. -/
theorem fs_hyperbolicHelgasonInversion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ (W : ℝ) (c : ℝ → ℂ), 0 < W ∧
      ∀ f : E → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        tsupport f ⊆ HyperbolicSpace.poincareBall E →
        HyperbolicSpace.HasInversion W c f := by
  sorry

/-! ## The Helgason--Fourier inversion formula on the manifold of positive definite matrices -/

/-- **The Helgason--Fourier inversion formula on `ℙ_m = GL(m,ℝ)/O(m)`**, the input the
reconstruction formula of Section 5 needs at the article's second example:

`f(x) = |W|^{-1} ∫_{𝔞*} ∫_{∂ℙ_m} f̂(λ,u) e^{(iλ+ϱ)⟨x,u⟩} |c(λ)|^{-2} du dλ`

read in the chart of upper-triangular coordinates, with `dλ` Lebesgue measure on `𝔞* ≅ ℝ^m`, `du`
the Haar probability measure of the orthogonal group standing in for `K/M`, and `dμ` the invariant
measure `|det x|^{-(m+1)/2} ∏_{i ≤ j} dx_{ij}`.

This is the higher-rank companion of `fs_hyperbolicHelgasonInversion`: the rank of `ℙ_m` is `m`, so
the frequency is a vector, and `fs_spd_reconstruction_of_inversion` turns this target into the
article's reconstruction formula with the Jacobian exponent `m`.

`ϱ` is *not* existential: `SpdSpace.HasInversion` fixes it to `SpdSpace.spdRho m`, the article's
`(-½,…,-½,(m-1)/4)`, which is the contour `Re s = -ρ` of A. Terras, *Harmonic Analysis on Symmetric
Spaces*, Thm 1.3.1(1), read in the coordinates this model uses — the leading principal minors, the
ones her power function `p_s(Y) = ∏_j |Y_j|^{s_j}` is written in. `|W|` and `c` stay existential:
Terras gives both explicitly, but her contour measure has to be converted to Lebesgue measure on
`𝔞*` first, and that conversion is part of proving this. -/
theorem fs_spdHelgasonInversion (m : ℕ) :
    ∃ (W : ℝ) (c : EuclideanSpace ℝ (Fin m) → ℂ), 0 < W ∧
      ∀ f : EuclideanSpace ℝ (SpdSpace.UpperIdx m) → ℂ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        tsupport f ⊆ SpdSpace.chart m →
        SpdSpace.HasInversion W c f := by
  sorry

end LeanRidgelet
