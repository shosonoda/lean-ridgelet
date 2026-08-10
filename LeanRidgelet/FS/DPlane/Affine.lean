/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.Stiefel
public import LeanRidgelet.ToMathlib.DiagonalScaling
public import LeanRidgelet.ToMathlib.LieGroup.SingularValueDecomposition

/-!
# Fourier slice method, Case IV: all full-column-rank matrices

Section 6 of `arXiv:2402.15984` over all matrices of full column rank, the article's `thm:affine`
and the result it reports as new. The derivation runs through the singular value decomposition `A =
U D Vᵀ`, and the layer is defined *in* those coordinates because the Jacobian that converts them to
Lebesgue measure on the matrix space — the article's Lemma C.3 — is not formalized. The
decomposition itself is, in `ToMathlib.LieGroup.SingularValueDecomposition`.

That the Jacobian is missing costs less than it looks like, for two reasons. The weight enters the
separation-of-variables condition only as a factor of the coefficient function, and the article's
coefficient function carries its reciprocal, so the two cancel and the reconstruction formula holds
for *every* weight. And the two layers have the same neurons, by `fs_exists_svd_frame`. So the
Jacobian is needed only to relate the two parameter *measures*.

## Main definitions and results

* `svdDiag`, `svdDiag_comm`, `inner_svdDiag`: the diagonal factor acting on a frequency
  coordinatewise, and the two facts the derivation uses about it.
* `fs_ae_forall_coord_ne_zero`: the coordinate hyperplanes are null, which is what the
  coordinatewise change of variables needs.
* `affineSynthesis`, `affineFourierExpression`, `fs_affine_fourierExpression_of_bias`: the layer in
  singular value coordinates and Step 1.
* `fs_affine_reconstruction_of_inversion`: **the reconstruction formula.** The derivation is the
  Stiefel one with two substitutions in front: the frequency is rotated by `V`, and the singular
  values are traded against the rotated frequency coordinatewise. The latter is
  `MeasureTheory.integral_comp_diagScale`, and it is where the `∏ |ωᵢ|^{-1}` of the article's scalar
  comes from rather than a power of `‖ω‖`.
* `fs_exists_svd_frame`: **the singular value coordinates reach every full-column-rank weight.**
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace LeanRidgelet

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### All full-column-rank matrices

The article's `thm:affine`, the first of the three reconstruction formulas and the one it reports as
new. The weight matrix now ranges over all `m × k` matrices of full column rank, and the derivation
runs through the singular value decomposition `A = U D Vᵀ`: the frame `U` is a point of the Stiefel
manifold, `V` a rotation of the frequency space, and `D` the `k` singular values, which act on a
frequency coordinatewise.

**The parametrization is part of the definition here.** The article's parameter measure is Lebesgue
measure `dA` on the matrix space, and converting it to the singular value coordinates is its Lemma
C.3 — the Jacobian `dA = δ(D) dD dU dV`, whose published proof goes through exterior differential
forms and which Mathlib is far from: it has singular *values*
(`LinearMap.singularValues`) but neither the decomposition, nor the Jacobian of the matrix polar
decomposition, nor Weyl's integration formula for symmetric matrices that the Jacobian factors
through. So the layer is defined *in* the singular value coordinates, with the weight `w` left as a
parameter, and the reconstruction formula is proved there. Granting Lemma C.3 with `w = δ`, this is
the article's theorem; what is not formalized is exactly that one statement, and nothing else in the
derivation needs it.

What the derivation does need is two changes of variables and then the matrix polar integration
formula of `ToMathlib.LieGroup.MatrixPolar` — the same one the Stiefel case ends with. The frequency
is rotated by `V`, which is an isometry hence measure preserving; the singular values are then
traded for the rotated frequency coordinatewise, `y = D ω'`, whose Jacobian is `∏ |ω'ᵢ|` — that is
`MeasureTheory.integral_comp_diagScale`. After both, the parameter integral is `∫_U ∫_y ‖U y‖^{m-k}
F(U y)`, which is what the matrix polar formula evaluates. So the affine case is the Stiefel case
with two substitutions in front of it, and the coordinatewise Jacobian is what puts `∏ |ωᵢ|^{-1}` —
rather than a power of `‖ω‖` — into the article's scalar.
-/

section Affine

open Metric

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The diagonal factor of a singular value decomposition, acting on a vector of the frequency space
coordinatewise: `(D ω)ᵢ = dᵢ ωᵢ`. -/
def svdDiag (d ω : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  MeasureTheory.diagScale (WithLp.ofLp d) ω

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem svdDiag_apply (d ω : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    svdDiag d ω i = d i * ω i := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The diagonal action is symmetric in its two arguments, both being coordinatewise
multiplication. -/
theorem svdDiag_comm (d ω : EuclideanSpace ℝ (Fin k)) : svdDiag d ω = svdDiag ω d := by
  ext i
  exact mul_comm _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A diagonal matrix is symmetric. -/
theorem inner_svdDiag (d a b : EuclideanSpace ℝ (Fin k)) :
    inner ℝ a (svdDiag d b) = inner ℝ (svdDiag d a) b := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, svdDiag_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coordinate hyperplanes are null.** Almost every frequency has all coordinates nonzero,
which is what the coordinatewise change of variables of the affine case needs. -/
theorem fs_ae_forall_coord_ne_zero :
    ∀ᵐ ω : EuclideanSpace ℝ (Fin k), ∀ i, ω i ≠ 0 := by
  have hker : ∀ i : Fin k,
      (volume : Measure (EuclideanSpace ℝ (Fin k)))
        {ω : EuclideanSpace ℝ (Fin k) | ω i = 0} = 0 := by
    intro i
    set K : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
      LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin k) i).toLinearMap with hK
    have hsub : {ω : EuclideanSpace ℝ (Fin k) | ω i = 0}
        = (K : Set (EuclideanSpace ℝ (Fin k))) := by
      ext ω
      simp [hK, LinearMap.mem_ker, EuclideanSpace.proj]
    have hne : K ≠ ⊤ := by
      intro htop
      have h1 : EuclideanSpace.single i (1 : ℝ) ∈ K := htop ▸ Submodule.mem_top
      rw [hK, LinearMap.mem_ker] at h1
      simp [EuclideanSpace.proj] at h1
    rw [hsub]
    exact Measure.addHaar_submodule _ K hne
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hker)
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hω
  obtain ⟨i, hi⟩ := hω
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable [Nontrivial E] [Nontrivial (EuclideanSpace ℝ (Fin k))]

/-- The `d`-plane layer over all full-column-rank matrices, in the singular value coordinates
`A = U D Vᵀ`:
`S[γ](x) = ∫ w(D) γ(U,D,V,b) σ(V D Uᵀ x - b) dD dV dU db`.
The weight `w` stands for the Jacobian `δ` of the singular value decomposition, which is left as a
parameter because Lemma C.3 is not formalized. -/
def affineSynthesis (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E))
    (w : EuclideanSpace ℝ (Fin k) → ℝ) (σ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) →
      unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ∫ U, (∫ V, (∫ d : EuclideanSpace ℝ (Fin k), ((w d : ℝ) : ℂ) *
      ∫ b : EuclideanSpace ℝ (Fin k), γ U d V b *
        σ (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)) - b))
    ∂ContinuousLinearMap.orthogonalHaar) ∂ν

/-- The Fourier expression of the affine layer, the output of Step 1. The bias frequency sits
outside the singular value integral, which is where the derivation needs it. -/
def affineFourierExpression (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E))
    (w : EuclideanSpace ℝ (Fin k) → ℝ) (Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) →
      unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℂ) (x : E) : ℂ :=
  ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
    ∫ U, (∫ V, (∫ ω : EuclideanSpace ℝ (Fin k), ∫ d : EuclideanSpace ℝ (Fin k),
        ((w d : ℝ) : ℂ) * (Γ U d V ω * Fσ ω *
          fourierSlicePhase (inner ℝ ω
            (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))))
      ∂ContinuousLinearMap.orthogonalHaar) ∂ν

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [Nontrivial (EuclideanSpace ℝ (Fin k))] in
/-- **Step 1 over the full-column-rank matrices**: the layer equals its Fourier expression. As in
the similitude case the analytic input is the `k`-dimensional bias identity at each matrix, together
with one Fubini exchange moving the bias frequency outside the singular value integral. -/
theorem fs_affine_fourierExpression_of_bias
    (ν : Measure (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)) (w : EuclideanSpace ℝ (Fin k) → ℝ)
    (σ Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (γ Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) →
      unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℂ) (x : E)
    (hbias : ∀ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (d : EuclideanSpace ℝ (Fin k))
      (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))),
      (∫ b : EuclideanSpace ℝ (Fin k), γ U d V b *
          σ (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)) - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k), Γ U d V ω * Fσ ω *
            fourierSlicePhase (inner ℝ ω
              (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)))))
    (hswap : ∀ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
      (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))),
      Integrable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
          ((w p.1 : ℝ) : ℂ) * (Γ U p.1 V p.2 * Fσ p.2 *
            fourierSlicePhase (inner ℝ p.2
              (Unitary.linearIsometryEquiv V (svdDiag p.1 (dPlaneCoord U x))))))
        (volume.prod volume)) :
    affineSynthesis ν w σ γ x = affineFourierExpression ν w Fσ Γ x := by
  rw [affineSynthesis, affineFourierExpression, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only []
  have hstep : ∀ d : EuclideanSpace ℝ (Fin k),
      ((w d : ℝ) : ℂ) * (∫ b : EuclideanSpace ℝ (Fin k), γ U d V b *
          σ (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)) - b))
        = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ *
          ∫ ω : EuclideanSpace ℝ (Fin k), ((w d : ℝ) : ℂ) * (Γ U d V ω * Fσ ω *
            fourierSlicePhase (inner ℝ ω
              (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))) := by
    intro d
    rw [hbias U d V, integral_const_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_const_mul,
    integral_integral_swap (hswap U V)]

/-- **The reconstruction formula over all full-column-rank matrices** — the article's `thm:affine`,
in the singular value coordinates. The separation-of-variables ansatz is the article's `eq:sov`:
after the frequency has been rotated to `ω = V ω'`, the product of the weight, the Jacobian
`∏ |ω'ᵢ|⁻¹` of the coordinatewise substitution, and the two spectra must be the Fourier data of the
target along the frame times a factor `Φ` of the rotation and the rotated frequency alone. Then the
`Φ`-integral is the article's scalar `⦅σ,ρ⦆` and the rest is the matrix polar integration formula.

`hconst` asks the `Φ`-integral to be the same at every rotation. The article's own computation of
`⦅σ,ρ⦆` needs exactly that: it drops `∫_{O(k)} dV` against the total mass `1`, which is legitimate
only when the inner integral does not depend on `V`. With `Φ(V,ω') = σ♯(Vω') conj(ρ♯(Vω')) ∏|ω'ᵢ|⁻¹`
that independence is not automatic — the coordinatewise weight is not rotation invariant — so it is
a hypothesis here rather than a step of the proof.

No convergence hypothesis is needed beyond integrability of the Fourier data: both changes of
variables are along equivalences, and the two convergence hypotheses of the matrix polar formula are
discharged from strong measurability. -/
theorem fs_affine_reconstruction_of_inversion
    (L₀ : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (c cphi : ℂ)
    (w : EuclideanSpace ℝ (Fin k) → ℝ) (Fσ : EuclideanSpace ℝ (Fin k) → ℂ)
    (Γ : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → EuclideanSpace ℝ (Fin k) →
      unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℂ)
    (Φ : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) →
      EuclideanSpace ℝ (Fin k) → ℂ)
    (Ff f : E → ℂ) (x : E) (hFfm : StronglyMeasurable Ff)
    (hansatz : ∀ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
      (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      (ω : EuclideanSpace ℝ (Fin k)), (∀ i, ω i ≠ 0) → ∀ d : EuclideanSpace ℝ (Fin k),
      ((w d : ℝ) : ℂ) *
            (Γ U d V (Unitary.linearIsometryEquiv V ω) * Fσ (Unitary.linearIsometryEquiv V ω)) *
            (((∏ i, |ω i|)⁻¹ : ℝ) : ℂ)
        = c * ((‖U (svdDiag ω d)‖ ^
              (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) : ℝ) : ℂ) *
            Ff (U (svdDiag ω d)) * Φ V ω)
    (hconst : ∀ V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)),
      (∫ ω : EuclideanSpace ℝ (Fin k), Φ V ω) = cphi)
    (hF : Integrable (fun ξ : E => Ff ξ * fourierSlicePhase (inner ℝ ξ x)) volume)
    (hinv : (∫ ξ : E, Ff ξ * fourierSlicePhase (inner ℝ ξ x))
      = (((2 * Real.pi) ^ Module.finrank ℝ E : ℝ) : ℂ) * f x) :
    ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        affineFourierExpression (ContinuousLinearMap.stiefelMeasure L₀) w Fσ Γ x
      = c * cphi *
          (((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere.real Set.univ : ℝ) : ℂ) *
          ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) * f x := by
  have hkE : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hkm : k ≤ Module.finrank ℝ E := by
    have := LinearMap.finrank_le_finrank_of_injective (f := L₀.toLinearMap) L₀.injective
    rwa [hkE] at this
  set F : E → ℂ := fun ξ => Ff ξ * fourierSlicePhase (inner ℝ ξ x) with hFdef
  have hFsm : StronglyMeasurable F :=
    hFfm.mul (continuous_fourierSlicePhase.comp
      (Continuous.inner continuous_id continuous_const)).stronglyMeasurable
  -- the weighted frame section, the integrand of the matrix polar integration formula
  set Y : (EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) → ℂ := fun U =>
    ∫ y : EuclideanSpace ℝ (Fin k),
      ‖U y‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (U y)
    with hYdef
  -- Steps 2 and 3 at a fixed frame and rotation
  have hframe : ∀ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E)
      (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))),
      (∫ ω : EuclideanSpace ℝ (Fin k), ∫ d : EuclideanSpace ℝ (Fin k),
          ((w d : ℝ) : ℂ) * (Γ U d V ω * Fσ ω *
            fourierSlicePhase (inner ℝ ω
              (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))))
        = cphi * (c * Y U) := by
    intro U V
    rw [← (Unitary.linearIsometryEquiv V).measurePreserving.integral_comp
      (Unitary.linearIsometryEquiv V).toMeasurableEquiv.measurableEmbedding
      (fun ω : EuclideanSpace ℝ (Fin k) => ∫ d : EuclideanSpace ℝ (Fin k),
        ((w d : ℝ) : ℂ) * (Γ U d V ω * Fσ ω *
          fourierSlicePhase (inner ℝ ω
            (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))))]
    have hpt : ∀ ω : EuclideanSpace ℝ (Fin k), (∀ i, ω i ≠ 0) →
        (∫ d : EuclideanSpace ℝ (Fin k), ((w d : ℝ) : ℂ) *
            (Γ U d V (Unitary.linearIsometryEquiv V ω) *
              Fσ (Unitary.linearIsometryEquiv V ω) *
              fourierSlicePhase (inner ℝ (Unitary.linearIsometryEquiv V ω)
                (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))))
          = Φ V ω * (c * Y U) := by
      intro ω hω
      have hprodne : (∏ i, |ω i|) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i _ => abs_ne_zero.2 (hω i)
      have hprodneC : (((∏ i, |ω i|) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hprodne
      -- the phase becomes a plane wave in `U (D ω)`
      have hphase : ∀ d : EuclideanSpace ℝ (Fin k),
          inner ℝ (Unitary.linearIsometryEquiv V ω)
              (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)))
            = inner ℝ (U (svdDiag ω d)) x := fun d => by
        rw [(Unitary.linearIsometryEquiv V).inner_map_map ω (svdDiag d (dPlaneCoord U x)),
          inner_svdDiag, inner_dPlaneCoord, svdDiag_comm]
      -- rewrite the integrand as a constant times a function of `y = D ω`
      have hint : ∀ d : EuclideanSpace ℝ (Fin k),
          ((w d : ℝ) : ℂ) * (Γ U d V (Unitary.linearIsometryEquiv V ω) *
              Fσ (Unitary.linearIsometryEquiv V ω) *
              fourierSlicePhase (inner ℝ (Unitary.linearIsometryEquiv V ω)
                (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)))))
            = ((((∏ i, |ω i|) : ℝ) : ℂ) * (Φ V ω * c)) *
                (‖U (MeasureTheory.diagScale (WithLp.ofLp ω) d)‖ ^
                    (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) •
                  F (U (MeasureTheory.diagScale (WithLp.ofLp ω) d))) := by
        intro d
        have hans := hansatz U V ω hω d
        have hmul : ((w d : ℝ) : ℂ) * (Γ U d V (Unitary.linearIsometryEquiv V ω) *
              Fσ (Unitary.linearIsometryEquiv V ω))
            = (((∏ i, |ω i|) : ℝ) : ℂ) *
              (c * ((‖U (svdDiag ω d)‖ ^
                  (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) : ℝ) : ℂ) *
                Ff (U (svdDiag ω d)) * Φ V ω) := by
          rw [← hans, Complex.ofReal_inv]
          field_simp
        rw [hphase d, show ((w d : ℝ) : ℂ) * (Γ U d V (Unitary.linearIsometryEquiv V ω) *
              Fσ (Unitary.linearIsometryEquiv V ω) *
              fourierSlicePhase (inner ℝ (U (svdDiag ω d)) x))
            = (((w d : ℝ) : ℂ) * (Γ U d V (Unitary.linearIsometryEquiv V ω) *
                Fσ (Unitary.linearIsometryEquiv V ω))) *
              fourierSlicePhase (inner ℝ (U (svdDiag ω d)) x) from by ring, hmul, hFdef,
          Complex.real_smul]
        simp only [svdDiag]
        ring
      have hYU : Y U = ∫ y : EuclideanSpace ℝ (Fin k),
          ‖U y‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (U y) := by
        simp only [hYdef]
      rw [integral_congr_ae (Filter.Eventually.of_forall hint), integral_const_mul,
        MeasureTheory.integral_comp_diagScale (w := WithLp.ofLp ω) (fun i => hω i)
          (fun y : EuclideanSpace ℝ (Fin k) =>
            ‖U y‖ ^ (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) • F (U y)),
        hYU, Complex.real_smul, Complex.ofReal_inv]
      field_simp
    rw [integral_congr_ae ((fs_ae_forall_coord_ne_zero (k := k)).mono hpt), integral_mul_const,
      hconst V]
  -- the rotation integral is constant, and the frame integral is the matrix polar formula
  have hV : ∀ U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E,
      (∫ V, (∫ ω : EuclideanSpace ℝ (Fin k), ∫ d : EuclideanSpace ℝ (Fin k),
          ((w d : ℝ) : ℂ) * (Γ U d V ω * Fσ ω *
            fourierSlicePhase (inner ℝ ω
              (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x))))))
        ∂ContinuousLinearMap.orthogonalHaar) = cphi * (c * Y U) := by
    intro U
    rw [integral_congr_ae (Filter.Eventually.of_forall (hframe U)), integral_const]
    simp
  have hpow : ((2 * (Real.pi : ℂ)) ^ Module.finrank ℝ E)
      = ((2 * (Real.pi : ℂ)) ^ k) * ((2 * (Real.pi : ℂ)) ^ (Module.finrank ℝ E - k)) := by
    rw [← pow_add]
    congr 1
    omega
  have hpi : ((2 * (Real.pi : ℂ)) ^ k) ≠ 0 := pow_ne_zero _ Fourier.two_mul_pi_complex_ne_zero
  have hpolar := MeasureTheory.toSphere_real_smul_integral_stiefelMeasure_of_stronglyMeasurable
    L₀ hFsm hF
  rw [affineFourierExpression, integral_congr_ae (Filter.Eventually.of_forall hV),
    integral_const_mul, integral_const_mul, ← hYdef]
  have hcollect : ((((volume : Measure E).toSphere.real Set.univ : ℝ) : ℂ)) *
        (((2 * (Real.pi : ℂ)) ^ k)⁻¹ * (cphi * (c *
          ∫ U, Y U ∂(ContinuousLinearMap.stiefelMeasure L₀))))
      = ((2 * (Real.pi : ℂ)) ^ k)⁻¹ * (cphi * c) *
        ((((volume : Measure E).toSphere.real Set.univ : ℝ)) •
          ∫ U, Y U ∂(ContinuousLinearMap.stiefelMeasure L₀)) := by
    rw [Complex.real_smul]
    ring
  rw [hcollect, hYdef, hpolar, hFdef, hinv, Complex.real_smul]
  push_cast
  rw [hpow]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [Nontrivial (EuclideanSpace ℝ (Fin k))] in
/-- **The singular value coordinates reach every full-column-rank weight.** For an injective
`A : ℝ^k → E` there are a frame `U`, positive singular values `d` and a rotation `V` whose neuron
has the same plane-wave frequency as `A` at every frequency and input,
`⟪ω, V D Uᵀx⟫ = ⟪Aω, x⟫`. So the layer defined in the singular value coordinates has the same
neurons as the article's layer over the full-column-rank matrices; what the unformalized Lemma C.3
adds is the relation between the two parameter *measures*, not between the two families of
neurons. -/
theorem fs_exists_svd_frame (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) (hA : Function.Injective A) :
    ∃ (U : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] E) (d : EuclideanSpace ℝ (Fin k))
      (V : unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))),
      (∀ i, 0 < d i) ∧ ∀ (ω : EuclideanSpace ℝ (Fin k)) (x : E),
        inner ℝ ω (Unitary.linearIsometryEquiv V (svdDiag d (dPlaneCoord U x)))
          = inner ℝ (A ω) x := by
  obtain ⟨U, d, V', hdpos, hsvd⟩ := MeasureTheory.exists_svd A hA
  refine ⟨U, d, ContinuousLinearMap.unitaryOfIsometryEquiv V', hdpos, fun ω x => ?_⟩
  have hV : Unitary.linearIsometryEquiv (ContinuousLinearMap.unitaryOfIsometryEquiv V') = V' :=
    Unitary.linearIsometryEquiv.apply_symm_apply V'
  rw [hV, show (inner ℝ ω (V' (svdDiag d (dPlaneCoord U x))) : ℝ)
      = inner ℝ (V'.symm ω) (svdDiag d (dPlaneCoord U x)) from by
    rw [← V'.inner_map_map (V'.symm ω) (svdDiag d (dPlaneCoord U x)), V'.apply_symm_apply],
    inner_svdDiag, inner_dPlaneCoord, hsvd ω]
  rfl

end Affine
end LeanRidgelet
