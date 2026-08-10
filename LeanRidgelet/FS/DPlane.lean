/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane.Defs
public import LeanRidgelet.FS.DPlane.CodimOne
public import LeanRidgelet.FS.DPlane.Stiefel
public import LeanRidgelet.FS.DPlane.Similitude
public import LeanRidgelet.FS.DPlane.Affine
public import LeanRidgelet.FS.DPlane.Consistency

/-!
# Fourier slice method, Case IV: the `d`-plane layer and pooling

Section 6 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984).

The activation becomes multivariate, `σ : ℝ^k → ℂ`, which models a pooling layer — average
pooling, max pooling, an `ℓ^p` norm — and the weight becomes a matrix. The null space of a
`d`-plane neuron `σ(Aᵀx - b)` is `d`-dimensional, `d = m - k`, so such a network sees
`d`-dimensional singularities of the target, and the corresponding Radon transform is the
`d`-plane transform.

The article gives three reconstruction formulas, for the weight matrix ranging over all
full-column-rank matrices, over the similitude group, and over the Stiefel manifold. All three are
here. The Stiefel manifold appears as the type of linear isometries `ℝ^k →ₗᵢ E`, which is what an
orthonormal `k`-frame is; the similitude group and the full-column-rank matrices appear through
their parametrizations, `(a, U)` and `(U, D, V)`, which is how the article's parameter measures are
given in the first case and how they are computed in the second.

## Main definitions and results

* `dPlaneCoord`: the coordinate vector `Aᵀx` of the input against the frame.
* `stiefelSynthesis`: the `d`-plane layer over the Stiefel manifold,
  `S[γ](x) = ∫ γ(U,b) σ(Uᵀx - b)`.
* `fs_fourier_dPlaneTransform_fractional`: **the identity behind the third reconstruction
  formula.** For `g` a fractional derivative of `f` of order `s`, the bias spectrum of
  `P_d[g](U, ·)` is `‖ω‖^s` times the Fourier data `𝓕 f (U ω)` of the target. So the coefficient
  function the method produces over the Stiefel manifold is the `d`-plane transform of a
  fractional derivative of the target, which is the article's observation that there the ridgelet
  transform degenerates to a Radon transform.
* `fs_matrixPolarIntegration_codim_one`: the matrix polar integration formula (Lemma C.2) at
  `k = 1`, where it is the two-sided polar formula and the constant is `c_{m,1} = 2`.
* `sphereSynthesis`, `fs_sphere_fourierExpression_of_bias`,
  `fs_sphere_reconstruction_of_inversion`: **the layer and the reconstruction formula at
  codimension one**, where the Stiefel manifold is the unit sphere.
* `fs_stiefel_reconstruction_codim_one`: **the article's Stiefel reconstruction formula at
  `k = 1`**, for an activation of spectrum `|ω|^t`, with the constant `c_{m,1}(2π)^{m-1}`.
* `fs_radon_reconstruction_codim_one`: **the classical Radon formula** of Carroll--Dickinson and
  Ito, as the instance at the actual spectrum `(iω)^{-1}` of the Heaviside step function.
* `inner_dPlaneCoord`: the coordinate map is the transpose of the frame, which is what makes the
  `d`-plane neuron a plane wave in `U ω`.
* `stiefelFourierExpression`, `fs_stiefel_fourierExpression_of_bias`,
  `fs_stiefel_reconstruction_of_inversion`: **the layer and the reconstruction formula in general
  codimension.** The derivation is the codimension-one one with the sphere replaced by the Stiefel
  manifold: the frame integral is evaluated by the matrix polar integration formula of
  `ToMathlib.LieGroup.MatrixPolar` and the remaining Euclidean integral by the inversion formula.
  There is still no Step 2, the Stiefel case having no scale parameter.
* `fs_angularFourier_slice_dPlaneTransform`, `fs_angularFourier_dPlaneTransform_fractional`: the
  Fourier slice theorem and the fractional-derivative identity in the angular convention, in general
  codimension.
* `fs_stiefel_reconstruction`: **the article's `thm:stiefel`**, for an activation of spectrum
  `‖ω‖^t` and the coefficient function `P_d[△^{(d-t)/2}f]`, with the constant `c_{m,k}(2π)^{d}`. It
  carries no convergence hypothesis: the ones the matrix polar formula needs are discharged from
  continuity of the Fourier transform of the target.
* `similitudeSynthesis`, `similitudeFourierExpression`,
  `fs_similitude_fourierExpression_of_bias`, `fs_similitude_reconstruction_of_inversion`: **the
  layer and the reconstruction formula over the similitude group**, the article's `thm:similitude`,
  for an arbitrary real `s`; and `rpow_similitude_split`, `rpow_similitude_radial`, the two exponent
  identities that make its scale–frequency substitution come out.
* `svdDiag`, `fs_ae_forall_coord_ne_zero`, `affineSynthesis`, `affineFourierExpression`,
  `fs_affine_fourierExpression_of_bias`, `fs_affine_reconstruction_of_inversion`: **the layer and
  the reconstruction formula over all full-column-rank matrices**, the article's `thm:affine`, in
  the singular value coordinates `A = U D Vᵀ`. The derivation is the Stiefel one with two
  substitutions
  in front: the frequency is rotated by `V`, and the singular values are traded for the rotated
  frequency coordinatewise, which is where the `∏ |ωᵢ|^{-1}` of the article's scalar comes from.
* `fs_exists_svd_frame`: **the singular value coordinates reach every full-column-rank weight.** So
  the layer above has the same neurons as the article's; what the unformalized Lemma C.3 adds is the
  relation between the two parameter measures, not between the two families of neurons.
* `fs_stiefelSynthesis_codimOne`: **the two developments are the same construction.** At `k = 1` the
  general-codimension layer is the codimension-one layer, up to the total mass of the surface
  measure, the invariant measure on the Stiefel manifold being normalized to a probability measure
  and `Measure.toSphere` not.

The general-codimension `d`-plane transform and its Fourier slice theorem, on which this rests,
are in `ToMathlib.DPlaneTransform`; they subsume the Radon transform of `ToMathlib.RadonTransform`
at `k = 1`, by `MeasureTheory.dPlaneTransform_codimOne`. So the coefficient function of the
codimension-one reconstruction formula, written here as a Radon transform, is literally the
article's `P_d` at `k = 1`. The identification of the two parameter spaces that
`fs_stiefelSynthesis_codimOne` runs on is in `ToMathlib.LieGroup.StiefelCodimOne`.

## What is not here

The Jacobian of the singular value decomposition, the article's Lemma C.3
`dA = δ(D) dD dU dV`, whose published proof goes through exterior differential forms. The
decomposition *itself* is in `ToMathlib.LieGroup.SingularValueDecomposition`, and it is what
`fs_exists_svd_frame` runs on; the Jacobian is the measure-theoretic half, and Mathlib has neither
the Jacobian of the matrix polar decomposition nor Weyl's integration formula for real symmetric
matrices, which it factors through.

Because of that, `affineSynthesis` is defined *in* the singular value coordinates with the Jacobian
left as a parameter `w`. That costs less than it looks like, for two reasons. First, `w` enters the
separation-of-variables ansatz only as a factor of the coefficient function, and the article's
coefficient function carries `1/δ(A)`, so the two cancel and
`fs_affine_reconstruction_of_inversion` holds for *every* weight `w`. Second, the two layers have
the same neurons, by `fs_exists_svd_frame`. So the Jacobian is needed only to relate the two
parameter measures — for the reading of the theorem, not for its proof.

The article's standing absolute-convergence assumption of Section 2 is *not* needed in general
codimension: the two convergence hypotheses of the matrix polar integration formula are discharged
in `ToMathlib.LieGroup.MatrixPolar` from strong measurability of the Fourier data, so the
general-codimension master identities ask for that instead, and `fs_stiefel_reconstruction` — the
article's `thm:stiefel` — asks for nothing beyond integrability of the target and of its Fourier
transform, the Fourier transform of an integrable function being continuous.

## Deviations from the article

*The constant of the Stiefel reconstruction formula is the reciprocal of the article's, and the
value of `c_{m,k}` differs.* The article's `thm:stiefel` reads
`S[R[f]](x) = ((2π)^d c_{m,k})^{-1} f(x)`, but its own derivation gives `c_{m,k}(2π)^d f(x)`: the
coefficient function of the theorem has `ρ♯ ≡ 1`, hence
`φ♯ ≡ 1`, whereas the constant quoted is the one belonging to `φ♯ = c_{m,k}^{-1}(2π)^{-d}`, the
normalization that makes the formula reproduce `f` exactly. At `k = 1` this is
`fs_stiefel_reconstruction_codim_one`, with `c_{m,1}(2π)^{m-1} = 2(2π)^{m-1}`, and the correction
is confirmed independently by the article's own Section 7: the classical Radon formula it quotes
there carries the factor `(2(2π)^{m-1})^{-1}`, which is the reciprocal of what is proved here — as
it must be, the classical formula being solved for `f`. In general codimension the constant proved
here is `c_{m,k}(2π)^d` with `c_{m,k} = |𝕊^{k-1}|/|𝕊^{m-1}|`, the invariant measure on the Stiefel
manifold being normalized to a probability measure; in the classical normalization that reads
`|𝕊^{k-1}| · σ_{m-1,k-1}`, which is the article's `c_{m,k}` with frames of the *orthogonal
complement* of the direction rather than of the whole space. See the module docstring of
`ToMathlib.LieGroup.MatrixPolar`.

*The identification of the step function with `t = -1` loses a factor `-i sgn ω`.* The article
restricts the activation to `σ♯(ω) = |ω|^t` and reads off the Dirac delta at `t = 0`, the step
function at `t = -1` and ReLU at `t = -2`. The step function's spectrum is `πδ(ω) + (iω)^{-1}`,
whose homogeneous part is `-i sgn(ω)|ω|^{-1}` and not `|ω|^{-1}`, so at `t = -1` the coefficient
function of `thm:stiefel` is `△_b^{m/2} P_d[f]` whereas the classical Radon formula's is
`∂_b(-△_b)^{(m-1)/2} P_d[f]`; the two differ by the factor `i sgn ω`, the reciprocal of the phase
dropped from the activation spectrum. Both are instances of the
general codimension-one identity `fs_sphere_reconstruction_of_inversion`, whose hypothesis is that
`γ♯(u,ω) σ♯(ω)` be a constant multiple of `f̂(ωu)|ω|^{m-1}` and which therefore does not need the
activation spectrum to be even; `fs_radon_reconstruction_codim_one` is the classical instance.

*The scalar of the similitude reconstruction formula is a radial integral, not an integral over
`ℝ^k`.* The article's `thm:similitude` writes
`⦅σ,ρ⦆_s ∝ ∫_{ℝ^k} σ♯(ω) conj(ρ♯(ω)) |ω|^{-(d-s+1)} dω`, but what its own derivation produces — and
what `fs_similitude_reconstruction_of_inversion` proves — is the *radial* integral
`∫_{𝕊^{k-1}} ∫_{r>0} r^{-(d-s+1)} σ♯(rv) conj(ρ♯(rv)) dr dv`, which is the same expression *without*
the Jacobian `r^{k-1}` of polar coordinates. The article's own appendix writes the constant as a
radial integral `∫_{ℝ_+} φ♯(r) dr` at the point where it is produced, so the `ℝ^k` form of the
theorem statement is where the Jacobian slips in. The two agree at `k = 1`.

*The scalar of the affine reconstruction formula is an average over `O(k)`, not its value at the
identity.* The article's `thm:affine` has
`⦅σ,ρ⦆ ∝ ∫_{ℝ^k} σ♯(ω) conj(ρ♯(ω)) ∏ᵢ|ωᵢ|^{-1} dω`, obtained from the derivation's
`∫_{O(k)} ∫_{ℝ^k} σ♯(Vω') conj(ρ♯(Vω')) ∏ᵢ|ω'ᵢ|^{-1} dω' dV` by dropping `∫_{O(k)} dV` against the
total mass `1`. That is legitimate only if the inner integral does not depend on `V`, and it does:
substituting `ω = Vω'` turns the weight into `∏ᵢ|(V⁻¹ω)ᵢ|^{-1}`, which is not rotation invariant,
and whose average over `O(k)` diverges for `k ≥ 2` — at `k = 2` it is `‖ω‖^{-2}` times
`∫_0^{2π}|cos θ sin θ|^{-1} dθ`. So the printed scalar is the value of the derivation's integrand at
`V = 1` rather than its average. Here that independence is the hypothesis `hconst` of
`fs_affine_reconstruction_of_inversion`, which is exactly what the article's step needs; the
derivation itself is proved without it, and produces the average. At `k = 1` the orthogonal group is
`{±1}` and the weight is invariant, so the two agree.

Two smaller points about the same theorem. The exponent range in its definition of `δ(A)` reads
`∏_{i=1}^{d}dᵢ^{d}` where there are only `k` singular values; the appendix's `|det D|^d` shows
`∏_{i=1}^{k}dᵢ^{d}` is meant. And the derivation extends the singular values from the positive
orthant to all of `ℝ^k` against a factor `2^{-k}` while dropping the ordering constraint
`d₁ > ⋯ > d_k` of the chart without a compensating `k!`; whether that is a further discrepancy
depends on the normalization in Lemma C.3, which is not formalized here, so it is left open.

One deviation remains planned rather than checked: the article's inversion formula for the `d`-plane
transform, its Lemma 6.2, omits a factor `c_{m,k}`.
-/
