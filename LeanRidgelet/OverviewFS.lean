/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.DPlane
public import LeanRidgelet.FS.Defs
public import LeanRidgelet.FS.Euclidean
public import LeanRidgelet.FS.FiniteField
public import LeanRidgelet.FS.GroupConv
public import LeanRidgelet.FS.Scheme
public import LeanRidgelet.FS.Symmetric
public import LeanRidgelet.FS.Targets

/-!
# Fourier slice method overview: main results of `2402.15984`

Roadmap of the formalization of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984),

developed in `LeanRidgelet/FS/`. This module only re-exports those files; it is the entry point
that names the article's results and points at the declaration proving each. This is plan
milestone M9.

Where the other two developments establish what the ridgelet transform of a depth-2
fully-connected network on Euclidean space *is*, this one abstracts the three-step derivation —
Fourier expression, change of the scale variable, separation of variables — and runs it on other
input domains. The formalization therefore centres on a single conditional theorem carrying the
three steps, with each case supplying an inversion formula on its own domain, the Jacobian of the
scale change of variables, and the integrability needed to exchange the order of integration.
Nothing is assumed as a structure or typeclass field: an inversion formula that Mathlib cannot yet
prove enters as an explicit hypothesis of a theorem.

## Status

Sections 2--7 are done, Section 5 conditionally on an inversion formula out of Mathlib's reach.
Section 6 has its transform, its Fourier slice theorem, and **all three of its reconstruction
formulas — over the Stiefel manifold, over the similitude group, and over all full-column-rank
matrices — in every codimension**, together with the classical Radon formula of Section 7 as an
instance. The measure theory that the general codimension needs is in `ToMathlib.LieGroup`, none of
it being in Mathlib: a compact orthogonal group, an invariant measure on the Stiefel manifold,
uniqueness of the rotation-invariant measure on the sphere, the matrix polar integration formula,
and the singular value decomposition. What remains there is the *Jacobian* of that decomposition,
needed only to relate two parameter measures and not by any proof; it is tracked as a separate long
project.

The Blueprint chapters `overview-fs` and `fs-theory` are published; nothing is development-only at
present, so both Blueprint modes build the same document. See `scripts/build-blueprint.sh`.

## The article's results and where they live

* `FS.Defs` — the shared pairing `fourierSlicePairing`, Section 2.
* `FS.Scheme` — **Section 2, the three steps as one conditional theorem. Complete, with no
  `sorry`.** Step 2 is `fs_changeOfVariables`, Steps 2 and 3 meet in `fs_slice_of_inversion`, and
  the reconstruction formula is `fs_reconstruction_of_inversion`, whose only hypothesis is an
  inversion formula on the input domain. Step 1 is `fs_fourierExpression_of_bias`: its analytic
  input is one-dimensional and enters as a hypothesis, and the rest is the Fubini rearrangement
  `MeasureTheory.integral_integral_integral_swap_left`.
* `FS.Euclidean` — **the classical instance, and the check against the L1 development.**
  `fs_reconstruction_euclidean` is the fully-connected network as an instance with a one-point
  direction space; `fs_separationOfVariables_euclideanRidgeletTransform` shows the ansatz is the
  L1 Fourier expression `eq:fstridge`, and `fs_admissibilityConstant_eq_fourierSlicePairing` that
  the two scalars agree up to `(2π)^m`. On a Euclidean input domain the inversion formula that the
  scheme asks for as a hypothesis is a theorem, `fs_angularFourier_inversion_inner`, which is
  Mathlib's inversion formula transported to the article's angular convention. Section 7's Fourier
  formula of Irie and Funahashi is here too, `fs_fourierFormula_irieFunahashi`: the method with the
  bias frequency pinned rather than integrated, which is why it needs no admissibility condition.
* `FS.FiniteField` — **Section 3, networks on a finite field. Complete, with no `sorry`.** The
  three steps are `fs_finiteField_fourierExpression`, `fs_finiteField_changeOfVariables` and
  `fs_dft_finiteFieldRidgelet`; the master identity is `fs_finiteField_synthesis_ridgelet` and the
  reconstruction formula (Theorem 3.2) is `fs_finiteField_reconstruction`. The general-purpose
  Fourier analysis it rests on — the discrete transform on `ι → ZMod N`, orthogonality of
  characters, and the convolution theorem — is in `ToMathlib.CyclicFourier`.
* `FS.GroupConv` — **Section 4, group convolutional networks on a Hilbert space.** The case
  reduces exactly to the Euclidean one through `fs_inner_frameVector`, so the file is algebra and
  takes whatever Euclidean reconstruction formula one has as a hypothesis. The master identity
  `fs_groupConv_synthesis_ridgelet` reproduces the target at the *projection* of the translated
  input; `fs_groupConv_reconstruction` is the article's conclusion under a compatibility
  hypothesis; `fs_groupConvSynthesis_congr_frameCoord` shows the projection is a limit of the
  architecture rather than of the proof.
* `FS.Symmetric` — **Section 5, networks on a noncompact symmetric space**, conditional on the
  Helgason--Fourier inversion formula. The geometry enters only as data — the composite distance,
  `ϱ`, the density built from `|W|` and the `c`-function, and the Helgason--Fourier transform of
  the target — and `fs_symmetric_reconstruction_of_inversion` is the instance of the abstract
  scheme that feeds the inversion formula to the hypothesis it already asks for. Proving that
  inversion formula is milestone M10.
* `FS.Targets` — **what remains, stated rather than described.** `fs_exists_fractionalDerivative`
  and `fs_svdJacobian` carry a `sorry` each, registered in `audit/Assumptions.lean`; the module
  docstring also records the three results of the article that are deliberately *not* stated, and
  why. No proof elsewhere depends on either target.
* `FS.DPlane` — **Section 6, the `d`-plane layer and pooling. Complete, with no `sorry`.** The case
  is large enough to have its own directory; `FS.DPlane` is its guide and carries the list of
  deviations, and the parts are:
  * `FS.DPlane.Defs` — what every codimension shares: `dPlaneCoord`, `stiefelSynthesis`, the
    fractional-derivative identity `fs_fourier_dPlaneTransform_fractional`, and
    `fs_matrixPolarIntegration_codim_one`, the matrix polar formula at `k = 1` where it *is*
    ordinary polar coordinates and `c_{m,1} = 2`. That degeneration is why codimension one needs no
    measure theory on frames.
  * `FS.DPlane.CodimOne` — the layer over the sphere, the master identity
    `fs_sphere_reconstruction_of_inversion`, the article's Stiefel formula at `k = 1`
    (`fs_stiefel_reconstruction_codim_one`) and the classical Radon formula of Carroll--Dickinson
    and Ito (`fs_radon_reconstruction_codim_one`), which the article's Section 7 quotes and which
    confirms the corrected constant.
  * `FS.DPlane.Stiefel` — the same three moves in general codimension, the frame integral now
    evaluated by the matrix polar integration formula of `ToMathlib.LieGroup.MatrixPolar`:
    `fs_stiefel_reconstruction_of_inversion` and the article's own form
    `fs_stiefel_reconstruction`. Also `fs_dPlaneInversion`, the article's Lemma 6.2, which falls out
    of the same two ingredients and is where its missing `c_{m,k}` shows.
  * `FS.DPlane.Similitude` — `fs_similitude_reconstruction_of_inversion`. There the scale genuinely
    interacts with the frequency — they couple through `y = a r`, so the network is *not* a scale
    mixture of Stiefel networks — and the Fubini exchange that handles it goes into Step 1, where
    the article puts it.
  * `FS.DPlane.Affine` — `fs_affine_reconstruction_of_inversion`, over all full-column-rank
    matrices, in the singular value coordinates. Two substitutions in front of the Stiefel case do
    it, and `fs_exists_svd_frame` shows those coordinates reach every such matrix.
  * `FS.DPlane.Consistency` — `fs_stiefelSynthesis_codimOne`: the general-codimension layer *is* the
    codimension-one layer at `k = 1`, so the specialization is a theorem and not a resemblance.

  The general-codimension `d`-plane transform and its Fourier slice theorem are in
  `ToMathlib.DPlaneTransform`, which subsumes `ToMathlib.RadonTransform` at `k = 1`.

## Deviations from the article

Recorded per file as the cases are formalized; see the *Deviations from the article* section of
`FS.FiniteField` for Section 3, where the scalar of the reconstruction formula is corrected, the
bias frequency `0` is excluded, and the ridgelet function is required to have vanishing mean, and
that of `FS.DPlane` for Section 6, where the constant of the Stiefel reconstruction formula is the
reciprocal of the article's, the identification of the step function with the exponent `t = -1`
loses a phase, the scalar of the similitude reconstruction formula is a radial integral rather than
an integral over `ℝ^k`, and the scalar of the affine one is an average over `O(k)` rather than its
value at the identity. One further deviation is settled in advance and stated in the Blueprint
overview chapter: the group convolutional reconstruction formula reproduces the target function
composed with the orthogonal projection onto the span of the chosen frame.
-/
