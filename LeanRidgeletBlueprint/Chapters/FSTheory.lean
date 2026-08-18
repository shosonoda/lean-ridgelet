import LeanRidgelet.OverviewFS
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
-- Verso directive headers and display mathematics must stay on one physical line.
set_option linter.style.longLine false
set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Fourier slice method: formalization details" =>
%%%
file := "fs-theory"
%%%

The machinery behind the results of the previous chapter, organized by Lean dependency rather than by publication order. Each section corresponds to one file of `LeanRidgelet/FS/`.

*Status: every file exists, and all of Sections 2--7 is proved — Section 5 conditionally on an inversion formula out of Mathlib's reach, and Section 6 in full, including its inversion formula and all three of its reconstruction formulas in every codimension.* What remains is stated rather than described: `FS.Targets` carries the two outstanding propositions with a `sorry` each — the existence of the fractional derivative, which is the one hypothesis Section 6's own form still carries, and the Jacobian of the singular value decomposition. No proof in this chapter depends on either. Three further results of the article are not stated at all, and `FS.Targets` says why: the inversion formula of Section 5 with its two examples needs the geometry constructed first, and Rubin's transform cannot be checked against its source.

*`FS.Defs`: the scalar every case shares*

:::definition "fs_pairing_detail" (lean := "LeanRidgelet.fourierSlicePairing")
*The Fourier slice pairing.* $`(\!(\sigma,\rho)\!)_r=\frac{1}{2\pi}\int_{\omega\neq0}\sigma^\sharp(\omega)\overline{\rho^\sharp(\omega)}|\omega|^{-r}\,\mathrm d\omega`, taking the two spectra rather than the two functions as arguments, since the activation is a tempered distribution in the manuscript and only its spectrum is ever used. The integral is over the complement of the origin, matching `LeanRidgelet.admissibilityConstant` of the L1 theory, which is the same scalar in the same convention.
:::

:::lemma_ "fs_pairing_algebra" (lean :="LeanRidgelet.fs_fourierSlicePairing_zero_left, LeanRidgelet.fs_fourierSlicePairing_zero_right, LeanRidgelet.fs_fourierSlicePairing_const_mul_left, LeanRidgelet.fs_fourierSlicePairing_conj") (uses := "fs_pairing_detail")
*The pairing is sesquilinear.* It vanishes when either spectrum does, it is homogeneous in the activation spectrum, and exchanging the two spectra conjugates it. These hold unconditionally, without any integrability hypothesis, because both sides degenerate to the same junk value when the integrand fails to be integrable.
:::

*`FS.Scheme`: the three steps as one conditional theorem*

:::theorem "fs_scheme_detail" (lean := "LeanRidgelet.fourierSlicePhase, LeanRidgelet.fourierExpressionSynthesis, LeanRidgelet.separationOfVariables, LeanRidgelet.inversionIntegral, LeanRidgelet.fs_changeOfVariables, LeanRidgelet.fs_slice_of_inversion, LeanRidgelet.sliceSynthesis, LeanRidgelet.fs_fourierExpression_of_bias, LeanRidgelet.fs_reconstruction_of_inversion") (uses := "fs_pairing_detail, mathlib_iterated_fubini")
*The abstract reconstruction theorem.* The scale space is a finite-dimensional real inner product space `V` with an additive Haar measure, whose dimension is the exponent `r`; the direction space `U` carries a measure; the input domain `X` needs no structure at all, since only the composite distance and the weight see it. Step 2 is the scaling behaviour of the Haar measure and holds for every integrand and every `ω`, both sides degenerating together. Steps 2 and 3 meet in the weight integral at a fixed bias frequency, which the ansatz turns into the inversion integral rescaled by the Jacobian. The reconstruction theorem composes them, with the inversion formula on the input domain as its only hypothesis.
:::

No integrability hypothesis appears in the reconstruction theorem, and none is needed: substituting the ansatz makes the bias frequency factor out of both inner integrals as a constant, so that proof never exchanges an order of integration. Fubini enters in Step 1 instead, and there it is unavoidable: `fs_fourierExpression_of_bias` takes the one-dimensional bias identity and the integrability of the triple integrand, and the rearrangement itself is the upstream-candidate `integral_integral_integral_swap_left`. Over a finite field both hypotheses are finite-sum statements and `fs_finite_field_detail` discharges them.

*`FS.Euclidean`: the classical case, and agreement with the L1 development*

:::theorem "fs_euclidean_detail" (lean := "LeanRidgelet.fs_inversionIntegral_euclidean, LeanRidgelet.fs_finrank_inputSpace, LeanRidgelet.fs_reconstruction_euclidean, LeanRidgelet.fs_separationOfVariables_euclideanRidgeletTransform, LeanRidgelet.fs_admissibilityConstant_eq_fourierSlicePairing, LeanRidgelet.fs_inversionIntegral_polar, LeanRidgelet.fs_integrable_angularFourier_iff, LeanRidgelet.fs_angularFourier_inversion_inner, LeanRidgelet.fs_integrable_angularFourier_mul_phase, LeanRidgelet.fs_angularFourier_inversion_inputSpace, LeanRidgelet.fs_angularFourier_inversion_ae, LeanRidgelet.fs_angularFourier1D_convolution, LeanRidgelet.fs_bias_fourierExpression_ae") (uses := "fs_scheme_detail, mathlib_polar_coordinates")
*The Euclidean instance, and the check against the L1 development.* Taking the direction space to be a point collapses its integral, leaving the plain inversion integral on $`\mathbb R^m`; the scale space is $`\mathbb R^m` itself, so $`r=m`. Two identities then check the abstraction against the L1 formalization, which predates it and was built independently: the ansatz at homogeneity index $`s=0` is the L1 Fourier expression `eq:fstridge`, and the L1 admissibility constant is $`(2\pi)^m` times the Fourier slice pairing of the same two spectra.
:::

The polar instance is there too: writing the weight as $`\boldsymbol a=\lambda\boldsymbol u` turns the instance with scale space $`\mathbb R^m` and a point for directions into one with scale space $`\mathbb R` and the sphere for directions, and `fs_inversionIntegral_polar` shows the inversion integral is the same. So both are instances of the scheme for the same domain and the same target, with Jacobian exponents $`m` and $`1`: *the rank is a property of the parametrization of the weight, not of the input domain.* The $`r=1` shape is the one the symmetric-space case takes, with the sphere in the role of the boundary. The density carries the factor $`2^{-1}` of the two-sided polar formula, which is the double cover $`(\lambda,\boldsymbol u)\mapsto\lambda\boldsymbol u`.

The one-dimensional input of Step 1 is discharged here too, for an integrable activation: `fs_bias_fourierExpression_ae` is the convolution theorem in the angular convention followed by Fourier inversion, and it holds almost everywhere, which is what inversion gives without a continuity hypothesis. Both are transported from the Mathlib $`2\pi` convention by rescaling the frequency, and the factor $`(2\pi)^{-1}` in front of the Fourier expression is the Jacobian of that rescaling.

So is the inversion formula that the abstract scheme asks for as a hypothesis: on a Euclidean input domain it is a theorem, `fs_angularFourier_inversion_inner`, Mathlib's inversion formula at a continuity point rescaled into the angular convention, and the constant $`(2\pi)^r` it produces is the reciprocal of the inversion density $`\kappa=(2\pi)^{-r}` the instance carries. The same rescaling matches the integrable Fourier transforms of the two conventions, which is what makes the inversion integrand integrable.

*`FS.FiniteField`: the discrete case*

:::theorem "fs_finite_field_detail" (lean := "LeanRidgelet.fs_finiteField_sum_slice, LeanRidgelet.fs_finiteField_synthesis_ridgelet") (uses := "mathlib_cyclic_fourier")
*Master identity over a finite field.* Steps 2 and 3 meet in the weight sum at a fixed bias frequency: at $`\omega\neq0` the change of variables turns it into Fourier inversion of $`f` at $`x`, and at $`\omega=0` the change of variables is unavailable and the sum collapses onto the total mass $`\sum_yf(y)` instead. That asymmetry is the entire difference from the Euclidean case, and it is what produces the rank-one defect in the unconditional identity. Everything is a finite sum, so no analytic hypothesis appears anywhere in the file.
:::

:::lemma_ "fs_finite_field_mean_zero" (lean := "LeanRidgelet.meanZeroPart, LeanRidgelet.fs_sum_meanZeroPart, LeanRidgelet.fs_dft_meanZeroPart, LeanRidgelet.fs_finiteFieldPairing_meanZeroPart") (uses := "fs_finite_field_detail")
*Normalizing the ridgelet function.* Subtracting its mean makes any $`\rho` satisfy the vanishing-mean hypothesis, changes no nonzero bias frequency — the spectrum of a constant is supported at the origin — and therefore leaves the scalar $`(\!(\sigma,\rho)\!)` unchanged. So the hypothesis is a normalization, not a restriction on which ridgelet functions may be used.
:::

*`FS.GroupConv`: reduction to the Euclidean case*

:::theorem "fs_gconv_detail" (lean := "LeanRidgelet.fs_frameCoord_frameVector, LeanRidgelet.fs_groupConvRidgelet_eq_euclidean, LeanRidgelet.fs_groupConv_compat_of_mem") (uses := "fs_euclidean_detail, fs_gconv_projection_structural")
*The reduction, and what it costs.* The file is algebra. One identity does the work — pairing a filter of the span of the frame against any input is pairing their coordinate vectors — and everything else follows from it: the network is a Euclidean network at the coordinate vector of the translated input, the ridgelet transform is the Euclidean ridgelet transform of the pulled-back target, and the network's dependence on the input factors through those coordinates. Orthonormality of the frame is needed only where the coordinates have to recover the coefficients: in the ridgelet transform, and in identifying the projection with the identity on the span.
:::

The Euclidean reconstruction formula enters as a hypothesis rather than a fixed theorem, so the `L¹` reconstruction of the L1 development and the Fourier slice scheme are both usable and the case commits to neither.

*`FS.Symmetric`: the conditional case*

:::theorem "fs_symmetric_detail" (lean := "LeanRidgelet.horosphericalWeight_zero, LeanRidgelet.fs_symmetric_reconstruction_of_inversion") (uses := "fs_scheme_detail, fs_symmetric_reconstruction")
*Reconstruction on a symmetric space, conditional on inversion.* The rank-$`r` instance of the abstract theorem, with the Helgason--Fourier inversion formula as an explicit hypothesis. Since the scale space is $`\mathbb R^r`, the Jacobian exponent is the rank rather than the dimension of the space, which is the one structural difference from the Euclidean case.
:::

Discharging the hypothesis in Euclidean *polar* coordinates would exhibit the same shape with $`r=1` and an honest direction space, and so keep the conditional theorem from being vacuous in a stronger sense than the one-point boundary already does. It is not here, and the obstacle is worth recording: the polar inversion formula needs $`\int_{\mathbb R}\int_{\mathbb S}|\lambda|^{m-1}G(\lambda u)=2\int_{\mathbb S}\int_0^\infty r^{m-1}G(ru)`, whose doubling step is invariance of the sphere measure under the antipodal map — a statement Mathlib does not have for `Measure.toSphere`. It is an upstream candidate in its own right, not an incidental step.

*`FS.DPlane`: the pooling case*

The case is large enough to have a directory of its own, `LeanRidgelet/FS/DPlane/`, split along the boundaries the article draws; `FS.DPlane` is the guide to it and carries the list of deviations. The paragraphs below follow those parts.

*`FS.DPlane.Defs`: what every codimension shares*

:::theorem "fs_dplane_detail" (lean := "LeanRidgelet.dPlaneCoord, LeanRidgelet.stiefelSynthesis, LeanRidgelet.fs_fourier_dPlaneTransform_fractional") (uses := "fs_scheme_detail, mathlib_dplane_transform")
*What the `d`-plane case rests on.* The transform and its Fourier slice theorem are in the upstream-candidates chapter, in general codimension; on top of them sits the identity that over the Stiefel manifold the coefficient function is the `d`-plane transform of a fractional derivative of the target.
:::

The two conventions do not agree on what a fractional derivative is: a multiplier $`\|\xi\|^s` in the Mathlib convention is $`(2\pi)^s\|\xi\|^s` in the angular one, so the codimension-one statements carry their own angular form of `fs_fourier_dPlaneTransform_fractional` rather than reusing it. The frequency $`\omega=0`, where the exponent arithmetic $`|\omega|^{d-t}|\omega|^t=|\omega|^d` fails, is null over $`\mathbb R` and the hypothesis is stated almost everywhere — the finite-field case is where that same point costs a rank-one defect instead.

*`FS.DPlane.CodimOne`: the sphere*

:::theorem "fs_dplane_codim_one_detail" (lean := "LeanRidgelet.sphereSynthesis, LeanRidgelet.sphereFourierExpression, LeanRidgelet.norm_smul_coe_sphere, LeanRidgelet.fs_matrixPolarIntegration_codim_one, LeanRidgelet.fs_sphere_fourierExpression_of_bias, LeanRidgelet.fs_sphere_reconstruction_of_inversion, LeanRidgelet.fs_angularFourier_slice_radonTransform, LeanRidgelet.fs_angularFourier_radonTransform_fractional, LeanRidgelet.fs_ae_ne_zero, LeanRidgelet.fs_stiefel_reconstruction_codim_one, LeanRidgelet.fs_radon_reconstruction_codim_one") (uses := "fs_dplane_detail, fs_euclidean_detail, mathlib_polar_coordinates, mathlib_stiefel_codim_one, fs_dplane_stiefel_codim_one, fs_radon_classical")
*Codimension one, where the Stiefel manifold is a sphere.* The layer over the sphere carries no scale parameter, so Step 2 is absent and Step 1 needs no Fubini: with nothing to rescale, the bias frequency may stay inside the direction integral. What is left is the master identity, whose hypothesis is that $`\gamma^\sharp(\boldsymbol u,\omega)\sigma^\sharp(\omega)` be a constant multiple of $`\widehat f(\omega\boldsymbol u)|\omega|^{m-1}` almost everywhere in $`\omega`, and whose proof is the two-sided polar formula followed by Fourier inversion. Everything the article's Appendix C needs at $`k=1` is `fs_matrixPolarIntegration_codim_one`, and the identification of the coefficient function with a Radon transform is the slice theorem in the angular convention.
:::

*`FS.DPlane.Stiefel`: general codimension, and the inversion formula*

The Stiefel case in general codimension is `fs_dplane_stiefel`, and it is the same three moves with the sphere replaced by the Stiefel manifold: the measure theory it rests on — a compact orthogonal group, an invariant measure on the Stiefel manifold, uniqueness of the rotation-invariant measure on the sphere, and the matrix polar integration formula — is all in the upstream-candidates chapter, none of it being in Mathlib. The article's own form of the theorem follows by specializing the auxiliary factor to `1`, the coefficient function being the `d`-plane transform of a fractional derivative; the fractional Laplacian enters only through its multiplier property in the *angular* convention, which is a different statement from the Mathlib-convention one because the rescaling of the frequency changes the multiplier by $`(2\pi)^s`.

Neither the Stiefel case nor the similitude case carries the article's standing absolute-convergence assumption. The two hypotheses of the matrix polar integration formula are discharged in the upstream-candidates chapter from strong measurability of the Fourier data — the unsigned form of the formula computes the integral of the norm, and almost every fibre of a finite integral is finite — so the master identities ask for measurability and the article's own form of `thm:stiefel` asks for nothing at all beyond integrability of the target and of its Fourier transform.

*`FS.DPlane.Similitude`: the scale that does not factor out*

The similitude case is `fs_dplane_similitude`. It is the one place where the scale genuinely interacts with the frequency — the two couple through $`y=ar`, so the network is not a scale mixture of Stiefel networks — and the interaction is handled by putting the Fubini exchange into Step 1, where the article puts it, after which the assembly needs polar coordinates in the frequency, a one-dimensional substitution, and the direction average, and no further exchange.

*`FS.DPlane.Affine`: all full-column-rank matrices*

The full-column-rank case is `fs_dplane_affine`, formalized in the singular value coordinates $`A=UDV^\top` because the Jacobian $`\mathrm dA=\delta(D)\,\mathrm dD\,\mathrm dU\,\mathrm dV` that converts them to Lebesgue measure on the matrix space — the article's Lemma C.3 — is not: its published proof goes through exterior differential forms, and Mathlib has singular *values* but not the decomposition, nor the Jacobian of the matrix polar decomposition, nor Weyl's integration formula for real symmetric matrices. The weight is therefore a parameter of the layer, which costs little: it enters the separation-of-variables condition only as a factor of the coefficient function, and the article's coefficient function carries its reciprocal, so the two cancel and the reconstruction formula holds for every weight. What the derivation needs instead is the rotation of the frequency by $`V` and the coordinatewise trade of the singular values against it, `mathlib_diagonal_scaling`, after which the matrix polar integration formula finishes exactly as in the Stiefel case. The fractional Laplacian as a Fourier multiplier is a further upstream candidate; where it is needed it enters as a multiplier hypothesis, never as a definition, and its multivariate form is what specializing the general-codimension identity to the article's `σ♯ = |ω|^t` family would need.

*`FS.DPlane.Consistency`: the two developments agree at codimension one*

That the two developments are the same construction is `fs_stiefelSynthesis_codimOne`: at $`k=1` the layer over the Stiefel manifold is the layer over the sphere, up to the total mass of the surface measure. Three identifications go into it, all of them in the upstream-candidates chapter — of the two parameter spaces, by `mathlib_stiefel_codim_one`; of the bias space $`\mathbb R^1` with $`\mathbb R`; and of the frame coordinate with the inner product against the unit vector, which is the transpose identity at $`k=1`.
