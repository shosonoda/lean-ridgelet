/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA

/-!
# Harmonic-analysis method: publication-order roadmap

Roadmap of the formalization of

> S. Sonoda, Y. Hashimoto, I. Ishikawa and M. Ikeda, *Deep Ridgelet Transform and Unified
> Universality Theorem for Deep and Shallow Joint-Group-Equivariant Machines*
> (arXiv:2405.13682).

The discovery principle is the short chain

`joint equivariance → intertwining maps → a commutant element → Schur scalarity → reconstruction`.

This file follows the article in publication order. The implementation modules are re-exported
through `LeanRidgelet.HA`, whose module documentation records their Lean dependency order.

## Sections 2 and 3: classical motivation and the abstract theorem

* Definitions 2.1 and 2.2 are represented by the affine ridge argument, its contragredient
  parameter action, and the corresponding Bochner synthesis and ridgelet formulas. Theorem 2.3 is
  identified with the classical declarations at homogeneity index zero: the affine Bochner pair is
  the Euclidean dual ridgelet transform and ridgelet transform of the L1 track, the classical
  synthesis integral of the L2 track is the same Bochner integral, and a Euclidean reconstruction
  identity reconstructs the composite with the same scalar. That identity is a hypothesis, as on
  the Fourier-slice side, because the L1 endpoints are truncated limits at index one.
* Theorem 2.4 is complete in `ToMathlib.LieGroup.Schur`. It proves the infinite-dimensional
  unitary Schur lemma and its converse using closed invariant subspaces and continuous functional
  calculus.
* For Theorem 2.5, the affine action, its Plancherel conjugate, the conull nonzero dual orbit, the
  inducing subgroup and character, the homogeneous-space `L²` model, the normalized-section
  induced model, its translation-character restriction, and its canonical indicator covariance
  are implemented. The spectral-projection criterion from Folland Theorem 4.44 is complete,
  including finite-measure density of Fourier characters. The operator-theoretic remainder of
  Theorem 6.28 is also proved using continuous spectral subspaces and the self-adjoint/skew-adjoint
  decomposition. Compact-kernel group-convolution continuity, pointwise representatives of
  `L²`-valued Bochner integrals, the approximate identity, compact cutoffs, and regular-section
  density required by Lemma 6.29 are proved. The extreme-subspace part of the inducing-fiber
  correspondence of Lemma 6.30 is now proved as well, from identity-coset evaluation of translated
  sections and from orthogonal-complement vanishing along a countable subcover of translates of a
  nonvanishing section. Lemma 6.29 is complete: the measurable induced-model lift, the slice
  integrability of its smoothing integrand, and the identification of the resulting pointwise
  convolution with the Bochner-smoothed class are proved, so Theorem 6.39 needs no analytic input.
  The one-dimensional fiber classification is proved. The induced-model and physical-space
  irreducibility theorems are unconditional.
* Definitions 3.1 and 3.2, Remark 3.3, and Lemmas 3.4 and 3.5 are implemented by the invariant or
  strongly quasi-invariant `L²` constructions and the pointwise joint-equivariance algebra.
* Definitions 3.6 and 3.8 and Lemmas 3.7 and 3.9 are implemented by the Bochner
  change-of-variables results and continuous intertwining maps. The implementation covers both
  individually bounded operators and the article's weaker bounded-extension hypothesis for the
  composite alone.
* Theorem 3.10 and Remark 3.11 are implemented as the Schur reduction and the normalized right
  inverse.

## Sections 4--8: examples and discussion

* Corollary 4.1 is proved for heterogeneous finite cascades.
* Section 5 feature covariance, the vector-valued product-group `L²` action, the standard
  complexified `O(m)` output representation, and the finite-output form of Lemma 5.1 are proved.
* The orbit-lift construction and Theorem 6.1 for group-convolutional networks are proved.
* The Section 7 quadratic-form example is implemented as far as its algebra goes: the symmetric
  coefficients as a subspace of the self-adjoint continuous endomorphisms, the linear parameter
  action of the affine group, joint invariance of the scalar argument and hence of the feature for
  every activation, the group-action law, and the block factorization of the parameter
  determinant. The quasi-invariant parameter measure and the resulting `L²` representation of the
  affine group on quadratic parameters are proved as well; the synthesis and ridgelet pair for
  this parameter space remains. Section 8 contains no additional formal target.

The Euclidean bounded synthesis and ridgelet maps used by the examples are reused from the L2
theory through `HA.L2Bridge`; the HA development does not duplicate their boundedness proof.

## Appendices A--E

The `L²` unitarity needed from Appendix A is implemented, as are the finite-output case of its
tensor irreducibility step and the group-convolution reductions. Appendix B is covered by the
Section 2 affine instance. Appendix C's uniform approximation of an integral representation by
finite networks is proved in general form, for a Lipschitz Banach-valued integrand on a compact
metric parameter space, and specializes to bounded continuous functions on an arbitrary data
space. The Hilbert--Schmidt criterion of Appendix D is proved in general form as well: a
square-integrable kernel gives a bounded operator on `L²`. What remains of those appendices is
their instantiation at the parameter spaces the L2 bridge does not cover. The Mackey route
supplies most of the input needed
for Appendix E, and the Folland-6.29 measurable-lift step above completes it, so no proof root
remains there.

The Blueprint chapters `overview-ha`, `ha-representations`, `ha-affine`, and `ha-architectures`
remain development-only until the HA theory stabilizes. This overview contains no declaration or
proof placeholder of its own.

## Deviations from the article

The complex reconstruction scalar is treated as sesquilinear rather than bilinear. The article's
general Bochner lemmas use invariant measures, whereas its affine examples require quasi-invariant
Lebesgue measures; `HA.BochnerIntertwining` therefore also states the corrected identities with
explicit pushforward densities and their square-root balance. `HA.Affine` derives the concrete
factors `‖det L‖₊` and `‖det L‖₊⁻¹` and instantiates that balance. For the quadratic feature the
corresponding determinant is kept abstract: only its non-vanishing is used, so the explicit
congruence determinant on symmetric coefficients is not computed. Individually bounded
synthesis/ridgelet maps and a bounded extension of their pointwise composite are exposed as
separate APIs, matching the two possible readings of the article's boundedness hypothesis.
-/
