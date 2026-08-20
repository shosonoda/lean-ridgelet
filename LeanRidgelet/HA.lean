/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.JointEquivariance
public import LeanRidgelet.HA.InducedRepresentation
public import LeanRidgelet.HA.BochnerIntertwining
public import LeanRidgelet.HA.Operators
public import LeanRidgelet.HA.Reconstruction
public import LeanRidgelet.HA.AdjointReconstruction
public import LeanRidgelet.HA.BochnerAdjoint
public import LeanRidgelet.HA.Deep
public import LeanRidgelet.HA.L2Bridge
public import LeanRidgelet.HA.FullyConnected
public import LeanRidgelet.HA.FullyConnectedIrreducibility
public import LeanRidgelet.HA.GroupConvolution
public import LeanRidgelet.HA.Affine
public import LeanRidgelet.HA.ClassicalComparison
public import LeanRidgelet.HA.L2BridgeEquivariance
public import LeanRidgelet.HA.AffineIrreducibility
public import LeanRidgelet.HA.AffineFourier
public import LeanRidgelet.HA.AffineFrequency
public import LeanRidgelet.HA.AffineMackey
public import LeanRidgelet.HA.AffineGroupHaar
public import LeanRidgelet.HA.AffineMackeyLift
public import LeanRidgelet.HA.AffineMackeySmoothing
public import LeanRidgelet.HA.Quadratic
public import LeanRidgelet.HA.QuadraticMeasure
public import LeanRidgelet.HA.QuadraticRelativeMeasure
public import LeanRidgelet.HA.QuadraticBounded
public import LeanRidgelet.HA.QuadraticComposite
public import LeanRidgelet.HA.QuadraticTransfer
public import LeanRidgelet.HA.BochnerMeasurability
public import LeanRidgelet.HA.QuadraticFiniteWidth
public import LeanRidgelet.HA.QuadraticParameterFactor
public import LeanRidgelet.HA.QuadraticShear
public import LeanRidgelet.HA.SecondDifference
public import LeanRidgelet.HA.QuadraticSecondDifference
public import LeanRidgelet.HA.QuadraticWeighted
public import LeanRidgelet.HA.ParametricDerivMeasurable
public import LeanRidgelet.HA.QuadraticSobolevSpace
public import LeanRidgelet.HA.QuadraticSobolevCarrier
public import LeanRidgelet.HA.QuadraticSobolevFourier
public import LeanRidgelet.HA.QuadraticReconstruction
public import LeanRidgelet.HA.QuadraticNonzero

/-!
# Harmonic-analysis method: detail import carrier

This module re-exports the implementation of the harmonic-analysis/Schur method in Lean
dependency order. It intentionally contains no publication-order roadmap and no mathematical
declaration of its own. See `LeanRidgelet.OverviewHA` for the map from arXiv:2405.13682 to the
formalization.

The dependency layers are, with the sections of the article each one serves:

1. joint-equivariant maps and invariant or quasi-invariant `L²` representations (Section 3);
2. Bochner integral identities and bounded intertwining maps (Definitions 3.6--3.9);
3. the commutant/reconstruction argument and finite cascades (Theorem 3.10, Corollary 4.1);
4. the fully-connected and group-convolutional examples (Sections 5 and 6);
5. the affine Fourier, orbit, homogeneous-space, and Mackey models used for irreducibility
   (Theorem 2.5, Appendix E), and the comparison with the classical transforms (Theorem 2.3); and
6. the quadratic-form network (Section 7), in four sublayers: its algebra, its two parameter
   measures, its endpoint from bounded intertwiners, and the boundedness route of Appendix D --
   the two square-integrability conditions, the obstruction that closes them, and the intermediate
   coefficient space that replaces them.

General results independent of ridgelet transforms remain in `LeanRidgelet.ToMathlib` and
`LeanRidgelet.ToMathlib.LieGroup` rather than being re-exported individually here. That includes
results this track produced: the Hilbert--Schmidt kernel bound, the Haar factorization over a
product, the one-variable weighted Sobolev identity, the congruence determinant on symmetric
matrices, and the measurability of an iterated derivative in a parameter.
-/
