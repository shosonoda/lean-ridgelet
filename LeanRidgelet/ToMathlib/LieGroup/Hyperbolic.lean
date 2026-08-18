/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.BallModel
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.BoundaryMobius
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.HelgasonFourier
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.Mobius
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusInverse
public import LeanRidgelet.ToMathlib.LieGroup.Hyperbolic.MobiusMeasure

/-!
# Real hyperbolic space, the rank-one noncompact symmetric space

Import carrier for the Poincaré ball model of `ℍ^m = SO⁺(1,m)/O(m)` and its Helgason--Fourier
theory. The abstract layer that this model instantiates is
`LeanRidgelet.ToMathlib.LieGroup.Symmetric`.
-/
