/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.CFunction
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Cocycle
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Defs
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.HorocycleRadon
public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Inversion

/-!
# Harmonic analysis on a noncompact symmetric space

Import carrier for the abstract layer of the Helgason--Fourier theory, which takes the geometry of
`X = G/K` — the composite distance, the constant `ϱ`, the invariant and boundary measures, and the
Harish-Chandra `c`-function — as data. The concrete models that supply that data live in
`LeanRidgelet.ToMathlib.LieGroup.Hyperbolic` (rank one) and
`LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite` (higher rank).
-/
