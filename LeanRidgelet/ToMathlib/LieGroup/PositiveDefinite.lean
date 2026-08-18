/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.Boundary
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.CFunction
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.Cholesky
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.CornerDet
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.HelgasonFourier
public import LeanRidgelet.ToMathlib.LieGroup.PositiveDefinite.SpdModel

/-!
# The manifold of positive definite matrices, a higher-rank symmetric space

Import carrier for `ℙ_m = GL(m,ℝ)/O(m)` and its Helgason--Fourier theory. Its Iwasawa
decomposition is the Cholesky decomposition, which Mathlib already has as `LDL.lower_conj_diag`.
The abstract layer that this model instantiates is
`LeanRidgelet.ToMathlib.LieGroup.Symmetric`.
-/
