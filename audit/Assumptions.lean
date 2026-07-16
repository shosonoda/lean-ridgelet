/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/

import LeanRidgelet
import Mathlib.Util.AssertNoSorry

/-!
# Assumption audit

This file checks every declaration in the `LeanRidgelet` namespace, not only a selected final
theorem. It enforces two repository policies:

1. A declaration may transitively depend only on Lean's standard classical axioms listed in
   `permittedAxioms`. In particular, project axioms and `sorryAx` are rejected.
2. A project-defined structure or class may not have a proposition-valued field unless that field
   has been reviewed and added to `permittedProofFields`.

The second check is deliberately conservative. It prevents analytic results from being moved into
an assumptions structure or typeclass where `#print axioms` would not identify them as axioms.
Run this file through `scripts/audit-assumptions.sh`; do not import it from the library.
-/

open Lean Meta Elab Command

namespace LeanRidgelet.Audit

/-- Kernel axioms routinely permitted by Mathlib's classical development. -/
private def permittedAxioms : NameSet :=
  ((({} : NameSet).insert ``propext).insert ``Quot.sound).insert ``Classical.choice

/-- Reviewed proposition-valued fields of project-defined structures and classes.

Keep this empty unless a proof field is mathematically part of a genuine data structure rather
than a device for hiding an unfinished theorem. Every addition requires manual review. -/
private def permittedProofFields : NameSet := {}

private def isProjectModule (name : Name) : Bool :=
  name.toString.startsWith "LeanRidgelet"

/-- Audit transitive axioms and proposition-valued fields of project declarations. -/
elab "audit_ridgelet_assumptions" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for importedModule in env.header.modules, data in env.header.moduleData do
    if isProjectModule importedModule.module then
      names := names ++ data.constNames
  let mut unexpectedAxioms : Array (Name × Name) := #[]
  for name in names do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless permittedAxioms.contains axiomName do
        unexpectedAxioms := unexpectedAxioms.push (name, axiomName)
  unless unexpectedAxioms.isEmpty do
    let details := String.intercalate "\n" <| unexpectedAxioms.toList.map fun (name, axiomName) =>
      s!"  {name}: {axiomName}"
    throwError m!"Unexpected axioms in LeanRidgelet declarations:\n{details}"
  let mut unexpectedProofFields : Array (Name × Name) := #[]
  for name in names do
    if let some info := getStructureInfo? env name then
      for fieldName in info.fieldNames do
        if let some fieldInfo := env.find? fieldName then
          let isProofField ← liftTermElabM <|
            forallTelescopeReducing fieldInfo.type fun _ resultType => isProp resultType
          if isProofField && !permittedProofFields.contains fieldName then
            unexpectedProofFields := unexpectedProofFields.push (name, fieldName)
  unless unexpectedProofFields.isEmpty do
    let details := String.intercalate "\n" <|
      unexpectedProofFields.toList.map fun (name, fieldName) => s!"  {name}.{fieldName}"
    throwError m!"Unreviewed proposition-valued structure/class fields:\n{details}"
  logInfo m!"Assumption audit passed for {names.size} LeanRidgelet declarations."

audit_ridgelet_assumptions

-- Representative public endpoints remain visible in the audit log.
assert_no_sorry LeanRidgelet.Fourier.paper_plancherel_schwartz_inner
assert_no_sorry LeanRidgelet.fourierDilationTransformCore_norm_sq
assert_no_sorry LeanRidgelet.hasSum_fiberRidgelet_coefficients
assert_no_sorry LeanRidgelet.eq_fiberCoefficient_of_hasSum_fiberRidgelet
assert_no_sorry LeanRidgelet.normalizedGaussianRightInverse_rightInverse

#print axioms LeanRidgelet.Fourier.paper_plancherel_schwartz_inner
#print axioms LeanRidgelet.fourierDilationTransformCore_norm_sq
#print axioms LeanRidgelet.hasSum_fiberRidgelet_coefficients
#print axioms LeanRidgelet.eq_fiberCoefficient_of_hasSum_fiberRidgelet
#print axioms LeanRidgelet.normalizedGaussianRightInverse_rightInverse

end LeanRidgelet.Audit
