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
   `permittedAxioms`. The only exceptions are the explicitly named unfinished overview results in
   `permittedSorryDeclarations`; all other uses of `sorryAx` and all project axioms are rejected.
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

/-- Named L2 and L1 overview statements whose proofs remain to be formalized.

Built by folding `NameSet.insert` over a flat list so that adding or removing an entry is a
single-line edit with no parenthesis bookkeeping. -/
private def permittedSorryDeclarations : NameSet :=
  List.foldl NameSet.insert ∅
    [``LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout,
     ``LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation,
     ``LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements,
     ``LeanRidgelet.l2_proposition_two_exact_finite_null_relations,
     ``LeanRidgelet.l1_balancing_weakRidgeletTransform_memLp,
     ``LeanRidgelet.l1_ridgeletTransform_bounded_L1_Linfty,
     ``LeanRidgelet.l1_structure_theorem_admissible_pairs,
     ``LeanRidgelet.l1_construction_of_admissible_pairs,
     ``LeanRidgelet.l1_reconstruction_formula,
     ``LeanRidgelet.l1_reconstruction_formula_radon,
     ``LeanRidgelet.l1_parseval_relation,
     ``LeanRidgelet.l1_plancherel_identity,
     ``LeanRidgelet.l1_ridgeletTransform_L2_extension,
     ``LeanRidgelet.l1_reconstruction_formula_L2,
     ``LeanRidgelet.l1_truncatedPower_admissible,
     ``LeanRidgelet.l1_relu_network_universal_approximation]

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
      unless permittedAxioms.contains axiomName ||
          (axiomName == ``sorryAx && permittedSorryDeclarations.contains name) do
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
assert_no_sorry LeanRidgelet.Fourier.paperFourierDistribution_paperFourierInvDistribution
assert_no_sorry LeanRidgelet.Fourier.paperFourierDistribution_toTemperedDistributionCLM_eq
assert_no_sorry LeanRidgelet.fourierDilationTransformCore_norm_sq
assert_no_sorry LeanRidgelet.continuous_fourierDilationTransformCore
assert_no_sorry LeanRidgelet.fiberDistribution_coe
assert_no_sorry LeanRidgelet.fiberBaseCoordinate_coe
assert_no_sorry LeanRidgelet.paperFourierDistribution_ridgeletFunctionCore
assert_no_sorry LeanRidgelet.ridgeletSpectrum_coe
assert_no_sorry LeanRidgelet.ridgeletFunction_coe
assert_no_sorry LeanRidgelet.paperFourierDistribution_ridgeletFunction
assert_no_sorry LeanRidgelet.unitarySynthesis_comp_unitaryRidgelet
assert_no_sorry LeanRidgelet.unitaryMoorePenroseInverse_rightInverse
assert_no_sorry LeanRidgelet.hasSum_unitaryRidgelet_coefficients
assert_no_sorry LeanRidgelet.hasSum_unitaryRidgelet_kernelBasis
assert_no_sorry LeanRidgelet.hasSum_fiberRidgelet_coefficients
assert_no_sorry LeanRidgelet.eq_fiberCoefficient_of_hasSum_fiberRidgelet
assert_no_sorry LeanRidgelet.mem_fourierDilationCompatibilityDomain_iff_memLp
assert_no_sorry LeanRidgelet.networkSynthesis_parameterSchwartzRealization_fourierPairing_ae
assert_no_sorry LeanRidgelet.fourierDilationTransform_ridgeletOperator_apply_ae
assert_no_sorry LeanRidgelet.mem_ker_networkSynthesis_iff_fourierDilation
assert_no_sorry LeanRidgelet.normalizedGaussianRightInverse_rightInverse
assert_no_sorry LeanRidgelet.l2_proposition_one_activation_hilbert_structure
assert_no_sorry LeanRidgelet.l2_theorem_one_bounded_synthesis
assert_no_sorry LeanRidgelet.l2_lemma_one_ridgelet_fiber_representation
assert_no_sorry LeanRidgelet.l2_theorem_two_reconstruction
assert_no_sorry LeanRidgelet.l2_lemma_two_adjoint
assert_no_sorry LeanRidgelet.l2_theorem_three_null_space_and_general_solution
assert_no_sorry LeanRidgelet.l1_ridgelet_pointwise_convergent_L1_bounded
assert_no_sorry LeanRidgelet.l1_hasFourierAwayFromOrigin_add_polynomial
assert_no_sorry LeanRidgelet.integral_pow_mul_paperFourier1D_eq_zero
assert_no_sorry LeanRidgelet.l1_truncatedPower_hasFourierAwayFromOrigin
assert_no_sorry LeanRidgelet.truncatedPowerFourier_pairing
assert_no_sorry LeanRidgelet.l1_dualRidgeletTransform_pairing
assert_no_sorry LeanRidgelet.l1_weakRidgeletTransform_eq_euclidean

#print axioms LeanRidgelet.Fourier.paper_plancherel_schwartz_inner
#print axioms LeanRidgelet.fourierDilationTransformCore_norm_sq
#print axioms LeanRidgelet.hasSum_fiberRidgelet_coefficients
#print axioms LeanRidgelet.eq_fiberCoefficient_of_hasSum_fiberRidgelet
#print axioms LeanRidgelet.normalizedGaussianRightInverse_rightInverse
#print axioms LeanRidgelet.l2_theorem_three_null_space_and_general_solution
#print axioms LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout
#print axioms LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation
#print axioms LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements
#print axioms LeanRidgelet.l2_proposition_two_exact_finite_null_relations

end LeanRidgelet.Audit
