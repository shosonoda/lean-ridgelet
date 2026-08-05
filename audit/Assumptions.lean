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

/-- Named L2 overview statements whose proofs remain to be formalized. The L1 theory is
complete: since 2026-08-05 it contains no placeholder.

Built by folding `NameSet.insert` over a flat list so that adding or removing an entry is a
single-line edit with no parenthesis bookkeeping. -/
private def permittedSorryDeclarations : NameSet :=
  List.foldl NameSet.insert ∅
    [``LeanRidgelet.l2_theorem_four_encoding_and_perturbative_readout,
     ``LeanRidgelet.l2_theorem_five_normalized_finite_width_approximation,
     ``LeanRidgelet.l2_corollary_one_discretizable_ridgelet_null_elements,
     ``LeanRidgelet.l2_proposition_two_exact_finite_null_relations]

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
assert_no_sorry LeanRidgelet.Fourier.angular_plancherel_schwartz_inner
assert_no_sorry LeanRidgelet.Fourier.angularFourierDistribution_angularFourierInvDistribution
assert_no_sorry LeanRidgelet.Fourier.angularFourierDistribution_toTemperedDistributionCLM_eq
assert_no_sorry LeanRidgelet.fourierDilationTransformCore_norm_sq
assert_no_sorry LeanRidgelet.continuous_fourierDilationTransformCore
assert_no_sorry LeanRidgelet.fiberDistribution_coe
assert_no_sorry LeanRidgelet.fiberBaseCoordinate_coe
assert_no_sorry LeanRidgelet.angularFourierDistribution_ridgeletFunctionCore
assert_no_sorry LeanRidgelet.ridgeletSpectrum_coe
assert_no_sorry LeanRidgelet.ridgeletFunction_coe
assert_no_sorry LeanRidgelet.angularFourierDistribution_ridgeletFunction
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
assert_no_sorry LeanRidgelet.integral_pow_mul_angularFourier1D_eq_zero
assert_no_sorry LeanRidgelet.l1_truncatedPower_hasFourierAwayFromOrigin
assert_no_sorry LeanRidgelet.truncatedPowerFourier_pairing
assert_no_sorry LeanRidgelet.l1_dualRidgeletTransform_pairing
assert_no_sorry LeanRidgelet.l1_weakRidgeletTransform_eq_euclidean
assert_no_sorry LeanRidgelet.l1_plancherel_identity
assert_no_sorry LeanRidgelet.l1_ridgeletTransform_L2_extension
assert_no_sorry MeasureTheory.Lp.dense_setOf_integrable
assert_no_sorry MeasureTheory.tendsto_integral_mul_smoothing_of_vanishing_moments
assert_no_sorry MeasureTheory.tendsto_integral_weight_norm_sub_comp_sub_right
assert_no_sorry MeasureTheory.tendsto_integral_weight_norm_smoothing_sub
assert_no_sorry LeanRidgelet.hasFourierAwayFromOrigin_pairing_extension
assert_no_sorry LeanRidgelet.truncatedDualRidgeletTransform_eq_section_pairing
assert_no_sorry LeanRidgelet.integrable_weight_truncatedReconstructionSection
assert_no_sorry LeanRidgelet.integral_pow_mul_truncatedReconstructionSection_eq_zero
assert_no_sorry LeanRidgelet.angularFourier1D_truncatedReconstructionSection
assert_no_sorry LeanRidgelet.norm_truncatedSpectralFactor_le_of_ne
assert_no_sorry LeanRidgelet.truncatedSpectralWindow_eq
assert_no_sorry LeanRidgelet.integrableOn_fourierData_truncatedReconstructionSection
assert_no_sorry LeanRidgelet.truncatedDualRidgeletTransform_eq_spectral_pairing
assert_no_sorry LeanRidgelet.tendsto_truncatedDualRidgeletTransform
assert_no_sorry LeanRidgelet.ae_integral_angularFourier_mul_exp
assert_no_sorry LeanRidgelet.l1_reconstruction_formula
assert_no_sorry LeanRidgelet.l1_reconstruction_formula_radon
assert_no_sorry LeanRidgelet.l1_parseval_relation
assert_no_sorry MeasureTheory.Integrable.integral_inner_fourier
assert_no_sorry MeasureTheory.MemLp.integrable_mul_conj
assert_no_sorry LeanRidgelet.Fourier.integral_angularFourierIntegralInner_mul_conj
assert_no_sorry LeanRidgelet.Fourier.integral_angularFourierIntegralInner_mul_exp
assert_no_sorry MeasureTheory.Integrable.fourierInv_fourier_ae_eq
assert_no_sorry MeasureTheory.measurePreserving_prodSwapRight
assert_no_sorry MeasureTheory.quasiMeasurePreserving_skewSubLeft
assert_no_sorry LeanRidgelet.l1_reconstruction_formula_L2
assert_no_sorry LeanRidgelet.eLpNorm_truncatedDualRidgeletTransform_sub_le
assert_no_sorry LeanRidgelet.setIntegral_annulus_ridgeletTransform_mul_conj
assert_no_sorry LeanRidgelet.tendsto_setIntegral_compl_annulus_norm_sq
assert_no_sorry LeanRidgelet.integrable_weight_indicator_euclideanRidgeletTransform
assert_no_sorry LeanRidgelet.integral_norm_euclideanRidgeletTransform_bias_le
assert_no_sorry LeanRidgelet.norm_truncatedDualRidgeletTransform_le
assert_no_sorry LeanRidgelet.aestronglyMeasurable_truncatedDualRidgeletTransform
assert_no_sorry MeasureTheory.eLpNorm_two_le_of_forall_indicator_pairing_le
assert_no_sorry MeasureTheory.MemLp.norm_integral_mul_conj_le
assert_no_sorry MeasureTheory.tendsto_intervalIntegral_sin_div_atTop
assert_no_sorry MeasureTheory.abs_intervalIntegral_sin_div_le
assert_no_sorry MeasureTheory.tendsto_intervalIntegral_sin_div_atTop_left
assert_no_sorry MeasureTheory.abs_sinDivTail_le
assert_no_sorry MeasureTheory.tendsto_sinDivTail_nhds_zero
assert_no_sorry MeasureTheory.intervalIntegral_sin_mul_div_eq
assert_no_sorry MeasureTheory.setIntegral_hilbert_eq_Ioi
assert_no_sorry MeasureTheory.intervalIntegral_hilbert_eq_fourier
assert_no_sorry MeasureTheory.setIntegral_hilbert_eq_fourier_tail
assert_no_sorry MeasureTheory.pvHilbertTransform_schwartz
assert_no_sorry MeasureTheory.pvHilbertTransform_schwartz_eq_fourierInv
assert_no_sorry LeanRidgelet.lambdaOperatorPow_eq_fourier_multiplier
assert_no_sorry LeanRidgelet.lambda_symbol_even
assert_no_sorry LeanRidgelet.lambda_symbol_odd
assert_no_sorry MeasureTheory.integral_eq_integral_prod_toSphere
assert_no_sorry MeasureTheory.integrable_prod_toSphere_of_integrable
assert_no_sorry MeasureTheory.integral_eq_integral_toSphere_integral_Ioi
assert_no_sorry MeasureTheory.schwartz_norm_le_one_add_norm_rpow
assert_no_sorry MeasureTheory.continuous_radonTransform_schwartz
assert_no_sorry MeasureTheory.radonTransform_eq_radonSchwartzSection
assert_no_sorry MeasureTheory.fourier_radonSchwartzSection
assert_no_sorry MeasureTheory.integral_volumeIoiPow
assert_no_sorry MeasureTheory.integrable_toSphere_integral_Ioi
assert_no_sorry LeanRidgelet.l1_radon_filtered_backprojection
assert_no_sorry LeanRidgelet.l1_relu_network_universal_approximation
assert_no_sorry LeanRidgelet.l1_truncatedPower_admissible_exists
assert_no_sorry LeanRidgelet.isAdmissiblePair_bumpRidgelet
assert_no_sorry LeanRidgelet.admissibilityConstant_bumpRidgelet_ne_zero
assert_no_sorry LeanRidgelet.integral_pow_mul_bumpRidgelet
assert_no_sorry LeanRidgelet.integrable_weight_bumpRidgelet
assert_no_sorry LeanRidgelet.angularFourier1D_bumpRidgelet
assert_no_sorry LeanRidgelet.hasFourierAwayFromOrigin_lambdaOperatorPow
assert_no_sorry mem_lizorkinSpace_iff_fourier_flat
assert_no_sorry Real.iteratedDeriv_fourier_zero
assert_no_sorry integral_polynomial_mul_eq_zero_of_mem_lizorkinSpace
assert_no_sorry LeanRidgelet.bumpRidgeletSchwartz_mem_lizorkinSpace
assert_no_sorry LeanRidgelet.lambdaOperatorPow_eq_angular
assert_no_sorry LeanRidgelet.l1_structure_theorem_admissible_pairs
assert_no_sorry LeanRidgelet.l1_construction_of_admissible_pairs
assert_no_sorry LeanRidgelet.l1_isAdmissiblePair_lambdaOperatorPow
assert_no_sorry LeanRidgelet.l1_truncatedPower_isAdmissiblePair_of_window
assert_no_sorry LeanRidgelet.integrable_lambdaOperatorPow_of_even
assert_no_sorry LeanRidgelet.integrable_lambdaOperatorPow
assert_no_sorry LeanRidgelet.l1_truncatedPower_admissible
assert_no_sorry LeanRidgelet.angularFourier1D_gaussianWindow
assert_no_sorry Real.gaussianSchwartz
assert_no_sorry Real.exists_polynomial_iteratedDeriv_gaussian
assert_no_sorry Real.abs_pow_mul_exp_neg_sq_div_two_le
assert_no_sorry LeanRidgelet.integral_iteratedDeriv_schwartz_eq_zero
assert_no_sorry MeasureTheory.integrableOn_schwartz_oddDiff
assert_no_sorry MeasureTheory.pvHilbertTransform_schwartz_eq_oddIntegral
assert_no_sorry MeasureTheory.coord_mul_pvHilbertTransform
assert_no_sorry MeasureTheory.memLp_two_pvHilbertTransform
assert_no_sorry MeasureTheory.integrable_pvHilbertTransform_of_integral_eq_zero
assert_no_sorry LeanRidgelet.l1_polynomial_not_isAdmissiblePair
assert_no_sorry LeanRidgelet.l1_step_not_isAdmissiblePair_lambdaOperatorPow
assert_no_sorry LeanRidgelet.hasFourierAwayFromOrigin_angularFourierInv
assert_no_sorry LeanRidgelet.angularFourier1D_lambdaOperatorPow
assert_no_sorry LeanRidgelet.l1_structure_theorem_sufficiency
assert_no_sorry LeanRidgelet.l1_structure_theorem_sufficiency_physical
assert_no_sorry LeanRidgelet.isAdmissiblePair_of_backprojection_ae
assert_no_sorry LeanRidgelet.hasFourierAwayFromOrigin_ae_eq
assert_no_sorry LeanRidgelet.hasFourierAwayFromOrigin_reflectedConjConvolution
assert_no_sorry LeanRidgelet.angularFourier1D_mul_conj_angularFourier1D
assert_no_sorry LeanRidgelet.integrable_abs_pow_mul_angularFourier1D
assert_no_sorry LeanRidgelet.coe_angularSchwartz

#print axioms LeanRidgelet.Fourier.angular_plancherel_schwartz_inner
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
