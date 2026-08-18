/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, OpenAI Codex
-/
module

public import LeanRidgelet.HA.Deep
public import LeanRidgelet.Operator.Ridgelet

/-!
# Reusing the L2 operator theory in the harmonic-analysis method

The Euclidean L2 development already constructs `networkSynthesis` and `ridgeletOperator` as
continuous linear maps and proves their exact composite. This file is the narrow bridge requested
by the architecture examples of arXiv:2405.13682: once their covariance under chosen data and
parameter representations is proved, the existing bounded maps are bundled as HA intertwiners.

No Bochner boundedness theorem is duplicated here. In particular, the synthesis estimate and the
scalar reconstruction identity below are exactly the L2 theorems.

## Deviations from the article

The bridge uses the transported L2 parameter-coordinate model. Equality with a classical
parameter-space Bochner integral belongs to the existing classical-realization compatibility
domain and is not asserted for arbitrary L2 equivalence classes.
-/

@[expose] public section

noncomputable section

open scoped ContRepresentation

namespace LeanRidgelet

variable {G : Type*} [Monoid G]

/-- Bundle the already bounded L2 synthesis operator as a joint-equivariant machine. -/
def l2NetworkSynthesisMachine (m : ℕ) [NeZero m] (s t : ℝ)
    (πParameter : ContRepresentation ℂ G (ParameterSpace m s t))
    (πData : ContRepresentation ℂ G (TargetSpace m)) (σ : ActivationSpace s t)
    (hintertwines : ∀ g γ,
      networkSynthesis m s t σ (πParameter g γ) =
        πData g (networkSynthesis m s t σ γ)) :
    JointEquivariantMachine πParameter πData where
  __ := networkSynthesis m s t σ
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro γ
    exact hintertwines g γ

/-- Bundle an already bounded L2 ridgelet operator as the reverse intertwiner. -/
def l2RidgeletIntertwiningMap (m : ℕ) [NeZero m] (s t : ℝ)
    (πParameter : ContRepresentation ℂ G (ParameterSpace m s t))
    (πData : ContRepresentation ℂ G (TargetSpace m)) (h : FiberSpace m s t)
    (hintertwines : ∀ g f,
      ridgeletOperator m s t h (πData g f) =
        πParameter g (ridgeletOperator m s t h f)) :
    JointEquivariantRidgelet πData πParameter where
  __ := ridgeletOperator m s t h
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro f
    exact hintertwines g f

/-- The HA machine retains the concrete L2 synthesis norm bound. -/
theorem norm_l2NetworkSynthesisMachine_le (m : ℕ) [NeZero m] (s t : ℝ)
    (πParameter : ContRepresentation ℂ G (ParameterSpace m s t))
    (πData : ContRepresentation ℂ G (TargetSpace m)) (σ : ActivationSpace s t)
    (hintertwines : ∀ g γ,
      networkSynthesis m s t σ (πParameter g γ) =
        πData g (networkSynthesis m s t σ γ)) :
    ‖(l2NetworkSynthesisMachine m s t πParameter πData σ hintertwines).toContinuousLinearMap‖ ≤
      (2 * Real.pi) ^ (m - 1) * ‖σ‖ :=
  norm_networkSynthesis_le m s t σ

/-- The HA composite of the L2 bounded operators is the L2 scalar reconstruction identity. -/
theorem l2_jointReconstructionOperator_eq (m : ℕ) [NeZero m] (s t : ℝ)
    (πParameter : ContRepresentation ℂ G (ParameterSpace m s t))
    (πData : ContRepresentation ℂ G (TargetSpace m)) (σ : ActivationSpace s t)
    (h : FiberSpace m s t)
    (hM : ∀ g γ,
      networkSynthesis m s t σ (πParameter g γ) =
        πData g (networkSynthesis m s t σ γ))
    (hR : ∀ g f,
      ridgeletOperator m s t h (πData g f) =
        πParameter g (ridgeletOperator m s t h f)) :
    jointReconstructionOperator
        (l2NetworkSynthesisMachine m s t πParameter πData σ hM)
        (l2RidgeletIntertwiningMap m s t πParameter πData h hR) =
      activationFiberFunctional m s t σ h •
        ContinuousLinearMap.id ℂ (TargetSpace m) := by
  apply ContinuousLinearMap.ext
  intro f
  have hf := congr($(networkSynthesis_comp_ridgeletOperator m s t σ h) f)
  exact hf

end LeanRidgelet
