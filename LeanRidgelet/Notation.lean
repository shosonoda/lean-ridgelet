/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.L1.Defs
public import LeanRidgelet.Operator.ClassicalRidgelet
public import LeanRidgelet.Operator.ClassicalSynthesis

/-!
# Manuscript notation

Scoped notation aligning Lean statements with the manuscript.  Everything here is opt-in:

- `open LeanRidgelet.Notation` enables the space abbreviations `𝓐 s t`, `𝓗 m s t`, `𝓖 m s t`
  of the L2 theory and `𝕐 m` for the L1 parameter space.
- `open scoped LeanRidgelet.Notation` enables the operator and transform notations. For the L2
  theory: `S[σ]`, `R[h]`, `R[f; ρ]`, `L[σ]`, `𝐓`, `𝐓⁻`, the angular Fourier transform `f♯`,
  and the Japanese brackets `⧼x⧽^r`, `⧼∂⧽^t`. For the L1 theory: `𝓡[s; ψ]`, `𝓡†[s; η]`,
  `K[m; ψ, Fη]` and `Λ^m`.

The notation layer never changes any declaration name: unfolding a notation always lands on the
established public API. The angular Fourier transform `♯` is overloaded across plain functions
`ℝ → ℂ`, the Schwartz class, tempered distributions, and `L²(ℝ)` through the small notation
class `AngularSharp`, mirroring how Mathlib overloads `𝓕`; on plain functions it is the
article's `ψ̂` of the L1 theory.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- Overloading class for the angular-frequency Fourier transform `f♯`. -/
class AngularSharp (α : Type*) (β : outParam Type*) where
  /-- The angular-frequency Fourier transform `f♯(ω) = ∫ z, exp (-i z ω) f(z) dz`. -/
  sharp : α → β

instance : AngularSharp (ℝ → ℂ) (ℝ → ℂ) :=
  ⟨angularFourier1D⟩

instance : AngularSharp (SchwartzMap ℝ ℂ) (SchwartzMap ℝ ℂ) :=
  ⟨Fourier.angularFourierSchwartz⟩

instance : AngularSharp (TemperedDistribution ℝ ℂ) (TemperedDistribution ℝ ℂ) :=
  ⟨Fourier.angularFourierDistribution⟩

instance : AngularSharp (L2 ℝ volume) (L2 ℝ volume) :=
  ⟨Fourier.angularFourierLp⟩

namespace Notation

/-- Manuscript notation for the activation space `A_{s,t}` in its `L²` coordinate model. -/
abbrev 𝓐 (s t : ℝ) := ActivationSpace s t

/-- Manuscript notation for the coefficient (fiber) Hilbert space `H_{s,t}`. -/
abbrev 𝓗 (m : ℕ) [NeZero m] (s t : ℝ) := FiberSpace m s t

/-- Manuscript notation for the parameter Hilbert space `G_{s,t}` in its transported model. -/
abbrev 𝓖 (m : ℕ) [NeZero m] (s t : ℝ) := ParameterSpace m s t

/-- Article notation for the L1 parameter space `𝕐^{m+1}` in Euclidean coordinates. -/
abbrev 𝕐 (m : ℕ) := RidgeletParameterSpace m

@[inherit_doc AngularSharp.sharp]
scoped postfix:max "♯" => AngularSharp.sharp

theorem sharp_schwartz_def (f : SchwartzMap ℝ ℂ) :
    f♯ = Fourier.angularFourierSchwartz f := rfl

theorem sharp_temperedDistribution_def (u : TemperedDistribution ℝ ℂ) :
    u♯ = Fourier.angularFourierDistribution u := rfl

theorem sharp_L2_def (f : L2 ℝ volume) : f♯ = Fourier.angularFourierLp f := rfl

theorem sharp_fun_def (g : ℝ → ℂ) : g♯ = angularFourier1D g := rfl

@[inherit_doc networkSynthesis]
scoped notation "S[" σ "]" => networkSynthesis _ _ _ σ

@[inherit_doc ridgeletOperator]
scoped notation "R[" h "]" => ridgeletOperator _ _ _ h

@[inherit_doc classicalRidgeletIntegral]
scoped notation "R[" f "; " ρ "]" => classicalRidgeletIntegral f ρ

@[inherit_doc activationFiberFunctional]
scoped notation "L[" σ "]" => activationFiberFunctional _ _ _ σ

@[inherit_doc fourierDilationTransform]
scoped notation "𝐓" => fourierDilationTransform _ _ _

@[inherit_doc inverseFourierDilationTransform]
scoped notation "𝐓⁻" => inverseFourierDilationTransform _ _ _

@[inherit_doc euclideanRidgeletTransform]
scoped notation "𝓡[" s "; " ψ "]" => euclideanRidgeletTransform _ s ψ

@[inherit_doc euclideanDualRidgeletTransform]
scoped notation "𝓡†[" s "; " η "]" => euclideanDualRidgeletTransform _ s η

@[inherit_doc admissibilityConstant]
scoped notation "K[" m "; " ψ ", " Fη "]" => admissibilityConstant m ψ Fη

@[inherit_doc lambdaOperatorPow]
scoped notation:max "Λ^" m:max => lambdaOperatorPow m

@[inherit_doc japaneseBracketPow]
scoped notation:max "⧼" x "⧽^" r:max => japaneseBracketPow r x

@[inherit_doc schwartzBesselPotential]
scoped notation:max "⧼∂⧽^" t:max => schwartzBesselPotential t

/-! Smoke tests: the notations elaborate against the intended declarations, with the implicit
index triple recovered from the argument types. -/

section Examples

variable {m : ℕ} [NeZero m] {s t : ℝ}

example (σ : 𝓐 s t) (γ : 𝓖 m s t) : TargetSpace m := S[σ] γ

example (h : 𝓗 m s t) (f : TargetSpace m) : 𝓖 m s t := R[h] f

example (σ : 𝓐 s t) (h : 𝓗 m s t) : ℂ := L[σ] h

example (γ : 𝓖 m s t) : BochnerL2 (InputSpace m) (FiberSpace m s t) volume := 𝐓 γ

example (u : BochnerL2 (InputSpace m) (FiberSpace m s t) volume) : 𝓖 m s t := 𝐓⁻ u

example (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := f♯

example (f : SchwartzMap (InputSpace m) ℂ) (ρ : ℝ → ℂ) (p : InputSpace m × ℝ) : ℂ :=
  R[(f : InputSpace m → ℂ); ρ] p

example (r x : ℝ) : ⧼x⧽^r = japaneseBracketPow r x := rfl

example (g : ℝ → ℂ) (ζ : ℝ) : g♯ ζ = angularFourier1D g ζ := rfl

example (s : ℝ) (ψ : ℝ → ℂ) (f : InputSpace 1 → ℂ) (p : 𝕐 1) : ℂ := 𝓡[s; ψ] f p

example (s : ℝ) (η : ℝ → ℂ) (T : 𝕐 1 → ℂ) (x : InputSpace 1) : ℂ := 𝓡†[s; η] T x

example (m : ℕ) (ψ Fη : ℝ → ℂ) : ℂ := K[m; ψ, Fη]

example (m : ℕ) (g : ℝ → ℂ) : ℝ → ℂ := Λ^m g

example (h : SchwartzMap ℝ ℂ) : (⧼∂⧽^t) h = schwartzBesselPotential t h := rfl

end Examples

end Notation

end LeanRidgelet
