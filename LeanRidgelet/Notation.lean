/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.Operator.ClassicalRidgelet
public import LeanRidgelet.Operator.ClassicalSynthesis

/-!
# Paper notation

Scoped notation aligning Lean statements with the manuscript.  Everything here is opt-in:

- `open LeanRidgelet.Paper` enables the space abbreviations `𝓐 s t`, `𝓗 m s t`, `𝓖 m s t`.
- `open scoped LeanRidgelet.Paper` enables the operator and transform notations
  `S[σ]`, `R[h]`, `R[f; ρ]`, `L[σ]`, `𝐓`, `𝐓⁻`, the paper Fourier transform `f♯`, and the
  Japanese brackets `⧼x⧽^r`, `⧼∂⧽^t`.

The notation layer never changes any declaration name: unfolding a notation always lands on the
established public API.  The paper Fourier transform `♯` is overloaded across the Schwartz
class, tempered distributions, and `L²(ℝ)` through the small notation class `PaperSharp`,
mirroring how Mathlib overloads `𝓕`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace LeanRidgelet

/-- Overloading class for the paper-normalized Fourier transform `f♯`. -/
class PaperSharp (α : Type*) (β : outParam Type*) where
  /-- The paper-normalized Fourier transform `f♯(ω) = ∫ z, exp (-i z ω) f(z) dz`. -/
  sharp : α → β

instance : PaperSharp (SchwartzMap ℝ ℂ) (SchwartzMap ℝ ℂ) :=
  ⟨Fourier.paperFourierSchwartz⟩

instance : PaperSharp (TemperedDistribution ℝ ℂ) (TemperedDistribution ℝ ℂ) :=
  ⟨Fourier.paperFourierDistribution⟩

instance : PaperSharp (L2 ℝ volume) (L2 ℝ volume) :=
  ⟨Fourier.paperFourierLp⟩

namespace Paper

/-- Paper notation for the activation space `A_{s,t}` in its `L²` coordinate model. -/
abbrev 𝓐 (s t : ℝ) := ActivationSpace s t

/-- Paper notation for the coefficient (fiber) Hilbert space `H_{s,t}`. -/
abbrev 𝓗 (m : ℕ) [NeZero m] (s t : ℝ) := FiberSpace m s t

/-- Paper notation for the parameter Hilbert space `G_{s,t}` in its transported model. -/
abbrev 𝓖 (m : ℕ) [NeZero m] (s t : ℝ) := ParameterSpace m s t

@[inherit_doc PaperSharp.sharp]
scoped postfix:max "♯" => PaperSharp.sharp

theorem sharp_schwartz_def (f : SchwartzMap ℝ ℂ) :
    f♯ = Fourier.paperFourierSchwartz f := rfl

theorem sharp_temperedDistribution_def (u : TemperedDistribution ℝ ℂ) :
    u♯ = Fourier.paperFourierDistribution u := rfl

theorem sharp_L2_def (f : L2 ℝ volume) : f♯ = Fourier.paperFourierLp f := rfl

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

example (h : SchwartzMap ℝ ℂ) : (⧼∂⧽^t) h = schwartzBesselPotential t h := rfl

end Examples

end Paper

end LeanRidgelet
