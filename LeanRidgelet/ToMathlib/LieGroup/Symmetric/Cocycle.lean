/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.ToMathlib.LieGroup.Symmetric.Defs

/-!
# The cocycle relation for the composite distance

This file is a Mathlib upstream candidate and has no dependencies on the rest of the
`LeanRidgelet` project.

On `X = G/K` the composite distance satisfies `A(g·x, g·b) = A(x,b) + A(g·o, g·b)`: moving a point
and a boundary normal by the same `g` translates the composite distance by a vector of `𝔞` that
depends on `g` and `b` but not on `x`. It is the Iwasawa cocycle identity, and it is the one
geometric input that makes the Helgason--Fourier transform transform like a Fourier transform
(S. Helgason, *Groups and Geometric Analysis*, Ch. II §1 No. 3 and Ch. III §1, and *Geometric
Analysis on Symmetric Spaces*, Ch. II §3 No. 4).

Mathlib has no Iwasawa decomposition, so `A` is data here, as in
`LeanRidgelet.ToMathlib.LieGroup.Symmetric.Defs`, and the identity is a predicate on that data:
`IsCompositeCocycle T S A shift` says that the pair of maps `(T, S)` — the action of a single
group element on `X` and on `B` — displaces `A` by `shift b`. Nothing refers to a group, and the
theorems below need only the predicate together with the invariance of the measure being
integrated against.

The consequence is a product formula. The character `e^{(iλ+ϱ)}` is multiplicative, so the additive
displacement of `A` becomes a multiplicative factor on the kernel: the Helgason--Fourier transform
at the moved boundary point is the transform of the moved function times the number
`e^{(-iλ+ϱ)(shift b)}`, whose modulus is `e^{ϱ(shift b)}` and does not depend on `λ`. When the
displacement vanishes — the element fixes the base point, `g ∈ K` — the factor is `1` and the
spherical function is invariant.

## Main definitions

* `SymmetricSpace.IsCompositeCocycle`: the transformation law `A(T x, S b) = A(x,b) + shift b` of
  the composite distance under a pair of maps.

## Main results

* `SymmetricSpace.isCompositeCocycle_id`: the identity pair displaces nothing.
* `SymmetricSpace.IsCompositeCocycle.comp`: the cocycle identity itself — composing two pairs adds
  the displacements after transporting the second one by the first boundary map.
* `SymmetricSpace.IsCompositeCocycle.helgasonFourier_apply`: the transformation law of the
  Helgason--Fourier transform, `f̂(λ, S b) = e^{(-iλ+ϱ)(shift b)} \widehat{f ∘ T}(λ, b)`.
* `SymmetricSpace.IsCompositeCocycle.norm_helgasonFourier_apply`: its modulus, where the factor is
  the real weight `e^{ϱ(shift b)}`.
* `SymmetricSpace.IsCompositeCocycle.sphericalFunction_apply`: the spherical function at a moved
  point, as the boundary integral of the character weighted by `e^{(iλ+ϱ)(shift b)}`.
* `SymmetricSpace.IsCompositeCocycle.sphericalFunction_apply_of_shift_eq_zero`: for a pair with
  vanishing displacement the spherical function is invariant.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SymmetricSpace

/-! ## The cocycle relation -/

section Cocycle

variable {E : Type*} [AddMonoid E] {X B : Type*}

/-- The transformation law of the composite distance under a pair of maps: `T` moves the points of
`X`, `S` moves the boundary normals of `B`, and `A` is displaced by a vector `shift b` of `𝔞` that
does not depend on the point.

On `X = G/K` this is the identity `⟨g·x, g·b⟩ = ⟨x,b⟩ + ⟨g·o, g·b⟩` for the composite distance,
with `T = (g · ·)` on `X`, `S = (g · ·)` on `B`, and `shift b = ⟨g·o, g·b⟩` the value at the base
point `o = eK` (Helgason, *Groups and Geometric Analysis*, Ch. II §1 No. 3). The displacement is
therefore not extra data in a concrete model: it is the composite distance of the moved base
point. -/
def IsCompositeCocycle (T : X → X) (S : B → B) (A : X → B → E) (shift : B → E) : Prop :=
  ∀ x b, A (T x) (S b) = A x b + shift b

/-- The identity pair of maps displaces the composite distance by nothing: the case `g = e`. -/
theorem isCompositeCocycle_id (A : X → B → E) :
    IsCompositeCocycle (id : X → X) (id : B → B) A 0 := by
  intro x b
  simp

/-- **The cocycle identity.** Composing two pairs of maps composes the cocycles: the displacement
of `(T₂ ∘ T₁, S₂ ∘ S₁)` is the displacement of the first pair plus the displacement of the second
pair *read at the boundary point already moved by the first*.

On `X = G/K` with `T_i = (g_i · ·)` this is the familiar
`⟨(g₂g₁)·o, (g₂g₁)·b⟩ = ⟨g₁·o, g₁·b⟩ + ⟨g₂·o, g₂·(g₁·b)⟩`, that is, the Iwasawa `A`-component is a
cocycle on `G × B` rather than a homomorphism. The transport by `S₁` is the whole content: without
it the displacement would be additive in the group element, which it is not. -/
theorem IsCompositeCocycle.comp {T₁ T₂ : X → X} {S₁ S₂ : B → B} {A : X → B → E}
    {shift₁ shift₂ : B → E} (hc₁ : IsCompositeCocycle T₁ S₁ A shift₁)
    (hc₂ : IsCompositeCocycle T₂ S₂ A shift₂) :
    IsCompositeCocycle (T₂ ∘ T₁) (S₂ ∘ S₁) A fun b => shift₁ b + shift₂ (S₁ b) := by
  intro x b
  simp only [Function.comp_apply]
  rw [hc₂ (T₁ x) (S₁ b), hc₁ x b, add_assoc]

end Cocycle

/-! ## The transformation law of the Helgason--Fourier transform -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]

omit [MeasurableSpace B] in
/-- **The transformation law of the Helgason--Fourier transform.** If `(T, S)` displaces the
composite distance by `shift` and `T` preserves the invariant measure, then

`f̂(λ, S b) = e^{(-iλ+ϱ)(shift b)} \cdot \widehat{f ∘ T}(λ, b)`.

This is the symmetric-space form of the elementary identity `\widehat{f(· - a)}(λ) = e^{-iλa}
f̂(λ)` of Euclidean Fourier analysis (Helgason, *Groups and Geometric Analysis*, Ch. III §1). Two
facts and nothing else go into it: the character is multiplicative, so the additive displacement of
`A` factors out of the kernel, and `T` preserves `μ`, so the change of variables is free. -/
theorem IsCompositeCocycle.helgasonFourier_apply {T : X → X} {S : B → B} {A : X → B → E}
    {shift : B → E} (hc : IsCompositeCocycle T S A shift) {μ : Measure X}
    (hT : MeasurePreserving T μ μ) (hTm : MeasurableEmbedding T) (rho : E) (f : X → ℂ) (lam : E)
    (b : B) :
    helgasonFourier μ A rho f lam (S b)
      = horosphericalCharacter rho (-lam) (shift b) * helgasonFourier μ A rho (f ∘ T) lam b := by
  have h : (∫ x : X, f (T x) * horosphericalCharacter rho (-lam) (A (T x) (S b)) ∂μ)
      = ∫ y : X, f y * horosphericalCharacter rho (-lam) (A y (S b)) ∂μ :=
    hT.integral_comp hTm fun y : X => f y * horosphericalCharacter rho (-lam) (A y (S b))
  simp only [helgasonFourier, Function.comp_apply]
  rw [← h]
  simp only [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hc x b, horosphericalCharacter_add]
  ring

omit [MeasurableSpace B] in
/-- The modulus of the transformation law: the factor is the real weight `e^{ϱ(shift b)}`, the
frequency contributing nothing. In particular the multiplier is bounded uniformly in `λ`, which is
what lets the transform be estimated on a whole `λ`-family at once. -/
theorem IsCompositeCocycle.norm_helgasonFourier_apply {T : X → X} {S : B → B} {A : X → B → E}
    {shift : B → E} (hc : IsCompositeCocycle T S A shift) {μ : Measure X}
    (hT : MeasurePreserving T μ μ) (hTm : MeasurableEmbedding T) (rho : E) (f : X → ℂ) (lam : E)
    (b : B) :
    ‖helgasonFourier μ A rho f lam (S b)‖
      = Real.exp (inner ℝ rho (shift b)) * ‖helgasonFourier μ A rho (f ∘ T) lam b‖ := by
  rw [hc.helgasonFourier_apply hT hTm rho f lam b, norm_mul, norm_horosphericalCharacter]

/-! ## The spherical function -/

omit [MeasurableSpace X] in
/-- The spherical function at a moved point. If `(T, S)` displaces the composite distance by
`shift` and `S` preserves the boundary measure, then `φ_λ(T x)` is the boundary integral of the
character at `x` weighted by `e^{(iλ+ϱ)(shift b)}`.

Only the weighted form is true in this generality: the displacement depends on `b`, so it does not
come out of the boundary integral, and `φ_λ(T x)` is genuinely a different integral from `φ_λ(x)`.
The invariance statement is
`SymmetricSpace.IsCompositeCocycle.sphericalFunction_apply_of_shift_eq_zero` below, under the
hypothesis that the displacement vanishes. -/
theorem IsCompositeCocycle.sphericalFunction_apply {T : X → X} {S : B → B} {A : X → B → E}
    {shift : B → E} (hc : IsCompositeCocycle T S A shift) {nu : Measure B}
    (hS : MeasurePreserving S nu nu) (hSm : MeasurableEmbedding S) (rho lam : E) (x : X) :
    sphericalFunction nu A rho lam (T x)
      = ∫ b : B, horosphericalCharacter rho lam (A x b) *
          horosphericalCharacter rho lam (shift b) ∂nu := by
  have h : (∫ b : B, horosphericalCharacter rho lam (A (T x) (S b)) ∂nu)
      = ∫ b : B, horosphericalCharacter rho lam (A (T x) b) ∂nu :=
    hS.integral_comp hSm fun b : B => horosphericalCharacter rho lam (A (T x) b)
  rw [sphericalFunction, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [hc x b, horosphericalCharacter_add]

omit [MeasurableSpace X] in
/-- The spherical function is invariant under a pair of maps with vanishing displacement.

The hypothesis `shift = 0` is what singles out an isometry fixing the base point, `g ∈ K`, since
the displacement is the composite distance of the moved base point; for a general `g` the spherical
function is *not* invariant and only the weighted formula
`SymmetricSpace.IsCompositeCocycle.sphericalFunction_apply` holds. Under that hypothesis this is
the `K`-invariance of `φ_λ`, the reason it descends to a function of the geodesic distance
(Helgason, *Groups and Geometric Analysis*, Ch. IV §2). -/
theorem IsCompositeCocycle.sphericalFunction_apply_of_shift_eq_zero {T : X → X} {S : B → B}
    {A : X → B → E} {shift : B → E} (hc : IsCompositeCocycle T S A shift) {nu : Measure B}
    (hS : MeasurePreserving S nu nu) (hSm : MeasurableEmbedding S) (hshift : shift = 0)
    (rho lam : E) (x : X) :
    sphericalFunction nu A rho lam (T x) = sphericalFunction nu A rho lam x := by
  rw [hc.sphericalFunction_apply hS hSm rho lam x, sphericalFunction]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  rw [hshift]
  simp

end SymmetricSpace

end

end
