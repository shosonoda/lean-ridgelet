/-
Copyright (c) 2026 Sho Sonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Claude
-/
module

public import LeanRidgelet.FS.Defs
public import LeanRidgelet.L1.Defs

/-!
# Fourier slice method, Case II: group convolutional networks on a Hilbert space

Section 4 of

> S. Sonoda, I. Ishikawa and M. Ikeda, *A unified Fourier slice method to derive ridgelet
> transform for a variety of depth-2 neural networks* (arXiv:2402.15984).

A generalized group convolution `(a * x)(g) = ⟪T_{g⁻¹}[x], a⟫` covers classical group convolution,
cyclic convolution for multi-channel images, DeepSets, and `E(n)`-equivariant maps in one
definition. The article's idea is to avoid Fourier analysis on the infinite-dimensional space `ℋ`
by restricting the convolution filter to the span of a finite orthonormal frame, where the Fourier
transform of `ℝ^m` is available.

Everything in this file is algebra: the whole case reduces to the Euclidean one, and the reduction
is exact. Once the reduction is in place, whatever Euclidean reconstruction formula one has —
`L1.Reconstruction` for integrable data, or the Fourier slice scheme of `FS.Scheme` — transports
verbatim. That transport is the hypothesis `hrec` below rather than a fixed choice, so the case
does not commit to one analytic setting.

## Main definitions and results

* `frameCoord`, `frameVector`, `frameProjection`: coordinates in the frame, the vector with given
  coordinates, and the orthogonal projection onto the span of the frame.
* `fs_inner_frameVector`: the identity the whole case rests on, `⟪frameVector c, x⟫ = ⟪c, coord x⟫`.
* `groupConvSynthesis`, `groupConvRidgelet`, `IsGroupEquivariant`: the network, the ridgelet
  transform, and equivariance.
* `fs_groupConvSynthesis_eq_euclidean`: the network is a Euclidean network read at the coordinate
  vector of the projected, translated input.
* `fs_groupConvSynthesis_equivariant`: the network is equivariant by construction.
* `fs_groupConvSynthesis_congr_frameCoord`: **the projection is not an artifact of the proof.** The
  network's value depends on the input only through that coordinate vector, so no coefficient
  function can see anything else.
* `fs_groupConv_synthesis_ridgelet`: the master identity, with no hypothesis on the target.
* `fs_groupConv_reconstruction`: the reconstruction formula under the compatibility hypothesis,
  with `fs_frameProjection_eq_self_of_mem` and `fs_mem_of_invariant` supplying it.
* `fs_span_orbit_le_of_invariant`: what delimits the natural sufficient condition.

## Deviations from the article

The article states Theorem 4.2 as `S[R[f;ρ]] = ⦅σ,ρ⦆ f` for every `(G,T)`-equivariant `f` with
`f(•)(e) ∈ L²(ℋ_m)`. As stated it does not hold for all `x ∈ ℋ` and `g ∈ G`.

Only an inversion formula on `ℋ_m` is available, so what the derivation returns is the target read
at `P_{ℋ_m}(T_{g⁻¹}[x])`, not at `T_{g⁻¹}[x]`. That is the master identity
`fs_groupConv_synthesis_ridgelet`, which needs no hypothesis on `f` at all. The article's
conclusion follows whenever the projection is invisible to `f` at that point, which is the
hypothesis of `fs_groupConv_reconstruction`, and equivariance then converts it to `f(x)(g)`.

The projection is not an artifact of the proof. The network sees `x` only through
`⟪T_{g⁻¹}[x], a⟫` with `a` in the span of the frame, hence only through the projection:
`fs_groupConvSynthesis_congr_frameCoord` states exactly this, and it holds for every coefficient
function. So without a hypothesis of this kind no network of this architecture represents a
general equivariant `f`.

The natural sufficient condition is that the span of the frame be `T`-invariant, since then the
projection is the identity along the whole orbit. It comes with a caveat that the article does not
raise: the construction needs a *finite-dimensional* invariant subspace. Those are plentiful when
the closure of the image of `T` is compact — for a finite group, for `𝕋` acting by rotation of
Fourier modes, for DeepSets — and, for a representation with no finite-dimensional
subrepresentation, only trivial. `fs_span_orbit_le_of_invariant` is the mechanism: a vector of a
finite-dimensional invariant subspace has an orbit spanning a finite-dimensional space, so a
vector whose translates are infinitely many linearly independent ones — an indicator function
under translation on `L²(ℝ)`, say — lies in no such subspace, and for such representations only
the pointwise hypothesis or a band-limited `f` is available.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LeanRidgelet

variable {m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {G : Type*} [Group G]

/-! ## The frame and its coordinates -/

/-- The coordinates of `x` in the frame `fr`, that is `⟪fr i, x⟫` for each `i`. -/
def frameCoord (fr : Fin m → H) (x : H) : InputSpace m :=
  WithLp.toLp 2 fun i => inner ℝ (fr i) x

/-- The vector of `ℋ` with coordinates `c` in the frame `fr`. Its image is the span of the
frame, the `m`-dimensional subspace `ℋ_m` the article restricts the convolution filter to. -/
def frameVector (fr : Fin m → H) (c : InputSpace m) : H := ∑ i, WithLp.ofLp c i • fr i

/-- The orthogonal projection onto the span of the frame, in the form the reconstruction formula
produces it. -/
def frameProjection (fr : Fin m → H) (x : H) : H := frameVector fr (frameCoord fr x)

/-- **The identity the whole case rests on.** Pairing a vector of `ℋ_m` against any vector of `ℋ`
is pairing their coordinate vectors, so the input enters only through its coordinates. Linearity
of the frame is all this needs; orthonormality is not used. -/
theorem fs_inner_frameVector (fr : Fin m → H) (c : InputSpace m) (x : H) :
    inner ℝ (frameVector fr c) x = inner ℝ c (frameCoord fr x) := by
  rw [frameVector, sum_inner]
  simp only [real_inner_smul_left, frameCoord, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For an orthonormal frame the coordinates recover the coefficients. -/
theorem fs_frameCoord_frameVector {fr : Fin m → H} (hfr : Orthonormal ℝ fr)
    (c : InputSpace m) : frameCoord fr (frameVector fr c) = c := by
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  simp only [frameCoord, frameVector, WithLp.ofLp_toLp]
  exact hfr.inner_right_fintype _ i

/-- A vector of the span of the frame is fixed by the projection. -/
theorem fs_frameProjection_eq_self_of_mem {fr : Fin m → H} (hfr : Orthonormal ℝ fr) {x : H}
    (hx : x ∈ Submodule.span ℝ (Set.range fr)) : frameProjection fr x = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  have hcx : frameVector fr (WithLp.toLp 2 c) = x := hc
  rw [frameProjection, ← hcx, fs_frameCoord_frameVector hfr]

/-! ## The network and the ridgelet transform -/

/-- The generalized `(G,T)`-convolution `(a * x)(g) = ⟪T_{g⁻¹}[x], a⟫`. -/
def groupConvolution (T : G → H → H) (a x : H) (g : G) : ℝ := inner ℝ a (T g⁻¹ x)

/-- The group convolutional network. The filter ranges over the span of the frame, parametrized by
its coordinates, which is what the article means by the Lebesgue measure on `ℋ_m` induced from
`ℝ^m`. -/
def groupConvSynthesis (fr : Fin m → H) (T : G → H → H) (σ : ℝ → ℂ)
    (γ : RidgeletParameterSpace m → ℂ) (x : H) (g : G) : ℂ :=
  ∫ p : RidgeletParameterSpace m, γ p * σ (groupConvolution T (frameVector fr p.1) x g - p.2)

/-- The ridgelet transform of the article: the filter is paired with the input by the plain scalar
product, not by the convolution, because both the target and the network are equivariant. -/
def groupConvRidgelet (fr : Fin m → H) (ρ : ℝ → ℂ) (f : H → G → ℂ)
    (p : RidgeletParameterSpace m) : ℂ :=
  ∫ y : InputSpace m, f (frameVector fr y) 1 *
    conj (ρ (inner ℝ (frameVector fr p.1) (frameVector fr y) - p.2))

/-- `(G,T)`-equivariance of a map `ℋ → ℂ^G`. -/
def IsGroupEquivariant (T : G → H → H) (f : H → G → ℂ) : Prop :=
  ∀ (x : H) (g h : G), f (T g x) h = f x (g⁻¹ * h)

/-! ## The reduction to the Euclidean case -/

/-- The network is a Euclidean network read at the coordinate vector of the translated input.
This is `fs_inner_frameVector` under the integral sign, and it is the whole of the reduction. -/
theorem fs_groupConvSynthesis_eq_euclidean (fr : Fin m → H) (T : G → H → H) (σ : ℝ → ℂ)
    (γ : RidgeletParameterSpace m → ℂ) (x : H) (g : G) :
    groupConvSynthesis fr T σ γ x g
      = euclideanDualRidgeletTransform m 0 σ γ (frameCoord fr (T g⁻¹ x)) := by
  rw [groupConvSynthesis, euclideanDualRidgeletTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [groupConvolution, fs_inner_frameVector, Real.rpow_zero]
  simp

/-- The ridgelet transform is the Euclidean ridgelet transform of the target pulled back to the
coordinates of the frame. -/
theorem fs_groupConvRidgelet_eq_euclidean {fr : Fin m → H} (hfr : Orthonormal ℝ fr) (ρ : ℝ → ℂ)
    (f : H → G → ℂ) (p : RidgeletParameterSpace m) :
    groupConvRidgelet fr ρ f p
      = euclideanRidgeletTransform m 0 ρ (fun y => f (frameVector fr y) 1) p := by
  rw [groupConvRidgelet, euclideanRidgeletTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [fs_inner_frameVector, fs_frameCoord_frameVector hfr, Real.rpow_zero]
  simp

/-- **The network is equivariant by construction**, as the article observes. -/
theorem fs_groupConvSynthesis_equivariant (fr : Fin m → H) {T : G → H → H}
    (hT : ∀ (a b : G) (y : H), T a (T b y) = T (a * b) y) (σ : ℝ → ℂ)
    (γ : RidgeletParameterSpace m → ℂ) (x : H) (g h : G) :
    groupConvSynthesis fr T σ γ (T g x) h = groupConvSynthesis fr T σ γ x (g⁻¹ * h) := by
  simp only [fs_groupConvSynthesis_eq_euclidean, hT, mul_inv_rev, inv_inv]

/-- **The projection is a limit of the architecture, not of the proof.** The value of the network
depends on the input only through the coordinate vector of the translated input, for every
coefficient function. Two inputs with the same coordinates are indistinguishable to every network
of this form, so no choice of coefficient function can reproduce a target that separates them. -/
theorem fs_groupConvSynthesis_congr_frameCoord (fr : Fin m → H) (T : G → H → H) (σ : ℝ → ℂ)
    (γ : RidgeletParameterSpace m → ℂ) {x x' : H} {g : G}
    (h : frameCoord fr (T g⁻¹ x) = frameCoord fr (T g⁻¹ x')) :
    groupConvSynthesis fr T σ γ x g = groupConvSynthesis fr T σ γ x' g := by
  rw [fs_groupConvSynthesis_eq_euclidean, fs_groupConvSynthesis_eq_euclidean, h]

/-! ## Reconstruction -/

/-- **The master identity.** With no hypothesis on the target beyond a Euclidean reconstruction
formula for the pulled-back data, the network built from the ridgelet transform reproduces the
target read at the *projection* of the translated input.

The Euclidean reconstruction formula is a hypothesis rather than a fixed theorem so that any of
them may be used: the `L¹` reconstruction of `L1.Reconstruction`, or the Fourier slice scheme. -/
theorem fs_groupConv_synthesis_ridgelet {fr : Fin m → H} (hfr : Orthonormal ℝ fr)
    (T : G → H → H) {σ ρ : ℝ → ℂ} {c : ℂ}
    (hrec : ∀ (F : InputSpace m → ℂ) (y : InputSpace m),
      euclideanDualRidgeletTransform m 0 σ (euclideanRidgeletTransform m 0 ρ F) y = c * F y)
    (f : H → G → ℂ) (x : H) (g : G) :
    groupConvSynthesis fr T σ (groupConvRidgelet fr ρ f) x g
      = c * f (frameProjection fr (T g⁻¹ x)) 1 := by
  rw [fs_groupConvSynthesis_eq_euclidean]
  have hcoef : groupConvRidgelet fr ρ f
      = euclideanRidgeletTransform m 0 ρ (fun y => f (frameVector fr y) 1) :=
    funext fun p => fs_groupConvRidgelet_eq_euclidean hfr ρ f p
  rw [hcoef, hrec]
  rfl

/-- **The reconstruction formula for the group convolutional network** (Theorem 4.2), under the
hypothesis that the projection is invisible to the target at the point in question. Equivariance
then turns the value at the translated input into the value at `(x, g)`. -/
theorem fs_groupConv_reconstruction {fr : Fin m → H} (hfr : Orthonormal ℝ fr) {T : G → H → H}
    {σ ρ : ℝ → ℂ} {c : ℂ}
    (hrec : ∀ (F : InputSpace m → ℂ) (y : InputSpace m),
      euclideanDualRidgeletTransform m 0 σ (euclideanRidgeletTransform m 0 ρ F) y = c * F y)
    {f : H → G → ℂ} (heq : IsGroupEquivariant T f) {x : H} {g : G}
    (hcompat : f (frameProjection fr (T g⁻¹ x)) 1 = f (T g⁻¹ x) 1) :
    groupConvSynthesis fr T σ (groupConvRidgelet fr ρ f) x g = c * f x g := by
  rw [fs_groupConv_synthesis_ridgelet hfr T hrec f x g, hcompat]
  have := heq x g⁻¹ 1
  rw [inv_inv, mul_one] at this
  rw [this]

/-- First sufficient condition for compatibility: the translated input already lies in the span of
the frame. -/
theorem fs_groupConv_compat_of_mem {fr : Fin m → H} (hfr : Orthonormal ℝ fr) {T : G → H → H}
    (f : H → G → ℂ) {x : H} {g : G}
    (hx : T g⁻¹ x ∈ Submodule.span ℝ (Set.range fr)) :
    f (frameProjection fr (T g⁻¹ x)) 1 = f (T g⁻¹ x) 1 := by
  rw [fs_frameProjection_eq_self_of_mem hfr hx]

/-- Second sufficient condition: the span of the frame is `T`-invariant and the input lies in it.
This is the natural one, but it needs a finite-dimensional invariant subspace to exist; see
`fs_span_orbit_le_of_invariant`. -/
theorem fs_mem_of_invariant {fr : Fin m → H} {T : G → H → H}
    (hinv : ∀ (g : G) (y : H), y ∈ Submodule.span ℝ (Set.range fr) →
      T g y ∈ Submodule.span ℝ (Set.range fr))
    {x : H} (hx : x ∈ Submodule.span ℝ (Set.range fr)) (g : G) :
    T g⁻¹ x ∈ Submodule.span ℝ (Set.range fr) := hinv g⁻¹ x hx

omit [Group G] in
/-- What delimits the invariance condition: the orbit of a vector of an invariant subspace stays
inside it, so its span is no larger. A vector whose orbit spans an infinite-dimensional space
therefore lies in no finite-dimensional invariant subspace, and for a representation with no
finite-dimensional subrepresentation the condition is vacuous. -/
theorem fs_span_orbit_le_of_invariant {T : G → H → H} {W : Submodule ℝ H}
    (hinv : ∀ (g : G) (y : H), y ∈ W → T g y ∈ W) {x : H} (hx : x ∈ W) :
    Submodule.span ℝ (Set.range fun g : G => T g x) ≤ W := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨g, rfl⟩
  exact hinv g x hx

omit [Group G] in
/-- **The invariance condition is vacuous for a representation whose orbits are large.** If the
orbit of `x` contains an infinite orthonormal family, then no finite-dimensional invariant
subspace contains `x`, so the second sufficient condition above is unavailable and only the
pointwise hypothesis or a band-limited target remains.

This is what separates the representations the article's construction covers from the ones it does
not: for a finite group, or any representation with precompact image, finite-dimensional invariant
subspaces are plentiful; for the translation representation on `L²(ℝ)`, the integer translates of
an indicator function are orthonormal, so there are none. -/
theorem fs_not_finiteDimensional_of_orthonormal_orbit {T : G → H → H} {W : Submodule ℝ H}
    (hinv : ∀ (g : G) (y : H), y ∈ W → T g y ∈ W) {x : H} (hx : x ∈ W)
    {v : ℕ → H} (hv : Orthonormal ℝ v) (hmem : ∀ n, v n ∈ Set.range fun g : G => T g x) :
    ¬ FiniteDimensional ℝ W := by
  intro hfin
  have hle := fs_span_orbit_le_of_invariant hinv hx
  have hvW : ∀ n, v n ∈ W := fun n => hle (Submodule.subset_span (hmem n))
  have hli : LinearIndependent ℝ (fun n : ℕ => (⟨v n, hvW n⟩ : W)) := by
    refine LinearIndependent.of_comp W.subtype ?_
    exact hv.linearIndependent
  have hfinite : Finite ℕ := hli.finite
  exact (Set.infinite_univ (α := ℕ)) (Set.finite_univ_iff.2 hfinite)

end LeanRidgelet
