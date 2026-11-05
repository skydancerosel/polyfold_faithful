import Polyfold
/-! Blind formalization of V3_73 (the text's §3.2, proof of Theorem 3.27, p. 84: the re-centring
step). Choices:
- Setting (Theorem 3.27): `X : Type` (universe 0) with an M-polyfold structure `PX`, `X` tame
  (`MPolyfold.IsTame`), `M ⊆ X` with the `n`-dimensional tangent germ property
  (Definition 3.25, written out as in my blind files V3_72 and the earlier V3_22:
  `HasTangentGermPropertyB`, data `IsGermData`), and data `(φ, N, Y, V, δ)` at some `x ∈ M`.  The
  claim is made for *every* such data, every `v₀ ∈ V`, and every data `(ψ, N', Y', V', τ)` at
  `x₀ = φ⁻¹(v₀ + δ(v₀))` (a point of `M` by (i)); `B` quantifies over all of them.
- `π : E → N` the projection along `Y` (`projN`, the `v ∈ N` with `z − v ∈ Y`, by choice; junk `0`
  never used since `E = N ⊕ Y`).  The map of the text is `k(w) = π φ ψ⁻¹(w + τ(w))`, `N' → N`
  (`kmap`; values far from `0` are junk and irrelevant).
- "has an invertible linearization at `0`": there is a linear isomorphism `Λ : N' ≅ N` which is the
  derivative of `k` at `0` within `V'`.
- "so it is a local diffeomorphism": there are relatively open neighbourhoods `W'` of `0` in
  `N' ∩ C'` (inside `V'` and inside the domain of `k`) and `W` of `v₀` in `N ∩ C` (inside `V`) such that
  `k : W' → W` is a bijection with inverse `κ`, both `C¹`, and for every `ℓ` the maps `k`, `κ` are
  `C^ℓ` on some relatively open neighbourhoods of `0`, resp. `v₀` (smooth as germs; the text's
  smoothness of `τ` is only that of a germ, with neighbourhoods depending on the order).
- "`δ` is an sc^∞-germ near `v₀`" / "`δ` is regular near `v₀`" (the same claim, stated once): the germ
  of `δ` at `v₀`, `w ↦ δ(v₀ + w)`, is an sc-smooth germ (Definition 3.2, `IsScSmoothGerm`) on some germ
  of neighbourhoods of `0` in the translate `(N ∩ C) − v₀` lying inside `V − v₀`
  (`IsScInftyGermNear`).
- **I believe the statement is false as quoted**, for `v₀` far from `0` in `V`: Definition 3.25
  controls `δ` only near `0`.  Counterexample: `X = E = ℝ²` (constant structure, `C = E`), `N = ℝ×0`,
  `Y = 0×ℝ`, `φ = id`, `V = (−1, 1) × 0`, `δ(v) = χ(v) · ∛(v − ½)` with `χ` smooth, `χ = 0` near `0`,
  `χ = 1` near `½`, and `M = graph δ`.  `M` is a smooth embedded curve (near `(½, 0)` it is
  `{(½ + t³, t)}`), so it has the `1`-dimensional tangent germ property, and `(id, N, Y, V, δ)` are
  data at `x = 0`.  At `v₀ = ½`, `δ` is not differentiable, and with the data at `x₀ = (½, 0)`
  given by `N' = 0×ℝ`, `τ(0, t) = (t³, 0)`, the map `k(t) = ½ + t³` has derivative `0` at `0`.
  I formalized the claim literally anyway (it holds for `v₀` near `0`).
-/
namespace RoundTrip.V3_73
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.25 (2)**: `(φ, N, Y, V, δ)` are data of the `n`-dimensional tangent germ property
of `M` at `x`. -/
def IsGermData {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) (x : X) (φ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N] (V : Set N)
    (δ : N → φ.model.E.lvl 0) : Prop :=
  PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
  IsTameRetract φ.model.E φ.model.C φ.model.O ∧
  Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
  (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
  IsGoodComplementB φ.model.E φ.model.C N Yc ∧
  (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
  -- (i)
  φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
  -- (ii)
  δ 0 = 0 ∧
  ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
    (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
    ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
      IsSc1GermWith G δ D ∧ D 0 = 0

/-- **Definition 3.25**: `M ⊆ X` has the `n`-dimensional tangent germ property. -/
def HasTangentGermPropertyB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N)
    (V : Set N) (δ : N → φ.model.E.lvl 0), IsGermData PX M n x φ N Yc V δ

/-- The projection `π : E → N` along `Y`: the `v ∈ N` with `z − v ∈ Y` (junk `0` if none). -/
noncomputable def projN {E : Type} [AddCommGroup E] [Module ℝ E] (N Yc : Submodule ℝ E) (z : E) :
    N := by
  classical
  exact if h : ∃ v : N, z - (v : E) ∈ Yc then h.choose else 0

/-- The re-centring map `k(w) = π φ ψ⁻¹(w + τ(w))`, `N' → N`. -/
noncomputable def kmap {X : Type} [TopologicalSpace X] (φ ψ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (N' : Submodule ℝ (ψ.model.E.lvl 0))
    (τ : N' → ψ.model.E.lvl 0) (w : N') : N :=
  projN N Yc (φ.toPartialEquiv (ψ.toPartialEquiv.symm ((w : ψ.model.E.lvl 0) + τ w)))

/-- `δ` is an sc^∞-germ near `v₀`: the translated germ `w ↦ δ(v₀ + w)` is an sc-smooth germ
(Definition 3.2) on a germ of neighbourhoods of `0` in `{w | v₀ + w ∈ N ∩ C}` inside `V − v₀`. -/
def IsScInftyGermNear (E : ScBanach) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N]
    (C : Set (E.lvl 0)) (V : Set N) (δ : N → E.lvl 0) (v₀ : N) : Prop :=
  ∃ G : ScNbhdGerm (ScBanach.const N) {w : N | ((v₀ + w : N) : E.lvl 0) ∈ C},
    (∀ w : N, w ∈ G.U 0 → v₀ + w ∈ V) ∧
    IsScSmoothGerm (F := E) G (fun w : N => δ (v₀ + w))

/-- The re-centring lemma (proof of Theorem 3.27): for data `(φ, N, Y, V, δ)` at `x ∈ M`, `v₀ ∈ V`
and data `(ψ, N', Y', V', τ)` at `x₀ = φ⁻¹(v₀ + δ(v₀))`, the map `k(w) = πφψ⁻¹(w + τ(w))` has an
invertible linearization at `0`, is a local diffeomorphism near `0 ↦ v₀`, and `δ` is an
sc^∞-germ near `v₀`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (M : Set X) (n : ℕ),
    PX.IsTame → HasTangentGermPropertyB PX M n →
    ∀ (x : X) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N]
      (V : Set N) (δ : N → φ.model.E.lvl 0),
      IsGermData PX M n x φ N Yc V δ →
    ∀ v₀ ∈ V,
    ∀ (ψ : MChart X) (N' Y' : Submodule ℝ (ψ.model.E.lvl 0)) [FiniteDimensional ℝ N']
      (V' : Set N') (τ : N' → ψ.model.E.lvl 0),
      IsGermData PX M n (φ.toPartialEquiv.symm ((v₀ : φ.model.E.lvl 0) + δ v₀)) ψ N' Y' V' τ →
      -- invertible linearization at `0`
      (∃ Λ : N' ≃L[ℝ] N, HasFDerivWithinAt (kmap φ ψ N Yc N' τ) (Λ : N' →L[ℝ] N) V' 0) ∧
      -- local diffeomorphism `(W', 0) → (W, v₀)`
      (∃ (W' : Set N') (W : Set N) (κ : N → N'),
        (∃ O' : Set N', IsOpen O' ∧ W' = O' ∩ (Subtype.val ⁻¹' ψ.model.C)) ∧
        (0 : N') ∈ W' ∧ W' ⊆ V' ∧
        (∀ w ∈ W', ψ.toPartialEquiv.symm ((w : ψ.model.E.lvl 0) + τ w) ∈ φ.source) ∧
        (∃ O : Set N, IsOpen O ∧ W = O ∩ (Subtype.val ⁻¹' φ.model.C)) ∧
        v₀ ∈ W ∧ W ⊆ V ∧
        Set.BijOn (kmap φ ψ N Yc N' τ) W' W ∧ Set.InvOn κ (kmap φ ψ N Yc N' τ) W' W ∧
        ContDiffOn ℝ 1 (kmap φ ψ N Yc N' τ) W' ∧ ContDiffOn ℝ 1 κ W ∧
        ∀ ℓ : ℕ,
          (∃ A' : Set N', (∃ O' : Set N', IsOpen O' ∧ A' = O' ∩ W') ∧ (0 : N') ∈ A' ∧
            ContDiffOn ℝ ℓ (kmap φ ψ N Yc N' τ) A') ∧
          (∃ A : Set N, (∃ O : Set N, IsOpen O ∧ A = O ∩ W) ∧ v₀ ∈ A ∧ ContDiffOn ℝ ℓ κ A)) ∧
      -- `δ` is an sc^∞-germ (regular) near `v₀`
      IsScInftyGermNear φ.model.E N φ.model.C V δ v₀

end RoundTrip.V3_73
