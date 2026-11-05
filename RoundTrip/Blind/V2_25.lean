import Polyfold
/-! Blind formalization of V2_25 (the text's §2.2, Proposition 2.21 (3), (4), p. 30).

Text: (for a sub-M-polyfold `A` of an M-polyfold `X`, with its natural M-polyfold structure of
Proposition 2.21 (1), (2)) (3) at a smooth `a ∈ A`, `T_aA` has an sc-complement in `T_aX`;
(4) for an (sc-smooth) retraction `s : W → W` onto `W ∩ A`, the induced map `W → A` is sc-smooth
and `Ts(a)T_aX = T_aA`.  (The "proof in coordinates", `t = s ∘ r`, `T_aA = Dt(a)E`,
`T_aO = Ds(a)Dr(a)E ⊕ (I − Ds(a))Dr(a)E`, is the proof, not part of the claim.)

Choices:
- Setting: `X : Type` (spaces put in `Type`, universe instance `u = 0`), Hausdorff, paracompact,
  `P : MPolyfold X`, `A` a sub-M-polyfold (`P.IsSubMPolyfold A`, Definition 2.20, checked with
  `#print`).  Sc-smoothness of maps: `IsScSmoothMap` / `IsScSmoothOn` (Definition 2.14, checked,
  see `RoundTrip/Blind/V2_24.lean`).
- "The natural structure" on `A` (subspace topology): B quantifies over EVERY paracompactness
  instance and EVERY `Q : MPolyfold ↥A` with properties (1) and (2) of Proposition 2.21
  (`IsNaturalSubStructureB`, as in `RoundTrip/Blind/V2_24.lean`, which asserts such a `Q`
  exists).  (1), (2) determine `Q` up to equivalence of atlases, so this is the definite
  description "the natural structure".
- Tangent spaces: the project's tangent bundle (Definition 2.18; checked with `#print`): `T_aX` is
  `P.tangentFiber a` (classes `[(a, φ, h)]`, `φ` a chart of the structure, `h ∈ T_{φ(a)}O`);
  `T_aA ⊆ T_aX` is its image under `Ti(a)`, `Q.tangentMap hi` (`hi` the sc-smoothness of `i`,
  part of (1); `tangentMap` checked: `[(x, φ, h)] ↦ [(f(x), ψ, (T(ψ ∘ f ∘ φ⁻¹)(φ(x), h))₂)]`).
  The linear (and sc-) structure of `T_aX` is the one transported by a chart: for a chart `φ` of
  `X` around `a` with model `(O, C, E)`, `P.tangentChartMap hφ` (checked: `[(x, ψ, h)] ↦
  T(φ ∘ ψ⁻¹)(ψ(x), h)`) maps `T_aX` onto `{φ(a)} × T_{φ(a)}O`; I compare second components in
  `E₀`.  Since these properties are chart-independent, B asserts them in EVERY chart around `a`.
- "smooth `a ∈ A`": `a ∈ Q.smoothSet` (`A_∞`); I also assume `a ∈ P.smoothSet`, which follows from
  (1) (sc-smooth maps preserve levels), to be able to name `a` as a point of `X₁`.
- "has an sc-complement in `T_aX`" (`IsScComplementInB E L B M`, in the chart, with
  `M = T_aX`, `L = T_aA`): `M`, `L`, `B` are sc-subspaces of `E` (Definition 1.5, the project's
  `IsScSubspace`, checked: closed, smooth points dense in every level; an sc-subspace of the
  sc-subspace `M` is the same as an sc-subspace of `E` inside `M`) and `M_m = L_m ⊕ B_m`
  algebraically on every level `m` (topological automatically, all three being closed).  B
  asserts that the chart images of `T_aA` and `T_aX` are linear subspaces `L`, `M` and that such a
  `B` exists.
- (4): `s` is read like `r` in Definition 2.20: `W` open, `s(W) ⊆ W`, `P.IsScSmoothOn P s W`,
  `s ∘ s = s` on `W`, `s(W) = W ∩ A`.  "The induced map `W → A` is sc-smooth": every `g : X → ↥A`
  equal to `s` on `W` satisfies `P.IsScSmoothOn Q g W` (this is (2) again, so it also follows from
  the hypothesis on `Q`).  `Ts(a) : T_aX → T_aX` (for `a ∈ A ∩ W`, `s(a) = a`) is computed with the
  project's `TangentPre.ftransport p s φ` (checked with `#print`: `T(φ ∘ s ∘ φ_p⁻¹)(φ_p(a), h)`,
  the tangent map of the coordinate representation on the retract `φ_p(dom φ_p ∩ s⁻¹(dom φ))`,
  Definition 2.7).  That representation is sc-smooth only when `dom φ_p ⊆ W` (`s` is junk off
  `W`), so I only use representatives `p = (a, φ_p, h)` with `dom φ_p ⊆ W`; every vector of
  `T_aX` has one (restrict a chart).  `Ts(a)T_aX = T_aA` is the equality of the second components
  in the chart `φ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_25
open Polyfold

/-- Properties (1) and (2) of Proposition 2.21 for the M-polyfold structure `Q` on `A` (as in
`RoundTrip/Blind/V2_24.lean`). -/
def IsNaturalSubStructureB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) [ParacompactSpace A] (Q : MPolyfold A) : Prop :=
  (Q.IsScSmoothMap P (Subtype.val : A → X) ∧ Topology.IsEmbedding (Subtype.val : A → X)) ∧
  (∀ (V : Set X) (r : X → X), IsOpen V → Set.MapsTo r V V → P.IsScSmoothOn P r V →
    (∀ x ∈ V, r (r x) = r x) → r '' V = A ∩ V →
    ∀ g : X → A, (∀ x ∈ V, (g x : X) = r x) → P.IsScSmoothOn Q g V)

/-- `L` has the sc-complement `B` in the sc-subspace `M` of `E`: `M_m = L_m ⊕ B_m` on every
level, with `L`, `B`, `M` sc-subspaces. -/
def IsScComplementInB (E : ScBanach) (L B M : Submodule ℝ (E.lvl 0)) : Prop :=
  E.IsScSubspace M ∧ E.IsScSubspace L ∧ E.IsScSubspace B ∧
  ∀ m : ℕ, Disjoint (E.levelSub L m) (E.levelSub B m) ∧
    E.levelSub L m ⊔ E.levelSub B m = E.levelSub M m

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `T_aX`, seen in the chart `φ` (second components of `Tφ`). -/
def tangentInChartB (P : MPolyfold X) {φ : MChart X} (hφ : P.IsChart φ) (a : X)
    (ha : a ∈ P.smoothSet) : Set (φ.model.E.lvl 0) :=
  (fun α => (P.tangentChartMap hφ α).2) '' P.tangentFiber ⟨a, Set.mem_iInter.1 ha 1⟩

/-- `Ti(a)T_aA ⊆ T_aX`, seen in the chart `φ` of `X`. -/
def subTangentInChartB (P : MPolyfold X) {A : Set X} [ParacompactSpace A] {Q : MPolyfold A}
    (hi : Q.IsScSmoothMap P (Subtype.val : A → X)) {φ : MChart X} (hφ : P.IsChart φ) (a : A)
    (ha : a ∈ Q.smoothSet) : Set (φ.model.E.lvl 0) :=
  (fun β => (P.tangentChartMap hφ (MPolyfold.tangentMap hi β)).2) ''
    Q.tangentFiber ⟨a, Set.mem_iInter.1 ha 1⟩

/-- `Ts(a)T_aX`, seen in the chart `φ`: the images `T(φ ∘ s ∘ φ_p⁻¹)(φ_p(a), h)` of the vectors
`[(a, φ_p, h)]`, over representatives whose chart domain lies in `W`. -/
def imageTangentInChartB (P : MPolyfold X) (W : Set X) (s : X → X) (φ : MChart X) (a : X) :
    Set (φ.model.E.lvl 0) :=
  (fun p : P.TangentPre => (p.ftransport s φ).2) '' {p | p.x = a ∧ p.φ.source ⊆ W}

end

/-- Proposition 2.21 (3), (4): at smooth points of a sub-M-polyfold `A`, `T_aA` has an
sc-complement in `T_aX`; for a retraction `s : W → W` onto `W ∩ A`, `W → A` is sc-smooth and
`Ts(a)T_aX = T_aA`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsSubMPolyfold A →
    ∀ [ParacompactSpace A] (Q : MPolyfold A), IsNaturalSubStructureB P A Q →
    ∀ (hi : Q.IsScSmoothMap P (Subtype.val : A → X)),
    -- (3) `T_aA` has an sc-complement in `T_aX`
    (∀ (a : A) (haA : a ∈ Q.smoothSet) (haX : (a : X) ∈ P.smoothSet)
      (φ : MChart X) (hφ : P.IsChart φ), (a : X) ∈ φ.source →
      ∃ L M B' : Submodule ℝ (φ.model.E.lvl 0),
        (L : Set (φ.model.E.lvl 0)) = subTangentInChartB P hi hφ a haA ∧
        (M : Set (φ.model.E.lvl 0)) = tangentInChartB P hφ (a : X) haX ∧
        IsScComplementInB φ.model.E L B' M) ∧
    -- (4) for a retraction `s : W → W` onto `W ∩ A`
    (∀ (W : Set X) (s : X → X), IsOpen W → Set.MapsTo s W W → P.IsScSmoothOn P s W →
      (∀ x ∈ W, s (s x) = s x) → s '' W = W ∩ A →
      -- the induced map `W → A` is sc-smooth
      (∀ g : X → A, (∀ x ∈ W, (g x : X) = s x) → P.IsScSmoothOn Q g W) ∧
      -- `Ts(a)T_aX = T_aA`
      (∀ (a : A) (haA : a ∈ Q.smoothSet), (a : X) ∈ P.smoothSet → (a : X) ∈ W →
        ∀ (φ : MChart X) (hφ : P.IsChart φ), (a : X) ∈ φ.source →
          imageTangentInChartB P W s φ (a : X) = subTangentInChartB P hi hφ a haA))

end RoundTrip.V2_25
