import Polyfold
/-! Blind formalization of V9_54 (the Springer 2021 book, Part II, §9.5, Lemma 9.5.9, p. 442;
2017: Lemma 9.18, p. 326): restrictions in the `G_x`-case, the isotropy and set part.

Text: for `U(x)` with the natural `G_x`-action and a local branching structure, `y ∈ U(x)` and a
small `V(y)` with the natural `G_y`-action, `μ^U_ω(K) = μ^V_ω(K)` for `K ∈ L(S)`,
`K ⊆ |M_V|`.  Proof: `H ≅ G_y`, `G = ⋃_{r ∈ R} rH`, `V` invariant under `H` and disjoint from
its other translates, the preimage of `K` is `⋃_r φ_r(K̃)`, and `♯R = ♯G/♯H`.

Choices:
- The item is "the isotropy and set part": the vocabulary has no sc-differential forms or
  integrals, so `μ^U_ω(K) = μ^V_ω(K)` itself is not formalized; B is the conjunction of the
  isotropy and set facts the proof asserts.
- Setting: `Obj Mor : Type` (universe 0), the project's ep-groupoid `X`, `Θ` a branched
  ep⁺-subgroupoid (project's `IsBranchedEpSubgroupoid`, compared in `RoundTrip/Blind/V9_1.lean`;
  used for "the preimage of `K`": `Θ` is a functor, positive exactly on `M_U` inside `U`).  The
  further standing assumptions of §9.5 (tame, oriented, `n`-dimensional, the form `ω`) only enter
  the integrals and are not added.
- "`U(x)` with the natural `G_x`-action": my `IsNatAction X x U Φ Γ` (copied from
  `RoundTrip/Blind/V9_34.lean` / `V7_21.lean`: the data of Theorem 7.1.13), with `U` connected
  (the text's `U(x)` is connected, as recorded in `RoundTrip/Blind/V7_37.lean`); `G_x` is the
  project's `X.Isotropy x` (`(g * h).val = g ∘ h`), `φ_r = Φ(r)`.  The same for `V(y)` and `G_y`.
  "a local branching structure": a project `LocalBranchingStructure Θ x` with `U(x)` as its
  domain; on `V` the restricted structure `Mᵢ ∩ V`, so `M_V = M_U ∩ V`, `M_U = ⋃ Mᵢ`.
- `H`: the stabilizer `{g | Φ(g)(y) = y}` (my `stabB`).  "`H ≅ G_y`": a group isomorphism given
  by `h ↦ Γ(h, y)` (the morphism `y → y` of `h`).  "`G = ⋃_{r ∈ R} rH`": a set `R` of left coset
  representatives exists (my `IsLeftCosetRepsB`: every `g` is `r h` for exactly one `r ∈ R`); the
  later facts are stated for every such `R`.  "`♯R = ♯G/♯H`": `Nat.card` and `ℕ`-division
  (`♯H` divides `♯G`).
- "a small `V(y)`": there is an open `W` with `y ∈ W ⊆ U` such that every connected open
  `V ∋ y` inside `W` with the natural `G_y`-action has the properties: `Φ(h)(V) = V` for `h ∈ H`
  ("invariant under `H`") and `Φ(g)(V) ∩ V = ∅` for `g ∉ H` ("disjoint from its other
  translates"), and for every `K ⊆ |M_V| = π(M_U ∩ V)` the preimage of `K` in `M_U` is
  `⋃_{r ∈ R} Φ(r)(K̃)`, `K̃ = M_V ∩ π⁻¹(K)` the preimage in `M_V`.  The measurability `K ∈ L(S)`
  plays no role in the set identity and is dropped.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_54
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1), as in `RoundTrip/Blind/V7_21.lean` and `RoundTrip/Blind/V9_34.lean`. -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- `H = {g ∈ G_x | g ∗ y = y}`, the elements of `G_x` fixing `y`. -/
def stabB {X : EpGroupoid Obj Mor} {x : Obj} (Φ : X.Isotropy x → Obj → Obj) (y : Obj) :
    Set (X.Isotropy x) :=
  {g | Φ g y = y}

end

/-- `R` is a set of representatives of the left cosets of `H` in `G`, `G = ⨆_{r ∈ R} rH`:
every `g` is `r h` (`h ∈ H`) for exactly one `r ∈ R`. -/
def IsLeftCosetRepsB {G : Type} [Group G] (H R : Set G) : Prop :=
  ∀ g : G, ∃! r : G, r ∈ R ∧ ∃ h ∈ H, g = r * h

/-- **Lemma 9.5.9, the isotropy and set part**: `H ≅ G_y` by `h ↦ Γ(h, y)`; `G_x = ⨆_{r ∈ R} rH`;
`♯R = ♯G_x/♯H`; small `V(y)` with the natural `G_y`-action are `H`-invariant and disjoint from
their other translates, and the preimage in `M_U` of `K ⊆ |M_V|` is `⋃_{r ∈ R} Φ(r)(K̃)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ (x : Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
      (B : X.LocalBranchingStructure Θ x),
      IsNatAction X x B.U Φ Γ → IsConnected B.U →
      ∀ y ∈ B.U,
        -- `H ≅ G_y`
        (∃ (Hs : Subgroup (X.Isotropy x)) (e : Hs ≃* X.Isotropy y),
          (Hs : Set (X.Isotropy x)) = stabB Φ y ∧ ∀ h : Hs, (e h).val = Γ h.1 y) ∧
        -- `G = ⋃_{r ∈ R} rH`
        (∃ R : Set (X.Isotropy x), IsLeftCosetRepsB (stabB Φ y) R) ∧
        -- `♯R = ♯G/♯H`
        (∀ R : Set (X.Isotropy x), IsLeftCosetRepsB (stabB Φ y) R →
          Nat.card R = Nat.card (X.Isotropy x) / Nat.card (stabB Φ y)) ∧
        -- the small `V(y)`
        ∃ W : Set Obj, IsOpen W ∧ y ∈ W ∧ W ⊆ B.U ∧
          ∀ (V : Set Obj) (Φ' : X.Isotropy y → Obj → Obj) (Γ' : X.Isotropy y → Obj → Mor),
            IsNatAction X y V Φ' Γ' → IsConnected V → V ⊆ W →
            -- `V` is invariant under `H`
            (∀ h ∈ stabB Φ y, Φ h '' V = V) ∧
            -- `V` is disjoint from its other translates
            (∀ g ∉ stabB Φ y, Disjoint (Φ g '' V) V) ∧
            -- the preimage of `K ⊆ |M_V|` is `⋃_r φ_r(K̃)`
            (∀ R : Set (X.Isotropy x), IsLeftCosetRepsB (stabB Φ y) R →
              ∀ K : Set X.OrbitSpace, K ⊆ X.π '' ((⋃ i, B.M i) ∩ V) →
                (⋃ i, B.M i) ∩ X.π ⁻¹' K =
                  ⋃ r ∈ R, Φ r '' ((⋃ i, B.M i) ∩ V ∩ X.π ⁻¹' K))

end RoundTrip.V9_54
