import Polyfold
/-! Blind formalization of V7_30 (the 2017 book, arXiv 1707.08941, Part II, §7.1, after
Definition 7.10, pp. 237–238: the facts (1)–(4) on the object set `A` of an ep-subgroupoid).

Text: (by Proposition 2.6 of Part I) the object set `A` of an ep-subgroupoid has an induced
M-polyfold structure with (1) `i : A → X` sc-smooth and a homeomorphism onto its image; (2) for
`a ∈ A` and every sc-smooth retraction `r : V → V` of an open neighbourhood `V` of `a` with
`r(V) = A ∩ V`, `i⁻¹ ∘ r : V → A` is sc-smooth; (3) at a smooth `a ∈ A`, `T_aA` has an
sc-complement in `T_aX`; (4) for `W ⊆ X` open with an sc-smooth retraction `r : W → W`,
`r(W) = A ∩ W`, the induced `r : W → A` is sc-smooth and, at a smooth `a ∈ A`,
`T_aA = (Tr)(a)T_aX`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), the project's
  `X : EpGroupoid Obj Mor` (`#print`ed), object M-polyfold `X.PObj`; `A : Set Obj` the object set
  of an ep-subgroupoid (Definition 7.10, written out as in my `RoundTrip/Blind/V7_29.lean`:
  `X.PObj.IsSubMPolyfold A` and `π⁻¹(π(A)) = A`; saturation is the text's hypothesis though
  (1)–(4) do not use it).
- The rest follows the earlier blind statements of Part I's Proposition 2.21 (= the book's
  Proposition 2.6), `RoundTrip/Blind/V2_24.lean` and `V2_25.lean`, whose helper definitions are
  copied: `A` with the subspace topology; paracompactness of `A` (part of "M-polyfold") is
  asserted (`∃`); "an induced M-polyfold structure for which (1)–(4) hold" is read as the
  existence of ONE structure `Q` with all four properties.  Sc-smoothness: project's
  `IsScSmoothMap` / `IsScSmoothOn`.  An "sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`":
  `V` open, `r(V) ⊆ V`, `r` sc-smooth on `V`, `r ∘ r = r` on `V`, `r '' V = A ∩ V`; `i⁻¹ ∘ r` is
  any `g : X → A` equal to `r` on `V`.  In (2) the point `a ∈ A ∩ V` is kept as in the md.
- Tangent spaces as in V2_25: `T_aX` is the project's `tangentFiber`, read in a chart `φ` of `X`
  around `a` (`tangentChartMap`, second components in `E₀`); `T_aA = Ti(a)T_aA ⊆ T_aX` via
  `tangentMap` of the inclusion; `(Tr)(a)T_aX` via `TangentPre.ftransport` with representatives
  whose chart domain lies in `W`.  B asserts (3), (4) in EVERY chart around `a`.  "Smooth
  `a ∈ A`": `a ∈ Q.smoothSet`; I also assume `a ∈ X_∞` (it follows from (1)).  "Has an
  sc-complement in `T_aX`": `IsScComplementInB` (levelwise algebraic direct sum of
  sc-subspaces), as in V2_25.  In (4), `a ∈ W` is added (needed for `(Tr)(a)`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_30
open Polyfold

/-- `L` has the sc-complement `B` in the sc-subspace `M` of `E`: `M_m = L_m ⊕ B_m` on every
level, with `L`, `B`, `M` sc-subspaces (as in `RoundTrip/Blind/V2_25.lean`). -/
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

/-- `Tr(a)T_aX`, seen in the chart `φ`: the images `T(φ ∘ r ∘ φ_p⁻¹)(φ_p(a), h)` of the vectors
`[(a, φ_p, h)]`, over representatives whose chart domain lies in `W`. -/
def imageTangentInChartB (P : MPolyfold X) (W : Set X) (s : X → X) (φ : MChart X) (a : X) :
    Set (φ.model.E.lvl 0) :=
  (fun p : P.TangentPre => (p.ftransport s φ).2) '' {p | p.x = a ∧ p.φ.source ⊆ W}

end

/-- The object set `A` of an ep-subgroupoid carries an M-polyfold structure with (1) `i : A → X`
an sc-smooth topological embedding, (2) every `i⁻¹ ∘ r` sc-smooth, (3) `T_aA` sc-complemented in
`T_aX` at smooth points, (4) `r : W → A` sc-smooth and `T_aA = Tr(a)T_aX`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (A : Set Obj),
    X.PObj.IsSubMPolyfold A → X.π ⁻¹' (X.π '' A) = A →
    ∃ (_ : ParacompactSpace A) (Q : MPolyfold A)
      (hi : Q.IsScSmoothMap X.PObj (Subtype.val : A → Obj)),
      -- (1) `i` is sc-smooth (`hi`) and a homeomorphism onto its image
      Topology.IsEmbedding (Subtype.val : A → Obj) ∧
      -- (2) `i⁻¹ ∘ r : V → A` is sc-smooth
      (∀ a ∈ A, ∀ (V : Set Obj) (r : Obj → Obj), IsOpen V → a ∈ V → Set.MapsTo r V V →
        X.PObj.IsScSmoothOn X.PObj r V → (∀ y ∈ V, r (r y) = r y) → r '' V = A ∩ V →
        ∀ g : Obj → A, (∀ y ∈ V, (g y : Obj) = r y) → X.PObj.IsScSmoothOn Q g V) ∧
      -- (3) `T_aA` has an sc-complement in `T_aX`
      (∀ (a : A) (haA : a ∈ Q.smoothSet) (haX : (a : Obj) ∈ X.PObj.smoothSet)
        (φ : MChart Obj) (hφ : X.PObj.IsChart φ), (a : Obj) ∈ φ.source →
        ∃ L M B' : Submodule ℝ (φ.model.E.lvl 0),
          (L : Set (φ.model.E.lvl 0)) = subTangentInChartB X.PObj hi hφ a haA ∧
          (M : Set (φ.model.E.lvl 0)) = tangentInChartB X.PObj hφ (a : Obj) haX ∧
          IsScComplementInB φ.model.E L B' M) ∧
      -- (4) for a retraction `r : W → W` onto `A ∩ W`
      (∀ (W : Set Obj) (r : Obj → Obj), IsOpen W → Set.MapsTo r W W →
        X.PObj.IsScSmoothOn X.PObj r W → (∀ y ∈ W, r (r y) = r y) → r '' W = A ∩ W →
        -- the induced map `W → A` is sc-smooth
        (∀ g : Obj → A, (∀ y ∈ W, (g y : Obj) = r y) → X.PObj.IsScSmoothOn Q g W) ∧
        -- `T_aA = Tr(a)T_aX`
        (∀ (a : A) (haA : a ∈ Q.smoothSet), (a : Obj) ∈ X.PObj.smoothSet → (a : Obj) ∈ W →
          ∀ (φ : MChart Obj) (hφ : X.PObj.IsChart φ), (a : Obj) ∈ φ.source →
            imageTangentInChartB X.PObj W r φ (a : Obj) = subTangentInChartB X.PObj hi hφ a haA))

end RoundTrip.V7_30
