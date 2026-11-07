import Polyfold
/-! Blind formalization of V7_31 (the 2017 book's Part II, §7.1, p. 238).

Text: for a saturated sub-M-polyfold `A` of the object space, `𝐀 = {φ ∈ 𝐗 | s(φ), t(φ) ∈ A}` has
in a natural way the structure of an M-polyfold.  For `φ ∈ 𝐀`, `a = s(φ)`, choose open `𝐔(φ) ⊆ 𝐗`,
`U(a) ⊆ X` with `s : 𝐔(φ) → U(a)` an sc-diffeomorphism and (shrinking) an sc-smooth retraction
`r : U(a) → U(a)` with `r(U(a)) = U(a) ∩ A`; then `𝐫 = (s|𝐔(φ))⁻¹ ∘ r ∘ s : 𝐔(φ) → 𝐔(φ)` is an
sc-smooth retraction and, `A` being saturated, `𝐫(𝐔(φ)) = 𝐔(φ) ∩ 𝐀`.  So `𝐀` is a sub-M-polyfold
of `𝐗`, and the properties listed for `A` also hold for `𝐀`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`), and
  `A ⊆ Obj` with `X.PObj.IsSubMPolyfold A` (Definition 2.20, checked with `#print`, see
  `RoundTrip/Blind/V2_24.lean`) and `X.IsSaturated A` (checked: `π⁻¹(π(A)) = A`, literally the
  text's Definition 7.10 (2)).
- `𝐀` is `X.morOn A` (checked: `{φ | s φ ∈ A ∧ t φ ∈ A}`).
- "sc-smooth retraction `r : U → U` with `r(U) = U ∩ A`" (`IsRetractOntoB`), as in Definition 2.20:
  `r(U) ⊆ U`, `r` sc-smooth on `U` (the project's `IsScSmoothOn`, which includes `U` open),
  `r ∘ r = r` on `U`, `r '' U = U ∩ A`.  Maps are total; only values on `U` matter.
- "`s : 𝐔 → U` an sc-diffeomorphism" with inverse `σ = (s|𝐔)⁻¹`: the project's
  `IsScDiffeoOn PMor PObj s σ 𝐔 U` (checked with `#print`).  `𝐫 = σ ∘ r ∘ s`.
- B is the conjunction of: (a) the choice is possible at every `φ ∈ 𝐀` (with `φ ∈ 𝐔`,
  `s φ ∈ U`); (b) for EVERY such choice, `𝐫` is an sc-smooth retraction of `𝐔` onto `𝐔 ∩ 𝐀` (the
  "then" of the text, for whatever choice is made); (c) `𝐀` is a sub-M-polyfold of `𝐗`; (d) "has
  in a natural way the structure of an M-polyfold ... the properties listed for `A` also hold for
  `𝐀`": the properties are facts (1)–(4) after Definition 7.10 (item V7_30, = Proposition 2.21
  (1)–(4) of Part I), and B asserts a paracompactness of `𝐀` and an M-polyfold structure `Q` on
  `𝐀` (subspace topology) with (1)–(4) relative to `𝐗` (`SubFactsB`).  (1), (2) determine `Q` up
  to equivalence (the identity of `𝐀` is locally `(i⁻¹ ∘ 𝐫) ∘ i`), which is "natural".
- `SubFactsB` copies `IsNaturalSubStructureB` of `RoundTrip/Blind/V2_24.lean` for (1), (2) and the
  tangent-space formulations of `RoundTrip/Blind/V2_25.lean` for (3), (4) (see their headers for
  the project tangent notions used: `tangentFiber`, `tangentChartMap`, `tangentMap`, `TangentPre`,
  `ftransport`, `IsScSubspace`, `levelSub`; I take them as checked there).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_31
open Polyfold

/-- `L` has the sc-complement `B` in the sc-subspace `M` of `E`: `M_m = L_m ⊕ B_m` on every
level, with `L`, `B`, `M` sc-subspaces (as in `RoundTrip/Blind/V2_25.lean`). -/
def IsScComplementInB (E : ScBanach) (L B M : Submodule ℝ (E.lvl 0)) : Prop :=
  E.IsScSubspace M ∧ E.IsScSubspace L ∧ E.IsScSubspace B ∧
  ∀ m : ℕ, Disjoint (E.levelSub L m) (E.levelSub B m) ∧
    E.levelSub L m ⊔ E.levelSub B m = E.levelSub M m

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `r : U → U` is an sc-smooth retraction with `r(U) = U ∩ A` (Definition 2.20). -/
def IsRetractOntoB (P : MPolyfold Z) (r : Z → Z) (U A : Set Z) : Prop :=
  Set.MapsTo r U U ∧ P.IsScSmoothOn P r U ∧ (∀ x ∈ U, r (r x) = r x) ∧ r '' U = U ∩ A

/-- `T_aZ`, seen in the chart `φ` (second components of `Tφ`), as in `V2_25`. -/
def tangentInChartB (P : MPolyfold Z) {φ : MChart Z} (hφ : P.IsChart φ) (a : Z)
    (ha : a ∈ P.smoothSet) : Set (φ.model.E.lvl 0) :=
  (fun α => (P.tangentChartMap hφ α).2) '' P.tangentFiber ⟨a, Set.mem_iInter.1 ha 1⟩

/-- `Ti(a)T_aA ⊆ T_aZ`, seen in the chart `φ` of `Z`, as in `V2_25`. -/
def subTangentInChartB (P : MPolyfold Z) {A : Set Z} [ParacompactSpace A] {Q : MPolyfold A}
    (hi : Q.IsScSmoothMap P (Subtype.val : A → Z)) {φ : MChart Z} (hφ : P.IsChart φ) (a : A)
    (ha : a ∈ Q.smoothSet) : Set (φ.model.E.lvl 0) :=
  (fun β => (P.tangentChartMap hφ (MPolyfold.tangentMap hi β)).2) ''
    Q.tangentFiber ⟨a, Set.mem_iInter.1 ha 1⟩

/-- `Tr(a)T_aZ`, seen in the chart `φ`, over representatives whose chart domain lies in `W`, as
in `V2_25`. -/
def imageTangentInChartB (P : MPolyfold Z) (W : Set Z) (s : Z → Z) (φ : MChart Z) (a : Z) :
    Set (φ.model.E.lvl 0) :=
  (fun p : P.TangentPre => (p.ftransport s φ).2) '' {p | p.x = a ∧ p.φ.source ⊆ W}

/-- Facts (1)–(4) after Definition 7.10 (Proposition 2.21) for the structure `Q` on the
sub-M-polyfold `A ⊆ Z`: (1) `i : A → Z` is sc-smooth and a homeomorphism onto its image; (2)
`i⁻¹ ∘ r` is sc-smooth for every sc-smooth retraction `r : V → V` onto `A ∩ V`; (3) at smooth
`a ∈ A`, `T_aA` has an sc-complement in `T_aZ`; (4) for an sc-smooth retraction `r : W → W` onto
`A ∩ W`, the induced `W → A` is sc-smooth and `T_aA = Tr(a)T_aZ` at smooth `a ∈ A ∩ W`. -/
def SubFactsB (P : MPolyfold Z) (A : Set Z) [ParacompactSpace A] (Q : MPolyfold A) : Prop :=
  -- (1)
  (Q.IsScSmoothMap P (Subtype.val : A → Z) ∧ Topology.IsEmbedding (Subtype.val : A → Z)) ∧
  -- (2)
  (∀ (V : Set Z) (r : Z → Z), IsOpen V → Set.MapsTo r V V → P.IsScSmoothOn P r V →
    (∀ x ∈ V, r (r x) = r x) → r '' V = A ∩ V →
    ∀ g : Z → A, (∀ x ∈ V, (g x : Z) = r x) → P.IsScSmoothOn Q g V) ∧
  ∀ (hi : Q.IsScSmoothMap P (Subtype.val : A → Z)),
    -- (3)
    (∀ (a : A) (haA : a ∈ Q.smoothSet) (haZ : (a : Z) ∈ P.smoothSet)
      (φ : MChart Z) (hφ : P.IsChart φ), (a : Z) ∈ φ.source →
      ∃ L M B' : Submodule ℝ (φ.model.E.lvl 0),
        (L : Set (φ.model.E.lvl 0)) = subTangentInChartB P hi hφ a haA ∧
        (M : Set (φ.model.E.lvl 0)) = tangentInChartB P hφ (a : Z) haZ ∧
        IsScComplementInB φ.model.E L B' M) ∧
    -- (4)
    (∀ (W : Set Z) (s : Z → Z), IsOpen W → Set.MapsTo s W W → P.IsScSmoothOn P s W →
      (∀ x ∈ W, s (s x) = s x) → s '' W = W ∩ A →
      (∀ g : Z → A, (∀ x ∈ W, (g x : Z) = s x) → P.IsScSmoothOn Q g W) ∧
      (∀ (a : A) (haA : a ∈ Q.smoothSet), (a : Z) ∈ P.smoothSet → (a : Z) ∈ W →
        ∀ (φ : MChart Z) (hφ : P.IsChart φ), (a : Z) ∈ φ.source →
          imageTangentInChartB P W s φ (a : Z) = subTangentInChartB P hi hφ a haA))

end

/-- The morphisms `𝐀` between points of a saturated sub-M-polyfold `A`: the retractions
`𝐫 = (s|𝐔)⁻¹ ∘ r ∘ s` exist and retract onto `𝐔 ∩ 𝐀`, so `𝐀` is a sub-M-polyfold of `𝐗`, with an
M-polyfold structure satisfying the facts (1)–(4) listed for `A`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (A : Set Obj), X.PObj.IsSubMPolyfold A → X.IsSaturated A →
    -- (a) the choices of `𝐔(φ)`, `U(a)`, `r` are possible
    (∀ φ ∈ X.morOn A, ∃ (W : Set Mor) (U : Set Obj) (σ : Obj → Mor) (r : Obj → Obj),
      φ ∈ W ∧ X.src φ ∈ U ∧ X.PMor.IsScDiffeoOn X.PObj X.src σ W U ∧
      IsRetractOntoB X.PObj r U A) ∧
    -- (b) for every such choice, `𝐫 = σ ∘ r ∘ s` retracts `𝐔` onto `𝐔 ∩ 𝐀`
    (∀ (W : Set Mor) (U : Set Obj) (σ : Obj → Mor) (r : Obj → Obj),
      X.PMor.IsScDiffeoOn X.PObj X.src σ W U → IsRetractOntoB X.PObj r U A →
      IsRetractOntoB X.PMor (σ ∘ r ∘ X.src) W (X.morOn A)) ∧
    -- (c) `𝐀` is a sub-M-polyfold of `𝐗`
    X.PMor.IsSubMPolyfold (X.morOn A) ∧
    -- (d) its M-polyfold structure, with the facts (1)–(4)
    (∃ (_ : ParacompactSpace (X.morOn A)) (Q : MPolyfold (X.morOn A)),
      SubFactsB X.PMor (X.morOn A) Q)

end RoundTrip.V7_31
