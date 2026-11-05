import Polyfold
/-! Blind formalization of V4_30 (the text's §4.2, proof of Theorem 4.18, pp. 160–161).

Text: "Taking `V` and `U` small, we may assume `V = φ⁻¹(O)`"; `t = φ ∘ s ∘ φ⁻¹ ∘ r` is a
retraction, "a sc⁺-retraction since `s` is a sc⁺-retraction", onto `φ(A ∩ V)`.

Choices:
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X`, `A ⊆ X`, and the
  data of Definition 4.13 at a point: an open `V ⊆ X` and an sc⁺-retraction `s : V → V` with
  `s(V) = A ∩ V` (my own `IsScPlusRetractionOnB`, copied from my V4_9: `V` open, `s` sc-smooth on
  `V`, `s(V) ⊆ V`, `s ∘ s = s` on `V`, `s(V) ⊆ X₁`, every lift `V → X¹` sc-smooth).  A chart
  `φ : V' → O` of the structure (`P.IsChart φ`, checked: compatible with the atlas), with model
  `(O, C, E)` and an sc-smooth retraction `r : U → U` onto `O` (`ScRetraction`, Definition 2.1).
  Theorem 4.18's hypotheses (tameness, good position) are not used by this step and are omitted.
- Reading of "`U`": the domain of the retraction `r` (so "`U` small" means `r` restricted to a
  smaller relatively open `U' ⊆ U`); "`V = φ⁻¹(O)`": `V` is the whole domain of the (restricted)
  chart, i.e. `V` lies in the domain of `φ` and `O = r(U) = φ(V)`.
- B is the conjunction of:
  (1) the reduction: for `a ∈ A ∩ V` in the domain of `φ`, there are an open `V' ∋ a` with
  `V' ⊆ V ∩ dom φ` such that `s` is still an sc⁺-retraction on `V'` with `s(V') = A ∩ V'`, and a
  restriction `r'` of `r` to a smaller `U' ⊆ U` which is an sc-smooth retraction onto `φ(V')`;
  (2) in the reduced situation (`V ⊆ dom φ`, `r(U) = φ(V)`): the map
  `t = φ ∘ s ∘ φ⁻¹ ∘ r` (a total function on `E₀`; only its values on `U` are specified) is an
  sc-smooth retraction of `U` (`ScRetraction` with the same `U`), an sc⁺-retraction
  (`IsScPlusRetractionB`, Definition 4.4, copied from my V4_9), and its image is `φ(A ∩ V)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_30
open Polyfold

/-- Definition 4.4 (first sentence): the sc-smooth retraction `r : U → U` is an sc⁺-retraction:
`r(U_m) ⊆ U_{m+1}` for every `m`, and a lift `U → E¹` of `r` is sc-smooth. -/
def IsScPlusRetractionB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  (∀ (m : ℕ) (x : E.lvl m), E.toBase m x ∈ R.U →
      ∃ y : E.lvl (m + 1), E.toBase (m + 1) y = R.toFun (E.toBase m x)) ∧
  ∃ g : E.lvl 0 → E.shift.lvl 0,
    (∀ x ∈ R.U, E.toBase 1 (g x) = R.toFun x) ∧ IsScSmooth (E := E) (F := E.shift) R.U g

/-- Definition 4.4 (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V` of
the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- The local representative `t = φ ∘ s ∘ φ⁻¹ ∘ r` of `s` in the chart `φ`. -/
def localRep {X : Type} [TopologicalSpace X] (φ : MChart X) (s : X → X)
    (r : ScRetraction φ.model.E φ.model.C) : φ.model.E.lvl 0 → φ.model.E.lvl 0 :=
  fun x => φ.toPartialEquiv (s (φ.toPartialEquiv.symm (r.toFun x)))

/-- Proof of Theorem 4.18: shrinking `V` and `U` we may assume `V = φ⁻¹(O)`; then
`t = φ ∘ s ∘ φ⁻¹ ∘ r` is an sc⁺-retraction onto `φ(A ∩ V)`. -/
def B : Prop :=
  -- (1) taking `V` and `U` small, we may assume `V = φ⁻¹(O)`
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (s : X → X) (V : Set X) (φ : MChart X) (r : ScRetraction φ.model.E φ.model.C)
    (a : X),
    IsScPlusRetractionOnB P s V → s '' V = A ∩ V → P.IsChart φ → r.retract = φ.model.O →
    a ∈ A ∩ V → a ∈ φ.toPartialEquiv.source →
      ∃ V' : Set X, a ∈ V' ∧ V' ⊆ V ∩ φ.toPartialEquiv.source ∧
        IsScPlusRetractionOnB P s V' ∧ s '' V' = A ∩ V' ∧
        ∃ r' : ScRetraction φ.model.E φ.model.C, r'.U ⊆ r.U ∧
          (∀ x ∈ r'.U, r'.toFun x = r.toFun x) ∧ r'.retract = φ.toPartialEquiv '' V') ∧
  -- (2) then `t = φ ∘ s ∘ φ⁻¹ ∘ r` is an sc⁺-retraction of `U` onto `φ(A ∩ V)`
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (s : X → X) (V : Set X) (φ : MChart X) (r : ScRetraction φ.model.E φ.model.C),
    IsScPlusRetractionOnB P s V → s '' V = A ∩ V → P.IsChart φ →
    V ⊆ φ.toPartialEquiv.source → r.retract = φ.toPartialEquiv '' V →
      ∃ T : ScRetraction φ.model.E φ.model.C, T.U = r.U ∧
        (∀ x ∈ r.U, T.toFun x = localRep φ s r x) ∧
        IsScPlusRetractionB T ∧ T.retract = φ.toPartialEquiv '' (A ∩ V))

end RoundTrip.V4_30
