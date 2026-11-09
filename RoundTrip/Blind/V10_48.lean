import Polyfold
/-! Blind formalization of V10_48 (the Springer 2021 book, Part II, §10.3, Remark 10.3.18,
pp. 492–493; 2017: Remark 10.3, p. 355): equivalence of pairs `(X, β)`.

Text: for metrizable `Z`, pairs `(X, β)` with `β : |X| → Z` a homeomorphism, equivalent through
generalized isomorphisms `f` with `β' ∘ |f| = β`; `f` is in general not unique.

Choices:
- This item is a definition with one embedded claim; B is the conjunction of (1) the definition
  and (2) the claim.
- Setting: `Z : Type u` metrizable (Mathlib's `TopologicalSpace.MetrizableSpace`), ep-groupoids
  `EP.{u}` in the same universe (any `u`).  A pair `(X, β)` is the project's `OrbitChart Z`
  (`#check`ed constructor: an `EP` and a homeomorphism `β : |X| ≃ₜ Z`).
- (1): the project's `OrbitChart.Rel p q` (`#print`ed only to learn the argument order: `p` is
  the source `(X, β)`, `q` the target `(X', β')`) holds iff some generalized isomorphism
  `f : X → X'` has `β' ∘ |f| = β`.  On my side `f = [d]` for a diagram `d : X → X'`,
  "generalized isomorphism" is my `IsGenIsoB d` (two-sided inverse up to common refinement, with
  the project's `Diagram.comp`, `Diagram.id`; as in `RoundTrip/Blind/V10_42.lean`) and
  `|f| = |Φ| ∘ |F|⁻¹` is my `orbB d` (as in `RoundTrip/Blind/V10_38.lean`).  (1) is asserted for
  metrizable `Z` only, the text's setting.
- (2) "`f` is in general not unique": there are a metrizable `Z`, pairs `(X, β)`, `(X', β')` and
  two generalized isomorphisms `[d] ≠ [d']` (no common refinement) `X → X'`, both with
  `β' ∘ |f| = β`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_48
open Polyfold Polyfold.EPLocalization

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `d` and `d'` have a common refinement (`[d] = [d']`). -/
def EquivB {X Y : EP.{u}} (d d' : Diagram X Y) : Prop :=
  ∃ d'' : Diagram X Y, IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- `[d]` has a two-sided inverse `[e]`: `[e] ∘ [d] = [1_X]`, `[d] ∘ [e] = [1_Y]`. -/
def IsGenIsoB {X Y : EP.{u}} (d : Diagram X Y) : Prop :=
  ∃ e : Diagram Y X, EquivB (d.comp e) (Diagram.id X) ∧ EquivB (e.comp d) (Diagram.id Y)

/-- `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|`, `|F|` being a homeomorphism as `F` is an equivalence. -/
noncomputable def orbB {X Y : EP.{u}} (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘
    (IsHomeomorph.homeomorph d.F.orbitMap d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- `(X, β) ~ (X', β')` iff a generalized isomorphism `f : X → X'` has `β' ∘ |f| = β`; such an
`f` need not be unique. -/
def B : Prop :=
  (∀ (Z : Type u) [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z]
      (c c' : OrbitChart Z),
      OrbitChart.Rel c c' ↔ ∃ d : Diagram c.X c'.X, IsGenIsoB d ∧ ⇑c'.β ∘ orbB d = ⇑c.β) ∧
  (∃ (Z : Type u) (_ : TopologicalSpace Z), TopologicalSpace.MetrizableSpace Z ∧
      ∃ (c c' : OrbitChart Z) (d d' : Diagram c.X c'.X),
        IsGenIsoB d ∧ IsGenIsoB d' ∧ ⇑c'.β ∘ orbB d = ⇑c.β ∧ ⇑c'.β ∘ orbB d' = ⇑c.β ∧
        ¬ EquivB d d')

end RoundTrip.V10_48
