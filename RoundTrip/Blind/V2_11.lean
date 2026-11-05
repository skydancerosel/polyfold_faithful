import Polyfold
/-! Blind formalization of V2_11 (the text's §2.2, Definition 2.12, p. 24).

Text: an sc-smooth atlas is a set of pairwise compatible charts covering `X`; two atlases are
equivalent if their union is an atlas.

Choices:
- This item is a definition; it asserts no further property.  Setting: a topological space
  `X : Type` (spaces put in `Type`; the project's `MAtlas` is universe-polymorphic, this is the
  instance `u = 0`).
- Charts and their compatibility (Definition 2.11) are the project's `MChart X` and
  `MChart.Compatible` (checked with `#print`: a local model `(O, C, E)` with a partial equivalence
  `X ≃ E₀` with open source `V`, target `O`, continuous both ways, i.e. a homeomorphism `V → O`;
  compatibility = both transition maps sc-smooth between the overlap retracts `φ(V ∩ V')`,
  `ψ(V ∩ V')`, Definition 2.7).  These are characterized as the text's notions in my
  `RoundTrip/Blind/V2_10.lean`.
- "Pairwise compatible" is `Set.Pairwise` (any two DISTINCT charts of the set are compatible), the
  literal reading; every chart is compatible with itself (its self-transition is the identity of
  `O`), so this agrees with requiring it for all pairs.  "Covering `X`": every point lies in the
  domain of some chart of the set.  My definition is `IsAtlasB`.
- B characterizes the project's notions: a set of charts is the chart set of a project `MAtlas`
  (checked with `#print`: fields `charts`, `compatible` (all pairs), `cover`) iff it is an atlas in
  my sense; and the project's `MAtlas.Equiv` (checked: there is an atlas whose charts are
  `A.charts ∪ A'.charts`) is "their union is an atlas".
-/
namespace RoundTrip.V2_11
open Polyfold

/-- **Definition 2.12**: an sc-smooth atlas, a set of pairwise compatible charts covering `X`. -/
def IsAtlasB {X : Type} [TopologicalSpace X] (S : Set (MChart X)) : Prop :=
  S.Pairwise MChart.Compatible ∧ ∀ x : X, ∃ c ∈ S, x ∈ c.source

/-- Definition 2.12: the project's atlases and their equivalence are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X],
    (∀ S : Set (MChart X), (∃ A : MAtlas X, A.charts = S) ↔ IsAtlasB S) ∧
    (∀ A A' : MAtlas X, A.Equiv A' ↔ IsAtlasB (A.charts ∪ A'.charts))

end RoundTrip.V2_11
