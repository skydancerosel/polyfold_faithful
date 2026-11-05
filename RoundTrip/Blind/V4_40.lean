import Polyfold
/-! Blind formalization of V4_40 (the text's §4.2, Definition 4.17, p. 159).

Text: a smooth finite-dimensional submanifold is tame if, with its induced M-polyfold structure,
it is tame.

Choices:
- This item is a definition.  B says that the project's notion (`IsTameSubmanifold`) is the
  text's: for a smooth finite-dimensional submanifold `A` of the M-polyfold `X`,
  `P.IsTameSubmanifold A ↔ ∃ hA : P.IsSubMPolyfold A, (P.subPolyfold hA).IsTame`.  The text
  asserts no further property.
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`.  I do not assume `X` tame: the item's wording does not, and the
  definition makes sense without it (B is then the more general statement).  `A`: my own
  `IsSmoothSubmanifoldB` (Definition 4.13), copied from V4_33.
- "its induced M-polyfold structure": a smooth finite-dimensional submanifold is a sub-M-polyfold
  (Proposition 4.15 (1)), with the structure of Proposition 2.21, the project's
  `P.subPolyfold hA` (`hA : P.IsSubMPolyfold A`; the structure does not depend on the proof
  `hA`).  The project needs `A` paracompact as an instance; B quantifies over it (a proposition).
  On the right-hand side I write `∃ hA`, so the right-hand side also records that `A` is a
  sub-M-polyfold (true for every smooth submanifold).
- "it is tame": Definition 2.37, the project's `MPolyfold.IsTame` (docstring: an equivalent atlas
  all of whose charts are modelled on tame sc-smooth retracts), applied to the induced structure.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_40
open Polyfold

/-- Definition 4.4 (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V` of
the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- Definition 4.13: `A` is a smooth finite-dimensional submanifold of `X`. -/
def IsSmoothSubmanifoldB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ (V : Set X) (s : X → X), IsOpen V ∧ a ∈ V ∧ IsScPlusRetractionOnB P s V ∧
    s '' V = A ∩ V

/-- **Definition 4.17**: a smooth finite-dimensional submanifold is tame iff, with its induced
M-polyfold structure, it is a tame M-polyfold. -/
def IsTameSubmanifoldB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) [ParacompactSpace A] : Prop :=
  ∃ hA : P.IsSubMPolyfold A, (P.subPolyfold hA).IsTame

/-- Definition 4.17: the project's tame submanifolds are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) [ParacompactSpace A], IsSmoothSubmanifoldB P A →
      (P.IsTameSubmanifold A ↔ IsTameSubmanifoldB P A)

end RoundTrip.V4_40
