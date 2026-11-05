import Polyfold
/-! Blind formalization of V4_29 (the text's §4.2, Definition 4.13, p. 157).

Text: `A ⊆ X` is a smooth finite-dimensional submanifold if every `a ∈ A` has an open `V ∋ a`
and an sc⁺-retraction `s : V → V` onto `s(V) = A ∩ V`.

Choices:
- This item is a definition.  B says that the project's notion is the text's:
  `P.IsSmoothSubmanifold A ↔ IsSmoothSubmanifoldB P A` for every M-polyfold `P` and `A ⊆ X`.
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X` (Definition 2.13).
- "an sc⁺-retraction `s : V → V`" on the open set `V` (Definition 4.4, second sentence): my own
  `IsScPlusRetractionOnB` (copied from my V4_9): `V` open, `s` sc-smooth on `V`
  (`P.IsScSmoothOn P s V`, Definition 2.14), `s(V) ⊆ V`, `s ∘ s = s` on `V`, `s(V) ⊆ X₁`
  (`P.levelSet 1`), and every lift `g : X → X₁` of `s` on `V` is sc-smooth on `V` as a map into
  the M-polyfold `X¹` (`P.shift`; its paracompactness is a project instance).  "Every lift"
  rather than "some lift" because a function `X → X₁` need not exist when `V = ∅`; for `V ≠ ∅`
  lifts exist and agree on `V`.
- "onto `s(V) = A ∩ V`": the image `s '' V` equals `A ∩ V`.  `s : X → X` is a total function;
  only its values on `V` matter.
- Compared with the project's `IsSmoothSubmanifold` (checked with `#print`: `∀ a ∈ A, ∃ V, IsOpen V
  ∧ a ∈ V ∧ ∃ s, P.IsScPlusRetractionOn s V ∧ s '' V = A ∩ V`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_29
open Polyfold

/-- Definition 4.4 (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V` of
the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- **Definition 4.13**: `A ⊆ X` is a **smooth finite-dimensional submanifold** if every `a ∈ A`
has an open neighbourhood `V` and an sc⁺-retraction `s : V → V` with `s(V) = A ∩ V`. -/
def IsSmoothSubmanifoldB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ (V : Set X) (s : X → X), IsOpen V ∧ a ∈ V ∧ IsScPlusRetractionOnB P s V ∧
    s '' V = A ∩ V

/-- Definition 4.13: the project's smooth finite-dimensional submanifolds are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsSmoothSubmanifold A ↔ IsSmoothSubmanifoldB P A

end RoundTrip.V4_29
