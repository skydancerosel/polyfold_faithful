import Polyfold
/-! Blind formalization of V4_34 (the text's §4.2, Proposition 4.15 (2), p. 158).

Text: (for a smooth finite-dimensional submanifold `A ⊆ X`) `A` is locally closed in `X`
(defined as: every `a` has an open `V(a)` such that `b ∈ V(a)` belongs to `A` if
`U ∩ A ≠ ∅` for all open `U ∋ b`).

Choices:
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X` (Definition 2.13); no tameness (Proposition 4.15 does not assume
  it).  `A ⊆ X` a smooth finite-dimensional submanifold (Definition 4.13): my own
  `IsSmoothSubmanifoldB`, copied from the prelude of V4_33 (same proposition): every `a ∈ A` has an
  open `V ∋ a` and an sc⁺-retraction `s : V → V` (`IsScPlusRetractionOnB`: `s` sc-smooth on `V`,
  `s(V) ⊆ V`, `s ∘ s = s` on `V`, `s(V) ⊆ X₁`, every lift `V → X¹` of `s` sc-smooth) with
  `s(V) = A ∩ V`.
- "Locally closed", with the text's own definition taken literally: for every `a ∈ A` there is an
  open `V ∋ a` ("`V(a)`" read as an open neighbourhood of `a`) such that every `b ∈ V` all of whose
  open neighbourhoods `U` meet `A` lies in `A` (i.e. `closure A ∩ V ⊆ A`).  I did not use
  Mathlib's `IsLocallyClosed` (equivalent, but not the text's wording).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_34
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

/-- The text's definition of "`A` is locally closed in `X`": every `a ∈ A` has an open
neighbourhood `V(a)` such that a point `b ∈ V(a)` all of whose open neighbourhoods meet `A`
belongs to `A`. -/
def IsLocallyClosedB {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧
    ∀ b ∈ V, (∀ U : Set X, IsOpen U → b ∈ U → (U ∩ A).Nonempty) → b ∈ A

/-- Proposition 4.15 (2): a smooth finite-dimensional submanifold is locally closed. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A → IsLocallyClosedB A

end RoundTrip.V4_34
