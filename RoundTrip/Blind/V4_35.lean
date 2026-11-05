import Polyfold
/-! Blind formalization of V4_35 (the text's §4.2, Proposition 4.15 (3), p. 158).

Text: (for a smooth finite-dimensional submanifold `A ⊆ X`)
`∂A = {a ∈ A : d_A(a) ≥ 1} ⊆ ∂X`.

Choices:
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`; no tameness (Proposition 4.15 does not assume it).  `A ⊆ X` a
  smooth finite-dimensional submanifold (Definition 4.13): my own `IsSmoothSubmanifoldB`, copied
  from the prelude of V4_33 (same proposition; sc⁺-retractions `IsScPlusRetractionOnB`).
- `d_A`: the degeneracy index (Definition 2.22, the project's `degIndex`, checked in vocabulary:
  the minimum over the charts around the point of `d_C` of its image) of `A` with its induced
  M-polyfold structure (Proposition 4.15 (1), via Proposition 2.21: the project's
  `P.subPolyfold hA` for `hA : P.IsSubMPolyfold A`).  The project needs `A` paracompact as an
  instance.  B quantifies over `hA` and the paracompactness instance (both are propositions, so
  the structure does not depend on them); that they exist is Proposition 4.15 (1) (item V4_33),
  so I do not repeat it here.
- `∂X = {x ∈ X : d_X(x) ≥ 1}` (Definition 2.25), written with `P.degIndex` like `∂A`; the
  inclusion `∂A ⊆ ∂X` is read through the inclusion `A ↪ X`: every `a ∈ A` with `d_A(a) ≥ 1` has
  `d_X(a) ≥ 1`.  (Equivalently with the project's `boundary`, whose docstring is Definition
  2.25; I wrote the indices out to follow the text's display.)
- Nothing looks false to me.
-/
namespace RoundTrip.V4_35
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

/-- Proposition 4.15 (3): the boundary `∂A = {d_A ≥ 1}` of a smooth finite-dimensional
submanifold (with its induced structure) lies in the boundary `∂X = {d_X ≥ 1}`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A →
      ∀ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A) (a : A),
        1 ≤ (P.subPolyfold hA).degIndex a → 1 ≤ P.degIndex (a : X)

end RoundTrip.V4_35
