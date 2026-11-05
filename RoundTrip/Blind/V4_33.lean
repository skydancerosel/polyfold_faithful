import Polyfold
/-! Blind formalization of V4_33 (the text's §4.2, Proposition 4.15 (1), p. 158).

Text: (for a smooth finite-dimensional submanifold `A ⊆ X`) `A ⊆ X_∞`, and `A` inherits the
M-polyfold structure of `X`; `A` has a tangent space at every point and `d_A` is defined.

Choices:
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X`, `A ⊆ X` a smooth
  finite-dimensional submanifold (Definition 4.13), my own `IsSmoothSubmanifoldB` (copied from my
  V4_29: every `a ∈ A` has an open `V ∋ a` and an sc⁺-retraction `s : V → V` with
  `s(V) = A ∩ V`; sc⁺-retraction on an open set as in my V4_9, `IsScPlusRetractionOnB`).
- "`A ⊆ X_∞`": `A ⊆ P.smoothSet` (`X_∞ = ⋂ X_m`).
- "`A` inherits the M-polyfold structure of `X`": `A` is a sub-M-polyfold (the project's
  `IsSubMPolyfold`, Definition 2.20, checked with `#print`: every `a ∈ A` has an open `V ∋ a` and an
  sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`), so that the induced structure
  `P.subPolyfold hA` (Proposition 2.21) exists; the project needs `A` paracompact as an instance,
  which B asserts (∃) as part of "`A` is an M-polyfold".
- "`A` has a tangent space at every point": tangent spaces (Definition 2.18) are defined at the
  points of level `1`; so: every point of `A` lies in `A_1` for the induced structure,
  `(P.subPolyfold hA).levelSet 1 = univ`.
- "`d_A` is defined": once `A` is an M-polyfold its degeneracy index
  `(P.subPolyfold hA).degIndex` (Definition 2.22) is defined; this carries no further content and
  is not a separate conjunct.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_33
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

/-- Proposition 4.15 (1): a smooth finite-dimensional submanifold consists of smooth points, is a
sub-M-polyfold (so carries the induced M-polyfold structure), and all its points are on level `1`
of the induced structure (so have tangent spaces). -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A →
      A ⊆ P.smoothSet ∧
      ∃ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A),
        (P.subPolyfold hA).levelSet 1 = Set.univ

end RoundTrip.V4_33
