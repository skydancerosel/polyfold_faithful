import Polyfold
/-! Blind formalization of V4_36 (the text's §4.2, Proposition 4.15 (4), p. 158).

Text: (for a smooth finite-dimensional submanifold `A ⊆ X`) `1_0^1 : A → A^1` is sc-smooth.

Choices:
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`; no tameness (Proposition 4.15 does not assume it).  `A ⊆ X` a
  smooth finite-dimensional submanifold (Definition 4.13): my own `IsSmoothSubmanifoldB`, copied
  from the prelude of V4_33 (same proposition; sc⁺-retractions `IsScPlusRetractionOnB`).
- `A` carries its induced M-polyfold structure (Proposition 4.15 (1), via Proposition 2.21): the
  project's `P.subPolyfold hA`, `hA : P.IsSubMPolyfold A`, with `A` paracompact (an instance the
  project needs).  B quantifies over `hA` and the instance (propositions: the structure does not
  depend on them); their existence is Proposition 4.15 (1) (item V4_33).
- `A^1`: the M-polyfold `A_1` with the level-1 charts (the paragraph after Definition 2.14), the
  project's `MPolyfold.shift` of the induced structure (its paracompactness is a project instance
  found by instance search, as in V4_27).
- `1_0^1 : A → A^1`: the identity `a ↦ a`.  For it to be a map `A → A^1` the text presupposes
  `A = A_1` (all points of `A` are on level `1` of `A`); I state this as the first conjunct (it is
  also part of item V4_33).  The map itself is the project's `toLevelOne a₀` (vocabulary: `x ↦ x`
  on `A_1`, a junk value `a₀` off `A_1`); since `A = A_1` is asserted, the junk value never
  occurs, and B asks sc-smoothness (`IsScSmoothMap`, Definition 2.14) for every `a₀`.  When `A`
  is empty there is no `a₀` and the statement is trivially true, as it should be.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_36
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

/-- Proposition 4.15 (4): for a smooth finite-dimensional submanifold `A` with its induced
structure, `A = A_1` and the identity `1_0^1 : A → A^1` is sc-smooth. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A →
      ∀ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A),
        (P.subPolyfold hA).levelSet 1 = Set.univ ∧
        ∀ a₀ : (P.subPolyfold hA).Level 1,
          (P.subPolyfold hA).IsScSmoothMap (P.subPolyfold hA).shift
            ((P.subPolyfold hA).toLevelOne a₀)

end RoundTrip.V4_36
