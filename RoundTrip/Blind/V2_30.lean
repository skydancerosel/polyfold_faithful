import Polyfold
/-! Blind formalization of V2_30 (the text's §2.3, Lemma 2.26, pp. 31–32).

Text: if `A` is a sub-M-polyfold of `X`, then `d_A(a) ≤ d_X(a)` for all `a ∈ A`.

Choices:
- Setting: `X : Type` (spaces put in `Type`, universe instance `u = 0`), Hausdorff, paracompact,
  `P : MPolyfold X`; `A` a sub-M-polyfold (`P.IsSubMPolyfold A`, Definition 2.20, checked with
  `#print`, see `RoundTrip/Blind/V2_24.lean`).
- `d_A` is the degeneracy index of `A` with its natural M-polyfold structure (Proposition 2.21).
  As in `RoundTrip/Blind/V2_25.lean`, B quantifies over EVERY paracompactness instance on `↥A`
  (subspace topology) and EVERY `Q : MPolyfold ↥A` with properties (1), (2) of Proposition 2.21
  (`IsNaturalSubStructureB`, copied from `RoundTrip/Blind/V2_24.lean`, which asserts that such a
  `Q` exists); (1), (2) determine `Q` up to equivalence of atlases, hence determine `d_A`.
- `d_A`, `d_X`: the project's `MPolyfold.degIndex` (Definition 2.22, checked; see
  `RoundTrip/Blind/V2_26.lean`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_30
open Polyfold

/-- Properties (1) and (2) of Proposition 2.21 for the M-polyfold structure `Q` on `A` (as in
`RoundTrip/Blind/V2_24.lean`). -/
def IsNaturalSubStructureB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) [ParacompactSpace A] (Q : MPolyfold A) : Prop :=
  (Q.IsScSmoothMap P (Subtype.val : A → X) ∧ Topology.IsEmbedding (Subtype.val : A → X)) ∧
  (∀ (V : Set X) (r : X → X), IsOpen V → Set.MapsTo r V V → P.IsScSmoothOn P r V →
    (∀ x ∈ V, r (r x) = r x) → r '' V = A ∩ V →
    ∀ g : X → A, (∀ x ∈ V, (g x : X) = r x) → P.IsScSmoothOn Q g V)

/-- Lemma 2.26: on a sub-M-polyfold, `d_A ≤ d_X`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsSubMPolyfold A →
    ∀ [ParacompactSpace A] (Q : MPolyfold A), IsNaturalSubStructureB P A Q →
    ∀ a : A, Q.degIndex a ≤ P.degIndex (a : X)

end RoundTrip.V2_30
