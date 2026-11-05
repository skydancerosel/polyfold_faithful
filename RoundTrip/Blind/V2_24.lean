import Polyfold
/-! Blind formalization of V2_24 (the text's §2.2, Proposition 2.21 (1), (2), pp. 28–30).

Text: a sub-M-polyfold `A` (of an M-polyfold `X`) has a natural M-polyfold structure for which
(1) the inclusion `i : A → X` is sc-smooth and a homeomorphism onto its image; (2) for every
sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`, `i⁻¹ ∘ r : V → A` is sc-smooth.

Choices:
- Setting: `X : Type` (spaces put in `Type`; the project's `MPolyfold` is universe-polymorphic,
  this is the instance `u = 0`), Hausdorff and paracompact, with an M-polyfold structure
  `P : MPolyfold X` (Definition 2.13, see `RoundTrip/Blind/V2_12.lean`).
- "Sub-M-polyfold" (Definition 2.20) is the project's `P.IsSubMPolyfold A` (checked with
  `#print`: every `a ∈ A` has an open `V ∋ a` and `r` with `r(V) ⊆ V`, `r` sc-smooth on `V`
  (`P.IsScSmoothOn P r V`), `r ∘ r = r` on `V`, `r(V) = A ∩ V`).
- "Sc-smooth" for maps between M-polyfolds is the project's `IsScSmoothMap` / `IsScSmoothOn`
  (Definition 2.14; checked with `#print`: `IsScSmoothMap = IsScSmoothOn · · · univ`; `IsScSmoothOn
  f U`: `U` open, `f` continuous on `U`, and for all charts `φ`, `ψ` of the two structures and every
  open `V ⊆ U ∩ dom φ` with `f(V) ⊆ dom ψ`, `ψ ∘ f ∘ φ⁻¹` is sc-smooth between the retracts
  `(φ(V), C, E)` and `(O', C', E')`).  Only the values of `f` on `U` matter.
- The M-polyfold structure on `A`: `A` carries the subspace topology (Lean's instance on `↥A`;
  Hausdorff automatically); paracompactness of `A` is part of "M-polyfold structure"
  (Definition 2.13), so B asserts it exists (`∃ _ : ParacompactSpace ↥A`).  With the subspace
  topology "`i` is a homeomorphism onto its image" is `Topology.IsEmbedding Subtype.val`, which then
  holds trivially; I keep it as a conjunct for literalness.
- "Natural": I read the claim as the existence of a structure `Q` with (1) and (2)
  (`IsNaturalSubStructureB`).  (1) and (2) determine `Q` up to equivalence of atlases (the
  identity of `A` is locally `(i⁻¹ ∘ r) ∘ i`), so nothing is lost.
- (2): an "sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`" is read as in Definition 2.20:
  `V ⊆ X` open, `r : X → X` (only values on `V` matter) with `r(V) ⊆ V`, `P.IsScSmoothOn P r V`,
  `r ∘ r = r` on `V`, `r '' V = A ∩ V`.  `i⁻¹ ∘ r : V → A` is any `g : X → ↥A` agreeing with it on
  `V` (`∀ g`, since `IsScSmoothOn` ignores values off `V`; with `A = ∅` no such `g` need exist,
  then `V = ∅` and the claim is empty).  Its sc-smoothness is `P.IsScSmoothOn Q g V`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_24
open Polyfold

/-- The M-polyfold structure `Q` on the sub-M-polyfold `A` has properties (1) and (2) of
Proposition 2.21. -/
def IsNaturalSubStructureB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) [ParacompactSpace A] (Q : MPolyfold A) : Prop :=
  -- (1) the inclusion is sc-smooth and a homeomorphism onto its image
  (Q.IsScSmoothMap P (Subtype.val : A → X) ∧ Topology.IsEmbedding (Subtype.val : A → X)) ∧
  -- (2) `i⁻¹ ∘ r : V → A` is sc-smooth for every sc-smooth retraction `r : V → V` onto `A ∩ V`
  (∀ (V : Set X) (r : X → X), IsOpen V → Set.MapsTo r V V → P.IsScSmoothOn P r V →
    (∀ x ∈ V, r (r x) = r x) → r '' V = A ∩ V →
    ∀ g : X → A, (∀ x ∈ V, (g x : X) = r x) → P.IsScSmoothOn Q g V)

/-- Proposition 2.21 (1), (2): a sub-M-polyfold carries an M-polyfold structure for which the
inclusion is an sc-smooth embedding and every `i⁻¹ ∘ r` is sc-smooth. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsSubMPolyfold A →
    ∃ (_ : ParacompactSpace A) (Q : MPolyfold A), IsNaturalSubStructureB P A Q

end RoundTrip.V2_24
