import Polyfold
/-! Blind formalization of V4_41 (the text's §4.2, Theorem 4.18, p. 159).

Text: let `X` be tame and `A ⊆ X` a smooth finite-dimensional submanifold in good position at
every point.  Then the induced structure on `A` is equivalent to a smooth manifold with boundary
with corners; in particular `A` is tame.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, `P : MPolyfold X` tame
  (`P.IsTame`, Definition 2.37, checked with `#print`: an equivalent atlas of charts on tame
  retracts — a property of the given structure).
- "smooth finite-dimensional submanifold": the project's `P.IsSmoothSubmanifold A` (Definition
  4.13, checked: every `a ∈ A` has an open `V ∋ a` and an sc⁺-retraction `s : V → V` — sc-smooth,
  idempotent, `s(V) ⊆ X₁`, `1₀¹ ∘ s : V → X¹` sc-smooth — with `s(V) = A ∩ V`).
- "in good position at every point": `∀ a ∈ A, P.IsGoodPositionAt A a` (Definition 4.16,
  checked: in some chart `φ` of `X` at `a`, with some data of Definition 4.13 and some presentation
  `T` of the partial quadrant, the tangent space `T_zA = T_z(φ(W ∩ A))` at the level-`1` point `z`
  over `φ(a)` is in good position, inside `T_zO`, to the partial cone `T_zO ∩ C_z`).  The text's
  notion is chart-free; the chart form "for some chart" is the weakest reading as a hypothesis.
- "the induced structure on `A`": `A` is in particular a sub-M-polyfold (an sc⁺-retraction is an
  sc-smooth retraction), and the induced structure is the project's `P.subPolyfold hA`
  (Proposition 2.21, the sub-charts).  It needs `A` paracompact as an instance; B asserts it (it
  is part of "the induced structure" being an M-polyfold).
- "equivalent to a smooth manifold with boundary with corners": `HasCornerStructure` of the
  induced structure (Definition 4.1, checked: an equivalent atlas of corner charts on relatively
  open subsets of partial quadrants of finite-dimensional spaces with the constant sc-structure).
- "in particular `A` is tame": the induced M-polyfold is tame (`IsTame`; Definition 4.17 says
  exactly this for a submanifold).  B is the conjunction.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_41
open Polyfold

/-- Theorem 4.18: a smooth finite-dimensional submanifold of a tame M-polyfold which is in good
position at every point is, with its induced structure, a smooth manifold with boundary with
corners, and is tame. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X),
    P.IsTame → P.IsSmoothSubmanifold A → (∀ a ∈ A, P.IsGoodPositionAt A a) →
      ∃ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A),
        (P.subPolyfold hA).HasCornerStructure ∧ (P.subPolyfold hA).IsTame

end RoundTrip.V4_41
