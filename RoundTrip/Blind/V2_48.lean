import Polyfold
/-! Blind formalization of V2_48 (the text's §2.4, Proposition 2.42, p. 44).

Text: in a tame M-polyfold every `x` has an open neighbourhood `V` such that each `y ∈ V` lies in
precisely `d_X(y)` faces of `V` and `d_V(y) = d_X(y)`; globally `x` lies in at most `d_X(x)`
faces.

Choices:
- Setting: `X : Type` (universe 0) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]`
  and `P : MPolyfold X` (Definition 2.13), tame: `P.IsTame` (Definition 2.37, checked with
  `#print`: some atlas equivalent to `P.atlas` has all its charts modelled on tame retracts — a
  property of the given structure, not "every compatible chart is tame"), as in
  `RoundTrip/Blind/V2_51.lean`.
- Faces: `MPolyfold.IsFace` (Definition 2.39, checked: `closure (connectedComponentIn {d = 1} x)`
  for some `x` with `d(x) = 1`); `d_X = P.degIndex` (Definition 2.22, checked: the minimum of
  `d_C(φ(x))` over the charts compatible with the structure).  Counts use `Set.encard`, so an
  infinite count is not `0`.
- "`V` with its induced structure", "faces of `V`", `d_V`: the open set `V` is a sub-M-polyfold
  (`r = id`), and its M-polyfold structure is the project's `P.subPolyfold hV` (Proposition 2.21,
  checked with `#print`: the atlas of all sub-charts `φ|_{W ∩ V}`, `W` open, for the charts `φ` of
  `X`; for an open `V` these are restrictions of charts of `X` to open subsets of `V`, so this is
  the usual open-subset structure up to equivalence, and `degIndex` only depends on the class).
  It needs `↥V` paracompact as an instance, which B asserts together with `V` (an open subset of
  the metrizable `X` is metrizable, so this is no extra claim of substance).  "Faces of `V`" are
  `(P.subPolyfold hV).IsFace`, subsets of `↥V` (closures taken in `V`), and `d_V` is
  `(P.subPolyfold hV).degIndex`.
- "Globally `x` lies in at most `d_X(x)` faces": `#{faces F of X with x ∈ F} ≤ d_X(x)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_48
open Polyfold

/-- Proposition 2.42: in a tame M-polyfold every point has an open neighbourhood `V` in which
each `y` lies in exactly `d_X(y)` faces of `V` and `d_V = d_X`; and every `x` lies in at most
`d_X(x)` faces of `X`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
      -- local: a neighbourhood `V` which is face-structured with `d_V = d_X`
      (∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∃ (hV : P.IsSubMPolyfold V) (_ : ParacompactSpace V),
          ∀ y : V,
            {G : Set V | (P.subPolyfold hV).IsFace G ∧ y ∈ G}.encard = (P.degIndex y : ℕ∞) ∧
            (P.subPolyfold hV).degIndex y = P.degIndex y) ∧
      -- global: at most `d_X(x)` faces through `x`
      (∀ x : X, {F : Set X | P.IsFace F ∧ x ∈ F}.encard ≤ (P.degIndex x : ℕ∞))

end RoundTrip.V2_48
