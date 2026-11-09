import Polyfold
/-! Blind formalization of V8_18 (the text's Part II, §8.1, Theorem 8.1.15 = 2017 Theorem 8.4,
2017 p. 268).

Text: if `X` is an ep-groupoid with paracompact orbit space `|X|`, then the tangent ep-groupoid
`TX` has a paracompact orbit space `|TX|` as well.

Choices:
- Setting: `X : EpGroupoid Obj Mor` with `Obj Mor : Type` (universe 0), as in
  `RoundTrip/Blind/V7_3.lean`.  The tangent ep-groupoid `TX = (TX, T𝐗)` is the project's
  `EpGroupoid.tangentEpGroupoid` (the 2017 Theorem 8.1; I trust it as the text's tangent
  ep-groupoid, its spaces are in `Type 1`).
- Orbit spaces: `|X| = X/∼` is the project's `GroupoidStr.OrbitSpace` (characterized in
  `RoundTrip/Blind/V7_1.lean`) with the quotient topology, which I write out explicitly as
  `TopologicalSpace.coinduced π` (`π : X → |X|` the quotient map), so that no other instance can
  enter.  "Paracompact" is Mathlib's `ParacompactSpace` (every open cover has a locally finite
  open refinement; no separation axiom; the text's proof uses that `|TX|` is regular Hausdorff,
  which it treats as known, and B does not need it).
- "ep-groupoid with paracompact orbit space" (2017 Definition 7.15: (1)–(4) of an ep-groupoid
  and (5) `|X|` paracompact) is the hypothesis `|X|` paracompact; the conclusion the same for `TX`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_18
open Polyfold

/-- `|G|` with the quotient topology is paracompact. -/
def OrbitParacompactB {Obj Mor : Type _} [TopologicalSpace Obj] (G : GroupoidStr Obj Mor) : Prop :=
  @ParacompactSpace G.OrbitSpace (TopologicalSpace.coinduced G.π inferInstance)

/-- Theorem 8.1.15: if `|X|` is paracompact, so is `|TX|`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    OrbitParacompactB X.toGroupoidStr → OrbitParacompactB X.tangentEpGroupoid.toGroupoidStr

end RoundTrip.V8_18
