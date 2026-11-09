import Polyfold
/-! Blind formalization of V8_11 (the text's Part II, §8.1, Lemma 8.1.9 (2017: 8.8), 2017 p. 263).

Text: if the ep-groupoid `(X, 𝐗)` is tame, so is the ep-groupoid `(TX, T𝐗)`.  (Proof: if
`φ : U → O`, `O = (O, C, E)`, is a tame chart and `O = r(U) ⊆ C` a tame retract, then
`Tr : TU → TU` is a tame retraction; so `TX` has a tame object space.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); the tangent M-polyfold `TX` is Part I's
  `tangentPolyfold` on `TangentSpace` (in `Type 1`).
- Tame ep-groupoid (Definition 7.6): its object M-polyfold is tame (`MPolyfold.IsTame`, the
  text's Definition 2.19 by `RoundTrip/Blind/V2_43.lean`; `RoundTrip/Blind/V7_8.lean`).  The
  object M-polyfold of `(TX, T𝐗)` is `TX`, so the claim is `X` tame ⇒ `TX` tame.  I do not use
  the project's `EpGroupoid.IsTame` of its tangent ep-groupoid (that would presuppose the project's
  construction has object M-polyfold `TX`, which is `RoundTrip/Blind/V8_1.lean`).
- Not formalized (proof only): "`Tr` is a tame retraction".
- Nothing looks false to me.
-/
namespace RoundTrip.V8_11
open Polyfold

/-- Lemma 8.1.9: if `X` is a tame ep-groupoid, then `TX` is a tame M-polyfold, i.e.
`(TX, T𝐗)` is tame. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.PObj.IsTame → X.PObj.tangentPolyfold.IsTame

end RoundTrip.V8_11
