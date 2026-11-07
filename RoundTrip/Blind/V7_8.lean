import Polyfold
/-! Blind formalization of V7_8 (the text's Part II, §7.1, Definition 7.6 and the paragraph after
it, p. 228 of the 2017 book).

Text: the ep-groupoid `(X, 𝐗)` is tame if the object space `X` is a tame M-polyfold
(Definition 2.19).  In a tame ep-groupoid `𝐗` is also a tame M-polyfold, since `𝐗` is locally
sc-diffeomorphic by `s` to `X` and the tameness condition is invariant under local
sc-diffeomorphisms.

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor`
  (`RoundTrip/Blind/V7_3.lean`).  A tame M-polyfold (the book's Definition 2.19, the 2014
  preprint's 2.37) is the project's `MPolyfold.IsTame` (checked with `#print`: an equivalent atlas
  whose charts are all modelled on tame sc-smooth retracts; stated to be the text's notion in
  `RoundTrip/Blind/V2_43.lean`).
- B (a) the definition: the project's `EpGroupoid.IsTame` (checked: `X.PObj.IsTame`) holds iff
  the object M-polyfold is tame; (b) the claim: then the morphism M-polyfold is tame; (c) the
  stated reason "the tameness condition is invariant under local sc-diffeomorphisms", in the form
  it is used: if `f : Y → Z` is a local sc-diffeomorphism (the project's
  `MPolyfold.IsLocalScDiffeo`, see `RoundTrip/Blind/V7_3.lean`) and `Z` is tame, then `Y` is
  tame.  I do not claim the converse direction (it needs `f` onto: tameness of `Z` away from the
  image of `f` is not controlled).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_8
open Polyfold

/-- Definition 7.6: tameness of an ep-groupoid is tameness of `X`; then `𝐗` is tame, because
tameness pulls back along local sc-diffeomorphisms. -/
def B : Prop :=
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- (a) the definition
    (X.IsTame ↔ X.PObj.IsTame) ∧
    -- (b) in a tame ep-groupoid, `𝐗` is tame
    (X.IsTame → X.PMor.IsTame)) ∧
  -- (c) the reason: tameness is invariant under (pull-back by) local sc-diffeomorphisms
  (∀ (Y Z : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Y) (Q : MPolyfold Z)
    (f : Y → Z), P.IsLocalScDiffeo Q f → Q.IsTame → P.IsTame)

end RoundTrip.V7_8
