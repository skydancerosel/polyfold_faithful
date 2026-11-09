import Polyfold
/-! Blind formalization of V11_33 (the text's Part II, §11.6, Lemma 11.6.1, p. 549 of the
Springer 2021 book; new in the 2021 edition).

Text: a proper covering functor `F : Y → X` is a surjective local sc-diffeomorphism on morphisms.

Choices:
- Setting as in `RoundTrip/Blind/V8_27.lean`: ep-groupoids `Y : EpGroupoid ObjY MorY`,
  `X : EpGroupoid ObjX MorX` (the project's Definition 7.3), all four spaces in `Type`
  (universe 0, as in the other Part II blind files); `F` an sc-smooth functor (`EpFunctor`,
  `RoundTrip/Blind/V7_9.lean`).
- "proper covering functor": the project's `EpFunctor.IsProperCovering` (2021 Definition 8.5.1;
  characterized against the text in `RoundTrip/Blind/V8_27.lean`).
- "on morphisms": the map `F.mor : 𝐘 → 𝐗` between the morphism M-polyfolds `Y.PMor`, `X.PMor`.
- "surjective": `Function.Surjective F.mor`.  "local sc-diffeomorphism": the project's
  `MPolyfold.IsLocalScDiffeo` (`#print`ed: every point has a neighbourhood `U` with
  `IsScDiffeoOn f g U V` for some `V`, `g`, i.e. `f` an sc-diffeomorphism between open sets; the
  same notion as in condition (1) of Definition 8.5.1, as used in V8_27 and V10_1).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_33
open Polyfold

/-- Lemma 11.6.1: a proper covering functor is a surjective local sc-diffeomorphism on
morphisms. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering →
      Function.Surjective F.mor ∧ Y.PMor.IsLocalScDiffeo X.PMor F.mor

end RoundTrip.V11_33
