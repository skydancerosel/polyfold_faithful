import Polyfold
/-! Blind formalization of V10_14 (the text's Part II, §10.1, Proposition 10.1.17, p. 475 of the
Springer 2021 book; new in the 2021 edition).

Text: if `F` is an equivalence, `X` satisfies (ZHOU) iff `Y` does.

Choices:
- Setting: `F : X → Y` with `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'` (the project's
  Definition 7.3, `RoundTrip/Blind/V7_3.lean`), all spaces in `Type` (universe 0, as in the other
  Part II blind files); `F` an sc-smooth functor (`EpFunctor`, `RoundTrip/Blind/V7_9.lean`).
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1, read with
  `#print`, characterized in `RoundTrip/Blind/V10_1.lean`).
- (ZHOU): the project's `EpGroupoid.IsZhou` (2021 Definition 7.4.5), read with `#print`: for a
  smooth object `x` (a point of `X_∞`) and `g ∈ G_x`, if `Tg` is the identity on the tangent
  fibre `T_xX`, then `g ∈ T_x` (`g` acts trivially: `Φ(g) = id` on some natural representation).
  Trusted as the text's notion.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_14
open Polyfold

/-- Proposition 10.1.17: the Zhou condition is invariant under equivalences. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence → (X.IsZhou ↔ Y.IsZhou)

end RoundTrip.V10_14
