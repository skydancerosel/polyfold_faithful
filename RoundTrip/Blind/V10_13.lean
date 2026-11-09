import Polyfold
/-! Blind formalization of V10_13 (the text's Part II, §10.1, Proposition 10.1.16, p. 474 of the
Springer 2021 book; new in the 2021 edition).

Text: if `F : X → Y` is an equivalence, `X` has (LUC) iff `Y` has.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'` (the project's
  Definition 7.3, checked in `RoundTrip/Blind/V7_3.lean`), all four spaces in `Type`
  (universe 0, as in the other Part II blind files), Hausdorff and paracompact as `EpGroupoid`
  requires; `F` an sc-smooth functor (`EpFunctor`, `RoundTrip/Blind/V7_9.lean`).
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1: full,
  faithful, `|F|` a homeomorphism, a local sc-diffeomorphism on objects; read with `#print` and
  characterized in `RoundTrip/Blind/V10_1.lean`).
- (LUC): the project's `EpGroupoid.IsLUC` (2021 Definition 7.2.18), read with `#print`: every
  object `x` has a natural representation `U(x)` (the project's `NaturalRep`, an open connected
  `U(x) ∋ x` with the natural `G_x`-action `Φ`, `Γ`) such that `Φ(g) = id` on a nonempty open
  subset of `U(x)` forces `Φ(g) = id` on `U(x)`.  Trusted, as in `RoundTrip/Blind/V8_45.lean`.
- No other hypotheses (the text has none in the statement).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_13
open Polyfold

/-- Proposition 10.1.16: (LUC) is invariant under equivalences. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence → (X.IsLUC ↔ Y.IsLUC)

end RoundTrip.V10_13
