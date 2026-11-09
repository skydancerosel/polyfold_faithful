import Polyfold
/-! Blind formalization of V10_47 (the Springer 2021 book, Part II, §10.3, Proposition 10.3.17,
p. 492; new in the 2021 edition): (LUC) is invariant under generalized isomorphisms.

Text: if `f : X → Y` is a generalized isomorphism and one of `X`, `Y` has (LUC), so has the
other.

Choices:
- Setting: `EP.{u}`, any universe `u`, and the project's `Diagram` (`RoundTrip/Blind/V10_37.lean`).
- A generalized map is a class `f = [d]`; B quantifies over the representatives `d : X → Y`.
  Generalized isomorphism (Definition 10.3.9): my `IsGenIsoB d`, a diagram `e : Y → X` with
  `[e] ∘ [d] = [1_X]`, `[d] ∘ [e] = [1_Y]` (common refinements, `Diagram.comp`, `Diagram.id`;
  copied from `RoundTrip/Blind/V10_42.lean`).
- (LUC), the local unique continuation property (2021 Definition 7.2.18): the project's
  `EpGroupoid.IsLUC` (docstring: every object has a natural representation `U(x)` on which an
  isotropy element acting as the identity on a nonempty open subset acts as the identity).
- "One of `X`, `Y` has (LUC), so has the other": `X.IsLUC ↔ Y.IsLUC`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_47
open Polyfold Polyfold.EPLocalization

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `d` and `d'` have a common refinement (`[d] = [d']`). -/
def EquivB {X Y : EP.{u}} (d d' : Diagram X Y) : Prop :=
  ∃ d'' : Diagram X Y, IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- `[d]` has a two-sided inverse `[e]`: `[e] ∘ [d] = [1_X]`, `[d] ∘ [e] = [1_Y]`. -/
def IsGenIsoB {X Y : EP.{u}} (d : Diagram X Y) : Prop :=
  ∃ e : Diagram Y X, EquivB (d.comp e) (Diagram.id X) ∧ EquivB (e.comp d) (Diagram.id Y)

/-- A generalized isomorphism `X → Y` transports (LUC) both ways. -/
def B : Prop :=
  ∀ (X Y : EP.{u}) (d : Diagram X Y), IsGenIsoB d → (X.X.IsLUC ↔ Y.X.IsLUC)

end RoundTrip.V10_47
