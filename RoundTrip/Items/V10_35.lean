import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_35

/-! Round trip for V10_35 (2021 Definition 10.3.3, p. 485; 2017: Definition 10.5, p. 349:
common refinements).

The only listed declaration, `Polyfold.EPLocalization.Diagram.IsCommonRefinement`
(`d''.IsRefinement d ∧ d''.IsRefinement d'`), is a definition, so `A = True`; the content of the
audit is the comparison of the project's definition with B's notion, which is B itself, proved
outright here (`B_holds`, by `Iff.rfl`: B's `IsRefinementB` is the project's `IsRefinement`
because `NaturallyEquivalent F G` is `Nonempty (EpNatTrans F G)`, and the argument order — the
candidate first, then the pair — agrees).  Universe: B is stated in `EP.{0}`, the project's
definition is universe-polymorphic (`u = 0` here). -/

namespace RoundTrip.V10_35
open Polyfold EPLocalization

/-- Only a definition is listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

theorem B_holds : B := fun _ _ _ _ _ => Iff.rfl

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

/-! No theorem is listed, so the banned lists are empty (the listed definition is the subject of
`B` itself and is necessarily reached; banning it fails trivially, as recorded below). -/

#rt_check RoundTrip.V10_35.A_to_B []
#rt_check RoundTrip.V10_35.B_to_A []
#rt_overlap RoundTrip.V10_35.B_to_A []
#rt_check RoundTrip.V10_35.B_holds []

/--
error: rt_check FAIL: RoundTrip.V10_35.B_holds uses [Polyfold.EPLocalization.Diagram.IsCommonRefinement]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_35.B_holds [Polyfold.EPLocalization.Diagram.IsCommonRefinement]

end RoundTrip.V10_35
