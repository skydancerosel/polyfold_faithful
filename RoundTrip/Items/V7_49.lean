import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_49

/-!
Round trip for V7_49 (Definition 7.14: component compact sets).

The only listed declaration, `Polyfold.EpGroupoid.IsComponentCompact`, is a definition, so
`A = True`; the content of the audit is `B` itself (the project's notion is the text's), proved
outright here (`B_holds`).  The project quantifies over points `z` and the components
`connectedComponent z`; `B` quantifies over sets `C` of that form.  Same universe (`Type`).
-/

namespace RoundTrip.V7_49
open Polyfold

/-- Only a definition is listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- The project's Definition 7.14 is the text's. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X K
  constructor
  · rintro h C ⟨z, rfl⟩
    exact h z
  · intro h z
    exact h _ ⟨z, rfl⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V7_49.A_to_B []
#rt_check RoundTrip.V7_49.B_to_A []
#rt_overlap RoundTrip.V7_49.B_to_A []
#rt_overlap RoundTrip.V7_49.A_to_B []

end RoundTrip.V7_49
