import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_49

/-! Round trip for V10_49 (2021 Definition 10.3.20, p. 494: `EP_reg` and `EP_reg(E⁻¹)`).

The item lists only definitions: `EPLocalization.EPreg`, `EPLocalization.EPLocReg` (Mathlib's
`ObjectProperty.FullSubcategory` of `EP` resp. `EPLoc` on the objects with (LR)) and the
witnesses `Examples.pointReg`, `Examples.pointLocReg`.  So `A = True`; the content of the audit
is the comparison of the project's definitions with B's notion "full subcategory on the objects
with (LR)", which is `B` itself, proved outright here (`B_holds`).

`B_holds`: for both categories the inclusion is Mathlib's `ObjectProperty.ι` (full and faithful
by `full_ι`, `faithful_ι`; on objects `X ↦ X.obj`, injective by `FullSubcategory.ext`; its image
is exactly the objects with (LR), by the field `property`).  Universes: `B` is stated at `0`
(`EP.{0}`, `EPLoc.{0}`; morphisms in `Type` resp. `Type 1`), the project's definitions are
universe-polymorphic. -/

namespace RoundTrip.V10_49
open Polyfold CategoryTheory

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- Mathlib's full subcategory on `p` is the full subcategory in the sense of `B`. -/
theorem isFullSubcatOnB_fullSubcategory.{v} {C : Type 1} [Category.{v} C] (p : C → Prop) :
    IsFullSubcatOnB C (ObjectProperty.FullSubcategory p) p := by
  refine ⟨ObjectProperty.ι p, inferInstance, inferInstance, ?_, fun c => ⟨?_, ?_⟩⟩
  · intro X Y h
    exact ObjectProperty.FullSubcategory.ext h
  · rintro ⟨d, rfl⟩
    exact d.property
  · intro hc
    exact ⟨⟨c, hc⟩, rfl⟩

theorem B_holds : B :=
  ⟨isFullSubcatOnB_fullSubcategory (C := EP.{0}) fun A => A.X.IsLR,
    isFullSubcatOnB_fullSubcategory (C := EPLocalization.EPLoc.{0}) fun A => A.toEP.X.IsLR⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V10_49.A_to_B []
#rt_check RoundTrip.V10_49.B_to_A []
#rt_overlap RoundTrip.V10_49.B_to_A []
#rt_check RoundTrip.V10_49.B_holds []

end RoundTrip.V10_49
