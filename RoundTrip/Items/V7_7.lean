import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_7

/-! Round trip for V7_7 (Definition 7.5: the induced degeneracy index `d_{|X|}`).

The listed declarations are the definition `EpGroupoid.degIndexOrbit` and the theorem
`EpGroupoid.degIndexOrbit_π`; `A` is the type of the latter, universe at `0`.

* `A → B`: (b) is `A`; the presupposition (a) (`d_X` is constant on isomorphism classes) follows
  from `A` too: `x ∼ x'` gives `π x = π x'`, so `d_X(x) = d_{|X|}(π x) = d_{|X|}(π x') = d_X(x')`.
  (That `degIndexOrbit` is well defined at all is the proof field of its `Quotient.lift`.)
* `B → A`: (b) is `A`. -/

namespace RoundTrip.V7_7
open Polyfold

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.degIndexOrbit_π.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.degIndexOrbit_π.{0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  refine ⟨fun x x' hxx' => ?_, fun x => hA X x⟩
  have hπ : X.π x = X.π x' := Quotient.sound hxx'
  rw [← hA X x, ← hA X x', hπ]

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X x
  exact (hB Obj Mor X).2 x

#rt_check RoundTrip.V7_7.A_to_B [Polyfold.EpGroupoid.degIndexOrbit_π]
#rt_check RoundTrip.V7_7.B_to_A [Polyfold.EpGroupoid.degIndexOrbit_π]
#rt_overlap RoundTrip.V7_7.B_to_A [Polyfold.EpGroupoid.degIndexOrbit_π]

end RoundTrip.V7_7
