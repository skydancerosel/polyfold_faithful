import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_50

/-! Round trip for V10_50 (2021 Theorem 10.3.21, p. 495: (LR), (LUC), (SLR), (SLUC), (ZHOU) are
invariant under generalized isomorphisms).

`A` is the conjunction of the types of the two listed theorems, universes at `0`:
`EPLoc.theorem_10_3_21` ((LUC), (SLUC), (ZHOU)) and `EPLoc.theorem_10_3_21_all` (all five).
Both are stated for `X Y : EP` and `f : of X ⟶ of Y`; `B` quantifies over `X Y : EPLoc` and
`f : X ⟶ Y`.  `EPLoc` is a one-field structure around `EP`, so `of X.toEP` and `X` agree by
structure eta and the two quantifications match definitionally.

* `A_to_B`: `theorem_10_3_21_all` at `X.toEP`, `Y.toEP`.
* `B_to_A`: `B` at `of X`, `of Y`; `theorem_10_3_21` is the (LUC), (SLUC), (ZHOU) part of it. -/

namespace RoundTrip.V10_50
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_21.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.theorem_10_3_21.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hall⟩ X Y f hf
  exact hall (X := X.toEP) (Y := Y.toEP) (f := f) hf

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X Y f} hf => ?_, fun {X Y f} hf => ?_⟩
  · obtain ⟨-, h2, -, h4, h5⟩ := hB (EPLocalization.EPLoc.of X) (EPLocalization.EPLoc.of Y) f hf
    exact ⟨h2, h4, h5⟩
  · exact hB (EPLocalization.EPLoc.of X) (EPLocalization.EPLoc.of Y) f hf

#rt_check RoundTrip.V10_50.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_10_3_21,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all]
#rt_check RoundTrip.V10_50.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_21,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all]
#rt_overlap RoundTrip.V10_50.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_21,
  Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all]

end RoundTrip.V10_50
