import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_44

/-! Round trip for V2_44 (Definition 2.39: faces and face-structured M-polyfolds).

`A` is the conjunction of the types of `Polyfold.MPolyfold.IsFace.isClosed` and
`Polyfold.MPolyfold.IsFace.subset_boundary`, universe instantiated at `0`.  `MPolyfold.IsFace` and
`MPolyfold.IsFaceStructured` are definitions (vocabulary).

The definitions agree with B's, on every M-polyfold (tame or not; B assumes tameness, which is
not needed): the project's face is `closure (connectedComponentIn {d_X = 1} x)` for some `x` with
`d_X(x) = 1`, B's is `closure (val '' connectedComponent s)` for some `s` in the subtype
`{d_X = 1}`; Mathlib's `connectedComponentIn_eq_image` identifies the two.  Face-structured is
the same `encard` condition on both sides.  So B holds outright and `A → B` does not use A.

`B → A` is proved only outright (B unused): A's lemmas hold for every M-polyfold (B speaks only
of tame ones) and are immediate from the definition — a closure is closed, and a component of
`{d_X = 1}` lies in `∂X = {d_X ≥ 1}`, which is closed (the project's `isClosed_boundary`,
Lemma 2.23); neither is stated in B. -/

namespace RoundTrip.V2_44
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsFace.isClosed.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsFace.subset_boundary.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsFace.isClosed.{0}, @Polyfold.MPolyfold.IsFace.subset_boundary.{0}⟩

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's faces are B's (for every M-polyfold). -/
theorem isFace_iff (P : MPolyfold X) (F : Set X) : P.IsFace F ↔ IsFaceB P F := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [connectedComponentIn_eq_image (show x ∈ {y | P.degIndex y = 1} from hx)]
    rfl
  · rintro ⟨⟨x, hx⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [connectedComponentIn_eq_image (show x ∈ {y | P.degIndex y = 1} from hx)]
    rfl

theorem isFaceStructured_iff (P : MPolyfold X) : P.IsFaceStructured ↔ IsFaceStructuredB P := by
  simp only [MPolyfold.IsFaceStructured, IsFaceStructuredB, isFace_iff]

end Glue

/-- B holds outright. -/
theorem B_holds : B := fun _ _ _ _ P _ => ⟨isFace_iff P, isFaceStructured_iff P⟩

/-- `A → B`: B holds outright (A unused). -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B → A`, outright (B unused). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro X _ _ _ P F h
    obtain ⟨x, _, rfl⟩ := h
    exact isClosed_closure
  · intro X _ _ _ P F h
    obtain ⟨x, _, rfl⟩ := h
    refine P.isClosed_boundary.closure_subset_iff.2 ?_
    exact (connectedComponentIn_subset _ _).trans fun y hy => le_of_eq hy.symm

#rt_check RoundTrip.V2_44.A_to_B [Polyfold.MPolyfold.IsFace.isClosed,
  Polyfold.MPolyfold.IsFace.subset_boundary]
#rt_check RoundTrip.V2_44.B_to_A [Polyfold.MPolyfold.IsFace.isClosed,
  Polyfold.MPolyfold.IsFace.subset_boundary]
#rt_overlap RoundTrip.V2_44.B_to_A [Polyfold.MPolyfold.IsFace.isClosed,
  Polyfold.MPolyfold.IsFace.subset_boundary]

end RoundTrip.V2_44
