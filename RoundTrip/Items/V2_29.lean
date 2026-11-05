import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_29

/-! Round trip for V2_29 (Definition 2.25: the boundary `∂X`).

`A` is the conjunction of the types of the listed theorems
`Polyfold.MPolyfold.isWithoutBoundary_iff`, `isClosed_boundary`, `isOpen_interior`,
`isClosed_corners` (universe `0`) and `Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff`
(universes `0, 0`).  `boundary`, `IsWithoutBoundary` and `corners` are definitions (vocabulary).

The definitions agree with B by `rfl`: `P.boundary = {x | 1 ≤ P.degIndex x}` and
`P.IsWithoutBoundary = ∀ x, P.degIndex x = 0` are literally the project's definitions.  So `A → B`
is proved outright (A unused).

`B → A`: `isWithoutBoundary_iff` and `mem_boundary_iff` are derived through B's description of
`∂X` (with Proposition 2.24, a project lemma outside this item, for the latter);
`isClosed_boundary` from B's description plus the project's `isClosed_setOf_le_degIndex`
(Lemma 2.23, item V2_27).  `isOpen_interior` (`{d_X = 0}` open) and `isClosed_corners`
(`{d_X ≥ 2}` closed; `corners` is not in B) are properties of `d_X`, not of the definition; they are
proved from `isOpen_setOf_degIndex_lt` / `isClosed_setOf_le_degIndex` without B. -/

namespace RoundTrip.V2_29
open Polyfold Set MPolyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.isWithoutBoundary_iff.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isClosed_boundary.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isOpen_interior.{0}) ∧
    (type_of% @Polyfold.MPolyfold.isClosed_corners.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isWithoutBoundary_iff.{0}, @Polyfold.MPolyfold.isClosed_boundary.{0},
    @Polyfold.MPolyfold.isOpen_interior.{0}, @Polyfold.MPolyfold.isClosed_corners.{0},
    @Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff.{0, 0}⟩

/-- `A → B`: both conjuncts of B are the project's definitions (`rfl`); A is not used. -/
theorem A_to_B : A → B := by
  intro _ X _ _ _ P
  exact ⟨rfl, Iff.rfl⟩

/-- `B → A`. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ P
    rw [(hB X P).2, (hB X P).1]
    constructor
    · intro h
      exact eq_empty_iff_forall_notMem.2 fun x hx => by
        have h1 : 1 ≤ P.degIndex x := hx
        rw [h x] at h1
        exact absurd h1 (by norm_num)
    · intro h x
      by_contra hx
      exact eq_empty_iff_forall_notMem.1 h x (Nat.one_le_iff_ne_zero.2 hx)
  · intro X _ _ _ P
    rw [(hB X P).1]
    exact P.isClosed_setOf_le_degIndex 1
  · intro X _ _ _ P
    have : {x | P.degIndex x = 0} = {x | P.degIndex x < 1} := by
      ext x; simp
    rw [this]
    exact P.isOpen_setOf_degIndex_lt 1
  · intro X _ _ _ P
    exact P.isClosed_setOf_le_degIndex 2
  · intro X _ _ _ Y _ _ _ Q P f g U V h x hx
    rw [(hB X P).1, (hB Y Q).1]
    change 1 ≤ P.degIndex x ↔ 1 ≤ Q.degIndex (f x)
    rw [proposition_2_24 h hx]

#rt_check RoundTrip.V2_29.A_to_B [Polyfold.MPolyfold.isWithoutBoundary_iff,
  Polyfold.MPolyfold.isClosed_boundary, Polyfold.MPolyfold.isOpen_interior,
  Polyfold.MPolyfold.isClosed_corners, Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff]
#rt_check RoundTrip.V2_29.B_to_A [Polyfold.MPolyfold.isWithoutBoundary_iff,
  Polyfold.MPolyfold.isClosed_boundary, Polyfold.MPolyfold.isOpen_interior,
  Polyfold.MPolyfold.isClosed_corners, Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff]
#rt_overlap RoundTrip.V2_29.B_to_A [Polyfold.MPolyfold.isWithoutBoundary_iff,
  Polyfold.MPolyfold.isClosed_boundary, Polyfold.MPolyfold.isOpen_interior,
  Polyfold.MPolyfold.isClosed_corners, Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff]

end RoundTrip.V2_29
