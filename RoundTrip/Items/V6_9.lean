import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_9

/-! Round trip for V6_9 (Definition 6.8: orientations of a Fredholm operator).

The listed declarations are the definition `Polyfold.FredholmOrientation` and the theorems
`nonempty_fredholmOrientation`, `exists_two_fredholmOrientation`, so `A` (universes at `0`) is: a
Fredholm operator (Mathlib's `IsFredholm`, normed spaces) has an orientation, and has exactly two.
B is the definitional reading of Definition 6.8: for Banach spaces and textbook-Fredholm `T`,
`FredholmOrientation T = Module.Ray ℝ (λ(ker T) ⊗ λ*(coker T))`.

* The definitions agree on the nose: `B_holds` is `rfl` (`FredholmOrientation T` is the
  abbreviation `Module.Ray ℝ (fredholmDet T)`, `fredholmDet T = linDet ↑T` is literally B's
  `detB T`).  Hence `A ⇒ B` is vacuous (`B_holds`, hypothesis unused).
* `B ⇒ A` is also vacuous: B, a type equality, carries no information on the number of rays; A is
  proved outright (`A_outright`) from `finrank_fredholmDet` (not banned here) and the fact that a
  real line has a ray and exactly two (`rays_of_line`), without the two banned theorems.
-/

namespace RoundTrip.V6_9
open Polyfold Module

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.nonempty_fredholmOrientation.{0, 0} ∧
    type_of% @Polyfold.exists_two_fredholmOrientation.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.nonempty_fredholmOrientation.{0, 0}, @Polyfold.exists_two_fredholmOrientation.{0, 0}⟩

/-- The definitional comparison: the project's orientations of `T` are B's rays of `det(T)`. -/
theorem B_holds : B := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- A real line has a ray, and exactly two. -/
theorem rays_of_line {L : Type} [AddCommGroup L] [Module ℝ L] (h1 : finrank ℝ L = 1) :
    Nonempty (Module.Ray ℝ L) ∧
      ∃ o₁ o₂ : Module.Ray ℝ L, o₁ ≠ o₂ ∧ ∀ o : Module.Ray ℝ L, o = o₁ ∨ o = o₂ := by
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h1
  refine ⟨⟨rayOfNeZero ℝ v hv⟩, rayOfNeZero ℝ v hv, -rayOfNeZero ℝ v hv,
    Module.Ray.ne_neg_self _, fun o => ?_⟩
  induction o using Module.Ray.ind with
  | h w hw =>
    obtain ⟨c, rfl⟩ := hall w
    rcases lt_or_gt_of_ne (left_ne_zero_of_smul hw) with hc | hc
    · right
      rw [neg_rayOfNeZero, ray_eq_iff]
      have : c • v = (-c) • (-v) := by rw [neg_smul, smul_neg, neg_neg]
      rw [this]
      exact SameRay.sameRay_pos_smul_left _ (neg_pos.2 hc)
    · left
      rw [ray_eq_iff]
      exact SameRay.sameRay_pos_smul_left _ hc

/-- A, proved without the two banned theorems. -/
theorem A_outright : A := by
  refine ⟨?_, ?_⟩
  · intro E F _ _ _ _ T hT
    exact (rays_of_line (L := fredholmDet T) (finrank_fredholmDet hT)).1
  · intro E F _ _ _ _ T hT
    exact (rays_of_line (L := fredholmDet T) (finrank_fredholmDet hT)).2

/-- `A ⇒ B` (vacuous: `B` holds by `rfl`). -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B ⇒ A` (vacuous: `A` is proved outright). -/
theorem B_to_A : B → A := fun _ => A_outright

#rt_check RoundTrip.V6_9.A_to_B [Polyfold.nonempty_fredholmOrientation,
  Polyfold.exists_two_fredholmOrientation]
#rt_check RoundTrip.V6_9.B_to_A [Polyfold.nonempty_fredholmOrientation,
  Polyfold.exists_two_fredholmOrientation]
#rt_overlap RoundTrip.V6_9.B_to_A [Polyfold.nonempty_fredholmOrientation,
  Polyfold.exists_two_fredholmOrientation]
#rt_check RoundTrip.V6_9.B_holds [Polyfold.nonempty_fredholmOrientation,
  Polyfold.exists_two_fredholmOrientation]

end RoundTrip.V6_9
