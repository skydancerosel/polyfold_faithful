import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_10

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_2_2_preprint, theorem_5_2_2_iff and B's Bd.IsScFredholmSection now all denote the germ reading of
Definition 3.14 (A and B moved together); theorem_5_2_2_preprint still has no tameness hypothesis and its
proof uses the germ data only at the zeros. Result unchanged: A ⇒ B by instantiation (B's
PX.IsTame unused), B ⇒ A fails because B says nothing about non-tame X.
-/

namespace RoundTrip.V5_10
open Polyfold

/-- The project's statement (Theorem 5.5 and its second sentence), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_5_2_2_preprint.{0, 0} ∧ type_of% @Polyfold.theorem_5_2_2_iff.{0, 0}

theorem A_holds : A := ⟨@Polyfold.theorem_5_2_2_preprint.{0, 0}, @Polyfold.theorem_5_2_2_iff.{0, 0}⟩

/-- `A ⇒ B`: B is A with the extra (unused) hypothesis `PX.IsTame`. -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd _hT
  exact ⟨fun f hf hS => hA.1 hf hS, fun f hf => hA.2 hf⟩

/-! `B ⇒ A` is not proved: B only speaks about tame `X` (`PX.IsTame`), A about every M-polyfold.
Obtaining A from B would mean re-proving Theorem 5.5 without tameness. -/

#rt_check RoundTrip.V5_10.A_to_B [Polyfold.theorem_5_2_2_preprint, Polyfold.theorem_5_2_2_iff]

end RoundTrip.V5_10
