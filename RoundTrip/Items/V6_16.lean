import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_16

namespace RoundTrip.V6_16
open Polyfold

/-- The project's statement (Lemma 6.14 and the existence of a stabilization), universes
instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_6_4_14.{0, 0} ∧ type_of% @Polyfold.exists_surjective_coprod.{0, 0}

theorem A_holds : A := ⟨@Polyfold.lemma_6_4_14.{0, 0}, @Polyfold.exists_surjective_coprod.{0, 0}⟩

/-- `A ⇒ B`: B's `Tphi`, `jS`, `piS`, `clsPhi` are definitionally the project's `T.coprod φ`,
`stabJ`, `stabPi`, `stabClass`; B's hypotheses `IsFredholmOp T` and completeness are unused. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ n T φ _hT hs
  exact hA.1 (T := T) (φ := φ) hs

/-! `B ⇒ A` is not proved, for two genuine reasons.
* A's `lemma_6_4_14` holds for arbitrary normed spaces (no `CompleteSpace`) and an arbitrary bounded
  `T` (no Fredholm hypothesis): the exactness is pure linear algebra.  B only speaks about Fredholm
  `T` between Banach spaces, so it says nothing about the other cases.
* A's second conjunct `exists_surjective_coprod` (for `T` Fredholm some `φ : ℝⁿ → F` makes `T_φ`
  onto: the text's remark introducing `T_φ`) has no counterpart in B, which takes `φ` as given. -/

#rt_check RoundTrip.V6_16.A_to_B [Polyfold.lemma_6_4_14, Polyfold.exists_surjective_coprod]

end RoundTrip.V6_16
