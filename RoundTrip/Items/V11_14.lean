import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_14

/-! Round trip for V11_14 (Definition 11.3.1 of the 2021 text, p. 535; 2017: Definition 11.4:
pull-back and push-forward of functors `Θ` along an equivalence).

The item lists the definitions `EpFunctor.pullbackTheta`, `EpFunctor.pushforwardTheta`
(vocabulary) and four theorems; `A` is the conjunction of their types, universes at `0`:
`pullbackTheta_apply` (`F^*Θ' x = Θ'(F x)`, `rfl`), `pushforwardTheta_of_not_exists` (the junk
value `0` where no `F(x)` is isomorphic to `y`), `exists_isomorphic_of_pushforwardTheta_ne_zero`
(its contrapositive) and `pushforwardTheta_nonneg` (`F_*` preserves `0 ≤ Θ`).  All four are
stated for an arbitrary sc-smooth functor `F` and arbitrary `Θ`.

`B` says that on the text's domain (an equivalence `F`, functors `Θ : X → ℚ⁺`) the project's
`pullbackTheta` is `Θ' ∘ F` and `pushforwardTheta Θ y = Θ x` for **every** `x` with a morphism
`F(x) → y`.

* `B_holds`: `B` is true outright.  The pull-back is `rfl`; the push-forward is the non-item
  project lemma `pushforwardTheta_eq` (well-definedness, Lemma 11.3.2 (1), from fullness).
* `A_to_B`: the pull-back part from `A`'s `pullbackTheta_apply`; the push-forward part needs
  well-definedness, which no conjunct of `A` gives (they are about the junk value and the sign):
  `pushforwardTheta_eq`.
* `B_to_A`: vacuous.  `A`'s four conjuncts concern arbitrary functors `F` and arbitrary `Θ`
  (outside the text's domain), where `B` says nothing; they are re-proved outright from the
  definitions. -/

namespace RoundTrip.V11_14
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.pullbackTheta_apply.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_of_not_exists.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_nonneg.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.pullbackTheta_apply.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_of_not_exists.{0, 0},
    @Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_nonneg.{0, 0}⟩

/-- `B` holds outright: the project's definitions are the text's on its domain. -/
theorem B_holds : B := by
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  exact ⟨fun Θ' _ => rfl, fun Θ hΘ y x ψ hs ht =>
    EpFunctor.pushforwardTheta_eq hF.full hΘ.2 ⟨ψ, hs, ht⟩⟩

theorem A_to_B : A → B := by
  rintro ⟨hpull, -, -, -⟩
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  exact ⟨fun Θ' _ => funext fun x => hpull F Θ' x, fun Θ hΘ y x ψ hs ht =>
    EpFunctor.pushforwardTheta_eq hF.full hΘ.2 ⟨ψ, hs, ht⟩⟩

/-- Vacuous: `A` is re-proved outright (its conjuncts lie outside `B`'s domain). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F Θ y h
    rw [EpFunctor.pushforwardTheta, dif_neg h]
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F Θ y h
    by_contra hn
    exact h (by rw [EpFunctor.pushforwardTheta, dif_neg hn])
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F Θ hΘ y
    unfold EpFunctor.pushforwardTheta
    split_ifs
    exacts [hΘ _, le_rfl]

#rt_check RoundTrip.V11_14.B_holds [Polyfold.EpFunctor.pullbackTheta_apply,
  Polyfold.EpFunctor.pushforwardTheta_of_not_exists,
  Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero,
  Polyfold.EpFunctor.pushforwardTheta_nonneg]
#rt_check RoundTrip.V11_14.A_to_B [Polyfold.EpFunctor.pullbackTheta_apply,
  Polyfold.EpFunctor.pushforwardTheta_of_not_exists,
  Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero,
  Polyfold.EpFunctor.pushforwardTheta_nonneg]
#rt_check RoundTrip.V11_14.B_to_A [Polyfold.EpFunctor.pullbackTheta_apply,
  Polyfold.EpFunctor.pushforwardTheta_of_not_exists,
  Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero,
  Polyfold.EpFunctor.pushforwardTheta_nonneg]
#rt_overlap RoundTrip.V11_14.B_to_A [Polyfold.EpFunctor.pullbackTheta_apply,
  Polyfold.EpFunctor.pushforwardTheta_of_not_exists,
  Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero,
  Polyfold.EpFunctor.pushforwardTheta_nonneg]
#rt_overlap RoundTrip.V11_14.A_to_B [Polyfold.EpFunctor.pullbackTheta_apply,
  Polyfold.EpFunctor.pushforwardTheta_of_not_exists,
  Polyfold.EpFunctor.exists_isomorphic_of_pushforwardTheta_ne_zero,
  Polyfold.EpFunctor.pushforwardTheta_nonneg]

end RoundTrip.V11_14
