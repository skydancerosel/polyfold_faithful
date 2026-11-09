import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_31

/-! Round trip for V11_31 (2021 §11.5, pp. 547–548: the multisection functors along a strong
bundle equivalence, Lemma 11.5.2).

The item lists the definitions `IsWFunctor`, `pullMult`, `pushMult` (vocabulary) and eight
theorems; `A` is the conjunction of their types, all universes at `0` (`α : Type`):
`isWFunctor_const`, `IsWFunctor.eq_of_π_eq`, `IsWFunctor.pullMult`, `π_obj_choose`,
`pushMult_eq` (independence of the choices), `lemma_11_5_2` (`Φ_*Λ` is a functor),
`pullMult_pushMult`, `pushMult_pullMult`.  All of them are about arbitrary functors
`Λ : W → α` (`IsWFunctor`), with no local section structure.

`B` (for an sc⁺-multisection `Λ : W → ℚ`, the blind author's `IsScPlusMultisectionB`: values
`≥ 0`, a functor, and locally `Λ(w) = ∑_{i : sᵢ(P w) = w} σᵢ` for local sc⁺-sections `sᵢ`):
(1) every `w'` has `w` with `Φ(w) ≅ w'`; (2) `Φ_*Λ(w') = Λ(w)` for every such `w`; (3) `Φ_*Λ` is
again an sc⁺-multisection.

* `A → B` fails at one point: the local section structure of `Φ_*Λ` in (3).  `A` has no
  statement about local sc⁺-sections (the project's header: "the local section structures of
  sc⁺-multisections (Definition 13.2.1 is not in the repository ...)" are not formalized); the
  transport needs `Φ` as a local strong bundle isomorphism at level `[1]` and the transport of
  sections along `ψ̂`.  Everything else is proved from `A`: `A_to_BFunctorPart` gives (1), (2)
  and the first two conjuncts of (3) (`Φ_*Λ ≥ 0` and `Φ_*Λ` a functor, from `lemma_11_5_2`).
* `B → A` fails: every conjunct of `A` is about arbitrary functors into an arbitrary `α`, while
  `B` only speaks about sc⁺-multisections into `ℚ` (which do not separate orbits, so (2) for
  them says nothing about a general functor).  `A`'s conjuncts are short and could be re-proved
  outright, but that would not use `B` (vacuous), so no `B_to_A` is given. -/

namespace RoundTrip.V11_31
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.isWFunctor_const.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.IsWFunctor.eq_of_π_eq.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.IsWFunctor.pullMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.π_obj_choose.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pushMult_eq.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.lemma_11_5_2.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.pullMult_pushMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.pushMult_pullMult.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.isWFunctor_const.{0, 0},
    @Polyfold.SBLocalization.IsWFunctor.eq_of_π_eq.{0, 0},
    @Polyfold.SBLocalization.IsWFunctor.pullMult.{0, 0},
    @Polyfold.SBLocalization.π_obj_choose.{0},
    @Polyfold.SBLocalization.pushMult_eq.{0, 0},
    @Polyfold.SBLocalization.lemma_11_5_2.{0, 0},
    @Polyfold.SBLocalization.pullMult_pushMult.{0, 0},
    @Polyfold.SBLocalization.pushMult_pullMult.{0, 0}⟩

/-! ### `A → B` without the local section structure -/

/-- `B` with the local section structure of `Φ_*Λ` dropped from the conclusion (the hypothesis
is still that `Λ` is an sc⁺-multisection). -/
def BFunctorPart : Prop :=
  ∀ (A A' : SEP.{0}) (Φ : A ⟶ A') (hΦ : SEP.equivalences Φ) (Λ : A.W → ℚ),
    IsScPlusMultisectionB A Λ →
      (∀ w' : A'.W, ∃ w : A.W, A'.E.toEpGroupoid.Isomorphic (Φ.Φ.obj w) w') ∧
      (∀ (w : A.W) (w' : A'.W), A'.E.toEpGroupoid.Isomorphic (Φ.Φ.obj w) w' →
        pushMult Φ hΦ Λ w' = Λ w) ∧
      (∀ w', 0 ≤ pushMult Φ hΦ Λ w') ∧ IsWFunctor A' (pushMult Φ hΦ Λ)

theorem A_to_BFunctorPart : A → BFunctorPart := by
  rintro ⟨-, -, -, -, hpush, hlemma, -, -⟩ A A' Φ hΦ Λ ⟨hnn, hΛ, -⟩
  refine ⟨fun w' => ?_, fun w w' h => hpush hΦ hΛ ((GroupoidStr.π_eq_π_iff _).2 h),
    fun w' => hnn _, hlemma hΦ hΛ⟩
  obtain ⟨w, ψ, hs, ht⟩ := (sbe hΦ).isEquivalence.exists_iso w'
  exact ⟨w, ψ, hs, ht⟩

open Classical in
/-- `B` is exactly `BFunctorPart` plus the local section structure of `Φ_*Λ`. -/
theorem BFunctorPart_and_local_iff_B :
    (BFunctorPart ∧ ∀ (A A' : SEP.{0}) (Φ : A ⟶ A') (hΦ : SEP.equivalences Φ) (Λ : A.W → ℚ),
      IsScPlusMultisectionB A Λ →
      ∀ x : A'.Obj, ∃ U : Set A'.Obj, IsOpen U ∧ x ∈ U ∧
        ∃ (k : ℕ) (s : Fin k → A'.Obj → A'.W) (σ : Fin k → ℚ),
          (∀ i, IsLocalScPlusSectionB A' U (s i)) ∧ (∀ i, 0 < σ i) ∧ ∑ i, σ i = 1 ∧
          ∀ w : A'.W, A'.P w ∈ U →
            pushMult Φ hΦ Λ w = ∑ i with s i (A'.P w) = w, σ i) ↔ B := by
  constructor
  · rintro ⟨hF, hL⟩ A A' Φ hΦ Λ hΛ
    obtain ⟨h1, h2, h3, h4⟩ := hF A A' Φ hΦ Λ hΛ
    exact ⟨h1, h2, h3, h4, hL A A' Φ hΦ Λ hΛ⟩
  · intro hB
    exact ⟨fun A A' Φ hΦ Λ hΛ => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hB A A' Φ hΦ Λ hΛ
      exact ⟨h1, h2, h3, h4⟩, fun A A' Φ hΦ Λ hΛ => (hB A A' Φ hΦ Λ hΛ).2.2.2.2⟩

#rt_check RoundTrip.V11_31.A_to_BFunctorPart [Polyfold.SBLocalization.isWFunctor_const,
  Polyfold.SBLocalization.IsWFunctor.eq_of_π_eq, Polyfold.SBLocalization.IsWFunctor.pullMult,
  Polyfold.SBLocalization.π_obj_choose, Polyfold.SBLocalization.pushMult_eq,
  Polyfold.SBLocalization.lemma_11_5_2, Polyfold.SBLocalization.pullMult_pushMult,
  Polyfold.SBLocalization.pushMult_pullMult]
#rt_check RoundTrip.V11_31.BFunctorPart_and_local_iff_B [Polyfold.SBLocalization.isWFunctor_const,
  Polyfold.SBLocalization.IsWFunctor.eq_of_π_eq, Polyfold.SBLocalization.IsWFunctor.pullMult,
  Polyfold.SBLocalization.π_obj_choose, Polyfold.SBLocalization.pushMult_eq,
  Polyfold.SBLocalization.lemma_11_5_2, Polyfold.SBLocalization.pullMult_pushMult,
  Polyfold.SBLocalization.pushMult_pullMult]

end RoundTrip.V11_31
