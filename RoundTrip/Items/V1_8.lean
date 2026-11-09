import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_8

/-! Round trip for V1_8 (Proposition 1.9: sc-Fredholm operators are regularizing).

`A` is the conjunction of the types of `Polyfold.proposition_1_1_10`,
`Polyfold.IsScFredholm.isRegularizing` and `Polyfold.isScFredholm_iff` (refresh 2026-11-02: the last
two were added to the row, with the vocabulary `ScOperator.IsRegularizing`).  No universe
parameters (`ScBanach` lives in `Type`).  `proposition_1_1_10` quantifies over the *data*
`s : ScFredholmSplitting T`, `B` over the proposition `IsScFredholmB T` (an existential over the
same four submodules with the same seven conditions), so the two are repackagings of each other;
`IsScFredholm.isRegularizing` is the same statement with `IsRegularizing` folded.

`isScFredholm_iff` (sc-Fredholm ⟺ Fredholm on level `0` and regularizing) goes beyond `B`: its
`→` direction is `B` plus the level-`0` Fredholm property of a splitting
(`ScFredholmSplitting.isFredholm`, a project lemma); its `←` direction is the criterion of §1.4.1,
which `B` does not speak about; `B_to_A` takes it from the project lemma
`isScFredholm_of_isRegularizing` (not banned for this item; it is V1_9's statement), so that part
of `A` is not derived from `B`. -/

namespace RoundTrip.V1_8
open Polyfold

/-- The blind `IsScFredholmB` is the project's `IsScFredholm` (same fields, repackaged). -/
theorem isScFredholmB_iff {E F : ScBanach} (T : ScOperator E F) :
    IsScFredholmB T ↔ IsScFredholm T := by
  constructor
  · rintro ⟨K, X, C, Y, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨K, X, C, Y, h1, h2, h3, h4, h5, h6, h7⟩⟩
  · rintro ⟨s⟩
    exact ⟨s.K, s.X, s.C, s.Y, s.splitE, s.splitF, s.ker_eq, s.finite_K, s.finite_C, s.range_eq,
      s.bijOn⟩

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_1_1_10) ∧ (type_of% @Polyfold.IsScFredholm.isRegularizing) ∧
    (type_of% @Polyfold.isScFredholm_iff)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_1_1_10, @Polyfold.IsScFredholm.isRegularizing, @Polyfold.isScFredholm_iff⟩

theorem A_to_B : A → B := by
  intro hA E F T hT m e he
  obtain ⟨s⟩ := (isScFredholmB_iff T).1 hT
  exact hA.1 s he

theorem B_to_A : B → A := by
  intro hB
  have hreg : ∀ {E F : ScBanach} {T : ScOperator E F}, IsScFredholm T → T.IsRegularizing :=
    fun {E F T} hT m e he => hB E F T ((isScFredholmB_iff T).2 hT) m e he
  refine ⟨fun {E F T} s e m he => hB E F T ((isScFredholmB_iff T).2 ⟨s⟩) m e he,
    fun hT => hreg hT, fun {E F T} => ⟨fun hT => ⟨?_, hreg hT⟩,
      fun h => isScFredholm_of_isRegularizing h.1 h.2⟩⟩
  obtain ⟨s⟩ := hT
  exact s.isFredholm 0

#rt_check RoundTrip.V1_8.A_to_B [Polyfold.proposition_1_1_10, Polyfold.IsScFredholm.isRegularizing,
  Polyfold.isScFredholm_iff]
#rt_check RoundTrip.V1_8.B_to_A [Polyfold.proposition_1_1_10, Polyfold.IsScFredholm.isRegularizing,
  Polyfold.isScFredholm_iff]
#rt_overlap RoundTrip.V1_8.B_to_A [Polyfold.proposition_1_1_10, Polyfold.IsScFredholm.isRegularizing,
  Polyfold.isScFredholm_iff]

end RoundTrip.V1_8
