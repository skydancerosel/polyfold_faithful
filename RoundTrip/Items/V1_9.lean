import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_9

/-! Round trip for V1_9 (Proposition 1.10, compact perturbation of sc-Fredholm operators).

`A` is the conjunction of the types of `Polyfold.proposition_1_10`,
`Polyfold.ScPlus.regularizing_add`, `Polyfold.isScFredholm_of_isRegularizing` and
`Polyfold.isScFredholm_of_isRegularizing_index` (refresh 2026-11-02: the last two were added to the
row).  None has universe parameters (`ScBanach` lives in `Type`).

* `A → B` (proved): `proposition_1_10` is `B` after repackaging `IsScFredholmB`.
* `B → A` (failed): `B` still gives `proposition_1_10` and `regularizing_add` (`B_to_A_old` below:
  `T + S` is sc-Fredholm, then Proposition 1.9), but the new conjuncts are the criterion of §1.4.1
  (an sc-operator that is Fredholm on level `0` and regularizing is sc-Fredholm, with the level-`0`
  index on every level).  `B` (sc-Fredholm + sc⁺ is sc-Fredholm) says nothing about operators not
  already known to be sc-Fredholm, and the criterion can only be had by redoing the construction of
  the splittings (Proposition 1.6 for the kernel, density of smooth points of the range, a smooth
  complement of the range), i.e. the project's argument; every project lemma that yields it goes
  through the banned `isScFredholm_of_isRegularizing`. -/

namespace RoundTrip.V1_9
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
  (type_of% @Polyfold.proposition_1_10) ∧ (type_of% @Polyfold.ScPlus.regularizing_add) ∧
    (type_of% @Polyfold.isScFredholm_of_isRegularizing) ∧
    (type_of% @Polyfold.isScFredholm_of_isRegularizing_index)

theorem A_holds : A := ⟨@Polyfold.proposition_1_10, @Polyfold.ScPlus.regularizing_add,
  @Polyfold.isScFredholm_of_isRegularizing, @Polyfold.isScFredholm_of_isRegularizing_index⟩

theorem A_to_B : A → B := by
  intro hA E F T S hT
  exact (isScFredholmB_iff _).2 (hA.1 ((isScFredholmB_iff T).1 hT) S)

/-- The part of `A` that `B` gives (the audit's former `A`): Proposition 1.10 is `B` itself; the
bootstrap lemma `regularizing_add` follows from `B` (`T + S` is sc-Fredholm) and Proposition 1.9
(sc-Fredholm operators are regularizing) applied to `T + S`.  The criterion conjuncts
`isScFredholm_of_isRegularizing(_index)` are not derived (see the header): no `B_to_A`. -/
theorem B_to_A_old : B →
    (type_of% @Polyfold.proposition_1_10) ∧ (type_of% @Polyfold.ScPlus.regularizing_add) := by
  intro hB
  refine ⟨fun {E F T} hT S => (isScFredholmB_iff _).1 (hB E F T S ((isScFredholmB_iff T).2 hT)), ?_⟩
  intro E F T s S e m he
  obtain ⟨s'⟩ := (isScFredholmB_iff _).1 (hB E F T S ((isScFredholmB_iff T).2 ⟨s⟩))
  exact proposition_1_9 s' he

#rt_check RoundTrip.V1_9.A_to_B [Polyfold.proposition_1_10, Polyfold.ScPlus.regularizing_add,
  Polyfold.isScFredholm_of_isRegularizing, Polyfold.isScFredholm_of_isRegularizing_index]
#rt_check RoundTrip.V1_9.B_to_A_old [Polyfold.proposition_1_10, Polyfold.ScPlus.regularizing_add,
  Polyfold.isScFredholm_of_isRegularizing, Polyfold.isScFredholm_of_isRegularizing_index]
#rt_overlap RoundTrip.V1_9.B_to_A_old [Polyfold.proposition_1_10, Polyfold.ScPlus.regularizing_add,
  Polyfold.isScFredholm_of_isRegularizing, Polyfold.isScFredholm_of_isRegularizing_index]

end RoundTrip.V1_9
