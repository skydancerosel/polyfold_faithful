import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_55

/-! Round trip for V10_55 (2021 Definition 10.5.1, p. 506; 2017: Definition 10.14, p. 366: the
category `SEP(F⁻¹)`).

The item lists the definitions `SEPLoc`, `SEPLoc.idHom`, `SEPLoc.localizationPrefunctor`,
`SDiagram.id`, `SDiagram.ofHom`, the instance `SEPLoc.category`, `SEPLoc.homMk` and
`SEPLoc.localizationFunctor` (vocabulary), and seven theorems; `A` is the conjunction of their
types, universes at `0`: `localizationPrefunctor_map_id`, `homMk_comp`, `id_eq`,
`homMk_eq_homMk_iff` (`[D] = [D']` iff `D`, `D'` have a common refinement: the transitivity of
the equivalence, strong bundle Lemma 10.3.4), `homMk_surjective`,
`localizationFunctor_toPrefunctor`, `isInvertedBy_localizationFunctor`.

`B` says: (1) `SEPLoc.toSEP` is a bijection (objects), (2) the hom-type `⟨A⟩ ⟶ ⟨A'⟩` is
`GenSBMap A A'` (morphisms), (3) the class of a diagram `W ←1 W →1 W` is the identity.

* `A_to_B`: (1), (2) hold by the definitions (one-field structure; `rfl`); (3) is `id_eq` of `A`
  after `subst` of the middle and the two legs.
* `B_to_A`: `id_eq` comes from `B` (3); `homMk_comp`, `localizationPrefunctor_map_id`,
  `localizationFunctor_toPrefunctor` are `rfl`; the three remaining conjuncts are not
  consequences of `B` (which has no composition) and are re-proved outright from non-item
  project lemmas: `homMk_eq_homMk_iff` from `SDiagram.cls_eq_cls_iff`, `homMk_surjective` from
  `SDiagram.cls_surjective`, and `isInvertedBy_localizationFunctor` with the explicit inverse
  `[W' ←Ψ W →1 W]` (`SDiagram.equiv_comp_symm`, `equiv_symm_comp`); not through
  `SEPLoc.theorem_10_3_10`, whose proof uses the banned `homMk_eq_homMk_iff`. -/

namespace RoundTrip.V10_55
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.homMk_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.id_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.homMk_surjective.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id.{0},
    @Polyfold.SBLocalization.SEPLoc.homMk_comp.{0},
    @Polyfold.SBLocalization.SEPLoc.id_eq.{0},
    @Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff.{0},
    @Polyfold.SBLocalization.SEPLoc.homMk_surjective.{0},
    @Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor.{0},
    @Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, hid, -, -, -, -⟩
  refine ⟨⟨fun a b h => ?_, fun A => ⟨⟨A⟩, rfl⟩⟩, fun A A' => rfl, ?_⟩
  · cases a; cases b; cases h; rfl
  · intro A D hB hΦ hΨ
    obtain ⟨C, Φ, hΦe, Ψ⟩ := D
    dsimp only at hB hΦ hΨ
    subst hB
    obtain rfl := eq_of_heq hΦ
    obtain rfl := eq_of_heq hΨ
    exact (hid C).symm

theorem B_to_A : B → A := by
  rintro ⟨-, -, hid⟩
  refine ⟨fun A => rfl, fun D E => rfl,
    fun A => (hid A (SBLocalization.SDiagram.id A) rfl HEq.rfl HEq.rfl).symm,
    fun {A A' D D'} => SBLocalization.SDiagram.cls_eq_cls_iff,
    fun {X Y} f => SBLocalization.SDiagram.cls_surjective f, rfl, ?_⟩
  intro A A' Ψ hΨ
  exact ⟨⟨SBLocalization.SEPLoc.homMk ((SBLocalization.SDiagram.ofHom Ψ).symm hΨ),
    SBLocalization.SDiagram.cls_eq_cls_of_equiv
      ((SBLocalization.SDiagram.ofHom Ψ).equiv_comp_symm hΨ),
    SBLocalization.SDiagram.cls_eq_cls_of_equiv
      ((SBLocalization.SDiagram.ofHom Ψ).equiv_symm_comp hΨ)⟩⟩

/-! ### Harness checks

The statement of `isInvertedBy_localizationFunctor` (and of `localizationFunctor_toPrefunctor`)
mentions the definition `localizationFunctor`, whose `map_comp` proof field
(`localizationFunctor._proof_2`) is proved with the banned `homMk_eq_homMk_iff`.  So every term
mentioning `A` reaches that theorem, and plain `#rt_check` fails on both directions (recorded
with `#guard_msgs`); `#rt_check_soft` passes, listing it as reached only through that proof
field. -/

/--
error: rt_check FAIL: RoundTrip.V10_55.A_to_B uses [Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_55.A_to_B [Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id,
  Polyfold.SBLocalization.SEPLoc.homMk_comp, Polyfold.SBLocalization.SEPLoc.id_eq,
  Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff,
  Polyfold.SBLocalization.SEPLoc.homMk_surjective,
  Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor,
  Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor]

/--
error: rt_check FAIL: RoundTrip.V10_55.B_to_A uses [Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_55.B_to_A [Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id,
  Polyfold.SBLocalization.SEPLoc.homMk_comp, Polyfold.SBLocalization.SEPLoc.id_eq,
  Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff,
  Polyfold.SBLocalization.SEPLoc.homMk_surjective,
  Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor,
  Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor]

#rt_check_soft RoundTrip.V10_55.A_to_B [Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id,
  Polyfold.SBLocalization.SEPLoc.homMk_comp, Polyfold.SBLocalization.SEPLoc.id_eq,
  Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff,
  Polyfold.SBLocalization.SEPLoc.homMk_surjective,
  Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor,
  Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor]
#rt_check_soft RoundTrip.V10_55.B_to_A [Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id,
  Polyfold.SBLocalization.SEPLoc.homMk_comp, Polyfold.SBLocalization.SEPLoc.id_eq,
  Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff,
  Polyfold.SBLocalization.SEPLoc.homMk_surjective,
  Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor,
  Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor]
#rt_overlap RoundTrip.V10_55.B_to_A [Polyfold.SBLocalization.SEPLoc.localizationPrefunctor_map_id,
  Polyfold.SBLocalization.SEPLoc.homMk_comp, Polyfold.SBLocalization.SEPLoc.id_eq,
  Polyfold.SBLocalization.SEPLoc.homMk_eq_homMk_iff,
  Polyfold.SBLocalization.SEPLoc.homMk_surjective,
  Polyfold.SBLocalization.SEPLoc.localizationFunctor_toPrefunctor,
  Polyfold.SBLocalization.SEPLoc.isInvertedBy_localizationFunctor]

end RoundTrip.V10_55
