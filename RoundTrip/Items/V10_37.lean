import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_37

/-! Round trip for V10_37 (2021 Definition 10.3.5, p. 486; 2017: Definition 10.6, p. 350:
equivalence of diagrams).

The item lists the definitions `Diagram.Equiv`, `Diagram.setoid` (vocabulary) and four
theorems.  `A` is the conjunction of their types, universes at `0`: `Equiv.refl`,
`Equiv.symm`, `equiv_iff` (`d ≈ d' ↔ Equiv d d'` for the setoid) and the witness
`Examples.equiv_pairToPoint_id` (no universe parameters: `point ←pairToPoint ℤ-pair →pairToPoint
point` is equivalent to `1_point`).

`B` (at universe `0`) says that the project's `Diagram.Equiv` is the blind author's `EquivB`
("have a common refinement", with refinements `IsRefinementB` written out from Definition
10.3.1) and that the classes of the project's setoid are the classes of `EquivB`.

* Glue: `IsRefinementB d' d` is definitionally the project's `Diagram.IsRefinement d' d`
  (`NaturallyEquivalent F G` is `Nonempty (EpNatTrans F G)`), so `EquivB` is definitionally
  `Diagram.Equiv`.
* `A ⇒ B`: the first conjunct is `Iff.rfl`; the second is `Quotient.eq` followed by
  `equiv_iff` from `A`.
* `B ⇒ A`: reflexivity and symmetry are transported from the equality of classes
  (`⟦d⟧ = ⟦d⟧`, `Eq.symm`) through `B`; `equiv_iff` is `Quotient.eq` and `B`; the witness is a
  common refinement (the diagram itself, by `1`, and `1_point`, by `pairToPoint`) turned into
  `Equiv` by `B`.

**Harness note.**  Every term mentioning the setoid `Diagram.setoid` (in `B`'s and in `A`'s
statement) reaches `Equiv.refl` and `Equiv.symm` through its proof field
`Diagram.setoid._proof_1` (the `iseqv` field).  So plain `#rt_check` fails on both directions
for these two names only (recorded with `#guard_msgs`), and `#rt_check_soft` passes.
-/

namespace RoundTrip.V10_37
open Polyfold Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.refl.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Examples.equiv_pairToPoint_id)

theorem A_holds : A :=
  ⟨@Diagram.Equiv.refl.{0}, @Diagram.Equiv.symm.{0}, @Diagram.equiv_iff.{0},
    @Examples.equiv_pairToPoint_id⟩

/-- Glue: the blind author's equivalence is the project's (definitional). -/
theorem equivB_iff {X Y : EP.{0}} (d d' : Diagram X Y) : EquivB d d' ↔ Diagram.Equiv d d' :=
  Iff.rfl

theorem A_to_B : A → B.{0} := by
  rintro ⟨-, -, hiff, -⟩ X Y d d'
  exact ⟨(equivB_iff d d').symm, Quotient.eq.trans (hiff.trans (equivB_iff d d').symm)⟩

theorem B_to_A : B.{0} → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y d
    exact (hB X Y d d).1.2 ((hB X Y d d).2.1 rfl)
  · intro X Y d d' h
    exact (hB X Y d' d).1.2 ((hB X Y d' d).2.1 ((hB X Y d d').2.2 ((hB X Y d d').1.1 h)).symm)
  · intro X Y d d'
    exact Quotient.eq.symm.trans ((hB X Y d d').2.trans (hB X Y d d').1.symm)
  · refine (hB _ _ _ _).1.2 ⟨⟨Examples.pairEP, EpGroupoid.Examples.pairToPoint,
      EpGroupoid.Examples.isEquivalence_pairToPoint, EpGroupoid.Examples.pairToPoint⟩, ?_, ?_⟩
    · exact ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, EpFunctor.NaturallyEquivalent.refl _,
        EpFunctor.NaturallyEquivalent.refl _⟩
    · exact ⟨EpGroupoid.Examples.pairToPoint, EpGroupoid.Examples.isEquivalence_pairToPoint,
        EpFunctor.NaturallyEquivalent.refl _, EpFunctor.NaturallyEquivalent.refl _⟩

/--
error: rt_check FAIL: RoundTrip.V10_37.A_to_B uses [Polyfold.EPLocalization.Diagram.Equiv.refl,
 Polyfold.EPLocalization.Diagram.Equiv.symm]
-/
#guard_msgs in
#rt_check RoundTrip.V10_37.A_to_B [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]
/--
error: rt_check FAIL: RoundTrip.V10_37.B_to_A uses [Polyfold.EPLocalization.Diagram.Equiv.refl,
 Polyfold.EPLocalization.Diagram.Equiv.symm]
-/
#guard_msgs in
#rt_check RoundTrip.V10_37.B_to_A [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]
#rt_check_soft RoundTrip.V10_37.A_to_B [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]
#rt_check_soft RoundTrip.V10_37.B_to_A [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]
open Lean Elab Command in
/-- `#rt_overlap_except_setoid T [nᵢ]`: as `#rt_overlap`, with the body of `Diagram.setoid` not
unfolded on the side of `T` (the shared theorems that the proof of `T` reaches otherwise). -/
elab "#rt_overlap_except_setoid " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList
    (NameSet.empty.insert ``Polyfold.EPLocalization.Diagram.setoid)
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      (`Polyfold).isPrefixOf n && !n.isInternal
  logInfo m!"rt_overlap_except_setoid {t.getId}: {shared.length} shared non-internal project theorems {shared}"

#rt_overlap_except_setoid RoundTrip.V10_37.B_to_A [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]
#rt_overlap RoundTrip.V10_37.B_to_A [Polyfold.EPLocalization.Diagram.Equiv.refl,
  Polyfold.EPLocalization.Diagram.Equiv.symm, Polyfold.EPLocalization.Diagram.equiv_iff,
  Polyfold.EPLocalization.Examples.equiv_pairToPoint_id]

end RoundTrip.V10_37
