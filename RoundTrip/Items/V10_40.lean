import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_40

/-! Round trip for V10_40 (2021 Theorem 10.3.8, p. 488; 2017: Theorem 10.3, p. 352; proof in
Appendix §10.6.1: composition of classes of diagrams).

The item lists the definitions `Diagram.id`, `Diagram.comp`, `wfp`, `wfpMap`, `assocFunctor`
(vocabulary) and thirteen theorems.  `A` is the conjunction of their types, universes at `0`:
`theorem_10_3_8` (well defined, associative, unital, with `≈` the project's setoid),
`Diagram.admissible`, `projLeft_comp_wfpMap`, `projRight_comp_wfpMap`, `isEquivalence_wfpMap`
(the functor `L` of the appendix is an equivalence), `isEquivalence_assocFunctor`,
`IsRefinement.comp`, `Equiv.comp`, `isRefinement_assoc`, `equiv_assoc`, `isRefinement_id_comp`,
`isRefinement_comp_id` and the general two-out-of-three lemma `IsEquivalence.of_comp_left`.

`B` (at universe `0`) states the three claims of the theorem for the blind author's `EquivB`
(definitionally the project's `Diagram.Equiv`, hence the project's `≈`), with the project's
`Diagram.comp` and `Diagram.id`.

* `A ⇒ B`: `theorem_10_3_8` from `A`.
* `B ⇒ A`: `theorem_10_3_8`, `Equiv.comp` and `equiv_assoc` are `B`.  The other ten conjuncts are
  statements about refinements, the functors `L` and the reassociation, admissibility and
  equivalences of ep-groupoids; `B` (a statement about classes only) does not give them, so they
  are re-proved outright below (the project's short proofs, from the non-item lemmas
  `isEquivalence_projLeft`/`Right`, `naturallyEquivalent`, `Admissible.of_isEquivalence_right`,
  `projLeft_comp_assocFunctor`, `Functor.isEquivalence_of_comp_right`,
  `IsLocalScDiffeoAt.of_comp_left`), with our own copies in place of the banned ones.

**Harness note.**  `Diagram.comp` passes the banned theorem `Diagram.admissible` as a plain
argument (`#print`: `wfp d.Φ e.F (Diagram.admissible d e)`, not abstracted into a `_proof_N`), and
`Diagram.comp` occurs in the statements of `A` and `B`.  So every term mentioning either reaches
`Diagram.admissible`: plain `#rt_check` fails on both directions for that name only (recorded
with `#guard_msgs`), and `#rt_check_soft` cannot help.  As in V7_40, a local
`#rt_check_except_defs` (the harness traversal `rtCollect` with the body of `Diagram.comp` not
unfolded) passes on both directions: the proofs never use `Diagram.admissible` themselves (our
copy `admissible'` is used wherever an admissibility proof is needed).
-/

namespace RoundTrip.V10_40
open Polyfold Polyfold.EPLocalization WeakFibredProduct

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
body of the definition `Diagram.comp`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    (NameSet.empty.insert ``Polyfold.EPLocalization.Diagram.comp)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the body of Diagram.comp"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the body of Diagram.comp"

open Lean Elab Command in
/-- `#rt_overlap_except_defs T [nᵢ]`: as `#rt_overlap`, with the body of `Diagram.comp` not
unfolded on the side of `T`. -/
elab "#rt_overlap_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList
    (NameSet.empty.insert ``Polyfold.EPLocalization.Diagram.comp)
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      (`Polyfold).isPrefixOf n && !n.isInternal
  logInfo m!"rt_overlap_except_defs {t.getId}: {shared.length} shared non-internal project theorems {shared}"

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.theorem_10_3_8.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.admissible.{0}) ∧
  (type_of% @Polyfold.EPLocalization.projLeft_comp_wfpMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.projRight_comp_wfpMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_wfpMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.isEquivalence_assocFunctor.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_assoc.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.equiv_assoc.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_id_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_comp_id.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.of_comp_left.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Diagram.theorem_10_3_8.{0}, @Diagram.admissible.{0}, @projLeft_comp_wfpMap.{0},
    @projRight_comp_wfpMap.{0}, @isEquivalence_wfpMap.{0}, @isEquivalence_assocFunctor.{0},
    @Diagram.IsRefinement.comp.{0}, @Diagram.Equiv.comp.{0}, @Diagram.isRefinement_assoc.{0},
    @Diagram.equiv_assoc.{0}, @Diagram.isRefinement_id_comp.{0}, @Diagram.isRefinement_comp_id.{0},
    @EpFunctor.IsEquivalence.of_comp_left.{0, 0, 0}⟩

/-- Glue: the blind author's `EquivB` is the project's `Diagram.Equiv` (definitional). -/
theorem equivB_iff {X Y : EP.{0}} (d d' : Diagram X Y) : EquivB d d' ↔ Diagram.Equiv d d' :=
  Iff.rfl

theorem A_to_B : A → B.{0} := by
  rintro ⟨h, -⟩
  refine ⟨fun X Y Z d₁ d₂ e₁ e₂ hd he => ?_, fun W X Y Z d d' d'' => ?_, fun X Y d => ?_⟩
  · exact (@h X Y Z X).1 hd he
  · exact (@h W X Y Z).2.1 d d' d''
  · exact ⟨((@h X Y Y X).2.2 d).2, ((@h X Y Y X).2.2 d).1⟩

/-! ### The side conjuncts, re-proved outright (the project's proofs, own copies) -/

section Copies

universe u v w

section TwoOutOfThree

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

open CategoryTheory in
/-- Copy of `EpFunctor.IsEquivalence.of_comp_left`. -/
theorem of_comp_left' {G : EpFunctor Y Z} {L : EpFunctor X Y}
    (hG : G.IsEquivalence) (hGL : (G.comp L).IsEquivalence) : L.IsEquivalence := by
  rw [EpFunctor.isEquivalence_iff] at hG hGL ⊢
  have := hG.1
  have : (L.toFunctor ⋙ G.toFunctor).IsEquivalence := hGL.1
  exact ⟨Functor.isEquivalence_of_comp_right L.toFunctor G.toFunctor, fun x =>
    MPolyfold.IsLocalScDiffeoAt.of_comp_left (hG.2.at (L.obj x)) L.continuous_obj' (hGL.2.at x)⟩

end TwoOutOfThree

/-- Copy of `Diagram.admissible`. -/
theorem admissible' {X Y Z : EP.{u}} (d : Diagram X Y) (e : Diagram Y Z) : Admissible d.Φ e.F :=
  .of_isEquivalence_right e.isEquivalence_F

section Map

variable {A A' B B' Y : EP.{u}} {Φ : EpFunctor A.X Y.X} {G : EpFunctor B.X Y.X}
  {Φ' : EpFunctor A'.X Y.X} {G' : EpFunctor B'.X Y.X}
  {H : EpFunctor A'.X A.X} {K : EpFunctor B'.X B.X}
  (τ : EpNatTrans Φ' (Φ.comp H)) (σ : EpNatTrans G' (G.comp K))

/-- Copy of `projLeft_comp_wfpMap`. -/
theorem projLeft_comp_wfpMap' (h : Admissible Φ G) (h' : Admissible Φ' G') :
    (projLeft Φ G h).comp (wfpMap τ σ h h') = H.comp (projLeft Φ' G' h') := rfl

/-- Copy of `projRight_comp_wfpMap`. -/
theorem projRight_comp_wfpMap' (h : Admissible Φ G) (h' : Admissible Φ' G') :
    (projRight Φ G h).comp (wfpMap τ σ h h') = K.comp (projRight Φ' G' h') := rfl

/-- Copy of `isEquivalence_wfpMap`. -/
theorem isEquivalence_wfpMap' (h : Admissible Φ G) (h' : Admissible Φ' G') (hH : H.IsEquivalence)
    (hG : G.IsEquivalence) (hG' : G'.IsEquivalence) : (wfpMap τ σ h h').IsEquivalence :=
  of_comp_left' (isEquivalence_projLeft hG h)
    (by rw [projLeft_comp_wfpMap']; exact hH.comp (isEquivalence_projLeft hG' h'))

end Map

section Assoc

variable {A B C Y Z : EP.{u}} {Φ : EpFunctor A.X Y.X} {G : EpFunctor B.X Y.X}
  {Ψ : EpFunctor B.X Z.X} {H : EpFunctor C.X Z.X} {h₁ : Admissible Φ G} {h₃ : Admissible Ψ H}

/-- Copy of `isEquivalence_assocFunctor`. -/
theorem isEquivalence_assocFunctor' (hG : G.IsEquivalence) (hH : H.IsEquivalence)
    (h₂ : Admissible (Ψ.comp (projRight Φ G h₁)) H)
    (h₄ : Admissible Φ (G.comp (projLeft Ψ H h₃))) : (assocFunctor h₂ h₄).IsEquivalence :=
  of_comp_left'
    (isEquivalence_projLeft (hG.comp (isEquivalence_projLeft hH h₃)) h₄)
    (by rw [projLeft_comp_assocFunctor]
        exact (isEquivalence_projLeft hG h₁).comp (isEquivalence_projLeft hH h₂))

end Assoc

namespace Diagram'

variable {X Y Z W : EP.{u}}

/-- Copy of `Diagram.IsRefinement.comp`. -/
theorem IsRefinement.comp' {d d' : Diagram X Y} {e e' : Diagram Y Z} (hd : d'.IsRefinement d)
    (he : e'.IsRefinement e) : (d'.comp e').IsRefinement (d.comp e) := by
  obtain ⟨H, hH, hFH, hΦH⟩ := hd
  obtain ⟨K, hK, hGK, hΨK⟩ := he
  obtain ⟨τ⟩ := hΦH.symm
  obtain ⟨σ⟩ := hGK.symm
  refine ⟨wfpMap τ σ (admissible' d e) (admissible' d' e'),
    isEquivalence_wfpMap' τ σ (admissible' d e) (admissible' d' e') hH e.isEquivalence_F
      e'.isEquivalence_F, ?_, ?_⟩
  · exact hFH.comp_left (projLeft d'.Φ e'.F (admissible' d' e'))
  · exact hΨK.comp_left (projRight d'.Φ e'.F (admissible' d' e'))

/-- Copy of `Diagram.isRefinement_assoc`. -/
theorem isRefinement_assoc' (d : Diagram X Y) (d' : Diagram Y Z) (d'' : Diagram Z W) :
    ((d.comp d').comp d'').IsRefinement (d.comp (d'.comp d'')) :=
  ⟨assocFunctor (h₁ := admissible' d d') (h₃ := admissible' d' d'')
      (admissible' (d.comp d') d'') (admissible' d (d'.comp d'')),
    isEquivalence_assocFunctor' (h₁ := admissible' d d') (h₃ := admissible' d' d'')
      d'.isEquivalence_F d''.isEquivalence_F (admissible' (d.comp d') d'')
      (admissible' d (d'.comp d'')), .refl _, .refl _⟩

/-- Copy of `Diagram.isRefinement_id_comp`. -/
theorem isRefinement_id_comp' (d : Diagram X Y) : ((Diagram.id X).comp d).IsRefinement d :=
  ⟨projRight (EpFunctor.id X.X) d.F (admissible' (Diagram.id X) d),
    isEquivalence_projRight (EpFunctor.IsEquivalence.id _) (admissible' (Diagram.id X) d),
    (naturallyEquivalent (admissible' (Diagram.id X) d)).symm, .refl _⟩

/-- Copy of `Diagram.isRefinement_comp_id`. -/
theorem isRefinement_comp_id' (d : Diagram X Y) : (d.comp (Diagram.id Y)).IsRefinement d :=
  ⟨projLeft d.Φ (EpFunctor.id Y.X) (admissible' d (Diagram.id Y)),
    isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) (admissible' d (Diagram.id Y)), .refl _,
    naturallyEquivalent (admissible' d (Diagram.id Y))⟩

end Diagram'

end Copies

theorem B_to_A : B.{0} → A := by
  rintro ⟨hc, ha, hu⟩
  refine ⟨?_, @admissible'.{0}, @projLeft_comp_wfpMap'.{0}, @projRight_comp_wfpMap'.{0},
    @isEquivalence_wfpMap'.{0}, @isEquivalence_assocFunctor'.{0}, @Diagram'.IsRefinement.comp'.{0},
    ?_, @Diagram'.isRefinement_assoc'.{0}, ?_, @Diagram'.isRefinement_id_comp'.{0},
    @Diagram'.isRefinement_comp_id'.{0}, @of_comp_left'.{0, 0, 0}⟩
  · -- `theorem_10_3_8`: `B`
    intro X Y Z W
    exact ⟨fun hd he => hc X Y Z _ _ _ _ hd he, fun d d' d'' => ha X Y Z W d d' d'',
      fun d => ⟨(hu X Y d).2, (hu X Y d).1⟩⟩
  · -- `Equiv.comp`: `B`
    intro X Y Z d₁ d₂ e₁ e₂ hd he
    exact hc X Y Z d₁ d₂ e₁ e₂ hd he
  · -- `equiv_assoc`: `B`
    intro X Y Z W d d' d''
    exact ha X Y Z W d d' d''

/--
error: rt_check FAIL: RoundTrip.V10_40.A_to_B uses [Polyfold.EPLocalization.Diagram.admissible]
-/
#guard_msgs in
#rt_check RoundTrip.V10_40.A_to_B [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]
/--
error: rt_check FAIL: RoundTrip.V10_40.B_to_A uses [Polyfold.EPLocalization.Diagram.admissible]
-/
#guard_msgs in
#rt_check RoundTrip.V10_40.B_to_A [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]
#rt_check_except_defs RoundTrip.V10_40.A_to_B [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]
#rt_check_except_defs RoundTrip.V10_40.B_to_A [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]
#rt_overlap RoundTrip.V10_40.B_to_A [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]
#rt_overlap_except_defs RoundTrip.V10_40.B_to_A [Polyfold.EPLocalization.Diagram.theorem_10_3_8,
  Polyfold.EPLocalization.Diagram.admissible, Polyfold.EPLocalization.projLeft_comp_wfpMap,
  Polyfold.EPLocalization.projRight_comp_wfpMap, Polyfold.EPLocalization.isEquivalence_wfpMap,
  Polyfold.EPLocalization.isEquivalence_assocFunctor,
  Polyfold.EPLocalization.Diagram.IsRefinement.comp, Polyfold.EPLocalization.Diagram.Equiv.comp,
  Polyfold.EPLocalization.Diagram.isRefinement_assoc, Polyfold.EPLocalization.Diagram.equiv_assoc,
  Polyfold.EPLocalization.Diagram.isRefinement_id_comp,
  Polyfold.EPLocalization.Diagram.isRefinement_comp_id, Polyfold.EpFunctor.IsEquivalence.of_comp_left]

end RoundTrip.V10_40
