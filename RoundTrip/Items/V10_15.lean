import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_15

/-! Round trip for V10_15 (2021 Proposition 10.1.18, p. 476: (SLUC) under equivalences).

The item lists the definition `EpFunctor.liftOne` (`F¹ : X¹ → Y¹`, vocabulary) and three
theorems; `A` is the conjunction of their types, universes instantiated at `0` (`B` lives in
`EP.{0}`): `EpFunctor.IsEquivalence.liftOne` (`F¹` is an equivalence), `EP.exists_isEquivalence_lift`
(there are equivalences `Fⁱ : Xⁱ → Yⁱ`) and `EP.proposition_10_1_18` (the proposition).

`B`'s `SLUC A` is `∀ i, (A.lift i).X.IsLUC`, which is the project's `EP.IsSLUC A` by `rfl`.

* `A_to_B`: `proposition_10_1_18` is `B` (with `SLUC = EP.IsSLUC` by `rfl`).
* `B_to_A`: `proposition_10_1_18` is `B`.  The two lemmas on lifts ("the lift of an equivalence
  is an equivalence") are steps of the text's proof, not consequences of `B` (which says nothing
  about `F¹`); they are re-proved outright (`liftOne'`: the project's proof, copied, from the
  non-item lemmas `lemma_10_1_2`, `IsLocalScDiffeo.levelOne`, `mem_levelSet_src_iff`, …;
  `exists_isEquivalence_lift'`: induction on `i` with `liftOne'`). -/

namespace RoundTrip.V10_15
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsEquivalence.liftOne.{0, 0}) ∧
  (type_of% @Polyfold.EP.exists_isEquivalence_lift.{0}) ∧
  (type_of% @Polyfold.EP.proposition_10_1_18.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsEquivalence.liftOne.{0, 0},
    @Polyfold.EP.exists_isEquivalence_lift.{0},
    @Polyfold.EP.proposition_10_1_18.{0}⟩

/-- `B`'s (SLUC) is the project's `EP.IsSLUC`. -/
theorem SLUC_eq (A : EP.{0}) : SLUC A = A.IsSLUC := rfl

theorem A_to_B : A → B := by
  rintro ⟨-, -, h⟩ A B F hF
  rw [SLUC_eq, SLUC_eq]
  exact h hF

/-! ### The lemmas on lifts, re-proved outright (the project's proofs) -/

section Lift

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem liftOne' {F : EpFunctor X Y} (hF : F.IsEquivalence) : F.liftOne.IsEquivalence := by
  have hd := hF.isLocalScDiffeo_obj
  refine F.liftOne.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he =>
        MPolyfold.level_ext (hF.mor_injective (congrArg (X.PObj.levelVal 1) hs)
          (congrArg (X.PObj.levelVal 1) ht) (congrArg (Y.PMor.levelVal 1) he))
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => ?_ } hd.levelOne
  · have hs' : Y.src (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x) :=
      congrArg (Y.PObj.levelVal 1) hs
    have ht' : Y.tgt (Y.PMor.levelVal 1 ψ) = F.obj (X.PObj.levelVal 1 x') :=
      congrArg (Y.PObj.levelVal 1) ht
    obtain ⟨φ, hφs, hφt, hφ⟩ := hF.exists_mor_eq hs' ht'
    have hφ1 : φ ∈ X.PMor.levelSet 1 :=
      (X.mem_levelSet_src_iff φ 1).1 (hφs ▸ MPolyfold.levelVal_mem x)
    refine ⟨X.PMor.levelMk 1 φ hφ1, MPolyfold.level_ext ?_, MPolyfold.level_ext ?_,
      MPolyfold.level_ext ?_⟩
    · rw [X.liftOne_src_val, MPolyfold.levelVal_levelMk, hφs]
    · rw [X.liftOne_tgt_val, MPolyfold.levelVal_levelMk, hφt]
    · change F.mor (X.PMor.levelVal 1 (X.PMor.levelMk 1 φ hφ1)) = _
      rw [MPolyfold.levelVal_levelMk, hφ]
  · obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (Y.PObj.levelVal 1 y)
    have hψ1 : ψ ∈ Y.PMor.levelSet 1 :=
      (Y.mem_levelSet_tgt_iff ψ 1).1 (ht ▸ MPolyfold.levelVal_mem y)
    have hx1 : x ∈ X.PObj.levelSet 1 :=
      (hd.mem_levelSet_iff x 1).1 (hs ▸ (Y.mem_levelSet_src_iff ψ 1).2 hψ1)
    refine ⟨X.PObj.levelMk 1 x hx1, Y.PMor.levelMk 1 ψ hψ1, MPolyfold.level_ext ?_,
      MPolyfold.level_ext ?_⟩
    · change Y.src ψ = F.obj (X.PObj.levelVal 1 (X.PObj.levelMk 1 x hx1))
      rw [MPolyfold.levelVal_levelMk, hs]
    · rw [Y.liftOne_tgt_val, MPolyfold.levelVal_levelMk, ht]

end Lift

theorem exists_isEquivalence_lift' {A B : EP.{0}} {F : EpFunctor A.X B.X}
    (hF : F.IsEquivalence) (i : ℕ) :
    ∃ G : EpFunctor (A.lift i).X (B.lift i).X, G.IsEquivalence := by
  induction i with
  | zero => exact ⟨F, hF⟩
  | succ i ih =>
    obtain ⟨G, hG⟩ := ih
    exact ⟨G.liftOne, liftOne' hG⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@liftOne', @exists_isEquivalence_lift', ?_⟩
  intro A B F hF
  rw [← SLUC_eq, ← SLUC_eq]
  exact hB A B F hF

#rt_check RoundTrip.V10_15.A_to_B [Polyfold.EpFunctor.IsEquivalence.liftOne,
  Polyfold.EP.exists_isEquivalence_lift, Polyfold.EP.proposition_10_1_18]
#rt_check RoundTrip.V10_15.B_to_A [Polyfold.EpFunctor.IsEquivalence.liftOne,
  Polyfold.EP.exists_isEquivalence_lift, Polyfold.EP.proposition_10_1_18]
#rt_overlap RoundTrip.V10_15.B_to_A [Polyfold.EpFunctor.IsEquivalence.liftOne,
  Polyfold.EP.exists_isEquivalence_lift, Polyfold.EP.proposition_10_1_18]

end RoundTrip.V10_15
