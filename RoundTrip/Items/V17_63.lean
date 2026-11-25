import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_63

set_option maxSynthPendingDepth 3

/-! Round trip for V17_63 (2021 Proposition 17.3.6, p. 786: a subpolyfold `A` inherits a natural
polyfold structure `(F_A, M)`).

The item lists the definitions `rtrPolyfold`, `subData`, `subConstruction` (vocabulary) and three
theorems; `A` is the conjunction of their types at universe `0`: `mem_subF_iff`
(`F_A(α) = {Ψ_A | Ψ ∈ F(α)}` for `subConstruction hS`), `proposition_17_3_6` (that, plus: every
`L ∈ F_A` is `Ψ_A` for the CHOSEN representative `Ψ = subData L`, and the transition M-polyfold
`M(L, L')` of `subConstruction hS` maps bijectively, as a local sc-diffeomorphism, onto the
sub-M-polyfold `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` of the chosen representatives), and
`reflection_subConstruction` (a non-degenerate witness on `ℤ/2 ⋉ ℝ`).

* `B_to_A`: `A` speaks about the project's specific `subConstruction`, which `B` does not
  mention; `A` is re-proved outright from non-item lemmas (`subInclOf_spec`, `subData_eq`, the
  definition of `subF`), so this direction does not use `B` (flagged).
* `A_to_B`: not proved.  `B` asks for one structure `S_A` whose `M(Ψ_A, Ψ'_A)` is identified
  with `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` for EVERY pair `Ψ, Ψ'` of `F` with the given restrictions, while
  `subConstruction` (and `A`) identifies it only with the chosen representatives
  `subData L, subData L'`.  Two uniformizers of `F` with the same restriction `Ψ_A` (they may
  differ off `A_Ψ`, and in Lean even the equality of the restricted types does not determine
  `Ψ`) carry independent transition data `M(Ψ₁, ·)`, `M(Ψ₂, ·)` in `S`; nothing in the axioms of
  a polyfold structure relates their topologies over `A`, so `A ⇒ B` would need a uniqueness
  statement for transition structures that neither side provides. -/

namespace RoundTrip.V17_63
open Polyfold GCT.PolyfoldConstruction Set Function

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.mem_subF_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.mem_subF_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6.{0},
    @Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction⟩

/-! ### `A`, re-proved outright (the project's proofs, without the item's theorems) -/

theorem mem_subF_iff' {C : GCT.{0}} {S : C.PolyfoldConstruction} {A : Set C.Obj}
    (hS : S.IsSubpolyfold A) (α : (C.sub A).Obj) (L : (C.sub A).LocalUniformizer) :
    L ∈ (subConstruction hS).F α ↔ ∃ Ψ, ∃ hΨ : Ψ ∈ S.F (show A from α).1,
      L = GCT.LocalUniformizer.restrict hS.1 (hS.2 _ (show A from α).2 Ψ hΨ) :=
  ⟨fun ⟨Ψ, hΨ, _, h⟩ => ⟨Ψ, hΨ, h⟩, fun ⟨Ψ, hΨ, h⟩ => ⟨Ψ, hΨ, _, h⟩⟩

theorem proposition_17_3_6' {C : GCT.{0}} {S : C.PolyfoldConstruction} {A : Set C.Obj}
    (hS : S.IsSubpolyfold A) :
    (∀ α L, L ∈ (subConstruction hS).F α ↔ ∃ Ψ, ∃ hΨ : Ψ ∈ S.F (show A from α).1,
      L = GCT.LocalUniformizer.restrict hS.1 (hS.2 _ (show A from α).2 Ψ hΨ)) ∧
    ∀ L L' : (subConstruction hS).Unif,
      L.1 = GCT.LocalUniformizer.restrict hS.1 (S.subData_sub hS.1 L) ∧
      ∃ ι : (subConstruction hS).Tr L L' →
          S.restrictTransSet (A := A) (S.subData hS.1 L) (S.subData hS.1 L'),
        Bijective ι ∧
        ((subConstruction hS).transPolyfold L L').IsLocalScDiffeo
          (MPolyfold.subPolyfold
            (isSubMPolyfold_restrictTransSet (S.subData hS.1 L') (S.subData_sub hS.1 L))) ι ∧
        ((subConstruction hS).transPolyfold L L').IsScSmoothMap
          (S.transPolyfold (S.subData hS.1 L) (S.subData hS.1 L')) (fun a => (ι a).1) ∧
        ∀ a : (subConstruction hS).Tr L L',
          (ι a).1.mor = (show C.toGroupoidStr.morOn A from a.mor).1 ∧
          (S.subData hS.1 L).1.obj (ι a).1.src = (show A from L.1.obj a.src).1 ∧
          (S.subData hS.1 L').1.obj (ι a).1.tgt = (show A from L'.1.obj a.tgt).1 := by
  refine ⟨mem_subF_iff' hS, fun L L' => ⟨S.subData_eq hS.1 L, ?_⟩⟩
  obtain ⟨hb, hl, hc⟩ := S.subInclOf_spec hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  let ι : (subConstruction hS).Tr L L' → _ := S.subInclOf hS.1 L.1 L'.1 (S.subData hS.1 L)
    (S.subData hS.1 L') (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L)
    (S.subData_eq hS.1 L')
  have hl' : ((subConstruction hS).transPolyfold L L').IsLocalScDiffeo
      (MPolyfold.subPolyfold
        (isSubMPolyfold_restrictTransSet (S.subData hS.1 L') (S.subData_sub hS.1 L))) ι := hl
  exact ⟨ι, hb, hl', (MPolyfold.subPolyfold_inclusion_isScSmooth _).comp hl'.isScSmoothMap, hc⟩

section Witness
open EpGroupoid.Examples

theorem reflection_subConstruction' :
    ∃ L ∈ (subConstruction reflection_isSubpolyfold_zero.1).F
        (show ({0} : Set (Fin 1 → ℝ)) from ⟨0, rfl⟩),
      Nontrivial L.G ∧ Nonempty L.O := by
  refine ⟨_, (mem_subF_iff' reflection_isSubpolyfold_zero.1 _ _).2
    ⟨_, reflection_isSubpolyfold_zero.2.2.1, rfl⟩, ?_, ?_⟩
  · refine nontrivial_of_ne (-1 : ℤˣ) 1 fun h => ?_
    have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    omega
  · exact ⟨⟨0, rfl⟩⟩

end Witness

/-- `B ⇒ A`, by proving `A` outright (does not use `B`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@mem_subF_iff', @proposition_17_3_6', reflection_subConstruction'⟩

/-- The main conjunct `proposition_17_3_6` from `B` (outright, does not use `B`). -/
theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6.{0} :=
  fun _ => @proposition_17_3_6'

#rt_check RoundTrip.V17_63.B_to_A [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction]
#rt_check RoundTrip.V17_63.B_to_main [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction]
#rt_overlap RoundTrip.V17_63.B_to_A [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction]

end RoundTrip.V17_63
