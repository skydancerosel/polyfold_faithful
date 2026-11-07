import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_36

/-! Round trip for V7_36 (Proposition 7.8, p. 240: `X_reg` is open and dense for effective `X`).

`A` is the conjunction of the types of `proposition_7_8` (`IsEffective → IsOpen regularSet ∧
Dense regularSet`), `isEffective_of_dense_regularSet` and `isEffective_iff_dense_regularSet`
(the converse and the equivalence, not in the text), universes at `0`.
`NaturalRep.stabilizerEquivIsotropy` is a definition (vocabulary).

Dictionary: `B`'s `IsEffectiveB` is `IsEffective` (`g.val ≠ 1_x` vs `g ≠ 1`) and `XregB` is
`regularSet` (`g.val = 1_x` vs `g = 1`), by `Isotropy.ext`.

* `A → B`: `proposition_7_8` through the dictionary.
* `B → A`: `proposition_7_8` is `B` through the dictionary.  The converse
  `isEffective_of_dense_regularSet` is not in the text and not a consequence of `B`; it is
  re-proved outright (a regular `a` near `x` with `Γ(g, a)` in a given open `W ∋ g` has
  `Γ(g, a) ≠ 1_a = Γ(1, a)`), from `theorem_7_1` and the `NaturalRep` API.  The equivalence
  combines the two.
-/

namespace RoundTrip.V7_36
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_7_8.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isEffective_of_dense_regularSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isEffective_iff_dense_regularSet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_7_8.{0}, @Polyfold.EpGroupoid.isEffective_of_dense_regularSet.{0},
    @Polyfold.EpGroupoid.isEffective_iff_dense_regularSet.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

theorem isEffectiveB_iff : IsEffectiveB X ↔ X.IsEffective := by
  refine ⟨fun h x g hg W hW hgW => h x g (fun he => hg (GroupoidStr.Isotropy.ext he)) W hW hgW,
    fun h x g hg W hW hgW => h x g (fun he => hg (by rw [he]; rfl)) W hW hgW⟩

theorem XregB_eq : XregB X = X.regularSet := by
  ext x
  refine ⟨fun h g => GroupoidStr.Isotropy.ext (h g), fun h g => ?_⟩
  rw [h g]
  rfl

end Dictionary

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X hX
  rw [XregB_eq]
  exact hA.1 X (isEffectiveB_iff.1 hX)

/-- The converse of Proposition 7.8, re-proved outright (not in the text, not in `B`). -/
theorem isEffective_of_dense' {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (h : Dense X.regularSet) : X.IsEffective := by
  intro x g hg W hW hgW
  obtain ⟨R, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  obtain ⟨a, ⟨ha, haW⟩, hreg⟩ := dense_iff_inter_open.1 h _
    ((R.continuousOn_Γ g).isOpen_inter_preimage R.isOpen_U hW)
    ⟨x, R.mem_U, by rw [mem_preimage, R.Γ_self]; exact hgW⟩
  refine ⟨R.Γ g a, haW, fun he => hg ?_⟩
  have hs := R.src_Γ g a ha
  have hv : R.Γ g a = X.unit a :=
    congrArg GroupoidStr.Isotropy.val (hreg ⟨R.Γ g a, hs, he.symm.trans hs⟩)
  rw [← R.Γ_one ha] at hv
  exact (R.Γ_inj ha).1 hv

theorem B_to_A : B → A := by
  intro hB
  have h78 : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      X.IsEffective → IsOpen X.regularSet ∧ Dense X.regularSet := by
    intro Obj Mor _ _ _ _ _ _ X hX
    rw [← XregB_eq]
    exact hB Obj Mor X (isEffectiveB_iff.2 hX)
  exact ⟨fun X hX => h78 X hX, fun X h => isEffective_of_dense' X h,
    fun X => ⟨fun h => (h78 X h).2, isEffective_of_dense' X⟩⟩

#rt_check RoundTrip.V7_36.A_to_B [Polyfold.EpGroupoid.proposition_7_8,
  Polyfold.EpGroupoid.isEffective_of_dense_regularSet,
  Polyfold.EpGroupoid.isEffective_iff_dense_regularSet]
#rt_check RoundTrip.V7_36.B_to_A [Polyfold.EpGroupoid.proposition_7_8,
  Polyfold.EpGroupoid.isEffective_of_dense_regularSet,
  Polyfold.EpGroupoid.isEffective_iff_dense_regularSet]
#rt_overlap RoundTrip.V7_36.B_to_A [Polyfold.EpGroupoid.proposition_7_8,
  Polyfold.EpGroupoid.isEffective_of_dense_regularSet,
  Polyfold.EpGroupoid.isEffective_iff_dense_regularSet]

end RoundTrip.V7_36
