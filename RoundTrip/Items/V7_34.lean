import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_34

/-! Round trip for V7_34 (Lemma 7.2, p. 239: the regular part is open).

`A` is the conjunction of the types of `EpGroupoid.NaturalRep.subset_regularSet` (for every
natural representation `R` at a regular `x`, `R.U ⊆ X_reg`) and `EpGroupoid.lemma_7_2`
(`IsOpen X.regularSet`), universes at `0`.

Dictionary: `B`'s `XregB X = {x | ∀ g : G_x, g.val = 1_x}` is the project's
`regularSet = {x | ∀ g : G_x, g = 1}` (`Isotropy.ext`, `val_one`).

* `A → B`: `lemma_7_2` with the dictionary.
* `B → A`: `lemma_7_2` is `B` with the dictionary.  `subset_regularSet` is a fact about an
  arbitrary natural representation, which `B` does not mention; it is re-proved outright from the
  fields of `NaturalRep` (`existsUnique_Γ`) and `NaturalRep.Γ_one` (`NaturalAction.lean`).
-/

namespace RoundTrip.V7_34
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.subset_regularSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_2.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.subset_regularSet.{0}, @Polyfold.EpGroupoid.lemma_7_2.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem XregB_eq (X : EpGroupoid Obj Mor) : XregB X = X.regularSet := by
  ext x
  refine ⟨fun h g => GroupoidStr.Isotropy.ext (h g), fun h g => ?_⟩
  rw [h g]
  rfl

end Dictionary

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  rw [XregB_eq]
  exact hA.2 X

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, fun {Obj Mor} _ _ _ _ _ _ X => ?_⟩
  · -- outright: every point of `U(x)` is regular when `x` is
    intro Obj Mor _ _ _ _ _ _ X x R hx a ha k
    obtain ⟨h, hh, -⟩ := R.existsUnique_Γ k.val (by rw [k.src_val]; exact ha)
      (by rw [k.tgt_val]; exact ha)
    rw [k.src_val, hx h, R.Γ_one ha] at hh
    exact GroupoidStr.Isotropy.ext hh.symm
  · rw [← XregB_eq]
    exact hB Obj Mor X

#rt_check RoundTrip.V7_34.A_to_B [Polyfold.EpGroupoid.NaturalRep.subset_regularSet,
  Polyfold.EpGroupoid.lemma_7_2]
#rt_check RoundTrip.V7_34.B_to_A [Polyfold.EpGroupoid.NaturalRep.subset_regularSet,
  Polyfold.EpGroupoid.lemma_7_2]
#rt_overlap RoundTrip.V7_34.B_to_A [Polyfold.EpGroupoid.NaturalRep.subset_regularSet,
  Polyfold.EpGroupoid.lemma_7_2]

end RoundTrip.V7_34
