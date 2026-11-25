import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_60

set_option maxSynthPendingDepth 3

/-! Round trip for V17_60 (2021 Proposition 17.3.4, p. 784: Definitions 17.3.1 and 17.3.2 are
equivalent).

The item lists seven declarations; `irrationalConstruction` is a definition (vocabulary), the other
six are theorems and `A` is the conjunction of their types at universe `0`:
`proposition_17_3_4` (equivalence under `HasUniformizers`, i.e. `F(α) ≠ ∅` for every `α`),
`proposition_17_3_4_of_nonempty` (under `HasCoveringUniformizers` and `F(α) ≠ ∅` on `A`),
`isSubpolyfold_iff_forall_unif`, `isSubpolyfold_of_isSubpolyfoldModel` (17.3.2 ⇒ 17.3.1, no
hypothesis), `isSubMPolyfold_of_isCoveringFamily`, and `proposition_17_3_4_empty_family` (a
polyfold structure on `ℤ/2 ⋉ ℝ` whose footprints cover `|C|` but with `F(x) = ∅` at the rational
`x`, where the rational points satisfy 17.3.1 vacuously but not 17.3.2).

`B` (with `Def1 = IsSubpolyfold`, `Def2 = IsSubpolyfoldModel`, both by `rfl`) asks for the
equivalence under `HasCoveringUniformizers` alone.  The project's `empty_family` witness lives in
universe `0` and refutes exactly this: `not_B`.  So `A → B` does not hold (`not_A_to_B`), and
`B → A` holds only ex falso.  The main conjunct `proposition_17_3_4` (hypothesis
`HasUniformizers`, which implies `HasCoveringUniformizers`) follows from `B` (`B_to_main`,
genuinely using `B`). -/

namespace RoundTrip.V17_60
open Polyfold GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty.{0},
    @Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif.{0},
    @Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel.{0},
    @Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family⟩

/-- `B`'s definitions are the project's. -/
theorem def1_iff {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) :
    Def1 S A ↔ S.IsSubpolyfold A := Iff.rfl

theorem def2_iff {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) :
    Def2 S A ↔ S.IsSubpolyfoldModel A := Iff.rfl

/-- The transfer along a covering family (the project's proof, copied from the non-item
`isSubMPolyfold_of_forall_tr`). -/
theorem transfer {C : GCT.{0}} {S : C.PolyfoldConstruction} {A : Set C.Obj}
    (hA : C.toGroupoidStr.IsSaturated A) {ι : Type} {Ψ : ι → S.Unif} (hc : S.IsCoveringFamily Ψ)
    (h : ∀ i, (Ψ i).1.P.IsSubMPolyfold ((Ψ i).1.obj ⁻¹' A)) (Ψ' : S.Unif) :
    Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A) :=
  isSubMPolyfold_of_forall_tr hA Ψ' fun a' _ => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hc.symm ▸ Set.mem_univ (C.toGroupoidStr.π (Ψ'.1.obj a')))
    obtain ⟨q, hq⟩ := (Ψ i).1.mem_footprint_iff.1 hi
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq.symm
    exact ⟨Ψ i, S.toTr (⟨a', φ, q, hs, ht⟩ : Ψ'.1.Trans (Ψ i).1), rfl, h i⟩

/-- **`B` does not hold**: the project's polyfold structure `(F', M)` on `ℤ/2 ⋉ ℝ` without
uniformizers at the rational points has covering footprints; the rational points satisfy
Definition 17.3.1 vacuously and not Definition 17.3.2. -/
theorem not_B : ¬ B := by
  intro hB
  have hcov : irrationalConstruction.HasCoveringUniformizers := by
    refine Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨irrationalUnif, ?_⟩
    change z ∈ reflectionUnif.1.footprint
    rw [reflectionUnif_footprint]
    exact Set.mem_univ z
  have h1 : Def1 irrationalConstruction ratPoints :=
    ⟨reflection_isSaturated_ratPoints, fun α hα Ψ hΨ => absurd hα hΨ.1⟩
  obtain ⟨hsat, c, hc⟩ := (hB _ irrationalConstruction hcov ratPoints).1 h1
  exact not_isSubMPolyfold_ratPoints (transfer hsat c.cover
    ((irrationalConstruction.isEpSubgroupoid_preimage_modelFunctor_iff c.Ψ hsat).1 hc)
    irrationalUnif)

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

theorem B_to_A : B → A := fun hB => (not_B hB).elim

/-- The main conjunct `proposition_17_3_4` from `B` (using `B`, not ex falso):
`HasUniformizers ⇒ HasCoveringUniformizers`. -/
theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4.{0} :=
  fun hB C S hS A =>
    hB C S (S.toUniformizerConstruction.hasCoveringUniformizers_of_hasUniformizers hS) A

#rt_check RoundTrip.V17_60.not_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel,
  Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family]
#rt_check RoundTrip.V17_60.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel,
  Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family]
#rt_check RoundTrip.V17_60.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel,
  Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family]
#rt_overlap RoundTrip.V17_60.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_iff_forall_unif,
  Polyfold.GCT.PolyfoldConstruction.isSubpolyfold_of_isSubpolyfoldModel,
  Polyfold.GCT.PolyfoldConstruction.isSubMPolyfold_of_isCoveringFamily,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_4_empty_family]

end RoundTrip.V17_60
