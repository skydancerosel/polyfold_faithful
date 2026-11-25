import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_95

set_option maxSynthPendingDepth 3

/-! Round trip for V17_95 (2021 Proposition 17.5.2, p. 813: push-forward and pull-back of
branched ep⁺-subgroupoids / subcategories along `Γ_Ψ`).

The item lists five theorems; `A` is the conjunction of their types at universe `0`:
`proposition_17_5_2_one` (for a covering family `Ψ`, `(Γ_Ψ)_*Θ` is a branched ep⁺-subcategory),
`proposition_17_5_2_two` (for ANY family `Ψ` of uniformizers from `F`, `Γ_Ψ^*Θ` is a branched
ep⁺-subgroupoid), `isBranchedEpSubgroupoid_modelPull_iff` (`Θ ∘ Γ_Ψ` is branched iff every
`Θ ∘ Ψ_λ` is), `modelPull_modelPush`, `modelPush_modelPull` (the two are inverse, the second for
covering families).  `B`'s `S.modelEpGroupoid c.Ψ` is `(S.modelEP c.Ψ).X` by `rfl`.

* `A_to_B`: (1) and (2) of `B` are `proposition_17_5_2_one` at `c.cover` and
  `proposition_17_5_2_two` at `c.Ψ`.
* `B_to_A`: `proposition_17_5_2_one` from `B (1)` at the covering family `⟨ι, Ψ, hc⟩`.  `B` speaks
  only of covering families, while `proposition_17_5_2_two` holds for every family (a family need
  not extend to a covering one when the footprints of `F` do not cover `|C|`); it, the summand-wise
  criterion and the two push/pull identities are re-proved from non-item lemmas
  (`localBranching_summand`, `localBranching_of_summand`, `mem_smoothSet_model_iff`,
  `IsBranchedSubcategory.unif`, `GroupoidFunctor.pushTheta_comp_obj(_eq)`). -/

namespace RoundTrip.V17_95
open Polyfold GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two.{0},
    @Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush.{0},
    @Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull.{0}⟩

theorem A_to_B : A → B := fun hA _ _ c =>
  ⟨fun _ h => hA.1 c.cover h, fun _ h => hA.2.1 h⟩

/-! ### The helper statements, re-proved from non-item lemmas -/

section Helpers
variable {C : GCT.{0}} {S : C.PolyfoldConstruction} {ι : Type} {Ψ : ι → S.Unif}

theorem modelPull_iff' {Θ : C.Obj → ℚ} (h0 : ∀ α, 0 ≤ Θ α)
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelEP Ψ).X.IsBranchedEpSubgroupoid (S.modelPull Ψ Θ) ↔
      ∀ i, (Ψ i).1.ep.IsBranchedEpSubgroupoid (Θ ∘ (Ψ i).1.obj) := by
  constructor
  · intro h i
    exact
      { nonneg := fun _ => h0 _
        isFunctorial := (Ψ i).1.isFunctorial_comp hΘ
        support_subset := fun q hq => (mem_smoothSet_model_iff i q).1
          (h.support_subset (a := ⟨i, q⟩) hq)
        paracompactSpace_orbitSupp := (Ψ i).1.paracompactSpace_subset _
        localBranching := fun q hq => by
          obtain ⟨B⟩ := h.localBranching ⟨i, q⟩ hq
          obtain ⟨B', -⟩ := localBranching_summand i q B
          exact ⟨B'⟩ }
  · intro h
    exact
      { nonneg := fun _ => h0 _
        isFunctorial := isFunctorial_modelPull hΘ
        support_subset := fun x hx => by
          obtain ⟨i, q⟩ := x
          exact (mem_smoothSet_model_iff i q).2 ((h i).support_subset hx)
        paracompactSpace_orbitSupp := paracompactSpace_model_subset _
        localBranching := fun x hx => by
          obtain ⟨i, q⟩ := x
          obtain ⟨B⟩ := (h i).localBranching q hx
          obtain ⟨B', -⟩ := localBranching_of_summand i q B
          exact ⟨B'⟩ }

theorem two' {Θ : C.Obj → ℚ} (h : S.IsBranchedSubcategory Θ) :
    (S.modelEP Ψ).X.IsBranchedEpSubgroupoid (S.modelPull Ψ Θ) :=
  (modelPull_iff' h.nonneg h.isFunctorial).2 fun i => h.unif (Ψ i)

theorem modelPull_modelPush' {Θ : S.ModelObj Ψ → ℚ} (hΘ : (S.modelEP Ψ).X.IsFunctorial Θ) :
    S.modelPull Ψ (S.modelPush Ψ Θ) = Θ :=
  GroupoidFunctor.pushTheta_comp_obj (S.modelFunctor_full Ψ) hΘ

theorem modelPush_modelPull' (hc : S.IsCoveringFamily Ψ) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) : S.modelPush Ψ (S.modelPull Ψ Θ) = Θ :=
  GroupoidFunctor.pushTheta_comp_obj_eq (S.modelFunctor_full Ψ) (modelFunctor_essSurj hc) hΘ

end Helpers

theorem B_to_A : B → A := fun hB =>
  ⟨fun {C} {S} {ι} {Ψ} hc _ h => (hB C S ⟨ι, Ψ, hc⟩).1 _ h,
    fun h => two' h, fun h0 hΘ => modelPull_iff' h0 hΘ,
    fun hΘ => modelPull_modelPush' hΘ, fun hc _ hΘ => modelPush_modelPull' hc hΘ⟩

/-- The main claim, (1) and (2) of the proposition. -/
def Main : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two.{0})

theorem main_to_B : Main → B := fun hA _ _ c =>
  ⟨fun _ h => hA.1 c.cover h, fun _ h => hA.2 h⟩

theorem B_to_main : B → Main := fun hB => ⟨(B_to_A hB).1, (B_to_A hB).2.1⟩

#rt_check RoundTrip.V17_95.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two,
  Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff,
  Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush,
  Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull]
#rt_check RoundTrip.V17_95.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two,
  Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff,
  Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush,
  Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull]
#rt_check RoundTrip.V17_95.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two,
  Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff,
  Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush,
  Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull]
#rt_check RoundTrip.V17_95.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two,
  Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff,
  Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush,
  Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull]
#rt_overlap RoundTrip.V17_95.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_one,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_5_2_two,
  Polyfold.GCT.PolyfoldConstruction.isBranchedEpSubgroupoid_modelPull_iff,
  Polyfold.GCT.PolyfoldConstruction.modelPull_modelPush,
  Polyfold.GCT.PolyfoldConstruction.modelPush_modelPull]

end RoundTrip.V17_95
