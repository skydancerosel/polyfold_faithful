import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_44

set_option maxSynthPendingDepth 3

/-! Round trip for V14_44 (2021 Proposition 14.1.8, p. 645, structurability over `∂X` under
generalized strong bundle isomorphisms; 2017: Proposition 14.1).

`A` is the conjunction of the types of the 29 listed theorems at universe `0`
(`IsScPlusOnFaceNear.of_restrict` has no universe parameter).  `B` is on `SEP.{0}`.

* `main_to_B` / `A_to_B`: from the conjuncts `GenSBMap.proposition_14_1_8` (`f̄_*Λ`, needs `X`,
  `X'` tame) and `GenSBMap.proposition_14_1_8_pullMult` (`f̄^*Λ'`, needs `X` tame); `B`'s
  paracompactness hypotheses are not used.  `B`'s `GenSBMap.pushMult hf` / `pullMult hf` are the
  project's operations.
* `B_to_A` is not proved.  The class-level conjuncts assume tameness only, while `B` also assumes
  `|X|`, `|X'|` paracompact (not derivable from tameness); `proposition_14_1_8_pullMult` needs only
  `X` tame, `B` both.  The other conjuncts are statements about representatives `W ←Φ V →Ψ W'`
  (`SDiagram`), single equivalences (`PullMap`, `pushMult F`), the hypotheses `FacePull_hyp` /
  `FacePush_hyp` and their proofs, and local lemmas on face-wise sc⁺-sections; `B` is about
  classes only and gives none of them.
-/

namespace RoundTrip.V14_44
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.IsScPlusOnFaceNear.of_restrict) ∧
  (type_of% @Polyfold.SBLocalization.isFaceScPlusSectionOn_iff_singleton.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isFaceScPlusSectionOn_of_localIso.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.facePull_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_localIso_act.{0}) ∧
  (type_of% @Polyfold.SBLocalization.facePush_hyp_of_equivalence.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isBoundaryStructurable_pushMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_pullMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isTame_B_ep.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_tame.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_pullMult_tame.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.facePull_hyp_id.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.facePull_hyp_of_boundary_eq_empty.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsFaceScPlusSectionOn.congr_of_eqOn_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.symm_mem_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.mem_boundary_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.exists_bdryPullData.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_pull_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.facePush_hyp_of_boundary_eq_empty.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isBoundaryWFunctor_pushMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pushMult_eq_bdry.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isBoundaryStructurable_pushMult_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_1_8_pullMult_hyp.{0})

theorem A_holds : A :=
  ⟨@Polyfold.IsScPlusOnFaceNear.of_restrict,
   @Polyfold.SBLocalization.isFaceScPlusSectionOn_iff_singleton.{0},
   @Polyfold.SBLocalization.isFaceScPlusSectionOn_of_localIso.{0},
   @Polyfold.SBLocalization.PullMap.facePull_hyp.{0},
   @Polyfold.SBLocalization.exists_localIso_act.{0},
   @Polyfold.SBLocalization.facePush_hyp_of_equivalence.{0},
   @Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull.{0},
   @Polyfold.SBLocalization.isBoundaryStructurable_pushMult.{0},
   @Polyfold.SBLocalization.proposition_14_1_8.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_pullMult.{0},
   @Polyfold.SBLocalization.SDiagram.isTame_B_ep.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_tame.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_pullMult_tame.{0},
   @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8.{0},
   @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult.{0},
   @Polyfold.SBLocalization.PullMap.facePull_hyp_id.{0},
   @Polyfold.SBLocalization.PullMap.facePull_hyp_of_boundary_eq_empty.{0},
   @Polyfold.SBLocalization.IsFaceScPlusSectionOn.congr_of_eqOn_boundary.{0},
   @Polyfold.SBLocalization.symm_mem_boundary.{0},
   @Polyfold.SBLocalization.PullMap.mem_boundary_iff.{0},
   @Polyfold.SBLocalization.PullMap.exists_bdryPullData.{0},
   @Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull_hyp.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_pull_hyp.{0},
   @Polyfold.SBLocalization.facePush_hyp_of_boundary_eq_empty.{0},
   @Polyfold.SBLocalization.isBoundaryWFunctor_pushMult.{0},
   @Polyfold.SBLocalization.pushMult_eq_bdry.{0},
   @Polyfold.SBLocalization.isBoundaryStructurable_pushMult_hyp.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_hyp.{0},
   @Polyfold.SBLocalization.proposition_14_1_8_pullMult_hyp.{0}⟩

/-- The main conjuncts (class level, `f̄_*` and `f̄^*`) give `B`. -/
theorem main_to_B
    (hpush : type_of% @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8.{0})
    (hpull : type_of% @Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult.{0}) : B :=
  fun _ _ _ hf hX _ hX' _ =>
    ⟨fun _ h => hpush hf hX hX' h, fun _ h => hpull hf hX h⟩

theorem A_to_B (hA : A) : B :=
  main_to_B hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#rt_check RoundTrip.V14_44.A_to_B [Polyfold.IsScPlusOnFaceNear.of_restrict,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_iff_singleton,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_of_localIso,
  Polyfold.SBLocalization.PullMap.facePull_hyp,
  Polyfold.SBLocalization.exists_localIso_act,
  Polyfold.SBLocalization.facePush_hyp_of_equivalence,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult,
  Polyfold.SBLocalization.proposition_14_1_8,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.SDiagram.isTame_B_ep,
  Polyfold.SBLocalization.proposition_14_1_8_tame,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_tame,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.PullMap.facePull_hyp_id,
  Polyfold.SBLocalization.PullMap.facePull_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.IsFaceScPlusSectionOn.congr_of_eqOn_boundary,
  Polyfold.SBLocalization.symm_mem_boundary,
  Polyfold.SBLocalization.PullMap.mem_boundary_iff,
  Polyfold.SBLocalization.PullMap.exists_bdryPullData,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pull_hyp,
  Polyfold.SBLocalization.facePush_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.isBoundaryWFunctor_pushMult,
  Polyfold.SBLocalization.pushMult_eq_bdry,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_hyp]
#rt_check RoundTrip.V14_44.main_to_B [Polyfold.IsScPlusOnFaceNear.of_restrict,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_iff_singleton,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_of_localIso,
  Polyfold.SBLocalization.PullMap.facePull_hyp,
  Polyfold.SBLocalization.exists_localIso_act,
  Polyfold.SBLocalization.facePush_hyp_of_equivalence,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult,
  Polyfold.SBLocalization.proposition_14_1_8,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.SDiagram.isTame_B_ep,
  Polyfold.SBLocalization.proposition_14_1_8_tame,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_tame,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.PullMap.facePull_hyp_id,
  Polyfold.SBLocalization.PullMap.facePull_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.IsFaceScPlusSectionOn.congr_of_eqOn_boundary,
  Polyfold.SBLocalization.symm_mem_boundary,
  Polyfold.SBLocalization.PullMap.mem_boundary_iff,
  Polyfold.SBLocalization.PullMap.exists_bdryPullData,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pull_hyp,
  Polyfold.SBLocalization.facePush_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.isBoundaryWFunctor_pushMult,
  Polyfold.SBLocalization.pushMult_eq_bdry,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_hyp]
#rt_overlap RoundTrip.V14_44.A_to_B [Polyfold.IsScPlusOnFaceNear.of_restrict,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_iff_singleton,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_of_localIso,
  Polyfold.SBLocalization.PullMap.facePull_hyp,
  Polyfold.SBLocalization.exists_localIso_act,
  Polyfold.SBLocalization.facePush_hyp_of_equivalence,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult,
  Polyfold.SBLocalization.proposition_14_1_8,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.SDiagram.isTame_B_ep,
  Polyfold.SBLocalization.proposition_14_1_8_tame,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_tame,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8,
  Polyfold.SBLocalization.GenSBMap.proposition_14_1_8_pullMult,
  Polyfold.SBLocalization.PullMap.facePull_hyp_id,
  Polyfold.SBLocalization.PullMap.facePull_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.IsFaceScPlusSectionOn.congr_of_eqOn_boundary,
  Polyfold.SBLocalization.symm_mem_boundary,
  Polyfold.SBLocalization.PullMap.mem_boundary_iff,
  Polyfold.SBLocalization.PullMap.exists_bdryPullData,
  Polyfold.SBLocalization.PullMap.isBoundaryStructurable_pull_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pull_hyp,
  Polyfold.SBLocalization.facePush_hyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.isBoundaryWFunctor_pushMult,
  Polyfold.SBLocalization.pushMult_eq_bdry,
  Polyfold.SBLocalization.isBoundaryStructurable_pushMult_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_hyp,
  Polyfold.SBLocalization.proposition_14_1_8_pullMult_hyp]

end RoundTrip.V14_44
