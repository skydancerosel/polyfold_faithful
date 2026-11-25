import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_25

set_option maxSynthPendingDepth 3

/-! Round trip for V14_25 (2021 Proposition 14.4.6, p. 661; 2017: Proposition 14.5: local
constancy of `∼_z`).

The item lists 32 theorems (and vocabulary: `ZData`, `ZData.trivial`, `ZSections`,
`ZSections.zero`, `proposition_14_4_6_2_statement`, `HasThetaLocalEq`, `ZLimitSetting`,
`ZSections.CompatNbhd`, `ZLimitRep`); `A` is the conjunction of their types at universe `0`
(`tendsto_comp_of_eventually` and `eq_of_isPreconnected` at `.{0,0}`).  `B` is on `SEP.{0}`.

* `A_to_B`: (1) is `ZData.proposition_14_4_6_1_open` for `S = C.toZData` (it even gives
  `O ⊆ V̂_a`).  (2) is `ZConcrete.proposition_14_4_6_2 C`: the sequence `z_k ∈ V_a`,
  `i ∼_{z_k} i'`, `z_k → z₀` puts `z₀` in the closure of `{y ∈ ∂X | i ∼_y i'}`
  (`mem_closure_of_tendsto`), and the resulting neighbourhood filter statement gives an open
  `O ∋ z₀` (`mem_nhds_iff`).  `B`'s standing hypotheses (tame, paracompact orbit space,
  partitions of unity) and `z₀ ∈ cl_X(V_a)` are not used.
* `B ⇒ A` is not proved; the two statements differ: `A` states (1) for every `ZData` on every
  ep-groupoid (`B` only for the data `C.toZData` of a `ZConcrete`), states (2) for `ZConcrete`
  data **without** the standing hypotheses of Theorem 14.1.9 that `B` assumes, and at every
  point of the closure of `{y ∈ ∂X | i ∼_y i'}` (`B` only at limits of sequences; the closure
  and the sequential closure agree only for first countable `X`, which is not an instance here).
  `A` also contains the intermediate statements of the proof (`ZLimitSetting`, `ZLimitRep`,
  `HasThetaLocalEq`, sheet and natural-representation lemmas), which do not follow from `B`.
-/

namespace RoundTrip.V14_25
open Polyfold Polyfold.SBLocalization Filter Topology

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.ZData.Arc.eventually_srcInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.ZData.proposition_14_4_6_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.ZData.proposition_14_4_6_1_open.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.ZData.eventually_zClass_subset.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.ZData.trivial_zRel.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tendsto_comp_of_eventually.{0,0}) ∧
  (type_of% @Polyfold.EpGroupoid.Sheet.tendsto_srcInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Sheet.eventually_srcInv_eq_unit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZSections.arc_transport.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZSections.zRel_sections_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZSections.proposition_14_4_6_2_of_mem.{0}) ∧
  (type_of% @Polyfold.SBLocalization.HasThetaLocalEq.proposition_14_4_6_2.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.eq_of_isPreconnected.{0,0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_morOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_sheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.srcInv_unit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_U.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_sheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRepFinite.exists_sheet_of_mem_morOn.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitRep.mem_o_of_mem_W.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitRep.sheet_subset_M.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitRep.tau_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitRep.arc_transport.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitRep.sections_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_near.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_yb.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZLimitSetting.exists_limitRep.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sections_eq_of_theta_closure.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasThetaLocalEq_of_limit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_4_6_2_of_limit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZConcrete.proposition_14_4_6_2.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZConcrete.hasThetaLocalEq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.ZData.Arc.eventually_srcInv.{0},
    @Polyfold.EpGroupoid.ZData.proposition_14_4_6_1.{0},
    @Polyfold.EpGroupoid.ZData.proposition_14_4_6_1_open.{0},
    @Polyfold.EpGroupoid.ZData.eventually_zClass_subset.{0},
    @Polyfold.EpGroupoid.ZData.trivial_zRel.{0},
    @Polyfold.EpGroupoid.tendsto_comp_of_eventually.{0,0},
    @Polyfold.EpGroupoid.Sheet.tendsto_srcInv.{0},
    @Polyfold.EpGroupoid.Sheet.eventually_srcInv_eq_unit.{0},
    @Polyfold.SBLocalization.ZSections.arc_transport.{0},
    @Polyfold.SBLocalization.ZSections.zRel_sections_eq.{0},
    @Polyfold.SBLocalization.ZSections.proposition_14_4_6_2_of_mem.{0},
    @Polyfold.SBLocalization.HasThetaLocalEq.proposition_14_4_6_2.{0},
    @Polyfold.EpGroupoid.eq_of_isPreconnected.{0,0},
    @Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_morOn.{0},
    @Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_sheet.{0},
    @Polyfold.EpGroupoid.NaturalRepFinite.srcInv_unit.{0},
    @Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_U.{0},
    @Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_sheet.{0},
    @Polyfold.EpGroupoid.NaturalRepFinite.exists_sheet_of_mem_morOn.{0},
    @Polyfold.SBLocalization.ZLimitRep.mem_o_of_mem_W.{0},
    @Polyfold.SBLocalization.ZLimitRep.sheet_subset_M.{0},
    @Polyfold.SBLocalization.ZLimitRep.tau_eq.{0},
    @Polyfold.SBLocalization.ZLimitRep.arc_transport.{0},
    @Polyfold.SBLocalization.ZLimitRep.sections_eq.{0},
    @Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_near.{0},
    @Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_yb.{0},
    @Polyfold.SBLocalization.ZLimitSetting.exists_limitRep.{0},
    @Polyfold.SBLocalization.sections_eq_of_theta_closure.{0},
    @Polyfold.SBLocalization.hasThetaLocalEq_of_limit.{0},
    @Polyfold.SBLocalization.proposition_14_4_6_2_of_limit.{0},
    @Polyfold.SBLocalization.ZConcrete.proposition_14_4_6_2.{0},
    @Polyfold.SBLocalization.ZConcrete.hasThetaLocalEq.{0}⟩

theorem A_to_B : A → B := by
  intro hA
  have h1 : type_of% @Polyfold.EpGroupoid.ZData.proposition_14_4_6_1_open.{0} := hA.2.2.1
  have h2 : type_of% @Polyfold.SBLocalization.ZConcrete.proposition_14_4_6_2.{0} := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, h, -⟩ := hA
    exact h
  intro Ab T P E Q C _ _ _
  refine ⟨fun a _ z₀ _ i i' hz => ?_, fun a ha i i' zs z₀ hzs hrel hlim _ => ?_⟩
  · obtain ⟨O, hO, hz₀, -, hOz⟩ := h1 C.toZData hz
    exact ⟨O, hO, hz₀, fun z hz' => hOz z hz'.1⟩
  · have hcl : z₀ ∈ closure {y | y ∈ Ab.X.PObj.boundary ∧ C.toZData.ZRel a y i i'} :=
      mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ⟨(hzs k).2, hrel k⟩)
    obtain ⟨O, hOsub, hO, hz₀⟩ := mem_nhds_iff.1 (h2 C a ha z₀ i i' hcl)
    exact ⟨O, hO, hz₀, fun y hy => hOsub hy.1 hy.2⟩

#rt_check RoundTrip.V14_25.A_to_B [Polyfold.EpGroupoid.ZData.Arc.eventually_srcInv,
  Polyfold.EpGroupoid.ZData.proposition_14_4_6_1,
  Polyfold.EpGroupoid.ZData.proposition_14_4_6_1_open,
  Polyfold.EpGroupoid.ZData.eventually_zClass_subset,
  Polyfold.EpGroupoid.ZData.trivial_zRel,
  Polyfold.EpGroupoid.tendsto_comp_of_eventually,
  Polyfold.EpGroupoid.Sheet.tendsto_srcInv,
  Polyfold.EpGroupoid.Sheet.eventually_srcInv_eq_unit,
  Polyfold.SBLocalization.ZSections.arc_transport,
  Polyfold.SBLocalization.ZSections.zRel_sections_eq,
  Polyfold.SBLocalization.ZSections.proposition_14_4_6_2_of_mem,
  Polyfold.SBLocalization.HasThetaLocalEq.proposition_14_4_6_2,
  Polyfold.EpGroupoid.eq_of_isPreconnected,
  Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_morOn,
  Polyfold.EpGroupoid.NaturalRepFinite.unit_mem_sheet,
  Polyfold.EpGroupoid.NaturalRepFinite.srcInv_unit,
  Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_U,
  Polyfold.EpGroupoid.NaturalRepFinite.eq_of_mem_sheet,
  Polyfold.EpGroupoid.NaturalRepFinite.exists_sheet_of_mem_morOn,
  Polyfold.SBLocalization.ZLimitRep.mem_o_of_mem_W,
  Polyfold.SBLocalization.ZLimitRep.sheet_subset_M,
  Polyfold.SBLocalization.ZLimitRep.tau_eq,
  Polyfold.SBLocalization.ZLimitRep.arc_transport,
  Polyfold.SBLocalization.ZLimitRep.sections_eq,
  Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_near,
  Polyfold.SBLocalization.ZLimitSetting.exists_nbhd_yb,
  Polyfold.SBLocalization.ZLimitSetting.exists_limitRep,
  Polyfold.SBLocalization.sections_eq_of_theta_closure,
  Polyfold.SBLocalization.hasThetaLocalEq_of_limit,
  Polyfold.SBLocalization.proposition_14_4_6_2_of_limit,
  Polyfold.SBLocalization.ZConcrete.proposition_14_4_6_2,
  Polyfold.SBLocalization.ZConcrete.hasThetaLocalEq]

end RoundTrip.V14_25
