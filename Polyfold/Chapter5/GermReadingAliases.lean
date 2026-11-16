import Polyfold.Chapter3.Chapter5BridgeG
import Polyfold.Chapter3.FredholmGermIndexG
import Polyfold.Chapter3.FredholmGermLinearizationG
import Polyfold.Chapter3.FredholmGermLinearizationScG
import Polyfold.Chapter3.FredholmSectionsG
import Polyfold.Chapter3.GermFillingChart
import Polyfold.Chapter3.GlobalIFTCenterG
import Polyfold.Chapter3.GlobalIFTFullG
import Polyfold.Chapter3.GlobalIFTG
import Polyfold.Chapter3.GlobalIFTIndexG
import Polyfold.Chapter3.GlobalIFTNearbyGraphG
import Polyfold.Chapter3.GlobalIFTNearbyKernelG
import Polyfold.Chapter3.GlobalIFTNearbyOntoG
import Polyfold.Chapter3.GlobalIFTNearbySurjG
import Polyfold.Chapter3.GlobalIFTTheoremsG
import Polyfold.Chapter3.GoodPositionGermG
import Polyfold.Chapter3.GoodPositionScG
import Polyfold.Chapter5.IndexLocallyConstantG
import Polyfold.Chapter3.LinearizationChartsG
import Polyfold.Chapter3.LinearizationChartsScG
import Polyfold.Chapter4.NonVacuityG
import Polyfold.Chapter3.ParamPerturbationG
import Polyfold.Chapter3.SectionCompactnessG
import Polyfold.Chapter3.TameGermsAddG
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1–§3.6: **the
`G` / `_germ` names of the germ-reading notions and theorems**, as aliases (Findings, Chapter 3,
items 330–339).

# `G` / `_germ` names (aliases)

## What is formalized

Nothing beyond aliases.  The germ-reading notions have the canonical names (`IsScFredholmGerm`,
`IsScFredholmSection`, `theorem_3_6_8`, …), the project's whole-chart notions and theorems the
suffix `…WholeChart` / `…_wholeChart`.  This file gives the germ-reading notions the names
`IsScFredholmGermG`, `IsScFredholmSectionG`, `IsScFredholmGermTameG`, `IsScFredholmSectionTameG`,
`IsGoodPositionGermG`, `IsGoodPositionGermTameG`, `IsGoodPositionGermFilledG`,
`IsGoodPositionGermScG` (as `abbrev`s) and the germ-reading theorems the names `X_germ` (or
`…G_…`) (as `alias`es).

## What the text leaves implicit, and the choices made

* A name without suffix denotes the germ reading, the statement with the text's hypotheses; only
  the `G` / `_germ` names need an alias.
-/

noncomputable section

namespace Polyfold

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)

/-- Alias of `StrongBundle.IsScFredholmGerm` (Definition 3.1.11 (preprint 3.11), germ reading). -/
abbrev StrongBundle.IsScFredholmGermG (f : X → Y) (x₀ : X) : Prop := B.IsScFredholmGerm f x₀

/-- Alias of `StrongBundle.IsScFredholmSection` (Definition 3.1.16 (preprint 3.14), germ reading). -/
abbrev StrongBundle.IsScFredholmSectionG (f : X → Y) : Prop := B.IsScFredholmSection f

/-- Alias of `StrongBundle.IsScFredholmGermTame` (Definition 3.6.3 (preprint 3.50), germ reading). -/
abbrev StrongBundle.IsScFredholmGermTameG (f : X → Y) (x₀ : X) : Prop := B.IsScFredholmGermTame f x₀

/-- Alias of `StrongBundle.IsScFredholmSectionTame` (Definition 3.6.4 (preprint 3.51), germ reading). -/
abbrev StrongBundle.IsScFredholmSectionTameG (f : X → Y) : Prop := B.IsScFredholmSectionTame f

/-- Alias of `StrongBundle.IsGoodPositionGerm` (Definition 3.6.6 (preprint 3.53), germ reading). -/
abbrev StrongBundle.IsGoodPositionGermG (f : X → Y) (x₀ : X) : Prop := B.IsGoodPositionGerm f x₀

/-- Alias of `StrongBundle.IsGoodPositionGermTame` (Definition 3.6.6 (preprint 3.53) in a tame chart, germ reading). -/
abbrev StrongBundle.IsGoodPositionGermTameG (f : X → Y) (x₀ : X) : Prop := B.IsGoodPositionGermTame f x₀

/-- Alias of `StrongBundle.IsGoodPositionGermFilled` (the strengthened good position of Theorem 3.6.8 (preprint 3.54) (1), germ reading). -/
abbrev StrongBundle.IsGoodPositionGermFilledG (f : X → Y) (x₀ : X) : Prop := B.IsGoodPositionGermFilled f x₀

/-- Alias of `StrongBundle.IsGoodPositionGermSc` (good position with an sc-complement, germ reading). -/
abbrev StrongBundle.IsGoodPositionGermScG (f : X → Y) (x₀ : X) : Prop := B.IsGoodPositionGermSc f x₀

end Bundle

/-- Alias of `ConjugationData.index_eq`. -/
alias ConjugationData.index_eq_germ := ConjugationData.index_eq

/-- Alias of `ConjugationData.scDeriv_isFredholm_index`. -/
alias ConjugationData.scDeriv_isFredholm_index_germ := ConjugationData.scDeriv_isFredholm_index

/-- Alias of `ConjugationData.scDeriv_isRegularizing`. -/
alias ConjugationData.scDeriv_isRegularizing_germ := ConjugationData.scDeriv_isRegularizing

/-- Alias of `ConjugationData.scDeriv_isScFredholm`. -/
alias ConjugationData.scDeriv_isScFredholm_germ := ConjugationData.scDeriv_isScFredholm

/-- Alias of `HalfSpaceBundle.hypotheses_theorem_3_6_11_halfSpace`. -/
alias HalfSpaceBundle.hypotheses_theorem_3_6_11_halfSpace_germ := HalfSpaceBundle.hypotheses_theorem_3_6_11_halfSpace

/-- Alias of `HalfSpaceBundle.isGoodPositionGermTame_graphSection`. -/
alias HalfSpaceBundle.isGoodPositionGermTameG_graphSection := HalfSpaceBundle.isGoodPositionGermTame_graphSection

/-- Alias of `HalfSpaceBundle.isScFredholmGermTame_graphSection`. -/
alias HalfSpaceBundle.isScFredholmGermTameG_graphSection := HalfSpaceBundle.isScFredholmGermTame_graphSection

/-- Alias of `HalfSpaceBundle.isScFredholmSection_graphSection`. -/
alias HalfSpaceBundle.isScFredholmSectionG_graphSection := HalfSpaceBundle.isScFredholmSection_graphSection

/-- Alias of `HalfSpaceBundle.isScFredholmSectionTame_graphSection`. -/
alias HalfSpaceBundle.isScFredholmSectionTameG_graphSection := HalfSpaceBundle.isScFredholmSectionTame_graphSection

/-- Alias of `IsConjugateToBasicGerm.scDeriv_isFredholm`. -/
alias IsConjugateToBasicGerm.scDeriv_isFredholm_germ := IsConjugateToBasicGerm.scDeriv_isFredholm

/-- Alias of `IsStrongBundleIso.pushforward_ker_isInGoodPosition`. -/
alias IsStrongBundleIso.pushforward_ker_isInGoodPosition_germ := IsStrongBundleIso.pushforward_ker_isInGoodPosition

/-- Alias of `IsStrongBundleIso.pushforward_linearization`. -/
alias IsStrongBundleIso.pushforward_linearization_germ := IsStrongBundleIso.pushforward_linearization

/-- Alias of `IsStrongBundleIso.pushforward_surjective`. -/
alias IsStrongBundleIso.pushforward_surjective_germ := IsStrongBundleIso.pushforward_surjective

/-- Alias of `StrongBundle.IsGoodPositionGermWholeChart.isGoodPositionGerm`. -/
alias StrongBundle.IsGoodPositionGerm.isGoodPositionGermG := StrongBundle.IsGoodPositionGermWholeChart.isGoodPositionGerm

/-- Alias of `StrongBundle.IsGoodPositionGermFilledWholeChart.isGoodPositionGermFilled`. -/
alias StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermFilledG := StrongBundle.IsGoodPositionGermFilledWholeChart.isGoodPositionGermFilled

/-- Alias of `StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame`. -/
alias StrongBundle.IsGoodPositionGermFilledG.isGoodPositionGermTameG := StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame

/-- Alias of `StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex`. -/
alias StrongBundle.IsGoodPositionGermG.exists_isSurjLinOfIndex := StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex

/-- Alias of `StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm`. -/
alias StrongBundle.IsGoodPositionGermG.forall_isGoodPositionAtGerm := StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm

/-- Alias of `StrongBundle.IsGoodPositionGerm.isLinSurjAt`. -/
alias StrongBundle.IsGoodPositionGermG.isLinSurjAt := StrongBundle.IsGoodPositionGerm.isLinSurjAt

/-- Alias of `StrongBundle.IsGoodPositionGerm.isScFredholmGerm`. -/
alias StrongBundle.IsGoodPositionGermG.isScFredholmGermG := StrongBundle.IsGoodPositionGerm.isScFredholmGerm

/-- Alias of `StrongBundle.IsGoodPositionGerm.toTame`. -/
alias StrongBundle.IsGoodPositionGermG.toTame := StrongBundle.IsGoodPositionGerm.toTame

/-- Alias of `StrongBundle.IsGoodPositionGermScWholeChart.isGoodPositionGermSc`. -/
alias StrongBundle.IsGoodPositionGermSc.isGoodPositionGermScG := StrongBundle.IsGoodPositionGermScWholeChart.isGoodPositionGermSc

/-- Alias of `StrongBundle.IsGoodPositionGermSc.isGoodPositionGermTame`. -/
alias StrongBundle.IsGoodPositionGermScG.isGoodPositionGermTameG := StrongBundle.IsGoodPositionGermSc.isGoodPositionGermTame

/-- Alias of `StrongBundle.IsGoodPositionGermTameWholeChart.isGoodPositionGermTame`. -/
alias StrongBundle.IsGoodPositionGermTame.isGoodPositionGermTameG := StrongBundle.IsGoodPositionGermTameWholeChart.isGoodPositionGermTame

/-- Alias of `StrongBundle.IsGoodPositionGermTame.congr_nhds`. -/
alias StrongBundle.IsGoodPositionGermTameG.congr_nhds := StrongBundle.IsGoodPositionGermTame.congr_nhds

/-- Alias of `StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm`. -/
alias StrongBundle.IsGoodPositionGermTameG.isGoodPositionGermG := StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm

/-- Alias of `StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc`. -/
alias StrongBundle.IsGoodPositionGermTameG.isGoodPositionGermScG := StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc

/-- Alias of `StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame`. -/
alias StrongBundle.IsGoodPositionGermTameG.isScFredholmGermTameG := StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame

/-- Alias of `StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm`. -/
alias StrongBundle.IsScFredholmGerm.isScFredholmGermG := StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm

/-- Alias of `StrongBundle.IsScFredholmGermWholeChart.sectionAdd_germG`. -/
alias StrongBundle.IsScFredholmGerm.sectionAdd_germG := StrongBundle.IsScFredholmGermWholeChart.sectionAdd_germG

/-- Alias of `StrongBundle.IsScFredholmGerm.param`. -/
alias StrongBundle.IsScFredholmGermG.param := StrongBundle.IsScFredholmGerm.param

/-- Alias of `StrongBundle.IsScFredholmGerm.sectionAdd`. -/
alias StrongBundle.IsScFredholmGermG.sectionAdd := StrongBundle.IsScFredholmGerm.sectionAdd

/-- Alias of `StrongBundle.IsScFredholmGermTameWholeChart.isScFredholmGermTame`. -/
alias StrongBundle.IsScFredholmGermTame.isScFredholmGermTameG := StrongBundle.IsScFredholmGermTameWholeChart.isScFredholmGermTame

/-- Alias of `StrongBundle.IsScFredholmGermTame.isScFredholmGerm`. -/
alias StrongBundle.IsScFredholmGermTameG.isScFredholmGermG := StrongBundle.IsScFredholmGermTame.isScFredholmGerm

/-- Alias of `StrongBundle.IsScFredholmGermTame.param`. -/
alias StrongBundle.IsScFredholmGermTameG.param := StrongBundle.IsScFredholmGermTame.param

/-- Alias of `StrongBundle.IsScFredholmGermTame.sectionAdd`. -/
alias StrongBundle.IsScFredholmGermTameG.sectionAdd := StrongBundle.IsScFredholmGermTame.sectionAdd

/-- Alias of `StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection`. -/
alias StrongBundle.IsScFredholmSection.isScFredholmSectionG := StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection

/-- Alias of `StrongBundle.IsScFredholmSection.germ`. -/
alias StrongBundle.IsScFredholmSectionG.germ := StrongBundle.IsScFredholmSection.germ

/-- Alias of `StrongBundle.IsScFredholmSection.isScSmooth`. -/
alias StrongBundle.IsScFredholmSectionG.isScSmooth := StrongBundle.IsScFredholmSection.isScSmooth

/-- Alias of `StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt`. -/
alias StrongBundle.IsScFredholmSectionG.mem_smoothSet_of_isZeroAt := StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt

/-- Alias of `StrongBundle.IsScFredholmSection.param`. -/
alias StrongBundle.IsScFredholmSectionG.param := StrongBundle.IsScFredholmSection.param

/-- Alias of `StrongBundle.IsScFredholmSection.regularizing`. -/
alias StrongBundle.IsScFredholmSectionG.regularizing := StrongBundle.IsScFredholmSection.regularizing

/-- Alias of `StrongBundle.IsScFredholmSectionTameWholeChart.isScFredholmSectionTame`. -/
alias StrongBundle.IsScFredholmSectionTame.isScFredholmSectionTameG := StrongBundle.IsScFredholmSectionTameWholeChart.isScFredholmSectionTame

/-- Alias of `StrongBundle.IsScFredholmSectionTame.germTame`. -/
alias StrongBundle.IsScFredholmSectionTameG.germTame := StrongBundle.IsScFredholmSectionTame.germTame

/-- Alias of `StrongBundle.IsScFredholmSectionTame.param`. -/
alias StrongBundle.IsScFredholmSectionTameG.param := StrongBundle.IsScFredholmSectionTame.param

/-- Alias of `StrongBundle.IsScFredholmSectionTame.toIsScFredholmSection`. -/
alias StrongBundle.IsScFredholmSectionTameG.toIsScFredholmSectionG := StrongBundle.IsScFredholmSectionTame.toIsScFredholmSection

/-- Alias of `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`. -/
alias StrongBundle.isGoodPositionGermG_iff_isLinSurjAt := StrongBundle.isGoodPositionGerm_iff_isLinSurjAt

/-- Alias of `StrongBundle.isGoodPositionGerm_of_chart`. -/
alias StrongBundle.isGoodPositionGermG_of_chart := StrongBundle.isGoodPositionGerm_of_chart

/-- Alias of `StrongBundle.isGoodPositionGerm_of_isLinSurjAt`. -/
alias StrongBundle.isGoodPositionGermG_of_isLinSurjAt := StrongBundle.isGoodPositionGerm_of_isLinSurjAt

/-- Alias of `StrongBundle.isGoodPositionGerm_of_linAt_surj`. -/
alias StrongBundle.isGoodPositionGermG_of_linAt_surj := StrongBundle.isGoodPositionGerm_of_linAt_surj

/-- Alias of `StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`. -/
alias StrongBundle.isGoodPositionGermG_of_linAt_surj_of_degIndex_eq_zero := StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero

/-- Alias of `StrongBundle.isGoodPositionGermSc_iff`. -/
alias StrongBundle.isGoodPositionGermScG_iff := StrongBundle.isGoodPositionGermSc_iff

/-- Alias of `StrongBundle.isGoodPositionGermTame_of_chart_dense`. -/
alias StrongBundle.isGoodPositionGermTameG_of_chart_dense := StrongBundle.isGoodPositionGermTame_of_chart_dense

/-- Alias of `StrongBundle.isLinOfIndex_of_conjugationData`. -/
alias StrongBundle.isLinOfIndex_of_conjugationData_germ := StrongBundle.isLinOfIndex_of_conjugationData

/-- Alias of `StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex`. -/
alias StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_germ := StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex

/-- Alias of `StrongBundle.isSurjLinOfIndex_of_conjugationData`. -/
alias StrongBundle.isSurjLinOfIndex_of_conjugationData_germ := StrongBundle.isSurjLinOfIndex_of_conjugationData

/-- Alias of `StrongBundle.linAt_index_of_conjugationData`. -/
alias StrongBundle.linAt_index_of_conjugationData_germ := StrongBundle.linAt_index_of_conjugationData

/-- Alias of `StrongBundle.linAt_isScFredholm`. -/
alias StrongBundle.linAt_isScFredholm_germ := StrongBundle.linAt_isScFredholm

/-- Alias of `StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`. -/
alias StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_germ := StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex

/-- Alias of `StrongBundle.linAt_sc_of_germ`. -/
alias StrongBundle.linAt_sc_of_germ_germ := StrongBundle.linAt_sc_of_germ

/-- Alias of `StrongBundle.regularizing_paramLift`. -/
alias StrongBundle.regularizing_paramLift_germ := StrongBundle.regularizing_paramLift

/-- Alias of `StrongBundle.regularizing_sectionAdd`. -/
alias StrongBundle.regularizing_sectionAdd_germ := StrongBundle.regularizing_sectionAdd

/-- Alias of `TrivialBundle.htame_fails_hypotheses_theorem_3_6_11_hold`. -/
alias TrivialBundle.htame_fails_hypotheses_theorem_3_6_11_hold_germ := TrivialBundle.htame_fails_hypotheses_theorem_3_6_11_hold

/-- Alias of `TrivialBundle.hypotheses_theorem_3_6_11_graphSection`. -/
alias TrivialBundle.hypotheses_theorem_3_6_11_graphSection_germ := TrivialBundle.hypotheses_theorem_3_6_11_graphSection

/-- Alias of `TrivialBundle.hypotheses_theorem_3_6_11_linear`. -/
alias TrivialBundle.hypotheses_theorem_3_6_11_linear_germ := TrivialBundle.hypotheses_theorem_3_6_11_linear

/-- Alias of `TrivialBundle.isGoodPositionGermTame_graphSection`. -/
alias TrivialBundle.isGoodPositionGermTameG_graphSection := TrivialBundle.isGoodPositionGermTame_graphSection

/-- Alias of `TrivialBundle.isScFredholmGermTame_graphSection`. -/
alias TrivialBundle.isScFredholmGermTameG_graphSection := TrivialBundle.isScFredholmGermTame_graphSection

/-- Alias of `TrivialBundle.isScFredholmSection_graphSection`. -/
alias TrivialBundle.isScFredholmSectionG_graphSection := TrivialBundle.isScFredholmSection_graphSection

/-- Alias of `TrivialBundle.isScFredholmSectionTame_graphSection`. -/
alias TrivialBundle.isScFredholmSectionTameG_graphSection := TrivialBundle.isScFredholmSectionTame_graphSection

/-- Alias of `corollary_3_1_15_preprint`. -/
alias corollary_3_1_15_germ := corollary_3_1_15_preprint

/-- Alias of `corollary_3_1_15_section`. -/
alias corollary_3_1_15_section_germ := corollary_3_1_15_section

/-- Alias of `corollary_3_1_27`. -/
alias corollary_3_1_27_germ := corollary_3_1_27

/-- Alias of `corollary_3_1_27_sc`. -/
alias corollary_3_1_27_sc_germ := corollary_3_1_27_sc

/-- Alias of `forall_isGoodPositionGermSc_iff`. -/
alias forall_isGoodPositionGermScG_iff := forall_isGoodPositionGermSc_iff

/-- Alias of `index_locally_constant_of_admitsBumpFunctions`. -/
alias index_locally_constant_of_admitsBumpFunctions_germ := index_locally_constant_of_admitsBumpFunctions

/-- Alias of `isGoodPositionGermFilled_of_isGoodPositionGerm`. -/
alias isGoodPositionGermFilledG_of_isGoodPositionGermG := isGoodPositionGermFilled_of_isGoodPositionGerm

/-- Alias of `isGoodPositionGermTame_paramSection_of_isParamGP`. -/
alias isGoodPositionGermTameG_paramSection_of_isParamGP := isGoodPositionGermTame_paramSection_of_isParamGP

/-- Alias of `isSurjLinOfIndex_of_forall_dim`. -/
alias isSurjLinOfIndex_of_forall_dim_germ := isSurjLinOfIndex_of_forall_dim

/-- Alias of `linAt_paramSection`. -/
alias linAt_paramSection_germ := linAt_paramSection

/-- Alias of `linAt_paramSection_zero`. -/
alias linAt_paramSection_zero_germ := linAt_paramSection_zero

/-- Alias of `proposition_3_6_5_preprint`. -/
alias proposition_3_6_5_germ := proposition_3_6_5_preprint

/-- Alias of `proposition_3_6_5_index`. -/
alias proposition_3_6_5_index_germ := proposition_3_6_5_index

/-- Alias of `proposition_3_6_5_local`. -/
alias proposition_3_6_5_local_germ := proposition_3_6_5_local

/-- Alias of `proposition_3_6_5_local_index`. -/
alias proposition_3_6_5_local_index_germ := proposition_3_6_5_local_index

/-- Alias of `proposition_3_6_5_local_sc`. -/
alias proposition_3_6_5_local_sc_germ := proposition_3_6_5_local_sc

/-- Alias of `proposition_3_6_5_sc`. -/
alias proposition_3_6_5_sc_germ := proposition_3_6_5_sc

/-- Alias of `scDeriv_paramSection`. -/
alias scDeriv_paramSection_germ := scDeriv_paramSection

/-- Alias of `theorem_3_1_13_preprint`. -/
alias theorem_3_1_13_germ := theorem_3_1_13_preprint

/-- Alias of `theorem_3_1_18_preprint`. -/
alias theorem_3_1_18_germ := theorem_3_1_18_preprint

/-- Alias of `theorem_3_1_18_tame`. -/
alias theorem_3_1_18_tame_germ := theorem_3_1_18_tame

/-- Alias of `theorem_3_1_21_preprint`. -/
alias theorem_3_1_21_germ := theorem_3_1_21_preprint

/-- Alias of `theorem_3_1_21'`. -/
alias theorem_3_1_21_germ' := theorem_3_1_21'

/-- Alias of `theorem_3_1_21_tame`. -/
alias theorem_3_1_21_tame_germ := theorem_3_1_21_tame

/-- Alias of `theorem_3_1_22'`. -/
alias theorem_3_1_22'_germ := theorem_3_1_22'

/-- Alias of `theorem_3_1_22`. -/
alias theorem_3_1_22_germ := theorem_3_1_22

/-- Alias of `theorem_3_1_22_index`. -/
alias theorem_3_1_22_index_germ := theorem_3_1_22_index

/-- Alias of `theorem_3_1_22_linearization`. -/
alias theorem_3_1_22_linearization_germ := theorem_3_1_22_linearization

/-- Alias of `theorem_3_1_22_linearization_index`. -/
alias theorem_3_1_22_linearization_index_germ := theorem_3_1_22_linearization_index

/-- Alias of `theorem_3_1_22_linearization_sc`. -/
alias theorem_3_1_22_linearization_sc_germ := theorem_3_1_22_linearization_sc

/-- Alias of `theorem_3_1_22_of_surjective`. -/
alias theorem_3_1_22_of_surjective_germ := theorem_3_1_22_of_surjective

/-- Alias of `theorem_3_1_26'`. -/
alias theorem_3_1_26'_germ := theorem_3_1_26'

/-- Alias of `theorem_3_1_26`. -/
alias theorem_3_1_26_germ := theorem_3_1_26

/-- Alias of `theorem_3_1_26_index`. -/
alias theorem_3_1_26_index_germ := theorem_3_1_26_index

/-- Alias of `theorem_3_1_26_of_nearby`. -/
alias theorem_3_1_26_of_nearby_germ := theorem_3_1_26_of_nearby

/-- Alias of `theorem_3_1_26_sc`. -/
alias theorem_3_1_26_sc_germ := theorem_3_1_26_sc

/-- Alias of `theorem_3_6_8'`. -/
alias theorem_3_6_8'_germ := theorem_3_6_8'

/-- Alias of `theorem_3_6_8_chart_graph`. -/
alias theorem_3_6_8_chart_graph_germ := theorem_3_6_8_chart_graph

/-- Alias of `theorem_3_6_8_chart_kernel`. -/
alias theorem_3_6_8_chart_kernel_germ := theorem_3_6_8_chart_kernel

/-- Alias of `theorem_3_6_8_chart_onto`. -/
alias theorem_3_6_8_chart_onto_germ := theorem_3_6_8_chart_onto

/-- Alias of `theorem_3_6_8`. -/
alias theorem_3_6_8_germ := theorem_3_6_8

/-- Alias of `theorem_3_6_8_graph`. -/
alias theorem_3_6_8_graph_germ := theorem_3_6_8_graph

/-- Alias of `theorem_3_6_8_graph_proj_conj`. -/
alias theorem_3_6_8_graph_proj_conj_germ := theorem_3_6_8_graph_proj_conj

/-- Alias of `theorem_3_6_8_graph_proj`. -/
alias theorem_3_6_8_graph_proj_germ := theorem_3_6_8_graph_proj

/-- Alias of `theorem_3_6_8_index`. -/
alias theorem_3_6_8_index_germ := theorem_3_6_8_index

/-- Alias of `theorem_3_6_8_index_locally_constant_general`. -/
alias theorem_3_6_8_index_locally_constant_general_germ := theorem_3_6_8_index_locally_constant_general

/-- Alias of `theorem_3_6_8_index_locally_constant`. -/
alias theorem_3_6_8_index_locally_constant_germ := theorem_3_6_8_index_locally_constant

/-- Alias of `theorem_3_6_8_index_locally_constant_sc`. -/
alias theorem_3_6_8_index_locally_constant_sc_germ := theorem_3_6_8_index_locally_constant_sc

/-- Alias of `theorem_3_6_8_ker_eq_tangent`. -/
alias theorem_3_6_8_ker_eq_tangent_germ := theorem_3_6_8_ker_eq_tangent

/-- Alias of `theorem_3_6_8_linear`. -/
alias theorem_3_6_8_linear_germ := theorem_3_6_8_linear

/-- Alias of `theorem_3_6_8_linear_of_isTameWith`. -/
alias theorem_3_6_8_linear_of_isTameWith_germ := theorem_3_6_8_linear_of_isTameWith

/-- Alias of `theorem_3_6_8_nearby`. -/
alias theorem_3_6_8_nearby_germ := theorem_3_6_8_nearby

/-- Alias of `theorem_3_6_8_nearby_kernel`. -/
alias theorem_3_6_8_nearby_kernel_germ := theorem_3_6_8_nearby_kernel

/-- Alias of `theorem_3_6_8_one'`. -/
alias theorem_3_6_8_one'_germ := theorem_3_6_8_one'

/-- Alias of `theorem_3_6_8_one`. -/
alias theorem_3_6_8_one_germ := theorem_3_6_8_one

/-- Alias of `theorem_3_6_8_one_sc`. -/
alias theorem_3_6_8_one_sc_germ := theorem_3_6_8_one_sc

/-- Alias of `theorem_3_6_8_one_sc_of_tame`. -/
alias theorem_3_6_8_one_sc_of_tame_germ := theorem_3_6_8_one_sc_of_tame

/-- Alias of `theorem_3_6_8_pushforward`. -/
alias theorem_3_6_8_pushforward_germ := theorem_3_6_8_pushforward

/-- Alias of `theorem_3_6_8_pushforward_section`. -/
alias theorem_3_6_8_pushforward_section_germ := theorem_3_6_8_pushforward_section

/-- Alias of `theorem_3_6_8_sc`. -/
alias theorem_3_6_8_sc_germ := theorem_3_6_8_sc

/-- Alias of `theorem_3_6_8_tangentGermChart`. -/
alias theorem_3_6_8_tangentGermChart_germ := theorem_3_6_8_tangentGermChart

/-- Alias of `theorem_3_6_8_tangentGermChart_index`. -/
alias theorem_3_6_8_tangentGermChart_index_germ := theorem_3_6_8_tangentGermChart_index

/-- Alias of `theorem_3_6_8_tangentGermChart_proj_conj`. -/
alias theorem_3_6_8_tangentGermChart_proj_conj_germ := theorem_3_6_8_tangentGermChart_proj_conj

/-- Alias of `theorem_3_6_8_tangentGermChart_proj`. -/
alias theorem_3_6_8_tangentGermChart_proj_germ := theorem_3_6_8_tangentGermChart_proj

/-- Alias of `theorem_3_6_8_tangentGermChart_solutionSet`. -/
alias theorem_3_6_8_tangentGermChart_solutionSet_germ := theorem_3_6_8_tangentGermChart_solutionSet

/-- Alias of `theorem_3_6_8_tangentGermChart_solutionSet_index`. -/
alias theorem_3_6_8_tangentGermChart_solutionSet_index_germ := theorem_3_6_8_tangentGermChart_solutionSet_index

/-- Alias of `theorem_3_6_8_two`. -/
alias theorem_3_6_8_two_germ := theorem_3_6_8_two

/-- Alias of `theorem_3_6_8_two_index`. -/
alias theorem_3_6_8_two_index_germ := theorem_3_6_8_two_index

/-- Alias of `theorem_3_6_10`. -/
alias theorem_3_6_10_germ := theorem_3_6_10

/-- Alias of `theorem_3_6_10_of_surjective`. -/
alias theorem_3_6_10_of_surjective_germ := theorem_3_6_10_of_surjective

/-- Alias of `theorem_3_6_10_sc`. -/
alias theorem_3_6_10_sc_germ := theorem_3_6_10_sc

/-- Alias of `theorem_3_6_10_tame`. -/
alias theorem_3_6_10_tame_germ := theorem_3_6_10_tame

/-- Alias of `theorem_3_6_11_dim`. -/
alias theorem_3_6_11_dim_germ := theorem_3_6_11_dim

/-- Alias of `theorem_3_6_11`. -/
alias theorem_3_6_11_germ := theorem_3_6_11

/-- Alias of `theorem_3_6_11_index`. -/
alias theorem_3_6_11_index_germ := theorem_3_6_11_index

/-- Alias of `theorem_3_6_11_sc`. -/
alias theorem_3_6_11_sc_germ := theorem_3_6_11_sc

end Polyfold
