import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_78

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

/-! Round trip for V16_78 (2021 Theorem 16.6.6, p. 739; 2017: Theorem 16.8: the invariant
`Φ_{(f,o)}` of an oriented sc-Fredholm section).

`A` is the conjunction of the types of the 150 theorems of the item (the 34 definitions are
vocabulary).  **Universes**: every universe parameter is instantiated at `0` (`B` lives in
`Type`); this includes the two-parameter lemmas `EpGroupoid.branchedMeasure_congr_orientation`,
`EP.exists_bumps_near_compact`, `SBLocalization.exists_bumps_of_controlsCompactness(_cylinder)`
(`.{0,0}`) and `MPolyfold.exists_nhds_compact_connected` (`.{0}`).

The main form of `A` is `theorem_16_6_6_wellDefined_unconditional` (with
`theorem_16_6_6_integral_eq_unconditional`, `theorem_16_6_6_all_admissible_unconditional`).
Its standing hypothesis in the model of `o` is `CanonicalGermInput o (m + 1)`: **tame germ data
of the representative `F`** (`IsScFredholmSectionTame`) and index `m + 1` at the smooth points.
`B` assumes the index only.

* `A ⇒ B` is not proved: `B` gives no tame germ data.  `A_to_Btame` proves `A ⇒ B` with that one
  hypothesis added (`Btame`).
* `B ⇒ A` is not proved: `A` also states the effective integral `∮` (which `B` does not mention),
  `[τ]`-dependence for every `θ̂` and every `τ`, and some 140 auxiliary lemmas (the proof's
  intermediate steps, the witnesses, the ep-groupoid Stokes and cobordism lemmas).
  `B_to_AmainInt` proves that `B` gives the `∫`-content of the main form under its hypotheses
  (with the compact solution set of the text added).
* Why tameness is a real hypothesis: the 2021 sc-Fredholm notion (Definitions 3.1.16 = 3.6.4)
  does not put the germ data in a tame chart, and `∂Z = ∅` (`d_X ≡ 0`) does not move them there
  (`UntamedCorner.isScFredholmGerm2021_not_tame`, over an M-polyfold without boundary).  In that
  example no orientation topology exists (`UntamedCorner.not_theorem_12_5_3_conclusion`), so it is
  not an `OrientationRep`; whether an `OrientationRep` with `∂Z = ∅` forces tame germ data is not
  settled in the project.
* `#rt_check` passes for `A_to_Btame` and `B_to_AmainInt`.  The overlap of `B_to_AmainInt` is the
  vocabulary of the statements (proof fields of the definitions), not a proof step.
* `hyps_satisfiable`: `CanonicalGermInput` and `IsCanonicalSolutionSet` hold together on the
  circle section of the project (so the main form is not vacuous).
-/

namespace RoundTrip.V16_78
open Polyfold StrongPolyfoldBundle PolyfoldClass

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.hasRestrictedFamilies_of_germInput.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_seedCentre_of_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_seedCentre.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_seeds_of_function_bounded.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_isOpen_isReducedOntoAtPt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_relGPFamily_of_openInclusion.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_naturalRep_cubeRestr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cylExtension_restrMult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_collarAuxNorm_cylExtension_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasRestrictedCylinderFamilies.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_finite_centres.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.cylinderInput_canonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cylinderOrientationStatement_of_isCanonical.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFrom_generalPosition_iff_of_correspondence.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFrom_of_correspondence_generalPosition.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.isScFredholmSectionTame.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isRegularPerturbation_pushMult.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.middleCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.canonSum_pullOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.pullSection.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.orientedRep_rel_of_diagram_pullSection.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.toCompact_eq_of_diagram_pullSection.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_eq_of_diagram_pullSection.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.theorem_16_6_6_canonical_hypotheses_circle) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_hypotheses_z3) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isInheritedFrom_generalPosition_halfDisc) ∧
  (type_of% @Polyfold.CanonicalOrientationPullbackExamples.toCompact_eq_of_diagram_pullSection_circle) ∧
  (type_of% @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection) ∧
  (type_of% @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_cylinderInput.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_toCompact.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integralEff_toCompact.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordism_ofRegular.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordismEff_ofRegular.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.branchedMeasure_congr_orientation.{0,0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isRegularPerturbation_of_admissible.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_hcob_witness.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCanonicalPerturbation_canonical.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.exists_isCanonicalPerturbation_halfSEP) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_hcob_witness.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_mk_rep.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordism_refl.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordismEff_refl.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.integral_add.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.integralEff_add.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.integral_d_eq_zero_of_boundary.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedRep.integralEff_d_eq_zero_of_boundary.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_d_eq_zero.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_d_eq_zero.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add_d.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScForm.toStructure_add.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScForm.toStructure_zero.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.not_mem_boundary_of_eq_empty.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_reduction.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.exists_generalPosition_hyp.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_of_isStructurable.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_isRegularPerturbation.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isControlledBy_of_isRegularPerturbation.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.CanonicalInput.canonicalBumpInput.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integral_toCompact.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integralEff_toCompact.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_of_bump.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_partitions.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle) ∧
  (type_of% @Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_circle) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_transversal.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_canonicalInput_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFrom_iff_of_correspondence_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_relative_of_seeds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_seeds.{0}) ∧
  (type_of% @Polyfold.EP.exists_bumps_near_compact.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_bumps_of_controlsCompactness.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_bumps_of_controlsCompactness_cylinder.{0,0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.CanonicalBumpInput.canonicalGermInput.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_noBumps.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_of_restrictedFamilies.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_restrictedFamilies.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_of_restrictedFamilies.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.isOrInvariant.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonContinuous_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientationLoc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSectionOrientationLoc_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_cylinder_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isTransversalPerturbation_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSectionOrientationLoc_restrOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOrInvariant_restrOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isIndexAt_restrSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedSolution.integral_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedSolution.integralEff_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_relative_of_families.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_families.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_restr.{0}) ∧
  (type_of% @Polyfold.LocalPart.exists_bump_near_compact.{0}) ∧
  (type_of% @Polyfold.LocalPart.exists_bump_near_compact_cube.{0}) ∧
  (type_of% @Polyfold.LocalPart.exists_bump_pos_on_compact_cube.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_preSeedRel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_seeds_of_function.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_seeds_of_function_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalParamSeedsRel_of_functions.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isParamOntoVecRel_localIso.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_naturalRep_component.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothOn_indicator_component.{0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_nhds_compact_connected.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_unconditional.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional.{0},
    @Polyfold.StrongPolyfoldBundle.hasRestrictedFamilies_of_germInput.{0},
    @Polyfold.SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres.{0},
    @Polyfold.SBLocalization.exists_seedCentre_of_le.{0},
    @Polyfold.SBLocalization.exists_seedCentre.{0},
    @Polyfold.SBLocalization.exists_seeds_of_function_bounded.{0},
    @Polyfold.SBLocalization.exists_isOpen_isReducedOntoAtPt.{0},
    @Polyfold.SBLocalization.exists_relGPFamily_of_openInclusion.{0},
    @Polyfold.SBLocalization.exists_naturalRep_cubeRestr.{0},
    @Polyfold.SBLocalization.cylExtension_restrMult.{0},
    @Polyfold.SBLocalization.pointwiseNorm_collarAuxNorm_cylExtension_restr.{0},
    @Polyfold.SBLocalization.hasRestrictedCylinderFamilies.{0},
    @Polyfold.SBLocalization.exists_finite_centres.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall.{0},
    @Polyfold.StrongPolyfoldBundle.cylinderInput_canonical.{0},
    @Polyfold.SBLocalization.cylinderOrientationStatement_of_isCanonical.{0},
    @Polyfold.StrongPolyfoldBundle.isInheritedFrom_generalPosition_iff_of_correspondence.{0},
    @Polyfold.StrongPolyfoldBundle.isInheritedFrom_of_correspondence_generalPosition.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition.{0},
    @Polyfold.SBLocalization.SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition.{0},
    @Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.isScFredholmSectionTame.{0},
    @Polyfold.StrongPolyfoldBundle.isRegularPerturbation_pushMult.{0},
    @Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.middleCanonical.{0},
    @Polyfold.SBLocalization.KernelBranching.canonSum_pullOr.{0},
    @Polyfold.SBLocalization.IsCanonicalFor.pullSection.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.orientedRep_rel_of_diagram_pullSection.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.toCompact_eq_of_diagram_pullSection.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_eq_of_diagram_pullSection.{0},
    @Polyfold.TrivialBundle.theorem_16_6_6_canonical_hypotheses_circle,
    @Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_hypotheses_z3,
    @Polyfold.HalfSpaceBundle.isInheritedFrom_generalPosition_halfDisc,
    @Polyfold.CanonicalOrientationPullbackExamples.toCompact_eq_of_diagram_pullSection_circle,
    @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection,
    @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc,
    @Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model.{0},
    @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_cylinderInput.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_toCompact.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.integralEff_toCompact.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordism_ofRegular.{0},
    @Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordismEff_ofRegular.{0},
    @Polyfold.EpGroupoid.branchedMeasure_congr_orientation.{0,0},
    @Polyfold.StrongPolyfoldBundle.isRegularPerturbation_of_admissible.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_hcob_witness.{0},
    @Polyfold.SBLocalization.isCanonicalPerturbation_canonical.{0},
    @Polyfold.HalfSpaceBundle.exists_isCanonicalPerturbation_halfSEP,
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_hcob_witness.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_mk_rep.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordism_refl.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordismEff_refl.{0},
    @Polyfold.PolyfoldClass.OrientedRep.integral_add.{0},
    @Polyfold.PolyfoldClass.OrientedRep.integralEff_add.{0},
    @Polyfold.PolyfoldClass.OrientedRep.integral_d_eq_zero_of_boundary.{0},
    @Polyfold.PolyfoldClass.OrientedRep.integralEff_d_eq_zero_of_boundary.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_d_eq_zero.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_d_eq_zero.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add_d.{0},
    @Polyfold.PolyfoldClass.ScForm.toStructure_add.{0},
    @Polyfold.PolyfoldClass.ScForm.toStructure_zero.{0},
    @Polyfold.PolyfoldClass.not_mem_boundary_of_eq_empty.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_reduction.{0},
    @Polyfold.StrongPolyfoldBundle.exists_generalPosition_hyp.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_of_isStructurable.{0},
    @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_isRegularPerturbation.{0},
    @Polyfold.StrongPolyfoldBundle.isControlledBy_of_isRegularPerturbation.{0},
    @Polyfold.StrongPolyfoldBundle.CanonicalInput.canonicalBumpInput.{0},
    @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integral_toCompact.{0},
    @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integralEff_toCompact.{0},
    @Polyfold.StrongPolyfoldBundle.ModelSolutionSet.isTransversalPerturbation.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_of_bump.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_partitions.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty.{0},
    @Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle,
    @Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_circle,
    @Polyfold.SBLocalization.corollary_15_3_10_3_transversal.{0},
    @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0},
    @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_canonicalInput_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder_all.{0},
    @Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d_all.{0},
    @Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_all.{0},
    @Polyfold.StrongPolyfoldBundle.isInheritedFrom_iff_of_correspondence_all.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition_all.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_relative_of_seeds.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_seeds.{0},
    @Polyfold.EP.exists_bumps_near_compact.{0,0},
    @Polyfold.SBLocalization.exists_bumps_of_controlsCompactness.{0,0},
    @Polyfold.SBLocalization.exists_bumps_of_controlsCompactness_cylinder.{0,0},
    @Polyfold.StrongPolyfoldBundle.CanonicalBumpInput.canonicalGermInput.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_noBumps.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_of_restrictedFamilies.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_restrictedFamilies.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_of_restrictedFamilies.{0},
    @Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc.{0},
    @Polyfold.StrongPolyfoldBundle.OrientationRep.isOrInvariant.{0},
    @Polyfold.SBLocalization.canonContinuous_loc.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientationLoc.{0},
    @Polyfold.SBLocalization.isSectionOrientationLoc_cubeOrientation.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_cylinder_loc.{0},
    @Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt_loc.{0},
    @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP.{0},
    @Polyfold.SBLocalization.isTransversalPerturbation_restr.{0},
    @Polyfold.SBLocalization.isSectionOrientationLoc_restrOr.{0},
    @Polyfold.SBLocalization.isOrInvariant_restrOr.{0},
    @Polyfold.SBLocalization.isIndexAt_restrSec.{0},
    @Polyfold.SBLocalization.IsCanonicalFor.restr.{0},
    @Polyfold.SBLocalization.OrientedSolution.integral_restr.{0},
    @Polyfold.SBLocalization.OrientedSolution.integralEff_restr.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_relative_of_families.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_families.{0},
    @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_loc.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_loc.{0},
    @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_restr.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_restr.{0},
    @Polyfold.LocalPart.exists_bump_near_compact.{0},
    @Polyfold.LocalPart.exists_bump_near_compact_cube.{0},
    @Polyfold.LocalPart.exists_bump_pos_on_compact_cube.{0},
    @Polyfold.SBLocalization.exists_preSeedRel.{0},
    @Polyfold.SBLocalization.exists_seeds_of_function.{0},
    @Polyfold.SBLocalization.exists_seeds_of_function_rel.{0},
    @Polyfold.SBLocalization.hasLocalParamSeedsRel_of_functions.{0},
    @Polyfold.SBLocalization.isParamOntoVecRel_localIso.{0},
    @Polyfold.EpGroupoid.exists_naturalRep_component.{0},
    @Polyfold.EpGroupoid.isScSmoothOn_indicator_component.{0},
    @Polyfold.MPolyfold.exists_nhds_compact_connected.{0}⟩

/-- `B` with the hypothesis of tame germ data of the representative of `o` added. -/
def Btame : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.boundary = ∅ →
    ∀ (f : c.FredholmSection) (o : StrongPolyfoldBundle.OrientationRep f) (m : ℕ),
    o.a.S.A.B.IsScFredholmSectionTame o.a.F →
    (∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((m + 1 : ℕ) : ℤ)) →
    (f : c.ScSection).HasCompactSolutionSet →
    ∀ (n : Y → ℝ) (U : Set Z),
    c.IsAuxNorm n → IsOpen U → (f : c.ScSection).solutionSet ⊆ U →
    (f : c.ScSection).ControlsCompactness n U →
      (∀ lam : c.ScPlusMultisection, Admissible f n U lam →
        ∃ Q : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
          Q.t = lam ∧ StrongPolyfoldBundle.IsCanonicalSolutionSet o Q) ∧
      (∀ Q : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q →
        ∀ (ω : c.polyfold.ScForm (m + 1)), PolyfoldClass.ScForm.d ω = 0 →
        ∀ (τ : c.polyfold.ScForm m),
          Q.toCompactOrientedSuborbifold.integral (ω + PolyfoldClass.ScForm.d τ) =
            Q.toCompactOrientedSuborbifold.integral ω) ∧
      (∀ Q Q' : StrongPolyfoldBundle.OrientedPerturbation (f : c.ScSection) m,
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q →
        Admissible f n U Q'.t → StrongPolyfoldBundle.IsCanonicalSolutionSet o Q' →
        ∀ (ω : c.polyfold.ScForm (m + 1)), PolyfoldClass.ScForm.d ω = 0 →
          Q.toCompactOrientedSuborbifold.integral ω =
            Q'.toCompactOrientedSuborbifold.integral ω)

/-- **`A ⇒ B` once tame germ data are assumed**: the main form
`theorem_16_6_6_wellDefined_unconditional` (the third conjunct of `A`) gives `B` with the
hypothesis `IsScFredholmSectionTame` added. -/
theorem A_to_Btame : A → Btame := by
  intro hA Y Z _ _ p c hbd f o m htame hidx _ n U hn hU _ hcc
  have H : CanonicalGermInput o (m + 1) := ⟨htame, hidx⟩
  obtain ⟨h1, h2, h3⟩ := hA.2.2.1 hbd hn hU hcc H
  refine ⟨fun lam hadm => ?_, fun Q _ _ ω _ τ => (h3 Q ω τ).1,
    fun Q Q' ha hc ha' hc' ω hω => (h2 Q Q' ha hc ha' hc' ω hω).1⟩
  obtain ⟨Q, hQ, -, hc⟩ := h1 lam hadm.1 hadm.2
  exact ⟨Q, hQ, hc⟩

/-- **The `∫`-content of the main form**, under its hypotheses (`CanonicalGermInput`) and the
compact solution set of the text: existence for every admissible `λ`, independence of `λ`, and
`[τ]`-dependence for the admissible canonically oriented `θ̂` and closed `τ`. -/
def AmainInt : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    {c : StrongPolyfoldBundle p}, c.polyfold.boundary = ∅ →
    ∀ {s : c.FredholmSection} {n : Y → ℝ}, c.IsAuxNorm n → ∀ {U : Set Z}, IsOpen U →
    s.1.ControlsCompactness n U → s.1.HasCompactSolutionSet →
    ∀ {m : ℕ} {o : OrientationRep s}, CanonicalGermInput o (m + 1) →
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet o Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U → IsCanonicalSolutionSet o Q₀ →
      Q₁.IsAdmissible n U → IsCanonicalSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 → Q₀.integral τ = Q₁.integral τ) ∧
    ∀ Q : OrientedPerturbation s.1 m, Q.IsAdmissible n U → IsCanonicalSolutionSet o Q →
      ∀ (τ : ScForm c.polyfold (m + 1)), ScForm.d τ = 0 → ∀ (η : ScForm c.polyfold m),
      Q.integral (τ + ScForm.d η) = Q.integral τ

/-- **`B` gives the `∫`-content of the main form of `A`.** -/
theorem B_to_AmainInt : B → AmainInt := by
  intro hB Y Z _ _ p c hbd s n hn U hU hcc hcpt m o H
  obtain ⟨h1, h2, h3⟩ := hB c hbd s o m H.index hcpt n U hn hU hcc.2.2.1 hcc
  refine ⟨fun t ht hgp => ?_, fun Q₀ Q₁ a₀ c₀ a₁ c₁ τ hτ => h3 Q₀ Q₁ a₀ c₀ a₁ c₁ τ hτ,
    fun Q a hc τ hτ η => h2 Q a hc τ hτ η⟩
  obtain ⟨Q, rfl, hc⟩ := h1 t ⟨ht, hgp⟩
  exact ⟨Q, rfl, ⟨ht, hgp⟩, hc⟩

/-- **The hypotheses of the main form are satisfiable together**: on the circle section of the
project, `CanonicalGermInput` holds in index `1` and an admissible canonically oriented `θ̂` with
nonempty support exists (from the item's witness
`TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle`). -/
theorem hyps_satisfiable :
    TrivialBundle.circlePolyfoldBundle.polyfold.boundary = ∅ ∧
    CanonicalGermInput TrivialBundle.circleOrientationRep (0 + 1) ∧
    ∃ Q : OrientedPerturbation TrivialBundle.circleFredholmSection.1 0,
      IsCanonicalSolutionSet TrivialBundle.circleOrientationRep Q := by
  obtain ⟨hbd, hB, -, Q, -, -, hQ⟩ :=
    Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle
  exact ⟨hbd, hB.canonicalGermInput, Q, hQ⟩

#rt_check RoundTrip.V16_78.A_to_Btame [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.hasRestrictedFamilies_of_germInput,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres,
  Polyfold.SBLocalization.exists_seedCentre_of_le,
  Polyfold.SBLocalization.exists_seedCentre,
  Polyfold.SBLocalization.exists_seeds_of_function_bounded,
  Polyfold.SBLocalization.exists_isOpen_isReducedOntoAtPt,
  Polyfold.SBLocalization.exists_relGPFamily_of_openInclusion,
  Polyfold.SBLocalization.exists_naturalRep_cubeRestr,
  Polyfold.SBLocalization.cylExtension_restrMult,
  Polyfold.SBLocalization.pointwiseNorm_collarAuxNorm_cylExtension_restr,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies,
  Polyfold.SBLocalization.exists_finite_centres,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall,
  Polyfold.StrongPolyfoldBundle.cylinderInput_canonical,
  Polyfold.SBLocalization.cylinderOrientationStatement_of_isCanonical,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_of_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition,
  Polyfold.SBLocalization.SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.isScFredholmSectionTame,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_pushMult,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.middleCanonical,
  Polyfold.SBLocalization.KernelBranching.canonSum_pullOr,
  Polyfold.SBLocalization.IsCanonicalFor.pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.orientedRep_rel_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.toCompact_eq_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_eq_of_diagram_pullSection,
  Polyfold.TrivialBundle.theorem_16_6_6_canonical_hypotheses_circle,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_hypotheses_z3,
  Polyfold.HalfSpaceBundle.isInheritedFrom_generalPosition_halfDisc,
  Polyfold.CanonicalOrientationPullbackExamples.toCompact_eq_of_diagram_pullSection_circle,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc,
  Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_cylinderInput,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordism_ofRegular,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordismEff_ofRegular,
  Polyfold.EpGroupoid.branchedMeasure_congr_orientation,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_of_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_hcob_witness,
  Polyfold.SBLocalization.isCanonicalPerturbation_canonical,
  Polyfold.HalfSpaceBundle.exists_isCanonicalPerturbation_halfSEP,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_hcob_witness,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_mk_rep,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordism_refl,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordismEff_refl,
  Polyfold.PolyfoldClass.OrientedRep.integral_add,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_add,
  Polyfold.PolyfoldClass.OrientedRep.integral_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add_d,
  Polyfold.PolyfoldClass.ScForm.toStructure_add,
  Polyfold.PolyfoldClass.ScForm.toStructure_zero,
  Polyfold.PolyfoldClass.not_mem_boundary_of_eq_empty,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_reduction,
  Polyfold.StrongPolyfoldBundle.exists_generalPosition_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_of_isStructurable,
  Polyfold.StrongPolyfoldBundle.OrientationRep.exists_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.isControlledBy_of_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.CanonicalInput.canonicalBumpInput,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_partitions,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_circle,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_canonicalInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder_all,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d_all,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_iff_of_correspondence_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition_all,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_seeds,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_seeds,
  Polyfold.EP.exists_bumps_near_compact,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness_cylinder,
  Polyfold.StrongPolyfoldBundle.CanonicalBumpInput.canonicalGermInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_noBumps,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isOrInvariant,
  Polyfold.SBLocalization.canonContinuous_loc,
  Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientationLoc,
  Polyfold.SBLocalization.isSectionOrientationLoc_cubeOrientation,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_loc,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt_loc,
  Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP,
  Polyfold.SBLocalization.isTransversalPerturbation_restr,
  Polyfold.SBLocalization.isSectionOrientationLoc_restrOr,
  Polyfold.SBLocalization.isOrInvariant_restrOr,
  Polyfold.SBLocalization.isIndexAt_restrSec,
  Polyfold.SBLocalization.IsCanonicalFor.restr,
  Polyfold.SBLocalization.OrientedSolution.integral_restr,
  Polyfold.SBLocalization.OrientedSolution.integralEff_restr,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_families,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_families,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_restr,
  Polyfold.LocalPart.exists_bump_near_compact,
  Polyfold.LocalPart.exists_bump_near_compact_cube,
  Polyfold.LocalPart.exists_bump_pos_on_compact_cube,
  Polyfold.SBLocalization.exists_preSeedRel,
  Polyfold.SBLocalization.exists_seeds_of_function,
  Polyfold.SBLocalization.exists_seeds_of_function_rel,
  Polyfold.SBLocalization.hasLocalParamSeedsRel_of_functions,
  Polyfold.SBLocalization.isParamOntoVecRel_localIso,
  Polyfold.EpGroupoid.exists_naturalRep_component,
  Polyfold.EpGroupoid.isScSmoothOn_indicator_component,
  Polyfold.MPolyfold.exists_nhds_compact_connected]
#rt_check RoundTrip.V16_78.B_to_AmainInt [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.hasRestrictedFamilies_of_germInput,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres,
  Polyfold.SBLocalization.exists_seedCentre_of_le,
  Polyfold.SBLocalization.exists_seedCentre,
  Polyfold.SBLocalization.exists_seeds_of_function_bounded,
  Polyfold.SBLocalization.exists_isOpen_isReducedOntoAtPt,
  Polyfold.SBLocalization.exists_relGPFamily_of_openInclusion,
  Polyfold.SBLocalization.exists_naturalRep_cubeRestr,
  Polyfold.SBLocalization.cylExtension_restrMult,
  Polyfold.SBLocalization.pointwiseNorm_collarAuxNorm_cylExtension_restr,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies,
  Polyfold.SBLocalization.exists_finite_centres,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall,
  Polyfold.StrongPolyfoldBundle.cylinderInput_canonical,
  Polyfold.SBLocalization.cylinderOrientationStatement_of_isCanonical,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_of_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition,
  Polyfold.SBLocalization.SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.isScFredholmSectionTame,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_pushMult,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.middleCanonical,
  Polyfold.SBLocalization.KernelBranching.canonSum_pullOr,
  Polyfold.SBLocalization.IsCanonicalFor.pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.orientedRep_rel_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.toCompact_eq_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_eq_of_diagram_pullSection,
  Polyfold.TrivialBundle.theorem_16_6_6_canonical_hypotheses_circle,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_hypotheses_z3,
  Polyfold.HalfSpaceBundle.isInheritedFrom_generalPosition_halfDisc,
  Polyfold.CanonicalOrientationPullbackExamples.toCompact_eq_of_diagram_pullSection_circle,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc,
  Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_cylinderInput,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordism_ofRegular,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordismEff_ofRegular,
  Polyfold.EpGroupoid.branchedMeasure_congr_orientation,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_of_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_hcob_witness,
  Polyfold.SBLocalization.isCanonicalPerturbation_canonical,
  Polyfold.HalfSpaceBundle.exists_isCanonicalPerturbation_halfSEP,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_hcob_witness,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_mk_rep,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordism_refl,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordismEff_refl,
  Polyfold.PolyfoldClass.OrientedRep.integral_add,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_add,
  Polyfold.PolyfoldClass.OrientedRep.integral_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add_d,
  Polyfold.PolyfoldClass.ScForm.toStructure_add,
  Polyfold.PolyfoldClass.ScForm.toStructure_zero,
  Polyfold.PolyfoldClass.not_mem_boundary_of_eq_empty,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_reduction,
  Polyfold.StrongPolyfoldBundle.exists_generalPosition_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_of_isStructurable,
  Polyfold.StrongPolyfoldBundle.OrientationRep.exists_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.isControlledBy_of_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.CanonicalInput.canonicalBumpInput,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_partitions,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_circle,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_canonicalInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder_all,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d_all,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_iff_of_correspondence_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition_all,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_seeds,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_seeds,
  Polyfold.EP.exists_bumps_near_compact,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness_cylinder,
  Polyfold.StrongPolyfoldBundle.CanonicalBumpInput.canonicalGermInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_noBumps,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isOrInvariant,
  Polyfold.SBLocalization.canonContinuous_loc,
  Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientationLoc,
  Polyfold.SBLocalization.isSectionOrientationLoc_cubeOrientation,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_loc,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt_loc,
  Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP,
  Polyfold.SBLocalization.isTransversalPerturbation_restr,
  Polyfold.SBLocalization.isSectionOrientationLoc_restrOr,
  Polyfold.SBLocalization.isOrInvariant_restrOr,
  Polyfold.SBLocalization.isIndexAt_restrSec,
  Polyfold.SBLocalization.IsCanonicalFor.restr,
  Polyfold.SBLocalization.OrientedSolution.integral_restr,
  Polyfold.SBLocalization.OrientedSolution.integralEff_restr,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_families,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_families,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_restr,
  Polyfold.LocalPart.exists_bump_near_compact,
  Polyfold.LocalPart.exists_bump_near_compact_cube,
  Polyfold.LocalPart.exists_bump_pos_on_compact_cube,
  Polyfold.SBLocalization.exists_preSeedRel,
  Polyfold.SBLocalization.exists_seeds_of_function,
  Polyfold.SBLocalization.exists_seeds_of_function_rel,
  Polyfold.SBLocalization.hasLocalParamSeedsRel_of_functions,
  Polyfold.SBLocalization.isParamOntoVecRel_localIso,
  Polyfold.EpGroupoid.exists_naturalRep_component,
  Polyfold.EpGroupoid.isScSmoothOn_indicator_component,
  Polyfold.MPolyfold.exists_nhds_compact_connected]
#rt_overlap RoundTrip.V16_78.B_to_AmainInt [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.hasRestrictedFamilies_of_germInput,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres,
  Polyfold.SBLocalization.exists_seedCentre_of_le,
  Polyfold.SBLocalization.exists_seedCentre,
  Polyfold.SBLocalization.exists_seeds_of_function_bounded,
  Polyfold.SBLocalization.exists_isOpen_isReducedOntoAtPt,
  Polyfold.SBLocalization.exists_relGPFamily_of_openInclusion,
  Polyfold.SBLocalization.exists_naturalRep_cubeRestr,
  Polyfold.SBLocalization.cylExtension_restrMult,
  Polyfold.SBLocalization.pointwiseNorm_collarAuxNorm_cylExtension_restr,
  Polyfold.SBLocalization.hasRestrictedCylinderFamilies,
  Polyfold.SBLocalization.exists_finite_centres,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall,
  Polyfold.StrongPolyfoldBundle.cylinderInput_canonical,
  Polyfold.SBLocalization.cylinderOrientationStatement_of_isCanonical,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_of_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition,
  Polyfold.SBLocalization.SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.isScFredholmSectionTame,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_pushMult,
  Polyfold.StrongPolyfoldBundle.OrientationRep.Correspondence.middleCanonical,
  Polyfold.SBLocalization.KernelBranching.canonSum_pullOr,
  Polyfold.SBLocalization.IsCanonicalFor.pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.orientedRep_rel_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.toCompact_eq_of_diagram_pullSection,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_eq_of_diagram_pullSection,
  Polyfold.TrivialBundle.theorem_16_6_6_canonical_hypotheses_circle,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_hypotheses_z3,
  Polyfold.HalfSpaceBundle.isInheritedFrom_generalPosition_halfDisc,
  Polyfold.CanonicalOrientationPullbackExamples.toCompact_eq_of_diagram_pullSection_circle,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection,
  Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc,
  Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_cylinderInput,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordism_ofRegular,
  Polyfold.StrongPolyfoldBundle.ModelPerturbation.hasCobordismEff_ofRegular,
  Polyfold.EpGroupoid.branchedMeasure_congr_orientation,
  Polyfold.StrongPolyfoldBundle.isRegularPerturbation_of_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_hcob_witness,
  Polyfold.SBLocalization.isCanonicalPerturbation_canonical,
  Polyfold.HalfSpaceBundle.exists_isCanonicalPerturbation_halfSEP,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_hcob_witness,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_mk_rep,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordism_refl,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.hasCobordismEff_refl,
  Polyfold.PolyfoldClass.OrientedRep.integral_add,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_add,
  Polyfold.PolyfoldClass.OrientedRep.integral_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedRep.integralEff_d_eq_zero_of_boundary,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_d_eq_zero,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integralEff_add_d,
  Polyfold.PolyfoldClass.ScForm.toStructure_add,
  Polyfold.PolyfoldClass.ScForm.toStructure_zero,
  Polyfold.PolyfoldClass.not_mem_boundary_of_eq_empty,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_reduction,
  Polyfold.StrongPolyfoldBundle.exists_generalPosition_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_of_isStructurable,
  Polyfold.StrongPolyfoldBundle.OrientationRep.exists_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.isControlledBy_of_isRegularPerturbation,
  Polyfold.StrongPolyfoldBundle.CanonicalInput.canonicalBumpInput,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integral_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.integralEff_toCompact,
  Polyfold.StrongPolyfoldBundle.ModelSolutionSet.isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_partitions,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_hypotheses_circle,
  Polyfold.TrivialBundle.theorem_16_6_6_all_admissible_circle,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_canonicalInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_of_forall_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_hyp_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_model_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_of_cylinder_all,
  Polyfold.PolyfoldClass.OrientedSuborbifold.integral_add_d_all,
  Polyfold.PolyfoldClass.CompactOrientedSuborbifold.integral_eq_of_hasCobordism_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFrom_iff_of_correspondence_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_correspondence_generalPosition_all,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_seeds,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_seeds,
  Polyfold.EP.exists_bumps_near_compact,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness,
  Polyfold.SBLocalization.exists_bumps_of_controlsCompactness_cylinder,
  Polyfold.StrongPolyfoldBundle.CanonicalBumpInput.canonicalGermInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_solutionSet_noBumps,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_integral_eq_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_all_admissible_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_of_restrictedFamilies,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientationLoc,
  Polyfold.StrongPolyfoldBundle.OrientationRep.isOrInvariant,
  Polyfold.SBLocalization.canonContinuous_loc,
  Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientationLoc,
  Polyfold.SBLocalization.isSectionOrientationLoc_cubeOrientation,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_loc,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt_loc,
  Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP,
  Polyfold.SBLocalization.isTransversalPerturbation_restr,
  Polyfold.SBLocalization.isSectionOrientationLoc_restrOr,
  Polyfold.SBLocalization.isOrInvariant_restrOr,
  Polyfold.SBLocalization.isIndexAt_restrSec,
  Polyfold.SBLocalization.IsCanonicalFor.restr,
  Polyfold.SBLocalization.OrientedSolution.integral_restr,
  Polyfold.SBLocalization.OrientedSolution.integralEff_restr,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_families,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal_of_families,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_restr,
  Polyfold.LocalPart.exists_bump_near_compact,
  Polyfold.LocalPart.exists_bump_near_compact_cube,
  Polyfold.LocalPart.exists_bump_pos_on_compact_cube,
  Polyfold.SBLocalization.exists_preSeedRel,
  Polyfold.SBLocalization.exists_seeds_of_function,
  Polyfold.SBLocalization.exists_seeds_of_function_rel,
  Polyfold.SBLocalization.hasLocalParamSeedsRel_of_functions,
  Polyfold.SBLocalization.isParamOntoVecRel_localIso,
  Polyfold.EpGroupoid.exists_naturalRep_component,
  Polyfold.EpGroupoid.isScSmoothOn_indicator_component,
  Polyfold.MPolyfold.exists_nhds_compact_connected]

end RoundTrip.V16_78
