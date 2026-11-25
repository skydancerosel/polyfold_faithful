import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_37

set_option maxSynthPendingDepth 3

/-! Round trip for V15_37 (2021 Corollary 15.4.4, p. 703: `d_X ≡ 0`, `|X|` paracompact, `|S_f|`
compact, `o` an orientation ⇒ a well-defined `Φ_{(f,o)} : H*_dR(X) → ℝ`,
`Φ([ω]) = ∫_{(Λ∘f, o)} ω` for a regular perturbation; effective version with (LUC)).

`A` is the conjunction of the types of the item's 135 theorems (universe `0` everywhere: `.{0}`
or `.{0,0}`, since `B` lives on `SEP.{0}`); the 24 listed definitions are vocabulary.

* `A_to_B`: not proved.  The conjuncts giving existence of a canonically oriented regular
  perturbation (`corollary_15_4_4_exists`, `..._wellDefined(_all)`, `..._index_zero_*`) and the
  well-definedness (`corollary_15_4_4_oriented_collar(_all)`, ...) all assume tame germ data
  `A.B.IsScFredholmSectionTame f`, sc-smooth bump functions (`AdmitsBumpFunctionsPointwise`) or
  partitions of unity on `X`, and `(A.cubeSEP 1).B.HasScPlusSectionsThrough`; `B` grants none.
* `B_to_A`: not proved.  `A` contains proof-step lemmas (cube orientations, matched kernels,
  local end identities, cylinder boundary measures), worked examples on specific bundles, and the
  existence of perturbations **in general position**, none of which follows from `B`.
* Main conjunct `corollary_15_4_4_oriented_collar_all` (the well-definedness of `Φ_{(f,o)}` in
  degree `m + 1`): `B_to_main` proves `B ⇒` it.  The conjunct has no compactness hypothesis on
  `|S_f|`; it is recovered from any regular perturbation
  (`hasCompactSolutionSetEp_of_controlsCompactness`).  Converse: not proved (the conjunct assumes
  `hft`, `hbump`, `hsec'`, and claims no existence, no effective and no index-`0` statement).
  For `corollary_15_4_4_wellDefined_all` (existence ∧ well-definedness), `B` gives the second
  half the same way, but not the first: `B` provides a canonically oriented regular perturbation,
  not one in general position (`IsInGeneralPosition`).
-/

namespace RoundTrip.V15_37
open Polyfold Polyfold.SBLocalization Polyfold.EpGroupoid

/-- The project's statement: the conjunction of the item's theorems at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_collar_of_admits.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_collar_local_ends.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOrInvariant_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isIntervalProductAt_morIso_cubeSEP.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.cubeProd_tgtInv_eq_near.{0}) ∧
  (type_of% @Polyfold.ChartPoint.ivOrFirst₀_conj.{0,0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.orVia_ivOrFirst₀.{0,0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.orVia_ivFirstFun.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_signed_frame_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched.{0}) ∧
  (type_of% @Polyfold.ChartPoint.exists_timeFirst_wedge_signed_of_slice.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_canonicalOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_cylinder.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isIndexAt_cubeLiftEp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOrInvariant_cubeOrientation_of_forall_unit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSectionOrientation_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_timeFirst_frame_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cylinderKernelFrameConvention_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.ChartPoint.exists_timeFirst_wedge_of_slice.{0,0}) ∧
  (type_of% @Polyfold.exists_timeFirst_coordinates.{0}) ∧
  (type_of% @Polyfold.isIndexAt_cubeLift_interval.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.isKernelCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_areMatchedAt_of_kernelCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_kernelCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_canonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isInGeneralPositionAt_cubeSecSlice.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sliceKernelStatement.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_matched_kernel_branching.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.one_le_dim_of_mem_submanifoldBoundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_matched_branching.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.boundaryStratum_cyl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalEndIdentity_of_matched.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCylinderBoundaryOf_of_matched.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.card_isotropy_cubeProd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integ_cubeFace.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sheetSum_boundaryFamily_cubeFace.{0}) ∧
  (type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward.{0}) ∧
  (type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryOrient_tangent_eq_faceOrient_of_end_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryOrient_tangent_ne_faceOrient_of_end_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.areMatchedAt_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.areMatchedAt_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_areMatchedAt_of_orientations.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_matchedOrientations.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalEndIdentity_of_structures.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCylinderBoundaryOf_of_local.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_local_ends.{0}) ∧
  (type_of% @Polyfold.SBLocalization.signedMeasure_closed_eq_of_local.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_or.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_canonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCanonicalPerturbation_canonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundary_cyl_time.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryMeasure_cyl_univ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryMeasureEff_cyl_univ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.signedMeasure_univ_eq_cylEnds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPartitionsOfUnity_cyl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_cylinder_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_cylinder_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_cylinder_of_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.tameBranchedIntegral_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.signedMeasure_univ_eq_zero_of_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryMeasure_univ_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_cobordism.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_hyp.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.cubeOrientation_halfSEP) ∧
  (type_of% @Polyfold.TrivialBundle.exists_matched_kernel_branching_diagSection) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_hypotheses_circleSection) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_circleSection) ∧
  (type_of% @Polyfold.TrivialBundle.exists_isCanonicalPerturbation_circleSection) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_oriented_collar_circleSection) ∧
  (type_of% @Polyfold.TrivialBundle.collar_cobordism_circleSection) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.isOrInvariant_cubeOrientation_z3) ∧
  (type_of% @Polyfold.TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3) ∧
  (type_of% @Polyfold.TrivialIsotropy.corollary_15_4_4_planeZ3) ∧
  (type_of% @Polyfold.TrivialIsotropy.exists_isCanonicalPerturbation_planeZ3) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_exists.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_wellDefined.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_isRegularPerturbation_isInGeneralPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_exists.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_cobordism_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.HasOrientedCobordism.to_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_hyp_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_canonical_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_loc_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsRegularPerturbation.isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusMultisection_cylExtension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_cylExtension_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_transversal.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_relative_of_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.Adm.isLocalEndIdentity_of_matched.{0}) ∧
  (type_of% @Polyfold.SBLocalization.Adm.exists_areMatchedAt_of_kernelCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_cylinder_local_ends_transversal.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.isTransversalPerturbation_unitMulti) ∧
  (type_of% @Polyfold.TrivialBundle.not_isRegularPerturbation_unitMulti) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_4_4_oriented_collar.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_collar.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_collar_of_admits.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_collar.{0},
    @Polyfold.SBLocalization.exists_collar_local_ends.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_oriented.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4.{0},
    @Polyfold.SBLocalization.isOrInvariant_cubeOrientation.{0},
    @Polyfold.SBLocalization.isIntervalProductAt_morIso_cubeSEP.{0},
    @Polyfold.EpGroupoid.cubeProd_tgtInv_eq_near.{0},
    @Polyfold.ChartPoint.ivOrFirst₀_conj.{0,0},
    @Polyfold.StrongBundle.LocalIso.orVia_ivOrFirst₀.{0,0},
    @Polyfold.StrongBundle.LocalIso.orVia_ivFirstFun.{0,0},
    @Polyfold.SBLocalization.corollary_15_4_4_loc.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero.{0},
    @Polyfold.SBLocalization.exists_signed_frame_cubeOrientation.{0},
    @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation.{0},
    @Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator.{0},
    @Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical.{0},
    @Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched.{0},
    @Polyfold.ChartPoint.exists_timeFirst_wedge_signed_of_slice.{0,0},
    @Polyfold.SBLocalization.corollary_15_4_4_canonicalOrientation.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_cylinder.{0},
    @Polyfold.SBLocalization.isIndexAt_cubeLiftEp.{0},
    @Polyfold.SBLocalization.isOrInvariant_cubeOrientation_of_forall_unit.{0},
    @Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_cubeOrientation.{0},
    @Polyfold.SBLocalization.isSectionOrientation_cubeOrientation.{0},
    @Polyfold.SBLocalization.exists_timeFirst_frame_cubeOrientation.{0},
    @Polyfold.SBLocalization.cylinderKernelFrameConvention_cubeOrientation.{0},
    @Polyfold.ChartPoint.exists_timeFirst_wedge_of_slice.{0,0},
    @Polyfold.exists_timeFirst_coordinates.{0},
    @Polyfold.isIndexAt_cubeLift_interval.{0,0},
    @Polyfold.SBLocalization.IsCanonicalFor.isKernelCanonical.{0},
    @Polyfold.SBLocalization.exists_areMatchedAt_of_kernelCanonical.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_kernelCanonical.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_canonical.{0},
    @Polyfold.SBLocalization.isInGeneralPositionAt_cubeSecSlice.{0},
    @Polyfold.SBLocalization.sliceKernelStatement.{0},
    @Polyfold.SBLocalization.exists_matched_kernel_branching.{0},
    @Polyfold.SBLocalization.KernelBranching.one_le_dim_of_mem_submanifoldBoundary.{0},
    @Polyfold.SBLocalization.exists_matched_branching.{0},
    @Polyfold.SBLocalization.KernelBranching.boundaryStratum_cyl.{0},
    @Polyfold.SBLocalization.isLocalEndIdentity_of_matched.{0},
    @Polyfold.SBLocalization.isCylinderBoundaryOf_of_matched.{0},
    @Polyfold.EpGroupoid.card_isotropy_cubeProd.{0},
    @Polyfold.SBLocalization.integ_cubeFace.{0},
    @Polyfold.SBLocalization.sheetSum_boundaryFamily_cubeFace.{0},
    @Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward.{0},
    @Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward.{0},
    @Polyfold.SBLocalization.boundaryOrient_tangent_eq_faceOrient_of_end_one.{0},
    @Polyfold.SBLocalization.boundaryOrient_tangent_ne_faceOrient_of_end_zero.{0},
    @Polyfold.SBLocalization.KernelBranching.areMatchedAt_one.{0},
    @Polyfold.SBLocalization.KernelBranching.areMatchedAt_zero.{0},
    @Polyfold.SBLocalization.exists_areMatchedAt_of_orientations.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_matchedOrientations.{0},
    @Polyfold.SBLocalization.isLocalEndIdentity_of_structures.{0},
    @Polyfold.SBLocalization.isCylinderBoundaryOf_of_local.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_local_ends.{0},
    @Polyfold.SBLocalization.signedMeasure_closed_eq_of_local.{0,0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_or.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_rel.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_canonical.{0},
    @Polyfold.SBLocalization.isCanonicalPerturbation_canonical.{0},
    @Polyfold.SBLocalization.boundary_cyl_time.{0},
    @Polyfold.SBLocalization.boundaryMeasure_cyl_univ.{0},
    @Polyfold.SBLocalization.boundaryMeasureEff_cyl_univ.{0},
    @Polyfold.EpGroupoid.signedMeasure_univ_eq_cylEnds.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder.{0},
    @Polyfold.SBLocalization.hasScPartitionsOfUnity_cyl.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_cylinder_hyp.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_cylinder_hyp.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_cylinder_of_rel.{0},
    @Polyfold.SBLocalization.tameBranchedIntegral_zero.{0},
    @Polyfold.SBLocalization.signedMeasure_univ_eq_zero_of_boundary.{0},
    @Polyfold.SBLocalization.boundaryMeasure_univ_eq_zero.{0},
    @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero.{0},
    @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1.{0},
    @Polyfold.SBLocalization.integral_eq_of_cobordism.{0},
    @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_hyp.{0},
    @Polyfold.HalfSpaceBundle.cubeOrientation_halfSEP,
    @Polyfold.TrivialBundle.exists_matched_kernel_branching_diagSection,
    @Polyfold.TrivialBundle.corollary_15_4_4_hypotheses_circleSection,
    @Polyfold.TrivialBundle.corollary_15_4_4_circleSection,
    @Polyfold.TrivialBundle.exists_isCanonicalPerturbation_circleSection,
    @Polyfold.TrivialBundle.corollary_15_4_4_oriented_collar_circleSection,
    @Polyfold.TrivialBundle.collar_cobordism_circleSection,
    @Polyfold.StrongBundleLocalizationExamples.isOrInvariant_cubeOrientation_z3,
    @Polyfold.TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3,
    @Polyfold.TrivialIsotropy.corollary_15_4_4_planeZ3,
    @Polyfold.TrivialIsotropy.exists_isCanonicalPerturbation_planeZ3,
    @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
    @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
    @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
    @Polyfold.SBLocalization.corollary_15_4_4_exists.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_wellDefined.{0},
    @Polyfold.SBLocalization.exists_isRegularPerturbation_isInGeneralPosition.{0},
    @Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPosition.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_exists.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_collar_all.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_collar_all.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder_all.{0},
    @Polyfold.SBLocalization.integral_eq_of_cobordism_all.{0},
    @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_all.{0},
    @Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1_all.{0},
    @Polyfold.SBLocalization.OrientedRegularPerturbation.HasOrientedCobordism.to_all.{0},
    @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_hyp_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_canonical_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_loc_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_all.{0},
    @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined_all.{0},
    @Polyfold.SBLocalization.IsRegularPerturbation.isTransversalPerturbation.{0},
    @Polyfold.SBLocalization.isScPlusMultisection_cylExtension.{0},
    @Polyfold.SBLocalization.pointwiseNorm_cylExtension_le.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_transversal.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_relative_of_le.{0},
    @Polyfold.SBLocalization.Adm.isLocalEndIdentity_of_matched.{0},
    @Polyfold.SBLocalization.Adm.exists_areMatchedAt_of_kernelCanonical.{0},
    @Polyfold.SBLocalization.exists_cylinder_local_ends_transversal.{0},
    @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0},
    @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation.{0},
    @Polyfold.TrivialBundle.isTransversalPerturbation_unitMulti,
    @Polyfold.TrivialBundle.not_isRegularPerturbation_unitMulti,
    @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one⟩

/-- `∫ 0 = 0` (the project's `tameBranchedIntegral_zero`, re-proved: it is on the item's list). -/
theorem tameBranchedIntegral_zero' {B : EP.{0}} {n : ℕ} (hn : 0 < n) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T) :
    (B.epFormsInftyEval n).tameBranchedIntegral hn hΘ hcpt hT hloc 0 = 0 := by
  simp only [FormEval.tameBranchedIntegral, FormEval.concreteBranchedIntegral, branchedIntegral,
    map_zero]
  rfl

theorem integral_zero' {A : SEP.{0}} {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m) : P.integral 0 = 0 :=
  tameBranchedIntegral_zero' _ _ _ _ _

set_option maxHeartbeats 2000000 in
/-- An exact form has class `0`. -/
theorem cls_d (A : SEP.{0}) (m : ℕ) (η : A.baseEP.epFormsInfty m) :
    cls A (m + 1) (A.baseEP.epFormsInftyD m η)
        (LinearMap.mem_ker.2 (A.baseEP.epFormsInftyD_epFormsInftyD m η)) =
      cls A (m + 1) 0 (Submodule.zero_mem _) := by
  have hmem : A.baseEP.epFormsInftyD m η ∈ A.baseEP.epFormsInftyDRange (m + 1) := ⟨η, rfl⟩
  have hz : (0 : A.baseEP.epFormsInfty (m + 1)) ∈ A.baseEP.epFormsInftyDRange (m + 1) :=
    Submodule.zero_mem _
  exact ((Submodule.Quotient.mk_eq_zero ((A.baseEP.epFormsInftyDRange (m + 1)).comap
      (LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))).subtype) (x := ⟨_, _⟩)).2 hmem).trans
    ((Submodule.Quotient.mk_eq_zero ((A.baseEP.epFormsInftyDRange (m + 1)).comap
      (LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))).subtype) (x := ⟨_, _⟩)).2 hz).symm

/-- A pair `(N, U)` controlling compactness forces `|S_f|` compact: `|S_f|` is closed (`S_f` is
closed and saturated) and lies in the compact `cl |{x ∈ U | N(f(x)) ≤ 1}|`. -/
theorem hasCompactSolutionSetEp_of_controlsCompactness {A : SEP.{0}} {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) : A.E.HasCompactSolutionSetEp f := by
  obtain ⟨⟨hsm, hfun⟩, -⟩ := hf
  obtain ⟨hN, -, -, hSU, hK⟩ := hcc
  have hsat : A.X.IsSaturated (solutionSet A.P f) := A.X.isSaturated_iff.2 fun φ hφ => by
    show f (A.X.tgt φ) = fiberZero A.P (A.X.tgt φ)
    rw [hfun φ]
    have e : EpStrongBundle.sectionPair hsm.1 φ =
        ⟨(φ, fiberZero A.P (A.X.src φ)), isSection_fiberZero (A.X.src φ)⟩ :=
      Subtype.ext (Prod.ext rfl hφ)
    rw [e, A.E.μ_fiberZero]
  have hcl := A.X.isClosed_image_π_of_isSaturated hsat (isClosed_solutionSet hsm)
  refine hK.of_isClosed_subset hcl ?_
  rintro _ ⟨x, hx, rfl⟩
  exact subset_closure
    ⟨x, ⟨hSU hx, (hN.isAuxNorm.auxLe_fiberZero x zero_le_one).congr hx.symm⟩, rfl⟩

/-- **`B` ⇒ the main conjunct `corollary_15_4_4_oriented_collar_all`.** -/
theorem B_to_main (hB : B) :
    type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all.{0} := by
  intro A f hd hf _hft hsec _hsec' o ho hinv m hidx hpara _hbump
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have key : ∀ P : OrientedRegularPerturbation A f m, ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
      ∀ P' : OrientedRegularPerturbation A f m, IsCanonicalFor P'.Λ hf.2 hsec o (m + 1) P'.T →
      ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
        Φ (cls A (m + 1) ω hω) = P'.integral ω := fun P =>
    ((hB A hd hpara f hf (hasCompactSolutionSetEp_of_controlsCompactness hf P.isRegular.1)
      hsec o ho hinv).1 m hidx).2.1
  refine ⟨fun P hP η => ?_, fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := key P
    have h1 := hΦ P hP (A.baseEP.epFormsInftyD m η)
      (LinearMap.mem_ker.2 (A.baseEP.epFormsInftyD_epFormsInftyD m η))
    have h0 := hΦ P hP 0 (Submodule.zero_mem _)
    rw [← h1, cls_d, h0, integral_zero']
  · obtain ⟨Φ, hΦ⟩ := key P₀
    exact (hΦ P₀ h₀ ω (LinearMap.mem_ker.2 hω)).symm.trans
      (hΦ P₁ h₁ ω (LinearMap.mem_ker.2 hω))

#rt_check RoundTrip.V15_37.B_to_main [Polyfold.SBLocalization.corollary_15_4_4_oriented_collar,
  Polyfold.SBLocalization.corollary_15_4_4_collar,
  Polyfold.SBLocalization.corollary_15_4_4_collar_of_admits,
  Polyfold.SBLocalization.hasOrientedCobordism_collar,
  Polyfold.SBLocalization.exists_collar_local_ends,
  Polyfold.SBLocalization.corollary_15_4_4_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4,
  Polyfold.SBLocalization.isOrInvariant_cubeOrientation,
  Polyfold.SBLocalization.isIntervalProductAt_morIso_cubeSEP,
  Polyfold.EpGroupoid.cubeProd_tgtInv_eq_near,
  Polyfold.ChartPoint.ivOrFirst₀_conj,
  Polyfold.StrongBundle.LocalIso.orVia_ivOrFirst₀,
  Polyfold.StrongBundle.LocalIso.orVia_ivFirstFun,
  Polyfold.SBLocalization.corollary_15_4_4_loc,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.SBLocalization.exists_signed_frame_cubeOrientation,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.ChartPoint.exists_timeFirst_wedge_signed_of_slice,
  Polyfold.SBLocalization.corollary_15_4_4_canonicalOrientation,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder,
  Polyfold.SBLocalization.isIndexAt_cubeLiftEp,
  Polyfold.SBLocalization.isOrInvariant_cubeOrientation_of_forall_unit,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt,
  Polyfold.SBLocalization.corollary_15_4_4_cubeOrientation,
  Polyfold.SBLocalization.isSectionOrientation_cubeOrientation,
  Polyfold.SBLocalization.exists_timeFirst_frame_cubeOrientation,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_cubeOrientation,
  Polyfold.ChartPoint.exists_timeFirst_wedge_of_slice,
  Polyfold.exists_timeFirst_coordinates,
  Polyfold.isIndexAt_cubeLift_interval,
  Polyfold.SBLocalization.IsCanonicalFor.isKernelCanonical,
  Polyfold.SBLocalization.exists_areMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_of_kernelCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_of_canonical,
  Polyfold.SBLocalization.isInGeneralPositionAt_cubeSecSlice,
  Polyfold.SBLocalization.sliceKernelStatement,
  Polyfold.SBLocalization.exists_matched_kernel_branching,
  Polyfold.SBLocalization.KernelBranching.one_le_dim_of_mem_submanifoldBoundary,
  Polyfold.SBLocalization.exists_matched_branching,
  Polyfold.SBLocalization.KernelBranching.boundaryStratum_cyl,
  Polyfold.SBLocalization.isLocalEndIdentity_of_matched,
  Polyfold.SBLocalization.isCylinderBoundaryOf_of_matched,
  Polyfold.EpGroupoid.card_isotropy_cubeProd,
  Polyfold.SBLocalization.integ_cubeFace,
  Polyfold.SBLocalization.sheetSum_boundaryFamily_cubeFace,
  Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward,
  Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward,
  Polyfold.SBLocalization.boundaryOrient_tangent_eq_faceOrient_of_end_one,
  Polyfold.SBLocalization.boundaryOrient_tangent_ne_faceOrient_of_end_zero,
  Polyfold.SBLocalization.KernelBranching.areMatchedAt_one,
  Polyfold.SBLocalization.KernelBranching.areMatchedAt_zero,
  Polyfold.SBLocalization.exists_areMatchedAt_of_orientations,
  Polyfold.SBLocalization.corollary_15_4_4_of_matchedOrientations,
  Polyfold.SBLocalization.isLocalEndIdentity_of_structures,
  Polyfold.SBLocalization.isCylinderBoundaryOf_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_of_local_ends,
  Polyfold.SBLocalization.signedMeasure_closed_eq_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_of_or,
  Polyfold.SBLocalization.corollary_15_4_4_of_rel,
  Polyfold.SBLocalization.corollary_15_4_4_canonical,
  Polyfold.SBLocalization.isCanonicalPerturbation_canonical,
  Polyfold.SBLocalization.boundary_cyl_time,
  Polyfold.SBLocalization.boundaryMeasure_cyl_univ,
  Polyfold.SBLocalization.boundaryMeasureEff_cyl_univ,
  Polyfold.EpGroupoid.signedMeasure_univ_eq_cylEnds,
  Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder,
  Polyfold.SBLocalization.hasScPartitionsOfUnity_cyl,
  Polyfold.SBLocalization.hasOrientedCobordism_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_cylinder_of_rel,
  Polyfold.SBLocalization.tameBranchedIntegral_zero,
  Polyfold.SBLocalization.signedMeasure_univ_eq_zero_of_boundary,
  Polyfold.SBLocalization.boundaryMeasure_univ_eq_zero,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1,
  Polyfold.SBLocalization.integral_eq_of_cobordism,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl,
  Polyfold.SBLocalization.corollary_15_4_4_hyp,
  Polyfold.HalfSpaceBundle.cubeOrientation_halfSEP,
  Polyfold.TrivialBundle.exists_matched_kernel_branching_diagSection,
  Polyfold.TrivialBundle.corollary_15_4_4_hypotheses_circleSection,
  Polyfold.TrivialBundle.corollary_15_4_4_circleSection,
  Polyfold.TrivialBundle.exists_isCanonicalPerturbation_circleSection,
  Polyfold.TrivialBundle.corollary_15_4_4_oriented_collar_circleSection,
  Polyfold.TrivialBundle.collar_cobordism_circleSection,
  Polyfold.StrongBundleLocalizationExamples.isOrInvariant_cubeOrientation_z3,
  Polyfold.TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3,
  Polyfold.TrivialIsotropy.corollary_15_4_4_planeZ3,
  Polyfold.TrivialIsotropy.exists_isCanonicalPerturbation_planeZ3,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.SBLocalization.corollary_15_4_4_exists,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined,
  Polyfold.SBLocalization.exists_isRegularPerturbation_isInGeneralPosition,
  Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPosition,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_exists,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all,
  Polyfold.SBLocalization.corollary_15_4_4_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordism_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder_all,
  Polyfold.SBLocalization.integral_eq_of_cobordism_all,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_all,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1_all,
  Polyfold.SBLocalization.OrientedRegularPerturbation.HasOrientedCobordism.to_all,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl_all,
  Polyfold.SBLocalization.corollary_15_4_4_hyp_all,
  Polyfold.SBLocalization.corollary_15_4_4_canonical_all,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined_all,
  Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4_all,
  Polyfold.SBLocalization.corollary_15_4_4_loc_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_all,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined_all,
  Polyfold.SBLocalization.IsRegularPerturbation.isTransversalPerturbation,
  Polyfold.SBLocalization.isScPlusMultisection_cylExtension,
  Polyfold.SBLocalization.pointwiseNorm_cylExtension_le,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_le,
  Polyfold.SBLocalization.Adm.isLocalEndIdentity_of_matched,
  Polyfold.SBLocalization.Adm.exists_areMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.exists_cylinder_local_ends_transversal,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.TrivialBundle.isTransversalPerturbation_unitMulti,
  Polyfold.TrivialBundle.not_isRegularPerturbation_unitMulti,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one]
#rt_overlap RoundTrip.V15_37.B_to_main [Polyfold.SBLocalization.corollary_15_4_4_oriented_collar,
  Polyfold.SBLocalization.corollary_15_4_4_collar,
  Polyfold.SBLocalization.corollary_15_4_4_collar_of_admits,
  Polyfold.SBLocalization.hasOrientedCobordism_collar,
  Polyfold.SBLocalization.exists_collar_local_ends,
  Polyfold.SBLocalization.corollary_15_4_4_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4,
  Polyfold.SBLocalization.isOrInvariant_cubeOrientation,
  Polyfold.SBLocalization.isIntervalProductAt_morIso_cubeSEP,
  Polyfold.EpGroupoid.cubeProd_tgtInv_eq_near,
  Polyfold.ChartPoint.ivOrFirst₀_conj,
  Polyfold.StrongBundle.LocalIso.orVia_ivOrFirst₀,
  Polyfold.StrongBundle.LocalIso.orVia_ivFirstFun,
  Polyfold.SBLocalization.corollary_15_4_4_loc,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.SBLocalization.exists_signed_frame_cubeOrientation,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.ChartPoint.exists_timeFirst_wedge_signed_of_slice,
  Polyfold.SBLocalization.corollary_15_4_4_canonicalOrientation,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder,
  Polyfold.SBLocalization.isIndexAt_cubeLiftEp,
  Polyfold.SBLocalization.isOrInvariant_cubeOrientation_of_forall_unit,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt,
  Polyfold.SBLocalization.corollary_15_4_4_cubeOrientation,
  Polyfold.SBLocalization.isSectionOrientation_cubeOrientation,
  Polyfold.SBLocalization.exists_timeFirst_frame_cubeOrientation,
  Polyfold.SBLocalization.cylinderKernelFrameConvention_cubeOrientation,
  Polyfold.ChartPoint.exists_timeFirst_wedge_of_slice,
  Polyfold.exists_timeFirst_coordinates,
  Polyfold.isIndexAt_cubeLift_interval,
  Polyfold.SBLocalization.IsCanonicalFor.isKernelCanonical,
  Polyfold.SBLocalization.exists_areMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_of_kernelCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_of_canonical,
  Polyfold.SBLocalization.isInGeneralPositionAt_cubeSecSlice,
  Polyfold.SBLocalization.sliceKernelStatement,
  Polyfold.SBLocalization.exists_matched_kernel_branching,
  Polyfold.SBLocalization.KernelBranching.one_le_dim_of_mem_submanifoldBoundary,
  Polyfold.SBLocalization.exists_matched_branching,
  Polyfold.SBLocalization.KernelBranching.boundaryStratum_cyl,
  Polyfold.SBLocalization.isLocalEndIdentity_of_matched,
  Polyfold.SBLocalization.isCylinderBoundaryOf_of_matched,
  Polyfold.EpGroupoid.card_isotropy_cubeProd,
  Polyfold.SBLocalization.integ_cubeFace,
  Polyfold.SBLocalization.sheetSum_boundaryFamily_cubeFace,
  Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward,
  Polyfold.MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward,
  Polyfold.SBLocalization.boundaryOrient_tangent_eq_faceOrient_of_end_one,
  Polyfold.SBLocalization.boundaryOrient_tangent_ne_faceOrient_of_end_zero,
  Polyfold.SBLocalization.KernelBranching.areMatchedAt_one,
  Polyfold.SBLocalization.KernelBranching.areMatchedAt_zero,
  Polyfold.SBLocalization.exists_areMatchedAt_of_orientations,
  Polyfold.SBLocalization.corollary_15_4_4_of_matchedOrientations,
  Polyfold.SBLocalization.isLocalEndIdentity_of_structures,
  Polyfold.SBLocalization.isCylinderBoundaryOf_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_of_local_ends,
  Polyfold.SBLocalization.signedMeasure_closed_eq_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_of_or,
  Polyfold.SBLocalization.corollary_15_4_4_of_rel,
  Polyfold.SBLocalization.corollary_15_4_4_canonical,
  Polyfold.SBLocalization.isCanonicalPerturbation_canonical,
  Polyfold.SBLocalization.boundary_cyl_time,
  Polyfold.SBLocalization.boundaryMeasure_cyl_univ,
  Polyfold.SBLocalization.boundaryMeasureEff_cyl_univ,
  Polyfold.EpGroupoid.signedMeasure_univ_eq_cylEnds,
  Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder,
  Polyfold.SBLocalization.hasScPartitionsOfUnity_cyl,
  Polyfold.SBLocalization.hasOrientedCobordism_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_cylinder_of_rel,
  Polyfold.SBLocalization.tameBranchedIntegral_zero,
  Polyfold.SBLocalization.signedMeasure_univ_eq_zero_of_boundary,
  Polyfold.SBLocalization.boundaryMeasure_univ_eq_zero,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1,
  Polyfold.SBLocalization.integral_eq_of_cobordism,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl,
  Polyfold.SBLocalization.corollary_15_4_4_hyp,
  Polyfold.HalfSpaceBundle.cubeOrientation_halfSEP,
  Polyfold.TrivialBundle.exists_matched_kernel_branching_diagSection,
  Polyfold.TrivialBundle.corollary_15_4_4_hypotheses_circleSection,
  Polyfold.TrivialBundle.corollary_15_4_4_circleSection,
  Polyfold.TrivialBundle.exists_isCanonicalPerturbation_circleSection,
  Polyfold.TrivialBundle.corollary_15_4_4_oriented_collar_circleSection,
  Polyfold.TrivialBundle.collar_cobordism_circleSection,
  Polyfold.StrongBundleLocalizationExamples.isOrInvariant_cubeOrientation_z3,
  Polyfold.TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3,
  Polyfold.TrivialIsotropy.corollary_15_4_4_planeZ3,
  Polyfold.TrivialIsotropy.exists_isCanonicalPerturbation_planeZ3,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.SBLocalization.corollary_15_4_4_exists,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined,
  Polyfold.SBLocalization.exists_isRegularPerturbation_isInGeneralPosition,
  Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPosition,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_exists,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all,
  Polyfold.SBLocalization.corollary_15_4_4_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordism_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordism_of_cylinder_all,
  Polyfold.SBLocalization.integral_eq_of_cobordism_all,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_all,
  Polyfold.SBLocalization.integral_d_eq_zero_of_degIndex_eq_zero_dim1_all,
  Polyfold.SBLocalization.OrientedRegularPerturbation.HasOrientedCobordism.to_all,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordism_refl_all,
  Polyfold.SBLocalization.corollary_15_4_4_hyp_all,
  Polyfold.SBLocalization.corollary_15_4_4_canonical_all,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined_all,
  Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4_all,
  Polyfold.SBLocalization.corollary_15_4_4_loc_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_all,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined_all,
  Polyfold.SBLocalization.IsRegularPerturbation.isTransversalPerturbation,
  Polyfold.SBLocalization.isScPlusMultisection_cylExtension,
  Polyfold.SBLocalization.pointwiseNorm_cylExtension_le,
  Polyfold.SBLocalization.corollary_15_3_10_3_transversal,
  Polyfold.SBLocalization.theorem_15_3_7_relative_of_le,
  Polyfold.SBLocalization.Adm.isLocalEndIdentity_of_matched,
  Polyfold.SBLocalization.Adm.exists_areMatchedAt_of_kernelCanonical,
  Polyfold.SBLocalization.exists_cylinder_local_ends_transversal,
  Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.TrivialBundle.isTransversalPerturbation_unitMulti,
  Polyfold.TrivialBundle.not_isRegularPerturbation_unitMulti,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one]

end RoundTrip.V15_37
