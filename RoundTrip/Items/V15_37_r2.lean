import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_37
import Polyfold.Chapter16.Corollary1544NoSectionsDeRham

set_option maxSynthPendingDepth 3

/-! Round trip for V15_37_r2 (refresh of V15_37: 2021 Corollary 15.4.4, p. 703: `d_X ≡ 0`, `|X|`
paracompact, `|S_f|` compact, `o` an orientation ⇒ a well-defined `Φ_{(f,o)} : H*_dR(X) → ℝ`,
`Φ([ω]) = ∫_{(Λ∘f, o)} ω` for a regular perturbation; effective version with (LUC)).  `B` is the
existing blind statement `RoundTrip.V15_37.B`.

* `A`: the types of the 17 theorems of `Chapter16/Corollary1544NoSections*` and of the row's 135
  theorems (universe `0`).  The new theorems drop the hypothesis
  `(A.cubeSEP 1).B.HasScPlusSectionsThrough`, which follows from sc-smooth bump functions on `X`
  (`hasScPlusSectionsThrough_cubeSEP_of_bump`), and state the corollary as maps on
  `H^k_dR(X) = EP.epDeRham` (`corollary_15_4_4_deRham`, `corollary_15_4_4_index_zero_deRham`).
* Main conjuncts `Amain`: `corollary_15_4_4_deRham ∧ corollary_15_4_4_index_zero_deRham`.
* `B_to_main`: proved.  `B`'s hypotheses are among the main conjuncts' (which also assume tame germ
  data `hft` and bump functions `hbump`) and its conclusion is theirs.
* `Bplus` is `B` with `hft` and `hbump` added.  `main_to_Bplus` and `Bplus_to_main` are proved:
  the main conjuncts are `Bplus`.  Hence `A_to_Bplus`.  The statements differ exactly by `hft`
  (tame germ data, the project's reading of "tame") and `hbump` (§15.3, 2021 p. 692: "We also
  assume that X admits sc-smooth bump functions"); Corollary 15.4.4 names neither.
* `A_to_B`: not proved (it would need existence of perturbations without `hft`, `hbump`).
* `B_to_A`: not proved (`A` contains proof steps, examples and existence in general position).
-/

namespace RoundTrip.V15_37_r2
open Polyfold Polyfold.SBLocalization

abbrev B : Prop := RoundTrip.V15_37.B

/-- The project's statement: the new theorems (`Chapter16/Corollary1544NoSections*`) and the
row's theorems, at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_loc_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_deRham_map.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3) ∧
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

set_option maxHeartbeats 4000000 in
theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_4_4_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_oriented_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_loc_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump.{0},
   @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump.{0},
   @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump.{0},
   @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump.{0},
   @Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump.{0},
   @Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub.{0},
   @Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub.{0},
   @Polyfold.SBLocalization.exists_deRham_map.{0,0},
   @Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3,
   @Polyfold.SBLocalization.corollary_15_4_4_oriented_collar.{0},
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

/-- The main conjuncts. -/
def Amain : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_deRham.{0}) ∧ (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham.{0})

/-- `B` with the two hypotheses of the project's forms that `B` does not state: tame germ data
`A.B.IsScFredholmSectionTame f` and sc-smooth bump functions `A.X.AdmitsBumpFunctionsPointwise`
(the standing assumption of §15.3, 2021 p. 692). -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    A.X.AdmitsBumpFunctionsPointwise →
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f),
      A.B.IsScFredholmSectionTame f →
      A.E.HasCompactSolutionSetEp f →
    ∀ (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
      -- index `m + 1 ≥ 1`
      (∀ m : ℕ, (∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) →
        (∃ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T) ∧
        (∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (RoundTrip.V15_37.cls A (m + 1) ω hω) = P.integral ω) ∧
        (∀ hL : A.X.IsLUC, ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (RoundTrip.V15_37.cls A (m + 1) ω hω) = P.integralEff hL ω)) ∧
      -- index `0`
      ((∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0) →
        (∃ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o) ∧
        (∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (RoundTrip.V15_37.cls A 0 ω hω) = P.count ω) ∧
        (∀ hL : A.X.IsLUC, ∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (RoundTrip.V15_37.cls A 0 ω hω) = P.countEff hL ω))

set_option maxHeartbeats 4000000 in
/-- **`B` ⇒ the main conjuncts.** -/
theorem B_to_main (hB : B) : Amain := by
  refine ⟨?_, ?_⟩
  · intro A f hd hf _hft hsec o ho hinv m hidx hpara _hbump hS
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara f hf hS hsec o ho hinv).1 m hidx
  · intro A f hd hf _hft hsec o ho hinv hidx hpara _hbump hS
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara f hf hS hsec o ho hinv).2 hidx

set_option maxHeartbeats 4000000 in
/-- **The main conjuncts ⇒ `B` with `hft` and `hbump`.** -/
theorem main_to_Bplus (h : Amain) : Bplus := by
  intro A _ _ hd hpara hbump f hF hft hS hsec o ho hinv
  exact ⟨fun m hidx => h.1 hd hF hft hsec o ho hinv hidx hpara hbump hS,
    fun hidx => h.2 hd hF hft hsec o ho hinv hidx hpara hbump hS⟩

set_option maxHeartbeats 4000000 in
/-- **`B` with `hft` and `hbump` ⇒ the main conjuncts** (so `Amain ↔ Bplus`). -/
theorem Bplus_to_main (hB : Bplus) : Amain := by
  refine ⟨?_, ?_⟩
  · intro A f hd hf hft hsec o ho hinv m hidx hpara hbump hS
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hbump f hf hft hS hsec o ho hinv).1 m hidx
  · intro A f hd hf hft hsec o ho hinv hidx hpara hbump hS
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hbump f hf hft hS hsec o ho hinv).2 hidx

theorem B_to_Bplus (hB : B) : Bplus := main_to_Bplus (B_to_main hB)

/-- **`A` ⇒ `B` with `hft` and `hbump`.** -/
theorem A_to_Bplus (hA : A) : Bplus := main_to_Bplus ⟨hA.1, hA.2.1⟩

set_option hygiene false in
/-- `#rt_check` of `t` against all of `A`'s theorems. -/
macro "rt_check_A " t:ident : command => `(#rt_check $t [
    Polyfold.SBLocalization.corollary_15_4_4_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump,
    Polyfold.SBLocalization.corollary_15_4_4_loc_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump,
    Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub,
    Polyfold.SBLocalization.exists_deRham_map,
    Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3,
    Polyfold.SBLocalization.corollary_15_4_4_oriented_collar,
    Polyfold.SBLocalization.corollary_15_4_4_collar,
    Polyfold.SBLocalization.corollary_15_4_4_collar_of_admits,
    Polyfold.SBLocalization.hasOrientedCobordism_collar,
    Polyfold.SBLocalization.exists_collar_local_ends,
    Polyfold.SBLocalization.corollary_15_4_4_oriented,
    Polyfold.SBLocalization.corollary_15_4_4_of_definition_12_5_4,
    Polyfold.SBLocalization.isOrInvariant_cubeOrientation,
    Polyfold.SBLocalization.isIntervalProductAt_morIso_cubeSEP,
    Polyfold.EpGroupoid.cubeProd_tgtInv_eq_near, Polyfold.ChartPoint.ivOrFirst₀_conj,
    Polyfold.StrongBundle.LocalIso.orVia_ivOrFirst₀,
    Polyfold.StrongBundle.LocalIso.orVia_ivFirstFun, Polyfold.SBLocalization.corollary_15_4_4_loc,
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
    Polyfold.SBLocalization.theorem_15_4_1_cylinder, Polyfold.SBLocalization.isIndexAt_cubeLiftEp,
    Polyfold.SBLocalization.isOrInvariant_cubeOrientation_of_forall_unit,
    Polyfold.SBLocalization.cylinderKernelFrameConvention_of_isIndexAt,
    Polyfold.SBLocalization.corollary_15_4_4_cubeOrientation,
    Polyfold.SBLocalization.isSectionOrientation_cubeOrientation,
    Polyfold.SBLocalization.exists_timeFirst_frame_cubeOrientation,
    Polyfold.SBLocalization.cylinderKernelFrameConvention_cubeOrientation,
    Polyfold.ChartPoint.exists_timeFirst_wedge_of_slice, Polyfold.exists_timeFirst_coordinates,
    Polyfold.isIndexAt_cubeLift_interval, Polyfold.SBLocalization.IsCanonicalFor.isKernelCanonical,
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
    Polyfold.EpGroupoid.card_isotropy_cubeProd, Polyfold.SBLocalization.integ_cubeFace,
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
    Polyfold.SBLocalization.boundary_cyl_time, Polyfold.SBLocalization.boundaryMeasure_cyl_univ,
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
    Polyfold.SBLocalization.corollary_15_4_4_hyp, Polyfold.HalfSpaceBundle.cubeOrientation_halfSEP,
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
    Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one])

rt_check_A RoundTrip.V15_37_r2.B_to_main
rt_check_A RoundTrip.V15_37_r2.main_to_Bplus
rt_check_A RoundTrip.V15_37_r2.Bplus_to_main
rt_check_A RoundTrip.V15_37_r2.A_to_Bplus

end RoundTrip.V15_37_r2
