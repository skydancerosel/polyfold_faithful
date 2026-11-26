import Polyfold
/-!
Trusted-base extraction. For each main declaration, collect the project constants in its type,
then close transitively: definitions/instances/opaques → type + value; structures/classes/
inductives → type + constructor types. Ordinary theorems met inside a value are proofs: their
statement is already fixed by the surrounding term (kernel terms carry all implicit arguments),
so they are not followed; auxiliary `proof_n` / `eq_n` theorems are followed (type only).
Stop at non-`Polyfold` modules.
Auxiliary constants (`match_n`, `proof_n`, `eq_n`, `_private`, `casesOn`, projections, ctors, …)
are followed but reported under their parent declaration.
Output: graph.tsv  (node, kind, module, direct deps)  and  mains.tsv  (label, name, kind, deps), in
Exposition/checklist/.  Run from the project folder: `lake env lean Exposition/checklist/TrustedBase.lean`,
then `python3 Exposition/checklist/build_checklist.py`.
-/
open Lean Meta Elab Command

def mains : List (String × String) := [
  ("core|Prop 1.1.11", "proposition_1_1_11"),
  ("core|Thm 1.3.1", "theorem_1_3_1"),
  ("core|Thm 1.3.5", "theorem_1_3_5"),
  ("core|Thm 2.1.15", "theorem_2_1_15"),
  ("core|Thm 2.3.10", "theorem_2_3_10"),
  ("core|Thm 2.3.16", "theorem_2_3_16"),
  ("core|Thm 2.4.12", "theorem_2_4_12"),
  ("core|Thm 2.4.12", "remark_2_4_8_isPartialQuadrant"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_interior"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_isSubMPolyfold_face"),
  ("core|Thm 2.5.17", "MPolyfold.theorem_2_5_17_isTame_face"),
  ("core|Thm 3.1.13", "theorem_3_1_13"),
  ("core|Thm 3.1.18", "theorem_3_1_18"),
  ("core|Thm 3.1.21", "theorem_3_1_21"),
  ("core|Thm 3.1.22", "theorem_3_1_22_2021def"),
  ("core|Thm 3.1.22", "theorem_3_1_22_book"),
  ("core|Thm 3.1.22", "theorem_3_1_22_book_ker"),
  ("core|Thm 3.1.26", "theorem_3_1_26_2021def"),
  ("core|Cor 3.1.27", "corollary_3_1_27_2021def"),
  ("core|Thm 3.2.3", "theorem_3_2_3_2021def"),
  ("core|Thm 3.2.3", "theorem_3_2_3_2021def_isChart"),
  ("core|Thm 3.6.8", "theorem_3_6_8_book"),
  ("core|Thm 3.6.10", "theorem_3_6_10_2021def"),
  ("core|Thm 3.6.11", "theorem_3_6_11_2021def"),
  ("core|Thm 4.1.2", "MPolyfold.theorem_4_1_2"),
  ("core|Thm 4.2.7", "MPolyfold.theorem_4_2_7"),
  ("core|Thm 4.2.11", "MPolyfold.theorem_4_2_11"),
  ("core|Thm 4.3.1", "theorem_4_3_1"),
  ("core|Cor 5.2.5", "corollary_5_2_5_2021def"),
  ("core|Thm 5.3.5", "theorem_5_3_5_2021def"),
  ("core|Thm 5.3.10", "theorem_5_3_10_book_2021def"),
  ("core|Thm 5.3.12", "theorem_5_3_12_book_2021def"),
  ("core|Prop 6.2.2", "proposition_6_2_2_interval_2021def"),
  ("core|Thm 5.4.2", "theorem_5_4_2"),
  ("orientation|Thm 6.6.11", "theorem_6_6_11"),
  ("orientation|Thm 6.6.11", "theorem_6_6_11_loc"),
  ("orientation|Thm 6.6.13", "theorem_6_6_13"),
  ("orientation|Thm 6.6.13", "theorem_6_6_13_loc"),
  ("orientation|Thm 6.6.17", "theorem_6_6_17"),
  ("orientation|Thm 6.6.17", "theorem_6_6_17_loc"),
  ("orientation|Thm 6.6.18", "theorem_6_6_18"),
  ("orientation|Thm 6.7.1", "theorem_6_7_1"),
  ("orientation|Thm 6.7.1", "theorem_6_7_1_interval"),
  ("orientation|Rem 6.6.19", "theorem_6_6_18_boundaryIntegral_interval_lateral"),
  ("partII|Thm 7.1.13", "EpGroupoid.theorem_7_1_13"),
  ("partII|Thm 7.2.14", "EpGroupoid.theorem_7_2_14"),
  ("partII|Thm 7.3.1", "EpGroupoid.theorem_7_3_1"),
  ("partII|Cor 7.3.6", "EpGroupoid.corollary_7_3_6"),
  ("partII|Thm 7.5.4", "EpGroupoid.theorem_7_5_4"),
  ("partII|Thm 7.5.7", "EpGroupoid.theorem_7_5_7"),
  ("partII|Thm 7.6.1", "EpGroupoid.theorem_7_6_1"),
  ("partII|Thm 8.1.1", "EpGroupoid.theorem_8_1_1"),
  ("partII|Thm 8.1.1", "EpGroupoid.theorem_8_1_1_tame"),
  ("partII|Thm 8.1.11", "EpFunctor.theorem_8_1_11"),
  ("partII|Thm 8.1.12", "theorem_8_1_12"),
  ("partII|Thm 8.1.12", "theorem_8_1_12_tame"),
  ("partII|Thm 8.1.15", "EpGroupoid.theorem_8_1_15"),
  ("partII|Prop 8.4.3", "EpStrongBundle.proposition_8_4_3_isLRLocal"),
  ("partII|Thm 8.5.3", "EpFunctor.theorem_8_5_3"),
  ("partII|Thm 8.5.8", "EpFunctor.theorem_8_5_8"),
  ("partII|Prop 9.1.11", "EpGroupoid.proposition_9_1_11_unique"),
  ("partII|Thm 9.2.1", "EpGroupoid.theorem_9_2_1"),
  ("partII|Thm 9.5.15", "EP.theorem_9_5_15"),
  ("partII|Thm 9.5.15", "EP.theorem_9_5_15_dim1_all"),
  ("partII|Thm 9.5.16", "EP.theorem_9_5_16"),
  ("partII|Thm 9.5.16", "EP.theorem_9_5_16_dim1_all"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17_dim1"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17_all"),
  ("partII|Thm 9.5.17", "EP.theorem_9_5_17_dim1_all"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18_dim1_isLUC"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18_all"),
  ("partII|Thm 9.5.18", "EP.theorem_9_5_18_dim1_all"),
  ("partII|Rem 9.5.19", "EP.stokesWithoutPartitions_all"),
  ("partII|Rem 9.5.20", "DimensionJump.remark_9_5_20_two_readings"),
  ("partII|Thm 10.1.7", "EpFunctor.theorem_10_1_7"),
  ("partII|Thm 10.2.2", "WeakFibredProduct.theorem_10_2_2"),
  ("partII|Thm 10.2.2", "WeakFibredProduct.theorem_10_2_2_both"),
  ("partII|Thm 10.3.8", "EPLocalization.Diagram.theorem_10_3_8"),
  ("partII|Thm 10.3.10", "EPLocalization.EPLoc.theorem_10_3_10"),
  ("partII|Thm 10.3.14", "EPLocalization.EPLoc.theorem_10_3_14"),
  ("partII|Thm 10.3.15", "EPLocalization.EPLoc.theorem_10_3_15"),
  ("partII|Thm 10.3.21", "EPLocalization.EPLoc.theorem_10_3_21"),
  ("partII|Thm 10.5.7", "SBLocalization.theorem_10_5_7_of_isEffective"),
  ("partII|Thm 10.5.7", "SBLocalization.theorem_10_5_7_of_isEffective_of_isLRLocal"),
  ("partII|Thm 11.1.1", "EPLocalization.EPLoc.theorem_11_1_1"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_one"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_two"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_three"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_four"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_five"),
  ("partII|Thm 11.3.3", "EPLocalization.EPLoc.theorem_11_3_3_six"),
  ("partII|Thm 11.3.5", "EPLocalization.EPLoc.theorem_11_3_5_push"),
  ("partII|Thm 11.3.5", "EPLocalization.EPLoc.theorem_11_3_5_pull"),
  ("partII|Thm 11.3.7", "EPLocalization.EPLoc.theorem_11_3_7_push"),
  ("partII|Thm 11.3.7", "EPLocalization.EPLoc.theorem_11_3_7_pull"),
  ("partII|Thm 11.3.8", "EPLocalization.EPLoc.theorem_11_3_8_push"),
  ("partII|Thm 11.3.8", "EPLocalization.EPLoc.theorem_11_3_8_pull"),
  ("partII|Thm 11.3.9", "EPLocalization.EPLoc.theorem_11_3_9_push_boundaryOrientation"),
  ("partII|Thm 11.3.9", "EPLocalization.EPLoc.theorem_11_3_9_pull_boundaryOrientation"),
  ("partII|Thm 11.6.6", "ProperCoveringHom.theorem_11_6_6"),
  ("partIII|Thm 12.2.2", "EpStrongBundle.theorem_12_2_2"),
  ("partIII|Thm 12.4.2", "EpStrongBundle.theorem_12_4_2"),
  ("partIII|Thm 13.1.8", "EpGroupoid.theorem_13_1_8"),
  ("partIII|Prop 16.1.4", "PolyfoldStructure.proposition_16_1_4"),
  ("partIII|Lemma 16.1.13", "PolyfoldStructure.lemma_16_1_13"),
  ("partIII|Lemma 16.1.19", "PolyfoldStructure.lemma_16_1_19"),
  ("partIII|Thm 12.2.7", "EpStrongBundle.theorem_12_2_7"),
  ("partIII|Thm 12.2.11", "EpStrongBundle.theorem_12_2_11"),
  ("partIII|Thm 12.3.9", "EpStrongBundle.theorem_12_3_9"),
  ("partIII|Thm 13.5.6", "SBLocalization.theorem_13_5_6"),
  ("partIII|Thm 15.2.2", "SBLocalization.theorem_15_2_2_hyp"),
  ("partIII|Thm 15.2.5", "SBLocalization.theorem_15_2_5_hyp"),
  ("partIII|Thm 15.2.5", "SBLocalization.theorem_15_2_5_isTameBranched_hyp"),
  ("partIII|Lemma 16.2.2", "PolyfoldClass.lemma_16_2_2"),
  ("partIII|Def 16.2.3", "PolyfoldClass.definition_16_2_3"),
  ("partIII|Thm 16.2.6", "PolyfoldClass.theorem_16_2_6_complex"),
  ("partIII|Thm 16.4.6", "PolyfoldClass.OrientedRep.theorem_16_4_6_of_epStokes"),
  ("partIII|Thm 16.4.6", "PolyfoldClass.OrientedRep.theorem_16_4_6_all"),
  ("partIII|Thm 12.2.13", "EpStrongBundle.theorem_12_2_13"),
  ("partIII|Prop 13.3.19", "SBLocalization.proposition_13_3_19"),
  ("partIII|Prop 13.3.19", "SBLocalization.proposition_13_3_19_of_paracompact"),
  ("partIII|Thm 13.4.1", "SBLocalization.theorem_13_4_1"),
  ("partIII|Thm 13.4.3", "SBLocalization.theorem_13_4_3"),
  ("partIII|Thm 13.4.4", "SBLocalization.theorem_13_4_4"),
  ("partIII|Thm 13.5.3", "SBLocalization.theorem_13_5_3"),
  ("partIII|Thm 13.5.7", "SBLocalization.theorem_13_5_7"),
  ("partIII|Thm 14.1.6", "EpGroupoid.theorem_14_1_6_hyp"),
  ("partIII|Prop 14.4.14", "SBLocalization.proposition_14_4_14"),
  ("partIII|Prop 14.4.14", "SBLocalization.ZConcrete.proposition_14_4_14"),
  ("partIII|Lemma 14.5.2", "SBLocalization.BoundaryCommData.lemma_14_5_2"),
  ("partIII|Thm 14.5.5", "SBLocalization.theorem_14_5_5"),
  ("partIII|Thm 15.1.1", "SBLocalization.theorem_15_1_1_functor"),
  ("partIII|Thm 15.1.1", "SBLocalization.linearization_eq"),
  ("partIII|Thm 15.1.1", "SBLocalization.linearization_eq_zero"),
  ("partIII|Thm 15.1.1", "SBLocalization.theorem_15_1_1_intrinsic"),
  ("partIII|Thm 15.4.3", "SBLocalization.theorem_15_4_3"),
  ("partIII|Thm 15.4.3", "SBLocalization.theorem_15_4_3_all"),
  ("partIII|Thm 16.2.4", "PolyfoldClass.theorem_16_2_4"),
  ("partIII|Thm 16.3.15", "StrongPolyfoldBundle.theorem_16_3_15_one"),
  ("partIII|Thm 16.3.17", "StrongPolyfoldBundle.theorem_16_3_17_one"),
  ("partIII|Thm 16.3.17", "StrongPolyfoldBundle.theorem_16_3_17_two"),
  ("partIII|Thm 16.6.4", "StrongPolyfoldBundle.theorem_16_6_4"),
  ("partIII|Thm 12.5.3", "EpStrongBundle.theorem_12_5_3_push"),
  ("partIII|Thm 12.5.3", "EpStrongBundle.theorem_12_5_3_loc"),
  ("partIII|Thm 12.5.3", "EpStrongBundle.theorem_12_5_3_iff_loc"),
  ("partIII|Prop 12.5.6", "EpStrongBundle.proposition_12_5_6_loc"),
  ("partIII|Prop 12.5.6", "EpStrongBundle.proposition_12_5_6_of_loc"),
  ("partIII|Prop 13.4.2", "SBLocalization.proposition_13_4_2"),
  ("partIII|Prop 14.4.6", "SBLocalization.ZConcrete.proposition_14_4_6_2"),
  ("partIII|Prop 14.5.4", "SBLocalization.TransportInput.proposition_14_5_4"),
  ("partIII|Thm 16.2.4", "theorem_16_2_4_eff"),
  ("partIII|Prop 16.4.3", "PolyfoldClass.BranchedSuborbifold.proposition_16_4_3_naturality"),
  ("partIII|Thm 12.5.7", "SBLocalization.GenSBMap.theorem_12_5_7_one_loc_cls"),
  ("partIII|Thm 12.5.7", "SBLocalization.GenSBMap.theorem_12_5_7_two_loc_cls_unique"),
  ("partIII|Thm 12.5.7", "EpStrongBundle.IsStrongBundleEquivalence.theorem_12_5_7_rep_indep"),
  ("partIII|Prop 14.1.8", "SBLocalization.GenSBMap.proposition_14_1_8"),
  ("partIII|Prop 14.1.8", "SBLocalization.GenSBMap.proposition_14_1_8_pullMult"),
  ("partIII|Thm 14.1.9", "SBLocalization.theorem_14_1_9"),
  ("partIII|Thm 14.6.3", "SBLocalization.SectionCompatibleFaceData.theorem_14_6_3"),
  ("partIII|Thm 14.6.3", "SBLocalization.CompatibleFaceData.theorem_14_6_3_extension"),
  ("partIII|Thm 14.6.3", "SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3"),
  ("partIII|Thm 15.3.7", "SBLocalization.theorem_15_3_7"),
  ("partIII|Thm 15.3.7", "SBLocalization.theorem_15_3_7_in_particular_hyp"),
  ("partIII|Thm 15.3.9", "SBLocalization.theorem_15_3_9"),
  ("partIII|Cor 15.3.10", "SBLocalization.corollary_15_3_10_1"),
  ("partIII|Cor 15.3.10", "SBLocalization.corollary_15_3_10_3_bump"),
  ("partIII|Thm 15.4.1", "SBLocalization.theorem_15_4_1"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_oriented_collar"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_index_zero_oriented"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_wellDefined"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_index_zero_wellDefined"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_oriented_collar_all"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_index_zero_oriented_all"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_wellDefined_all"),
  ("partIII|Cor 15.4.4", "SBLocalization.corollary_15_4_4_index_zero_wellDefined_all"),
  ("partIII|Cor 15.4.4", "SBLocalization.integral_eq_of_isTransversalPerturbation"),
  ("partIII|Cor 15.4.4", "SBLocalization.pointCount_eq_of_isTransversalPerturbation"),
  ("partIII|Prop 16.3.16", "StrongPolyfoldBundle.proposition_16_3_16_two"),
  ("partIII|Thm 16.5.7", "StrongPolyfoldBundle.theorem_16_5_7"),
  ("partIII|Def 16.6.5", "StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_canonical"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_correspondence"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_canonical_wellDefined"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_canonical_solutionSet"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_all_admissible"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_all_admissible_wellDefined"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_all_admissible_unconditional"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional"),
  ("partIII|Thm 16.6.6", "StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional"),
  ("partIV|Prop 17.1.11", "GCT.PolyfoldConstruction.proposition_17_1_11"),
  ("partIV|Thm 17.1.14", "GCT.PolyfoldConstruction.theorem_17_1_14"),
  ("partIV|Thm 17.1.18", "GCT.PolyfoldConstruction.theorem_17_1_18"),
  ("partIV|Prop 17.1.23", "GCT.PolyfoldConstruction.proposition_17_1_23"),
  ("partIV|Prop 17.1.24", "GCT.PolyfoldConstruction.proposition_17_1_24"),
  ("partIV|Thm 17.1.26", "GCT.PolyfoldConstruction.theorem_17_1_26"),
  ("partIV|Thm 17.1.27", "GCT.PolyfoldConstruction.theorem_17_1_27"),
  ("partIV|Thm 17.1.28", "GCT.PolyfoldConstruction.theorem_17_1_28_gct"),
  ("partIV|Thm 17.1.28", "GCT.PolyfoldConstruction.theorem_17_1_28"),
  ("partIV|Thm 17.1.28", "GCT.UniformizedPolyfold.theorem_17_1_28_levels"),
  ("partIV|Cor 17.1.29", "GCT.PolyfoldConstruction.corollary_17_1_29_model"),
  ("partIV|Cor 17.1.29", "GCT.PolyfoldConstruction.corollary_17_1_29_of_coveringFamily"),
  ("partIV|Cor 17.1.29", "GCT.PolyfoldConstruction.corollary_17_1_29"),
  ("partIV|Prop 17.2.4", "GCT.PolyfoldConstruction.proposition_17_2_4"),
  ("partIV|Prop 17.2.4", "GCT.PolyfoldConstruction.proposition_17_2_4_banachable"),
  ("partIV|Prop 17.2.4", "GCT.PolyfoldConstruction.proposition_17_2_4_sc"),
  ("partIV|Prop 17.2.5", "GCT.PolyfoldConstruction.proposition_17_2_5"),
  ("partIV|Prop 17.2.12", "GCT.PolyfoldConstruction.proposition_17_2_12"),
  ("partIV|Prop 17.2.14", "GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt"),
  ("partIV|Prop 17.2.14", "GCT.PolyfoldConstruction.proposition_17_2_14"),
  ("partIV|Prop 17.2.15", "GCT.PolyfoldConstruction.proposition_17_2_15"),
  ("partIV|Prop 17.2.16", "GCT.PolyfoldConstruction.proposition_17_2_16"),
  ("partIV|Prop 17.3.4", "GCT.PolyfoldConstruction.proposition_17_3_4"),
  ("partIV|Prop 17.3.4", "GCT.PolyfoldConstruction.proposition_17_3_4_of_nonempty"),
  ("partIV|Prop 17.3.6", "GCT.PolyfoldConstruction.proposition_17_3_6"),
  ("partIV|Prop 17.3.8", "GCT.PolyfoldConstruction.proposition_17_3_8"),
  ("partIV|Thm 17.4.16", "GCT.PolyfoldConstruction.theorem_17_4_16"),
  ("partIV|Prop 17.5.2", "GCT.PolyfoldConstruction.proposition_17_5_2_one"),
  ("partIV|Prop 17.5.2", "GCT.PolyfoldConstruction.proposition_17_5_2_two"),
  ("partIV|Prop 17.5.5", "GCT.PolyfoldConstruction.proposition_17_5_5_one"),
  ("partIV|Prop 17.5.5", "GCT.PolyfoldConstruction.proposition_17_5_5_two"),
  ("partIV|Prop 17.5.7", "GCT.PolyfoldConstruction.proposition_17_5_7"),
  ("partIV|Thm 17.6.4", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4"),
  ("partIV|Thm 17.6.4", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book"),
  ("partIV|Thm 17.6.6", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6"),
  ("partIV|Thm 17.6.6", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1"),
  ("partIV|Thm 17.6.6", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_book"),
  ("partIV|Thm 17.6.6", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_6_dim1_book"),
  ("partIV|Thm 17.6.7", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all"),
  ("partIV|Thm 17.6.7", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all"),
  ("partIV|Thm 17.6.8", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8"),
  ("partIV|Thm 17.6.8", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book"),
  ("partIV|Thm 17.6.9", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9"),
  ("partIV|Thm 17.6.9", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1"),
  ("partIV|Thm 17.6.9", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_book"),
  ("partIV|Thm 17.6.9", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_9_dim1_book"),
  ("partIV|Thm 17.6.10", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all"),
  ("partIV|Thm 17.6.10", "GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_dim1_book_all"),
  ("partIV|Prop 17.8.6", "proposition_17_8_6"),
  ("partIV|Prop 17.8.15", "ProperPolyfoldCoveringStructure.proposition_17_8_15"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16_one"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16_two"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16_four"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16_three"),
  ("partIV|Prop 17.8.16", "ProperCoveringUniformizerConstruction.proposition_17_8_16_branched_tame"),
  ("partIV|Thm 18.1.5", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5"),
  ("partIV|Thm 18.1.5", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_subcategory"),
  ("partIV|Thm 18.1.5", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5_model"),
  ("partIV|Thm 18.1.12", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one"),
  ("partIV|Thm 18.1.12", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two"),
  ("partIV|Thm 18.1.12", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three"),
  ("partIV|Thm 18.1.12", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive"),
  ("partIV|Thm 18.2.2", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2"),
  ("partIV|Thm 18.2.6", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6"),
  ("partIV|Thm 18.3.5", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5"),
  ("partIV|Thm 18.3.6", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6"),
  ("partIV|Prop 18.4.3", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3"),
  ("partIV|Prop 18.4.3", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula"),
  ("partIV|Prop 18.4.3", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text"),
  ("partIV|Prop 18.4.3", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff"),
  ("partIV|Thm 18.4.4", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4"),
  ("partIV|Thm 18.4.4", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4_modelFree"),
  ("partIV|Prop 18.5.6", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp"),
  ("partIV|Prop 18.5.6", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp"),
  ("partIV|Prop 18.5.6", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented"),
  ("partIV|Thm 18.6.1", "GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_oriented_modelFree"),
  ("partIV|Thm 19.2.2", "GroupoidalCategory.BasicConstruction.theorem_19_2_2_one"),
  ("partIV|Thm 19.2.2", "GroupoidalCategory.BasicConstruction.theorem_19_2_2_two"),
  ("partIV|Thm 19.2.2", "GroupoidalCategory.BasicConstruction.theorem_19_2_2_three"),
  ("partIV|Thm 19.2.2", "GroupoidalCategory.BasicConstruction.theorem_19_2_2_four"),
  ("partIV|Thm 19.2.2", "GroupoidalCategory.BasicConstruction.theorem_19_2_2_five"),
  ("partIV|Thm 19.3.3", "GroupoidalCategory.BasicConstruction.theorem_19_3_3"),
  ("partIV|Prop 19.3.4", "GroupoidalCategory.BasicConstruction.proposition_19_3_4"),
  ("partIV|Prop 19.3.4", "GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology"),
  ("partIV|Prop 19.3.5", "GroupoidalCategory.BasicConstruction.proposition_19_3_5"),
  ("partIV|Prop 19.3.7", "GroupoidalCategory.BasicConstruction.proposition_19_3_7"),
  ("partIV|Prop 19.4.2", "GroupoidalCategory.BasicConstruction.proposition_19_4_2"),
  ("partIV|Prop 19.4.2", "GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two"),
  ("partIV|Prop 19.4.2", "GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three"),
  ("partIV|Prop 19.4.2", "GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp"),
  ("partIV|Prop 19.4.4", "GroupoidalCategory.BasicConstruction.proposition_19_4_4"),
  ("partIV|Prop 19.4.5", "GroupoidalCategory.BasicConstruction.proposition_19_4_5"),
  ("partIV|Thm 19.4.6", "GroupoidalCategory.BasicConstruction.theorem_19_4_6_one"),
  ("partIV|Thm 19.4.6", "GroupoidalCategory.BasicConstruction.theorem_19_4_6_two"),
  ("partIV|Prop 19.4.7", "GroupoidalCategory.BasicConstruction.proposition_19_4_7"),
  ("partIV|Cor 19.4.8", "GroupoidalCategory.BasicConstruction.corollary_19_4_8"),
  ("partIV|Thm 19.5.1", "GroupoidalCategory.BasicConstruction.theorem_19_5_1"),
  ("partIV|Thm 19.5.1", "GroupoidalCategory.BasicConstruction.theorem_19_5_1_natural"),
  ("partIV|Cor 19.5.2", "GroupoidalCategory.BasicConstruction.corollary_19_5_2"),
  ("partIV|Thm 19.5.3", "GroupoidalCategory.BasicConstruction.theorem_19_5_3_one"),
  ("partIV|Thm 19.5.3", "GroupoidalCategory.BasicConstruction.theorem_19_5_3_two"),
  ("partIV|Prop 19.5.7", "GroupoidalCategory.BasicConstruction.proposition_19_5_7"),
  ("partIV|Prop 19.5.9", "GroupoidalCategory.BasicConstruction.proposition_19_5_9"),
  ("partIV|Prop 19.5.11", "GroupoidalCategory.BasicConstruction.proposition_19_5_11"),
  ("partIV|Thm 19.6.8", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_8_one"),
  ("partIV|Thm 19.6.8", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_8_two"),
  ("partIV|Thm 19.6.8", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_8_three"),
  ("partIV|Thm 19.6.8", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_8_four"),
  ("partIV|Thm 19.6.8", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_8_five"),
  ("partIV|Prop 19.6.9", "GroupoidalCategory.BasicStrongBundleConstruction.proposition_19_6_9"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_one"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_two"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_three"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_four"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_five"),
  ("partIV|Thm 19.6.11", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_11_six"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_H"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_total"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_s"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_t"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_u"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_inv"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_of_bundleTransitionData"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_book"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.StrongBundleUniformizerConstruction.theorem_19_6_13_m"),
  ("partIV|Thm 19.6.13", "GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13_m"),
  ("partIV|Prop 19.7.13", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13"),
  ("partIV|Prop 19.7.14", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_14"),
  ("partIV|Prop 19.7.15", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one"),
  ("partIV|Prop 19.7.15", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp"),
  ("partIV|Prop 19.7.23", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_23_hyp"),
  ("partIV|Prop 19.7.24", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_24_hyp"),
  ("partIV|Prop 19.7.26", "GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26"),
  ("partIV|Thm 19.7.28", "GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_one_hyp"),
  ("partIV|Thm 19.7.28", "GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_two_hyp"),
  ("partIV|Thm 19.7.28", "GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_three_hyp"),
  ("partIV|Thm 19.7.29", "GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_29_hyp"),
  ("partIV|Thm 19.8.6", "GroupoidalCategory.PullbackUniformizerConstruction.theorem_19_8_6_one_four"),
  ("partIV|Thm 19.8.6", "GroupoidalCategory.PullbackUniformizerConstruction.theorem_19_8_6_hyp"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareUniformizerConstruction.theorem_19_8_22_topology_hyp"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareUniformizerConstruction.theorem_19_8_22_inv_hyp"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareUniformizerConstruction.theorem_19_8_22_unit"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareUniformizerConstruction.theorem_19_8_22_mul_hyp"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareBasicConstruction.theorem_19_8_22_inv_hyp"),
  ("partIV|Thm 19.8.22", "GroupoidalCategory.SquareBasicConstruction.theorem_19_8_22_hyp"),
  ("tame|Thm 2.7.13", "MPolyfold.theorem_2_7_13_book"),
  ("tame|Thm 7.6.9", "EpGroupoid.theorem_7_6_9_book")]

def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

def auxComp : Name → Bool
  | .str _ s => s.startsWith "_" ||
      (s.startsWith "match_" && isDigits (s.drop 6).toString) ||
      (s.startsWith "proof_" && isDigits (s.drop 6).toString) ||
      (s.startsWith "eq_" && isDigits (s.drop 3).toString) ||
      ["eq_def", "brecOn", "below", "binductionOn", "ibelow", "casesOn", "recOn", "rec",
       "noConfusion", "noConfusionType", "ctorIdx", "inj", "injEq", "sizeOf_spec"].contains s
  | .num .. => true
  | .anonymous => false

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.getRoot == `Polyfold
  | none => false

/-- The declaration a constant is reported under. -/
def parentOf (env : Environment) (n : Name) : Name := Id.run do
  let n := privateToUserName n
  let cs := n.components
  let n' := match cs.findIdx? auxComp with
    | some i => Name.fromComponents (cs.take i)
    | none => n
  match env.find? n' with
  | some (.ctorInfo c) => return c.induct
  | some (.recInfo _) => return n'.getPrefix
  | _ =>
    match env.getProjectionFnInfo? n' with
    | some p => match env.find? p.ctorName with
      | some (.ctorInfo c) => return c.induct
      | _ => return n'
    | none => return n'

def directDeps (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some (.defnInfo d) => d.type.getUsedConstantsAsSet ∪ d.value.getUsedConstantsAsSet
  | some (.opaqueInfo d) => d.type.getUsedConstantsAsSet ∪ d.value.getUsedConstantsAsSet
  | some (.thmInfo d) => d.type.getUsedConstantsAsSet
  | some (.axiomInfo d) => d.type.getUsedConstantsAsSet
  | some (.inductInfo i) => i.ctors.foldl (fun s c => match env.find? c with
      | some ci => s ∪ ci.type.getUsedConstantsAsSet | none => s) i.type.getUsedConstantsAsSet
  | some (.ctorInfo c) => c.type.getUsedConstantsAsSet.insert c.induct
  | some (.recInfo r) => ({} : NameSet).insert r.getMajorInduct
  | _ => {}

/-- Project constants we follow: everything except ordinary (non-auxiliary) theorems. -/
def follow (env : Environment) (d : Name) : Bool :=
  isProject env d && (!(env.find? d matches some (.thmInfo _)) || parentOf env d != d)

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo d) =>
    if isInstanceCore env n then "instance"
    else if d.hints matches .abbrev then "abbrev" else "def"
  | some (.inductInfo _) =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.axiomInfo _) => "axiom"
  | some _ => "other"
  | none => "missing"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let out := "Exposition/checklist/"
  let mut work : Array Name := #[]
  let mut mainLines : Array String := #[]
  for (lab, s) in mains do
    let n := `Polyfold ++ s.toName
    match env.find? n with
    | none => logWarning m!"missing main {n}"
    | some ci =>
      let ds := ci.type.getUsedConstantsAsSet.toList.filter (follow env)
      work := work ++ ds.toArray
      let ps := (ds.map (parentOf env)).eraseDups.filter (· != n)
      mainLines := mainLines.push
        s!"{lab}\t{n}\t{kindOf env n}\t{env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!}\t{" ".intercalate (ps.map toString)}"
  -- BFS over raw constants; edges between parents
  let mut seen : NameSet := {}
  let mut edges : Std.HashMap Name NameSet := {}
  while !work.isEmpty do
    let r := work.back!
    work := work.pop
    if seen.contains r then continue
    seen := seen.insert r
    let p := parentOf env r
    if !seen.contains p then work := work.push p
    let mut es := edges.getD p {}
    for d in (directDeps env r).toList do
      if follow env d then
        let q := parentOf env d
        if q != p then es := es.insert q
        if !seen.contains d then work := work.push d
    edges := edges.insert p es
  let mut lines : Array String := #[]
  for (p, es) in edges.toList do
    let m := match env.getModuleIdxFor? p with
      | some i => env.header.moduleNames[i.toNat]!.toString | none => "?"
    lines := lines.push s!"{p}\t{kindOf env p}\t{m}\t{" ".intercalate (es.toList.map toString)}"
  IO.FS.writeFile (out ++ "graph.tsv") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out ++ "mains.tsv") ("\n".intercalate mainLines.toList ++ "\n")
  logInfo m!"mains {mainLines.size}, raw constants {seen.size}, nodes {edges.size}"
