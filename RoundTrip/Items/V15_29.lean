import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_29

set_option maxSynthPendingDepth 3

/-! Round trip for V15_29 (2021 Theorem 15.3.7, pp. 693–698; 2017: Theorem 15.4): general
position, existence of the perturbation.

`A` is the conjunction of the types of the 109 theorems of the item (the other 32 declarations
are definitions: vocabulary), at universe `0` (`nonempty_scPlusGPFamily_biUnion`,
`nonempty_gpFamily_biUnion` at `0, 0`, the index type in `Type`; the `epSEP` examples have no
universe parameter).  The main conjunct is `theorem_15_3_7`:
`theorem_15_3_7_existence_statement A ∧ (Nonempty A.X.GoodSystem → theorem_15_3_7_statement A)`.

* `A_to_B`: not proved.  Every form of the theorem in `A` assumes, besides `B`'s hypotheses,
  (i) the tame-germ hypothesis `A.B.IsScFredholmSectionTame f`, (ii) bump functions in the
  pointwise reading `AdmitsBumpFunctionsPointwise` (non-zero at the given point; `B` has the
  reading as printed, `AdmitsBumpFunctions`, non-zero somewhere), and (iii) for a structurable
  `Λ`, a good system (`Nonempty A.X.GoodSystem`, e.g. from paracompact `|X|`); without (iii) `A`
  gives an sc⁺-multisection functor only (`theorem_15_3_7_existence`, Remark 15.3.8).  `B` asks
  for a structurable `Λ` with none of (i)–(iii).  With (i)–(iii) (paracompact `|X|` for (iii))
  added to `B` (`Bplus`), `A ⇒ Bplus` is proved (`A_to_Bplus`, from the conjunct
  `theorem_15_3_7_of_paracompact`).
* `B_to_A` (main conjunct): proved (`B_to_main`): `B`'s hypotheses are among the main
  conjunct's (the pointwise bump functions give the printed ones,
  `AdmitsBumpFunctionsPointwise.weak`), and structurable gives sc⁺-multisection.
  `B_to_statement`: `B` gives `theorem_15_3_7_statement A` for every `A`, hence also the conjuncts
  `theorem_15_3_7_existence`, `theorem_15_3_7_of_goodSystem`, `theorem_15_3_7_of_paracompact`
  (`B_to_forms`).
* `B_to_A` (all of `A`): not proved: the other conjuncts are proof steps (families `GPFamily`,
  seeds, parametric transversality, norm estimates, examples on `ℝⁿ × ℝ⁰`) that `B` does not
  state.
-/

namespace RoundTrip.V15_29
open Set Function Polyfold Polyfold.SBLocalization

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_existence.{0}) ∧
  (type_of% @Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_scPlusGPFamily_nhds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasPointwiseParamOnto.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasParamOntoOpen.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_tameChart_centred.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem) ∧
  (type_of% @Polyfold.SBLocalization.isParamOntoAt_iff_vec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.muLin_surjective.{0}) ∧
  (type_of% @Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsParamOntoVec.of_mor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.transSec_eq_muLin.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_transSec_eqOn.{0}) ∧
  (type_of% @Polyfold.SBLocalization.transSec_of_eq_tgt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_linearRep_of_mor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsParamOntoAt.of_mor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mem_solutionSet_tgt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.src_mem_levelSet_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_eq_paramSlice.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusSection_paramSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sectionSupport_paramSec_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_fiberZero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.natTerm_paramSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.atom_R.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.atom_V.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isAtomic_Λ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isSection_branch.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isLocalRepOn_branch.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isLocalRepOn_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isLinearFamily.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isStructurable_Λ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.domSupp_Λ_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.norm_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SeedData.isParamOntoAt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_seeds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalParamSeeds_of.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_pointwise.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isParamOntoVec_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise) ∧
  (type_of% @Polyfold.SBLocalization.isSection_negRestrict.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusSection_negRestrict.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pbLin_restrictSection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pbLin_injective.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSlice_branch_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fiberLin_toIntr_subDeriv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.principal_eq_fiberLin.{0}) ∧
  (type_of% @Polyfold.SBLocalization.principal_restrictTo_negRestrict.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isParamGP_restrictTo_of_onto.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isGeneralPositionGerm_branchParam.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_local_paramGP.{0}) ∧
  (type_of% @Polyfold.SBLocalization.auxLe_of_pos.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_pos_auxLe_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasParametricGeneralPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_hyp_local.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_local.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto) ∧
  (type_of% @Polyfold.SBLocalization.nonempty_gpFamily_biUnion.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_gpFamily_of_compact.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_norm_lt_of_ae) ∧
  (type_of% @Polyfold.SBLocalization.sum_abs_lt_one) ∧
  (type_of% @Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.fiber_eq_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_apply.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSection_paramSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramFib.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_fin_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSection_append.{0}) ∧
  (type_of% @Polyfold.SBLocalization.paramSec_append.{0}) ∧
  (type_of% @Polyfold.SBLocalization.normW_paramSec_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_le_of_linear.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalRepOn_famAdd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsLinearFamily.famAdd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsParamOntoAt.famAdd_left.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsParamOntoAt.famAdd_right.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_of_multisectionAdd_pos.{0}) ∧
  (type_of% @Polyfold.SBLocalization.normW_add_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.domSupp_multisectionAdd_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalRepOn_zeroMultisection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_zeroMultisection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.domSupp_zeroMultisection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_3_7.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_existence.{0},
    @Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion.{0, 0},
    @Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact.{0},
    @Polyfold.SBLocalization.exists_scPlusGPFamily_nhds.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0},
    @Polyfold.SBLocalization.hasPointwiseParamOnto.{0},
    @Polyfold.SBLocalization.hasParamOntoOpen.{0},
    @Polyfold.SBLocalization.exists_tameChart_centred.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem,
    @Polyfold.SBLocalization.isParamOntoAt_iff_vec.{0},
    @Polyfold.SBLocalization.muLin_surjective.{0},
    @Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport.{0},
    @Polyfold.SBLocalization.IsParamOntoVec.of_mor.{0},
    @Polyfold.SBLocalization.transSec_eq_muLin.{0},
    @Polyfold.SBLocalization.paramSec_transSec_eqOn.{0},
    @Polyfold.SBLocalization.transSec_of_eq_tgt.{0},
    @Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn.{0},
    @Polyfold.SBLocalization.exists_linearRep_of_mor.{0},
    @Polyfold.SBLocalization.IsParamOntoAt.of_mor.{0},
    @Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv.{0},
    @Polyfold.SBLocalization.mem_solutionSet_tgt.{0},
    @Polyfold.SBLocalization.src_mem_levelSet_one.{0},
    @Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds.{0},
    @Polyfold.SBLocalization.paramSec_eq_paramSlice.{0},
    @Polyfold.SBLocalization.isScPlusSection_paramSec.{0},
    @Polyfold.SBLocalization.sectionSupport_paramSec_subset.{0},
    @Polyfold.SBLocalization.paramSec_fiberZero.{0},
    @Polyfold.SBLocalization.natTerm_paramSec.{0},
    @Polyfold.SBLocalization.SeedData.atom_R.{0},
    @Polyfold.SBLocalization.SeedData.atom_V.{0},
    @Polyfold.SBLocalization.SeedData.isAtomic_Λ.{0},
    @Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ.{0},
    @Polyfold.SBLocalization.SeedData.isSection_branch.{0},
    @Polyfold.SBLocalization.SeedData.isLocalRepOn_branch.{0},
    @Polyfold.SBLocalization.SeedData.isLocalRepOn_zero.{0},
    @Polyfold.SBLocalization.SeedData.isLinearFamily.{0},
    @Polyfold.SBLocalization.SeedData.isStructurable_Λ.{0},
    @Polyfold.SBLocalization.SeedData.domSupp_Λ_subset.{0},
    @Polyfold.SBLocalization.SeedData.norm_le.{0},
    @Polyfold.SBLocalization.SeedData.isParamOntoAt.{0},
    @Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_seeds.{0},
    @Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero,
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds,
    @Polyfold.SBLocalization.hasLocalParamSeeds_of.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_pointwise.{0},
    @Polyfold.SBLocalization.isParamOntoVec_epSEP_zero,
    @Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero,
    @Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero,
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise,
    @Polyfold.SBLocalization.isSection_negRestrict.{0},
    @Polyfold.SBLocalization.isScPlusSection_negRestrict.{0},
    @Polyfold.SBLocalization.pbLin_restrictSection.{0},
    @Polyfold.SBLocalization.pbLin_injective.{0},
    @Polyfold.SBLocalization.paramSlice_branch_eq.{0},
    @Polyfold.SBLocalization.fiberLin_toIntr_subDeriv.{0},
    @Polyfold.SBLocalization.principal_eq_fiberLin.{0},
    @Polyfold.SBLocalization.principal_restrictTo_negRestrict.{0},
    @Polyfold.SBLocalization.isParamGP_restrictTo_of_onto.{0},
    @Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec.{0},
    @Polyfold.SBLocalization.isGeneralPositionGerm_branchParam.{0},
    @Polyfold.SBLocalization.exists_local_paramGP.{0},
    @Polyfold.SBLocalization.auxLe_of_pos.{0},
    @Polyfold.SBLocalization.exists_pos_auxLe_subset.{0},
    @Polyfold.SBLocalization.hasParametricGeneralPosition.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_hyp_local.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_local.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local,
    @Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto,
    @Polyfold.SBLocalization.nonempty_gpFamily_biUnion.{0, 0},
    @Polyfold.SBLocalization.exists_gpFamily_of_compact.{0},
    @Polyfold.SBLocalization.exists_norm_lt_of_ae,
    @Polyfold.SBLocalization.sum_abs_lt_one,
    @Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_hyp.{0},
    @Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero,
    @Polyfold.SBLocalization.fiber_eq_epSEP_zero,
    @Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero,
    @Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero,
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp,
    @Polyfold.SBLocalization.paramSec_apply.{0},
    @Polyfold.SBLocalization.isSection_paramSec.{0},
    @Polyfold.SBLocalization.paramFib.{0},
    @Polyfold.SBLocalization.paramSec_fin_zero.{0},
    @Polyfold.SBLocalization.isSection_append.{0},
    @Polyfold.SBLocalization.paramSec_append.{0},
    @Polyfold.SBLocalization.normW_paramSec_le.{0},
    @Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn.{0},
    @Polyfold.SBLocalization.pointwiseNorm_le_of_linear.{0},
    @Polyfold.SBLocalization.isLocalRepOn_famAdd.{0},
    @Polyfold.SBLocalization.IsLinearFamily.famAdd.{0},
    @Polyfold.SBLocalization.IsParamOntoAt.famAdd_left.{0},
    @Polyfold.SBLocalization.IsParamOntoAt.famAdd_right.{0},
    @Polyfold.SBLocalization.exists_of_multisectionAdd_pos.{0},
    @Polyfold.SBLocalization.normW_add_le.{0},
    @Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le.{0},
    @Polyfold.SBLocalization.domSupp_multisectionAdd_subset.{0},
    @Polyfold.SBLocalization.isLocalRepOn_zeroMultisection.{0},
    @Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero,
    @Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero.{0},
    @Polyfold.SBLocalization.pointwiseNorm_zeroMultisection.{0},
    @Polyfold.SBLocalization.domSupp_zeroMultisection.{0},
    @Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero⟩

/-- **B ⇒ `theorem_15_3_7_statement A`** for every `A`. -/
theorem B_to_statement (hB : B) (A : SEP.{0}) : theorem_15_3_7_statement A := by
  intro hX hbump f hf _ hS N U hcc h hhc hhφ hh
  obtain ⟨Λ, -, hst, hN, hdom, htr, hgp⟩ :=
    hB A hX hbump.weak f hf hS N U hcc h ⟨hhc, hh, hhφ⟩
  exact ⟨Λ, hst, hN, hdom, htr, hgp⟩

/-- **B ⇒ the main conjunct** `theorem_15_3_7`. -/
theorem B_to_main : B → (type_of% @Polyfold.SBLocalization.theorem_15_3_7.{0}) := by
  intro hB A
  refine ⟨fun hX hbump f hf hft hS N U hcc h hhc hhφ hh => ?_, fun _ => B_to_statement hB A⟩
  obtain ⟨Λ, hst, hN, hdom, htr, hgp⟩ :=
    B_to_statement hB A hX hbump f hf hft hS N U hcc h hhc hhφ hh
  exact ⟨Λ, hst.1, hN, hdom, htr, hgp⟩

/-- **B ⇒ the other full forms of the theorem in `A`.** -/
theorem B_to_forms : B →
    (type_of% @Polyfold.SBLocalization.theorem_15_3_7_existence.{0}) ∧
    (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem.{0}) ∧
    (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0}) := by
  intro hB
  exact ⟨fun {A} => (B_to_main hB (A := A)).1, fun {A} _ => B_to_statement hB A,
    fun {A} _ => B_to_statement hB A⟩

/-- `B` with the hypotheses of `A`'s forms of the theorem added: tame germ data, pointwise bump
functions (in place of the printed reading), paracompact `|X|` (for the good system). -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise → A.X.HasParacompactOrbitSpace →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
      ∃ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ ∧ IsStructurable A Λ ∧
        (∀ x, pointwiseNorm N Λ x < h x) ∧ domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧
        IsInGeneralPosition A f Λ

theorem paracompact_to_Bplus :
    (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0}) → Bplus := by
  intro H A hX hbump hpara f hf hft hS N U hcc h hh
  obtain ⟨Λ, hst, hN, hdom, htr, hgp⟩ :=
    H hpara hX hbump f hf hft hS N U hcc h hh.1 hh.2.2 hh.2.1
  exact ⟨Λ, hst.1, hst, hN, hdom, htr, hgp⟩

theorem A_to_Bplus : A → Bplus := fun hA => paracompact_to_Bplus hA.2.2.2.2.2.2.1

/-- `Bplus` is `B` with more hypotheses. -/
theorem B_to_Bplus : B → Bplus := fun hB A hX hbump _ f hf _ hS N U hcc h hh =>
  hB A hX hbump.weak f hf hS N U hcc h hh

#rt_check RoundTrip.V15_29.B_to_main [Polyfold.SBLocalization.theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_existence, Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion, Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact, Polyfold.SBLocalization.exists_scPlusGPFamily_nhds, Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.SBLocalization.hasPointwiseParamOnto, Polyfold.SBLocalization.hasParamOntoOpen, Polyfold.SBLocalization.exists_tameChart_centred, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem, Polyfold.SBLocalization.isParamOntoAt_iff_vec, Polyfold.SBLocalization.muLin_surjective, Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport, Polyfold.SBLocalization.IsParamOntoVec.of_mor, Polyfold.SBLocalization.transSec_eq_muLin, Polyfold.SBLocalization.paramSec_transSec_eqOn, Polyfold.SBLocalization.transSec_of_eq_tgt, Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn, Polyfold.SBLocalization.exists_linearRep_of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv, Polyfold.SBLocalization.mem_solutionSet_tgt, Polyfold.SBLocalization.src_mem_levelSet_one, Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds, Polyfold.SBLocalization.paramSec_eq_paramSlice, Polyfold.SBLocalization.isScPlusSection_paramSec, Polyfold.SBLocalization.sectionSupport_paramSec_subset, Polyfold.SBLocalization.paramSec_fiberZero, Polyfold.SBLocalization.natTerm_paramSec, Polyfold.SBLocalization.SeedData.atom_R, Polyfold.SBLocalization.SeedData.atom_V, Polyfold.SBLocalization.SeedData.isAtomic_Λ, Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ, Polyfold.SBLocalization.SeedData.isSection_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_zero, Polyfold.SBLocalization.SeedData.isLinearFamily, Polyfold.SBLocalization.SeedData.isStructurable_Λ, Polyfold.SBLocalization.SeedData.domSupp_Λ_subset, Polyfold.SBLocalization.SeedData.norm_le, Polyfold.SBLocalization.SeedData.isParamOntoAt, Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds, Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds, Polyfold.SBLocalization.theorem_15_3_7_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_of, Polyfold.SBLocalization.theorem_15_3_7_of_pointwise, Polyfold.SBLocalization.isParamOntoVec_epSEP_zero, Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero, Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise, Polyfold.SBLocalization.isSection_negRestrict, Polyfold.SBLocalization.isScPlusSection_negRestrict, Polyfold.SBLocalization.pbLin_restrictSection, Polyfold.SBLocalization.pbLin_injective, Polyfold.SBLocalization.paramSlice_branch_eq, Polyfold.SBLocalization.fiberLin_toIntr_subDeriv, Polyfold.SBLocalization.principal_eq_fiberLin, Polyfold.SBLocalization.principal_restrictTo_negRestrict, Polyfold.SBLocalization.isParamGP_restrictTo_of_onto, Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec, Polyfold.SBLocalization.isGeneralPositionGerm_branchParam, Polyfold.SBLocalization.exists_local_paramGP, Polyfold.SBLocalization.auxLe_of_pos, Polyfold.SBLocalization.exists_pos_auxLe_subset, Polyfold.SBLocalization.hasParametricGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp_local, Polyfold.SBLocalization.theorem_15_3_7_of_local, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local, Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto, Polyfold.SBLocalization.nonempty_gpFamily_biUnion, Polyfold.SBLocalization.exists_gpFamily_of_compact, Polyfold.SBLocalization.exists_norm_lt_of_ae, Polyfold.SBLocalization.sum_abs_lt_one, Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp, Polyfold.SBLocalization.theorem_15_3_7_of_hyp, Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero, Polyfold.SBLocalization.fiber_eq_epSEP_zero, Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero, Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp, Polyfold.SBLocalization.paramSec_apply, Polyfold.SBLocalization.isSection_paramSec, Polyfold.SBLocalization.paramFib, Polyfold.SBLocalization.paramSec_fin_zero, Polyfold.SBLocalization.isSection_append, Polyfold.SBLocalization.paramSec_append, Polyfold.SBLocalization.normW_paramSec_le, Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn, Polyfold.SBLocalization.pointwiseNorm_le_of_linear, Polyfold.SBLocalization.isLocalRepOn_famAdd, Polyfold.SBLocalization.IsLinearFamily.famAdd, Polyfold.SBLocalization.IsParamOntoAt.famAdd_left, Polyfold.SBLocalization.IsParamOntoAt.famAdd_right, Polyfold.SBLocalization.exists_of_multisectionAdd_pos, Polyfold.SBLocalization.normW_add_le, Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le, Polyfold.SBLocalization.domSupp_multisectionAdd_subset, Polyfold.SBLocalization.isLocalRepOn_zeroMultisection, Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero, Polyfold.SBLocalization.pointwiseNorm_zeroMultisection, Polyfold.SBLocalization.domSupp_zeroMultisection, Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero]
#rt_check RoundTrip.V15_29.B_to_forms [Polyfold.SBLocalization.theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_existence, Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion, Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact, Polyfold.SBLocalization.exists_scPlusGPFamily_nhds, Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.SBLocalization.hasPointwiseParamOnto, Polyfold.SBLocalization.hasParamOntoOpen, Polyfold.SBLocalization.exists_tameChart_centred, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem, Polyfold.SBLocalization.isParamOntoAt_iff_vec, Polyfold.SBLocalization.muLin_surjective, Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport, Polyfold.SBLocalization.IsParamOntoVec.of_mor, Polyfold.SBLocalization.transSec_eq_muLin, Polyfold.SBLocalization.paramSec_transSec_eqOn, Polyfold.SBLocalization.transSec_of_eq_tgt, Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn, Polyfold.SBLocalization.exists_linearRep_of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv, Polyfold.SBLocalization.mem_solutionSet_tgt, Polyfold.SBLocalization.src_mem_levelSet_one, Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds, Polyfold.SBLocalization.paramSec_eq_paramSlice, Polyfold.SBLocalization.isScPlusSection_paramSec, Polyfold.SBLocalization.sectionSupport_paramSec_subset, Polyfold.SBLocalization.paramSec_fiberZero, Polyfold.SBLocalization.natTerm_paramSec, Polyfold.SBLocalization.SeedData.atom_R, Polyfold.SBLocalization.SeedData.atom_V, Polyfold.SBLocalization.SeedData.isAtomic_Λ, Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ, Polyfold.SBLocalization.SeedData.isSection_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_zero, Polyfold.SBLocalization.SeedData.isLinearFamily, Polyfold.SBLocalization.SeedData.isStructurable_Λ, Polyfold.SBLocalization.SeedData.domSupp_Λ_subset, Polyfold.SBLocalization.SeedData.norm_le, Polyfold.SBLocalization.SeedData.isParamOntoAt, Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds, Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds, Polyfold.SBLocalization.theorem_15_3_7_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_of, Polyfold.SBLocalization.theorem_15_3_7_of_pointwise, Polyfold.SBLocalization.isParamOntoVec_epSEP_zero, Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero, Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise, Polyfold.SBLocalization.isSection_negRestrict, Polyfold.SBLocalization.isScPlusSection_negRestrict, Polyfold.SBLocalization.pbLin_restrictSection, Polyfold.SBLocalization.pbLin_injective, Polyfold.SBLocalization.paramSlice_branch_eq, Polyfold.SBLocalization.fiberLin_toIntr_subDeriv, Polyfold.SBLocalization.principal_eq_fiberLin, Polyfold.SBLocalization.principal_restrictTo_negRestrict, Polyfold.SBLocalization.isParamGP_restrictTo_of_onto, Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec, Polyfold.SBLocalization.isGeneralPositionGerm_branchParam, Polyfold.SBLocalization.exists_local_paramGP, Polyfold.SBLocalization.auxLe_of_pos, Polyfold.SBLocalization.exists_pos_auxLe_subset, Polyfold.SBLocalization.hasParametricGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp_local, Polyfold.SBLocalization.theorem_15_3_7_of_local, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local, Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto, Polyfold.SBLocalization.nonempty_gpFamily_biUnion, Polyfold.SBLocalization.exists_gpFamily_of_compact, Polyfold.SBLocalization.exists_norm_lt_of_ae, Polyfold.SBLocalization.sum_abs_lt_one, Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp, Polyfold.SBLocalization.theorem_15_3_7_of_hyp, Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero, Polyfold.SBLocalization.fiber_eq_epSEP_zero, Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero, Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp, Polyfold.SBLocalization.paramSec_apply, Polyfold.SBLocalization.isSection_paramSec, Polyfold.SBLocalization.paramFib, Polyfold.SBLocalization.paramSec_fin_zero, Polyfold.SBLocalization.isSection_append, Polyfold.SBLocalization.paramSec_append, Polyfold.SBLocalization.normW_paramSec_le, Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn, Polyfold.SBLocalization.pointwiseNorm_le_of_linear, Polyfold.SBLocalization.isLocalRepOn_famAdd, Polyfold.SBLocalization.IsLinearFamily.famAdd, Polyfold.SBLocalization.IsParamOntoAt.famAdd_left, Polyfold.SBLocalization.IsParamOntoAt.famAdd_right, Polyfold.SBLocalization.exists_of_multisectionAdd_pos, Polyfold.SBLocalization.normW_add_le, Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le, Polyfold.SBLocalization.domSupp_multisectionAdd_subset, Polyfold.SBLocalization.isLocalRepOn_zeroMultisection, Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero, Polyfold.SBLocalization.pointwiseNorm_zeroMultisection, Polyfold.SBLocalization.domSupp_zeroMultisection, Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero]
#rt_check RoundTrip.V15_29.paracompact_to_Bplus [Polyfold.SBLocalization.theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_existence, Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion, Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact, Polyfold.SBLocalization.exists_scPlusGPFamily_nhds, Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.SBLocalization.hasPointwiseParamOnto, Polyfold.SBLocalization.hasParamOntoOpen, Polyfold.SBLocalization.exists_tameChart_centred, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem, Polyfold.SBLocalization.isParamOntoAt_iff_vec, Polyfold.SBLocalization.muLin_surjective, Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport, Polyfold.SBLocalization.IsParamOntoVec.of_mor, Polyfold.SBLocalization.transSec_eq_muLin, Polyfold.SBLocalization.paramSec_transSec_eqOn, Polyfold.SBLocalization.transSec_of_eq_tgt, Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn, Polyfold.SBLocalization.exists_linearRep_of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv, Polyfold.SBLocalization.mem_solutionSet_tgt, Polyfold.SBLocalization.src_mem_levelSet_one, Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds, Polyfold.SBLocalization.paramSec_eq_paramSlice, Polyfold.SBLocalization.isScPlusSection_paramSec, Polyfold.SBLocalization.sectionSupport_paramSec_subset, Polyfold.SBLocalization.paramSec_fiberZero, Polyfold.SBLocalization.natTerm_paramSec, Polyfold.SBLocalization.SeedData.atom_R, Polyfold.SBLocalization.SeedData.atom_V, Polyfold.SBLocalization.SeedData.isAtomic_Λ, Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ, Polyfold.SBLocalization.SeedData.isSection_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_zero, Polyfold.SBLocalization.SeedData.isLinearFamily, Polyfold.SBLocalization.SeedData.isStructurable_Λ, Polyfold.SBLocalization.SeedData.domSupp_Λ_subset, Polyfold.SBLocalization.SeedData.norm_le, Polyfold.SBLocalization.SeedData.isParamOntoAt, Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds, Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds, Polyfold.SBLocalization.theorem_15_3_7_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_of, Polyfold.SBLocalization.theorem_15_3_7_of_pointwise, Polyfold.SBLocalization.isParamOntoVec_epSEP_zero, Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero, Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise, Polyfold.SBLocalization.isSection_negRestrict, Polyfold.SBLocalization.isScPlusSection_negRestrict, Polyfold.SBLocalization.pbLin_restrictSection, Polyfold.SBLocalization.pbLin_injective, Polyfold.SBLocalization.paramSlice_branch_eq, Polyfold.SBLocalization.fiberLin_toIntr_subDeriv, Polyfold.SBLocalization.principal_eq_fiberLin, Polyfold.SBLocalization.principal_restrictTo_negRestrict, Polyfold.SBLocalization.isParamGP_restrictTo_of_onto, Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec, Polyfold.SBLocalization.isGeneralPositionGerm_branchParam, Polyfold.SBLocalization.exists_local_paramGP, Polyfold.SBLocalization.auxLe_of_pos, Polyfold.SBLocalization.exists_pos_auxLe_subset, Polyfold.SBLocalization.hasParametricGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp_local, Polyfold.SBLocalization.theorem_15_3_7_of_local, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local, Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto, Polyfold.SBLocalization.nonempty_gpFamily_biUnion, Polyfold.SBLocalization.exists_gpFamily_of_compact, Polyfold.SBLocalization.exists_norm_lt_of_ae, Polyfold.SBLocalization.sum_abs_lt_one, Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp, Polyfold.SBLocalization.theorem_15_3_7_of_hyp, Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero, Polyfold.SBLocalization.fiber_eq_epSEP_zero, Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero, Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp, Polyfold.SBLocalization.paramSec_apply, Polyfold.SBLocalization.isSection_paramSec, Polyfold.SBLocalization.paramFib, Polyfold.SBLocalization.paramSec_fin_zero, Polyfold.SBLocalization.isSection_append, Polyfold.SBLocalization.paramSec_append, Polyfold.SBLocalization.normW_paramSec_le, Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn, Polyfold.SBLocalization.pointwiseNorm_le_of_linear, Polyfold.SBLocalization.isLocalRepOn_famAdd, Polyfold.SBLocalization.IsLinearFamily.famAdd, Polyfold.SBLocalization.IsParamOntoAt.famAdd_left, Polyfold.SBLocalization.IsParamOntoAt.famAdd_right, Polyfold.SBLocalization.exists_of_multisectionAdd_pos, Polyfold.SBLocalization.normW_add_le, Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le, Polyfold.SBLocalization.domSupp_multisectionAdd_subset, Polyfold.SBLocalization.isLocalRepOn_zeroMultisection, Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero, Polyfold.SBLocalization.pointwiseNorm_zeroMultisection, Polyfold.SBLocalization.domSupp_zeroMultisection, Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero]
/- `A_to_Bplus` itself cannot pass `#rt_check`/`#rt_check_soft`: the statement `A` mentions the
banned theorems `isSection_paramSec`, `isSection_negRestrict`, `isScPlusSection_negRestrict` as
proof arguments inside the types of other conjuncts, so every term mentioning `A` reaches them.
`A_to_Bplus` is the projection of `A` to its conjunct `theorem_15_3_7_of_paracompact` followed by
`paracompact_to_Bplus`, which passes. -/
#rt_overlap RoundTrip.V15_29.B_to_main [Polyfold.SBLocalization.theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_existence, Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion, Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact, Polyfold.SBLocalization.exists_scPlusGPFamily_nhds, Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.SBLocalization.hasPointwiseParamOnto, Polyfold.SBLocalization.hasParamOntoOpen, Polyfold.SBLocalization.exists_tameChart_centred, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem, Polyfold.SBLocalization.isParamOntoAt_iff_vec, Polyfold.SBLocalization.muLin_surjective, Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport, Polyfold.SBLocalization.IsParamOntoVec.of_mor, Polyfold.SBLocalization.transSec_eq_muLin, Polyfold.SBLocalization.paramSec_transSec_eqOn, Polyfold.SBLocalization.transSec_of_eq_tgt, Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn, Polyfold.SBLocalization.exists_linearRep_of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv, Polyfold.SBLocalization.mem_solutionSet_tgt, Polyfold.SBLocalization.src_mem_levelSet_one, Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds, Polyfold.SBLocalization.paramSec_eq_paramSlice, Polyfold.SBLocalization.isScPlusSection_paramSec, Polyfold.SBLocalization.sectionSupport_paramSec_subset, Polyfold.SBLocalization.paramSec_fiberZero, Polyfold.SBLocalization.natTerm_paramSec, Polyfold.SBLocalization.SeedData.atom_R, Polyfold.SBLocalization.SeedData.atom_V, Polyfold.SBLocalization.SeedData.isAtomic_Λ, Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ, Polyfold.SBLocalization.SeedData.isSection_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_zero, Polyfold.SBLocalization.SeedData.isLinearFamily, Polyfold.SBLocalization.SeedData.isStructurable_Λ, Polyfold.SBLocalization.SeedData.domSupp_Λ_subset, Polyfold.SBLocalization.SeedData.norm_le, Polyfold.SBLocalization.SeedData.isParamOntoAt, Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds, Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds, Polyfold.SBLocalization.theorem_15_3_7_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_of, Polyfold.SBLocalization.theorem_15_3_7_of_pointwise, Polyfold.SBLocalization.isParamOntoVec_epSEP_zero, Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero, Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise, Polyfold.SBLocalization.isSection_negRestrict, Polyfold.SBLocalization.isScPlusSection_negRestrict, Polyfold.SBLocalization.pbLin_restrictSection, Polyfold.SBLocalization.pbLin_injective, Polyfold.SBLocalization.paramSlice_branch_eq, Polyfold.SBLocalization.fiberLin_toIntr_subDeriv, Polyfold.SBLocalization.principal_eq_fiberLin, Polyfold.SBLocalization.principal_restrictTo_negRestrict, Polyfold.SBLocalization.isParamGP_restrictTo_of_onto, Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec, Polyfold.SBLocalization.isGeneralPositionGerm_branchParam, Polyfold.SBLocalization.exists_local_paramGP, Polyfold.SBLocalization.auxLe_of_pos, Polyfold.SBLocalization.exists_pos_auxLe_subset, Polyfold.SBLocalization.hasParametricGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp_local, Polyfold.SBLocalization.theorem_15_3_7_of_local, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local, Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto, Polyfold.SBLocalization.nonempty_gpFamily_biUnion, Polyfold.SBLocalization.exists_gpFamily_of_compact, Polyfold.SBLocalization.exists_norm_lt_of_ae, Polyfold.SBLocalization.sum_abs_lt_one, Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp, Polyfold.SBLocalization.theorem_15_3_7_of_hyp, Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero, Polyfold.SBLocalization.fiber_eq_epSEP_zero, Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero, Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp, Polyfold.SBLocalization.paramSec_apply, Polyfold.SBLocalization.isSection_paramSec, Polyfold.SBLocalization.paramFib, Polyfold.SBLocalization.paramSec_fin_zero, Polyfold.SBLocalization.isSection_append, Polyfold.SBLocalization.paramSec_append, Polyfold.SBLocalization.normW_paramSec_le, Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn, Polyfold.SBLocalization.pointwiseNorm_le_of_linear, Polyfold.SBLocalization.isLocalRepOn_famAdd, Polyfold.SBLocalization.IsLinearFamily.famAdd, Polyfold.SBLocalization.IsParamOntoAt.famAdd_left, Polyfold.SBLocalization.IsParamOntoAt.famAdd_right, Polyfold.SBLocalization.exists_of_multisectionAdd_pos, Polyfold.SBLocalization.normW_add_le, Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le, Polyfold.SBLocalization.domSupp_multisectionAdd_subset, Polyfold.SBLocalization.isLocalRepOn_zeroMultisection, Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero, Polyfold.SBLocalization.pointwiseNorm_zeroMultisection, Polyfold.SBLocalization.domSupp_zeroMultisection, Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero]
#rt_overlap RoundTrip.V15_29.B_to_forms [Polyfold.SBLocalization.theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_existence, Polyfold.SBLocalization.nonempty_scPlusGPFamily_biUnion, Polyfold.SBLocalization.exists_scPlusGPFamily_of_compact, Polyfold.SBLocalization.exists_scPlusGPFamily_nhds, Polyfold.SBLocalization.theorem_15_3_7_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.SBLocalization.hasPointwiseParamOnto, Polyfold.SBLocalization.hasParamOntoOpen, Polyfold.SBLocalization.exists_tameChart_centred, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_goodSystem, Polyfold.SBLocalization.isParamOntoAt_iff_vec, Polyfold.SBLocalization.muLin_surjective, Polyfold.SBLocalization.tangentMorCLE_mem_reducedTangentFiber_transport, Polyfold.SBLocalization.IsParamOntoVec.of_mor, Polyfold.SBLocalization.transSec_eq_muLin, Polyfold.SBLocalization.paramSec_transSec_eqOn, Polyfold.SBLocalization.transSec_of_eq_tgt, Polyfold.SBLocalization.IsLocalRepOn.congr_eqOn, Polyfold.SBLocalization.exists_linearRep_of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor, Polyfold.SBLocalization.IsParamOntoAt.of_mor_inv, Polyfold.SBLocalization.mem_solutionSet_tgt, Polyfold.SBLocalization.src_mem_levelSet_one, Polyfold.SBLocalization.hasLocalGPFamilies_of_nhds, Polyfold.SBLocalization.paramSec_eq_paramSlice, Polyfold.SBLocalization.isScPlusSection_paramSec, Polyfold.SBLocalization.sectionSupport_paramSec_subset, Polyfold.SBLocalization.paramSec_fiberZero, Polyfold.SBLocalization.natTerm_paramSec, Polyfold.SBLocalization.SeedData.atom_R, Polyfold.SBLocalization.SeedData.atom_V, Polyfold.SBLocalization.SeedData.isAtomic_Λ, Polyfold.SBLocalization.SeedData.isScPlusMultisection_Λ, Polyfold.SBLocalization.SeedData.isSection_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_branch, Polyfold.SBLocalization.SeedData.isLocalRepOn_zero, Polyfold.SBLocalization.SeedData.isLinearFamily, Polyfold.SBLocalization.SeedData.isStructurable_Λ, Polyfold.SBLocalization.SeedData.domSupp_Λ_subset, Polyfold.SBLocalization.SeedData.norm_le, Polyfold.SBLocalization.SeedData.isParamOntoAt, Polyfold.SBLocalization.hasLocalGPFamilies_of_seeds, Polyfold.SBLocalization.theorem_15_3_7_hyp_seeds, Polyfold.SBLocalization.theorem_15_3_7_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_seeds, Polyfold.SBLocalization.hasLocalParamSeeds_of, Polyfold.SBLocalization.theorem_15_3_7_of_pointwise, Polyfold.SBLocalization.isParamOntoVec_epSEP_zero, Polyfold.SBLocalization.hasPointwiseParamOnto_epSEP_zero, Polyfold.SBLocalization.hasParamOntoOpen_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_pointwise, Polyfold.SBLocalization.isSection_negRestrict, Polyfold.SBLocalization.isScPlusSection_negRestrict, Polyfold.SBLocalization.pbLin_restrictSection, Polyfold.SBLocalization.pbLin_injective, Polyfold.SBLocalization.paramSlice_branch_eq, Polyfold.SBLocalization.fiberLin_toIntr_subDeriv, Polyfold.SBLocalization.principal_eq_fiberLin, Polyfold.SBLocalization.principal_restrictTo_negRestrict, Polyfold.SBLocalization.isParamGP_restrictTo_of_onto, Polyfold.SBLocalization.isScPlusSectionOn_of_paramSec, Polyfold.SBLocalization.isGeneralPositionGerm_branchParam, Polyfold.SBLocalization.exists_local_paramGP, Polyfold.SBLocalization.auxLe_of_pos, Polyfold.SBLocalization.exists_pos_auxLe_subset, Polyfold.SBLocalization.hasParametricGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp_local, Polyfold.SBLocalization.theorem_15_3_7_of_local, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_local, Polyfold.SBLocalization.theorem_15_3_7_of_paramOnto, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_paramOnto, Polyfold.SBLocalization.nonempty_gpFamily_biUnion, Polyfold.SBLocalization.exists_gpFamily_of_compact, Polyfold.SBLocalization.exists_norm_lt_of_ae, Polyfold.SBLocalization.sum_abs_lt_one, Polyfold.SBLocalization.isTransversal_of_isInGeneralPosition, Polyfold.SBLocalization.theorem_15_3_7_hyp, Polyfold.SBLocalization.theorem_15_3_7_of_hyp, Polyfold.SBLocalization.nonempty_goodSystem_epSEP_zero, Polyfold.SBLocalization.fiber_eq_epSEP_zero, Polyfold.SBLocalization.hasParametricGeneralPosition_epSEP_zero, Polyfold.SBLocalization.hasLocalGPFamilies_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero_of_hyp, Polyfold.SBLocalization.paramSec_apply, Polyfold.SBLocalization.isSection_paramSec, Polyfold.SBLocalization.paramFib, Polyfold.SBLocalization.paramSec_fin_zero, Polyfold.SBLocalization.isSection_append, Polyfold.SBLocalization.paramSec_append, Polyfold.SBLocalization.normW_paramSec_le, Polyfold.SBLocalization.pointwiseNorm_le_of_isLocalRepOn, Polyfold.SBLocalization.pointwiseNorm_le_of_linear, Polyfold.SBLocalization.isLocalRepOn_famAdd, Polyfold.SBLocalization.IsLinearFamily.famAdd, Polyfold.SBLocalization.IsParamOntoAt.famAdd_left, Polyfold.SBLocalization.IsParamOntoAt.famAdd_right, Polyfold.SBLocalization.exists_of_multisectionAdd_pos, Polyfold.SBLocalization.normW_add_le, Polyfold.SBLocalization.pointwiseNorm_multisectionAdd_le, Polyfold.SBLocalization.domSupp_multisectionAdd_subset, Polyfold.SBLocalization.isLocalRepOn_zeroMultisection, Polyfold.SBLocalization.isStructurable_zeroMultisection_of_goodSystem, Polyfold.SBLocalization.theorem_15_3_7_statement_epSEP_zero, Polyfold.SBLocalization.theorem_15_3_7_of_isInGeneralPosition_zero, Polyfold.SBLocalization.pointwiseNorm_zeroMultisection, Polyfold.SBLocalization.domSupp_zeroMultisection, Polyfold.SBLocalization.isInGeneralPosition_epSEP_zero]

end RoundTrip.V15_29
