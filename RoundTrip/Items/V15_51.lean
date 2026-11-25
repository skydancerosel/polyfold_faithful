import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_51

set_option maxSynthPendingDepth 3

/-! Round trip for V15_51 (2021 Theorem 15.4.1, p. 702: the canonical oriented lift of `T_Θ`,
locally `∑ σᵢ · ((f − sᵢ)'(y), o_{i,y})`, independent of the local sc⁺-section structure).

`A` is the conjunction of the types of the item's 50 theorems (universe `0`: `.{0}` or
`.{0,0}`); the 10 listed definitions are vocabulary.  No direction is proved; the diagnosis:

* `A_to_B`: the main conjunct `theorem_15_4_1` gives `IsCanonicalFor Λ o n canonicalOrientation`
  under `hbump : A.X.PObj.AdmitsBumpFunctions`, `hft : A.B.IsScFredholmSectionTame f` and a
  **constant index `n` on `supp(Λ ∘ f)`**; `B` grants none of the three (it has no index
  hypothesis at all).  The local existence `(a)` is `exists_kernelBranching`, which also needs
  `hft`.  `(b)` (`CanonIndependent`) is proved in the project inside `theorem_15_4_1_of_*` but
  again under `hft`.
* `B_to_A`, main conjunct `theorem_15_4_1`: the conjunct assumes good position on the whole
  support (which contains `B`'s `IsTransversal` and good position at boundary points) but not
  that `Θ` is a branched ep⁺-subgroupoid, which `B` presupposes (derivable from good position by
  `localBranching_of_isGoodPositionAt`-type arguments, i.e. re-proving).  Then `B` gives some
  orientation `T` agreeing with the kernel sums at smooth points of the support, while the
  conjunct asks for `IsCanonicalFor` of `canonicalOrientation`: the frames' continuity
  (`KernelBranching.framesContinuous`) and the sheet dimensions `= n`
  (`KernelBranching.dim_eq_of_isIndexAt`) are item theorems that `B` does not provide; re-proving
  them is the substance of Theorem 15.4.1.  The remaining conjuncts (transfer lemmas, pull-back
  of canonical orientations, `IsPosOr` facts, half-space and orbifold-square examples) are
  proof steps and examples.
-/

namespace RoundTrip.V15_51
open Polyfold

/-- The project's statement: the conjunction of the item's theorems at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_branch_tangent_eq_ker.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_kernelBranching.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.dim_eq_of_isIndexAt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_kernelBranching_dim.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.canonSum_mem.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.grForget_canonSum.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_local.{0}) ∧
  (type_of% @Polyfold.SBLocalization.orKer_orTransfer.{0}) ∧
  (type_of% @Polyfold.SBLocalization.kerFrames_orTransfer.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.frames_eq_chart.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonIndependent.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_natural_continuous.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonNatural.{0}) ∧
  (type_of% @Polyfold.SBLocalization.linOrTangent_conj.{0}) ∧
  (type_of% @Polyfold.SBLocalization.subOp_eq_linZero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mem_kerFrames_iff_tangentOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.mem_frames_iff_tangentOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonContinuous.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.framesContinuous.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientation.{0}) ∧
  (type_of% @Polyfold.isLineOrientation_tangentOr_of_family.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.subOp_mem_linSet.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mapDomain_toF_linW.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonLift_spec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_lift.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_indep.{0}) ∧
  (type_of% @Polyfold.SBLocalization.canonLift_linW_eq_sum.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_4_1_hypotheses_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_4_1_halfSEP) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_definition_12_5_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.definition_12_5_4_iff_isOrInvariant_isSectionOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_of_index_on_paths.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isIndexAt_of_scPath.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.definition_12_5_4_orOfLoc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSectionOrientation_orOfLoc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.canonSum_pullOr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.eq_pullSection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.pullSection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalPerturbation.isCanonicalFor_pullSection.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_4_1_of_definition_12_5_4_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_4_1_of_index_on_paths_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_4_1_loc_halfSEP) ∧
  (type_of% @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection) ∧
  (type_of% @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc) ∧
  (type_of% @Polyfold.SBLocalization.KernelBranching.frameSign_orTangent_eq_one_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalFor.signedWeight_eq.{0}) ∧
  (type_of% @Polyfold.isPosOr_iff_of_path.{0,0}) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.positiveZeros_sqOrientationRepPos)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_4_1.{0},
    @Polyfold.SBLocalization.exists_branch_tangent_eq_ker.{0},
    @Polyfold.SBLocalization.exists_kernelBranching.{0},
    @Polyfold.SBLocalization.KernelBranching.dim_eq_of_isIndexAt.{0},
    @Polyfold.SBLocalization.exists_kernelBranching_dim.{0},
    @Polyfold.SBLocalization.KernelBranching.canonSum_mem.{0},
    @Polyfold.SBLocalization.KernelBranching.grForget_canonSum.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_of_local.{0},
    @Polyfold.SBLocalization.orKer_orTransfer.{0},
    @Polyfold.SBLocalization.kerFrames_orTransfer.{0},
    @Polyfold.SBLocalization.KernelBranching.frames_eq_chart.{0},
    @Polyfold.SBLocalization.canonIndependent.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_of_natural_continuous.{0},
    @Polyfold.SBLocalization.canonNatural.{0},
    @Polyfold.SBLocalization.linOrTangent_conj.{0},
    @Polyfold.SBLocalization.subOp_eq_linZero.{0},
    @Polyfold.SBLocalization.mem_kerFrames_iff_tangentOr.{0},
    @Polyfold.SBLocalization.KernelBranching.mem_frames_iff_tangentOr.{0},
    @Polyfold.SBLocalization.canonContinuous.{0},
    @Polyfold.SBLocalization.KernelBranching.framesContinuous.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_of_isSectionOrientation.{0},
    @Polyfold.isLineOrientation_tangentOr_of_family.{0,0},
    @Polyfold.SBLocalization.subOp_mem_linSet.{0},
    @Polyfold.SBLocalization.mapDomain_toF_linW.{0},
    @Polyfold.SBLocalization.canonLift_spec.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_lift.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_indep.{0},
    @Polyfold.SBLocalization.canonLift_linW_eq_sum.{0},
    @Polyfold.HalfSpaceBundle.theorem_15_4_1_hypotheses_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_15_4_1_halfSEP,
    @Polyfold.SBLocalization.theorem_15_4_1_of_definition_12_5_4.{0},
    @Polyfold.SBLocalization.definition_12_5_4_iff_isOrInvariant_isSectionOrientation.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_of_index_on_paths.{0},
    @Polyfold.SBLocalization.isIndexAt_of_scPath.{0},
    @Polyfold.SBLocalization.theorem_15_4_1_loc.{0},
    @Polyfold.SBLocalization.definition_12_5_4_orOfLoc.{0},
    @Polyfold.SBLocalization.isSectionOrientation_orOfLoc.{0},
    @Polyfold.SBLocalization.KernelBranching.canonSum_pullOr.{0},
    @Polyfold.SBLocalization.IsCanonicalFor.eq_pullSection.{0},
    @Polyfold.SBLocalization.IsCanonicalFor.pullSection.{0},
    @Polyfold.SBLocalization.IsCanonicalPerturbation.isCanonicalFor_pullSection.{0},
    @Polyfold.HalfSpaceBundle.theorem_15_4_1_of_definition_12_5_4_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_15_4_1_of_index_on_paths_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_15_4_1_loc_halfSEP,
    @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_negSection,
    @Polyfold.CanonicalOrientationPullbackExamples.isCanonicalFor_pullSection_halfDisc,
    @Polyfold.SBLocalization.KernelBranching.frameSign_orTangent_eq_one_iff.{0},
    @Polyfold.SBLocalization.IsCanonicalFor.signedWeight_eq.{0},
    @Polyfold.isPosOr_iff_of_path.{0,0},
    @Polyfold.Examples.OrbifoldSquare.positiveZeros_sqOrientationRepPos⟩

-- No direction between `A` and `B` is proved (see the module docstring).

end RoundTrip.V15_51
