import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_36

set_option maxSynthPendingDepth 3

/-! Round trip for V15_36 (2021 Theorem 15.4.3, pp. 702–703: compactness, branching and
Stokes for `Θ = Λ ∘ f` with the canonical orientation; effective version under (LUC)).

`A` is the conjunction of the types of the item's 26 theorems at universe `0` (`B` lives on
`SEP.{0}`).  No direction is proved; the diagnosis:

* `A_to_B`: every conjunct that yields `Θ` branched/compact or a canonical orientation assumes
  tame germ data `A.B.IsScFredholmSectionTame f` (`hft`), and those giving the canonical
  orientation also sc-smooth bump functions `A.X.PObj.AdmitsBumpFunctions` (`hbump`, Theorem
  15.4.1's input); `B` grants neither.  Beyond that, `B` claims `Θ` tame (`IsTameBranched`, no
  conjunct states it), Stokes in index `1` with the canonical orientation (the conjunct
  `theorem_15_4_3_dim1_hyp(_all)` takes the orientation as input), and the effective Stokes
  formula in index `1`.
* `B_to_A`, main conjunct `theorem_15_4_3_all` (Theorem 15.4.3 with no partitions of unity): its
  index hypothesis is `IsIndexAt f x (m + 1)` only at the points of `supp(Λ ∘ f)`, while `B`
  needs the index at every smooth object; `B` cannot be applied.  (`|S_f|` compact, which `B`
  also needs, follows from `(N, U)` controlling compactness, see V15_37's
  `hasCompactSolutionSetEp_of_controlsCompactness`; `hbump`, `hft` are extra hypotheses of the
  conjunct and harmless.)  Even with a global index, the conjunct speaks of the specific
  `canonicalOrientation` while `B` gives some `P.T` with `IsCanonicalFor`; transferring the
  integrals needs the project's `IsCanonicalPerturbation.integral_eq` (an item theorem), i.e.
  re-proving it.  The other conjuncts (good position from (2)+(3), local branching, the
  `_hyp`/`_loc`/`_of_definition_12_5_4` variants, the half-space example) are proof steps or
  variants not derivable from `B`.
-/

namespace RoundTrip.V15_36
open Polyfold

/-- The project's statement: the conjunction of the item's theorems at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isGoodPositionAt_of_transversal.{0}) ∧
  (type_of% @Polyfold.SBLocalization.localBranching_of_isGoodPositionAt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_isBranched_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_dim1_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_of_definition_12_5_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_of_index_on_paths.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsCanonicalPerturbation.integralEff_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_canonical_eq.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.integral_eq_of_isCanonicalPerturbation_halfSEP) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_hyp_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_hyp_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_dim1_hyp_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_of_definition_12_5_4_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_of_definition_12_5_4_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_of_index_on_paths_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_loc_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_3_eff_loc_all.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_4_3.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff.{0},
    @Polyfold.SBLocalization.isGoodPositionAt_of_transversal.{0},
    @Polyfold.SBLocalization.localBranching_of_isGoodPositionAt.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_isBranched_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_dim1_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_of_definition_12_5_4.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_of_index_on_paths.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_loc.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_loc.{0},
    @Polyfold.SBLocalization.IsCanonicalPerturbation.integral_eq.{0},
    @Polyfold.SBLocalization.IsCanonicalPerturbation.integralEff_eq.{0},
    @Polyfold.SBLocalization.integral_canonical_eq.{0},
    @Polyfold.HalfSpaceBundle.integral_eq_of_isCanonicalPerturbation_halfSEP,
    @Polyfold.SBLocalization.theorem_15_4_3_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_hyp_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_hyp_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_dim1_hyp_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_of_definition_12_5_4_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_of_definition_12_5_4_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_of_index_on_paths_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_loc_all.{0},
    @Polyfold.SBLocalization.theorem_15_4_3_eff_loc_all.{0}⟩

-- No direction between `A` and `B` is proved (see the module docstring).

end RoundTrip.V15_36
