import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_8

set_option maxSynthPendingDepth 3

/-! Round trip for V14_8 (2021 Theorem 14.1.9, p. 646, the ∂-extension theorem; 2017:
Theorem 14.2).

The item lists 59 theorems (and vocabulary definitions); `A` is the conjunction of their types at
universe `0` (`StrongBundle.exists_isTameChart` at `.{0,0}`; the half-space example has no
universe parameter).  `B` is on `SEP.{0}`.

**Neither direction is proved.**  What is proved:

* `B_to_main`: `B` implies the main conjunct `theorem_14_1_9`.  The two statements differ in the
  partition-of-unity hypothesis: `theorem_14_1_9_statement` assumes that the object M-polyfold
  admits sc-smooth partitions of unity (`A.X.PObj.AdmitsScPartitionsOfUnity`, every open cover),
  `B` assumes the ep-groupoid notion of Definition 7.5.5 (`A.X.HasScPartitionsOfUnity`, saturated
  covers, invariant partitions).  With `|X|` paracompact the first gives the second
  (`theorem_7_5_7`), so `B`'s hypotheses follow from `A`'s; the invariance of `f` is stated
  in the opposite order (`f(t φ) = f(s φ)` against `f(s φ) = f(t φ)`).
* `A_to_B_of_pu`: `A` gives `B` when the M-polyfold hypothesis is added.  Without it, `A ⇒ B`
  would need `HasScPartitionsOfUnity ⇒ AdmitsScPartitionsOfUnity`, which is not available: an
  invariant partition of unity cannot be localized below saturations, while the project's proof
  uses non-invariant cut-offs on arbitrary (non-saturated) sets (`exists_scSmooth_cutoff`,
  `AssemblyInput.exists_cutoff`).
* The other 58 conjuncts of `A` are the intermediate statements of the proof of §§14.3–14.5
  (`AssemblyInput.*`, `sizeControl`, `AssemblyHyp`), helper lemmas on `pointwiseNorm` and
  saturation, and the half-space example `halfSEP`; they do not follow from `B`, and re-proving
  them would copy the whole construction of Chapter 14.
-/

namespace RoundTrip.V14_8
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0}) ∧
  (type_of% @Polyfold.SBLocalization.assemblyHyp_holds.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_extension_statement_holds.{0}) ∧
  (type_of% @Polyfold.SEP.exists_isTameChart.{0}) ∧
  (type_of% @Polyfold.StrongBundle.exists_isTameChart.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.IsBoundaryStructurable.chargesBoundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_charged.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sizeControl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_iff.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isTame_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.hasParacompactOrbitSpace_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.admitsScPartitionsOfUnity_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.hB_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.zero_mem_boundary_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.mem_boundary_halfSEP_iff) ∧
  (type_of% @Polyfold.HalfSpaceBundle.nontrivial_fibre_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_14_1_9_charged_hypotheses_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_14_1_9_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isScPlusSectionOn_constSec) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isBoundaryStructurable_constMulti) ∧
  (type_of% @Polyfold.HalfSpaceBundle.chargesBoundary_constMulti) ∧
  (type_of% @Polyfold.HalfSpaceBundle.boundaryDomSupp_constMulti_nonempty) ∧
  (type_of% @Polyfold.HalfSpaceBundle.pointwiseNorm_constMulti) ∧
  (type_of% @Polyfold.HalfSpaceBundle.continuous_normW_constSec) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_14_1_9_constSec) ∧
  (type_of% @Polyfold.SBLocalization.boundaryDomSupp_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_statement_hyp_witness.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOpen_pointwiseNorm_lt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_tgt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_src_le_tgt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_nonneg.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn_normW.{0}) ∧
  (type_of% @Polyfold.SBLocalization.normW_le_of_multisectionSmul_pos.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_smulFun_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.multisectionSmulFun_of_eq_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.domSupp_zeroMultisection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSaturated_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSaturated_closure.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isSaturated_union.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_extension_statement_of_assembly.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9_of_assembly.{0}) ∧
  (type_of% @Polyfold.SBLocalization.assemblyHyp_of_boundary_eq_empty.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fibAct_eq_fiberZero_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fibAct_comp_inv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CriterionData.hasLocalSectionStructure.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.mult_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.isWFunctor_mult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.crit_nonempty.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.isStructurable_mult.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.mult_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.domSupp_mult_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.isSaturated_boundaryDomSupp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.exists_cutoff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.extension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.ssec_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.s0_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.mult_of_not_mem_C.{0}) ∧
  (type_of% @Polyfold.SBLocalization.AssemblyInput.isOpen_critV.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_14_1_9.{0},
    @Polyfold.SBLocalization.assemblyHyp_holds.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_extension_statement_holds.{0},
    @Polyfold.SEP.exists_isTameChart.{0},
    @Polyfold.StrongBundle.exists_isTameChart.{0,0},
    @Polyfold.SBLocalization.IsBoundaryStructurable.chargesBoundary.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_charged.{0},
    @Polyfold.SBLocalization.sizeControl.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_iff.{0},
    @Polyfold.HalfSpaceBundle.isTame_halfSEP,
    @Polyfold.HalfSpaceBundle.hasParacompactOrbitSpace_halfSEP,
    @Polyfold.HalfSpaceBundle.admitsScPartitionsOfUnity_halfSEP,
    @Polyfold.HalfSpaceBundle.hB_halfSEP,
    @Polyfold.HalfSpaceBundle.zero_mem_boundary_halfSEP,
    @Polyfold.HalfSpaceBundle.mem_boundary_halfSEP_iff,
    @Polyfold.HalfSpaceBundle.nontrivial_fibre_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_14_1_9_charged_hypotheses_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_14_1_9_halfSEP,
    @Polyfold.HalfSpaceBundle.isScPlusSectionOn_constSec,
    @Polyfold.HalfSpaceBundle.isBoundaryStructurable_constMulti,
    @Polyfold.HalfSpaceBundle.chargesBoundary_constMulti,
    @Polyfold.HalfSpaceBundle.boundaryDomSupp_constMulti_nonempty,
    @Polyfold.HalfSpaceBundle.pointwiseNorm_constMulti,
    @Polyfold.HalfSpaceBundle.continuous_normW_constSec,
    @Polyfold.HalfSpaceBundle.theorem_14_1_9_constSec,
    @Polyfold.SBLocalization.boundaryDomSupp_zero.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_statement_hyp_witness.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_hyp.{0},
    @Polyfold.SBLocalization.isOpen_pointwiseNorm_lt.{0},
    @Polyfold.SBLocalization.pointwiseNorm_tgt.{0},
    @Polyfold.SBLocalization.pointwiseNorm_src_le_tgt.{0},
    @Polyfold.SBLocalization.pointwiseNorm_nonneg.{0},
    @Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn_normW.{0},
    @Polyfold.SBLocalization.normW_le_of_multisectionSmul_pos.{0},
    @Polyfold.SBLocalization.pointwiseNorm_smulFun_le.{0},
    @Polyfold.SBLocalization.multisectionSmulFun_of_eq_one.{0},
    @Polyfold.SBLocalization.domSupp_zeroMultisection.{0},
    @Polyfold.SBLocalization.isSaturated_boundary.{0},
    @Polyfold.SBLocalization.isSaturated_closure.{0},
    @Polyfold.SBLocalization.isSaturated_union.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_extension_statement_of_assembly.{0},
    @Polyfold.SBLocalization.theorem_14_1_9_of_assembly.{0},
    @Polyfold.SBLocalization.assemblyHyp_of_boundary_eq_empty.{0},
    @Polyfold.SBLocalization.fibAct_eq_fiberZero_iff.{0},
    @Polyfold.SBLocalization.fibAct_comp_inv.{0},
    @Polyfold.SBLocalization.CriterionData.hasLocalSectionStructure.{0},
    @Polyfold.SBLocalization.AssemblyInput.mult_eq.{0},
    @Polyfold.SBLocalization.AssemblyInput.isWFunctor_mult.{0},
    @Polyfold.SBLocalization.AssemblyInput.crit_nonempty.{0},
    @Polyfold.SBLocalization.AssemblyInput.isStructurable_mult.{0},
    @Polyfold.SBLocalization.AssemblyInput.mult_boundary.{0},
    @Polyfold.SBLocalization.AssemblyInput.domSupp_mult_subset.{0},
    @Polyfold.SBLocalization.AssemblyInput.isSaturated_boundaryDomSupp.{0},
    @Polyfold.SBLocalization.AssemblyInput.exists_cutoff.{0},
    @Polyfold.SBLocalization.AssemblyInput.extension.{0},
    @Polyfold.SBLocalization.AssemblyInput.ssec_boundary.{0},
    @Polyfold.SBLocalization.AssemblyInput.s0_eq_zero.{0},
    @Polyfold.SBLocalization.AssemblyInput.mult_of_not_mem_C.{0},
    @Polyfold.SBLocalization.AssemblyInput.isOpen_critV.{0}⟩

/-- **`B` gives the main conjunct** `theorem_14_1_9` (M-polyfold partitions of unity and
paracompact `|X|` give the ep-groupoid ones, `theorem_7_5_7`). -/
theorem B_to_main (hB : B) : type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0} := by
  intro A hX hpara hpu Λ hΛ N hN U hUo hUs hsub f hf hf0 hfinv hts hlt
  exact hB A hX hpara (A.X.theorem_7_5_7 hpara hpu) Λ hΛ N hN U hUo hUs hsub f hf hf0
    (fun φ => (hfinv φ).symm) hts hlt

/-- `B` with the M-polyfold partition-of-unity hypothesis added. -/
def Bpu : Prop :=
  ∀ A : SEP.{0}, A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.HasScPartitionsOfUnity →
  A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
  ∀ Ut : Set A.Obj, IsOpen Ut → A.X.IsSaturated Ut → boundaryDomSupp Λ ⊆ Ut →
  ∀ f : A.Obj → ℝ, Continuous f → (∀ x, 0 ≤ f x) →
    (∀ φ : A.Mor, f (A.X.src φ) = f (A.X.tgt φ)) → tsupport f ⊆ Ut →
    (∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < f x) →
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧
      (∀ x : A.Obj, pointwiseNorm N Λ' x ≤ f x) ∧
      domSupp Λ' ⊆ Ut ∧
      ∀ w : A.W, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w

/-- **`A`'s main conjunct gives `B` with the M-polyfold partition-of-unity hypothesis added.**
(Stated with the conjunct `theorem_14_1_9` as hypothesis rather than all of `A`: `A`'s statement
mentions `AssemblyInput.crit`, whose field `isOpen_V := D.isOpen_critV` is the banned theorem
itself, not an abstracted proof field, so every term mentioning `A` fails both checks.) -/
theorem A_to_B_of_pu (hA : type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0}) : Bpu := by
  intro A hX hpara _ hpu Λ hΛ N hN U hUo hUs hsub f hf hf0 hfinv hts hlt
  exact hA hX hpara hpu Λ hΛ N hN U hUo hUs hsub f hf hf0 (fun φ => (hfinv φ).symm) hts hlt

example (hA : A) : Bpu := A_to_B_of_pu hA.1

#rt_check RoundTrip.V14_8.B_to_main [Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.SBLocalization.assemblyHyp_holds,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_holds,
  Polyfold.SEP.exists_isTameChart,
  Polyfold.StrongBundle.exists_isTameChart,
  Polyfold.SBLocalization.IsBoundaryStructurable.chargesBoundary,
  Polyfold.SBLocalization.theorem_14_1_9_charged,
  Polyfold.SBLocalization.sizeControl,
  Polyfold.SBLocalization.theorem_14_1_9_iff,
  Polyfold.HalfSpaceBundle.isTame_halfSEP,
  Polyfold.HalfSpaceBundle.hasParacompactOrbitSpace_halfSEP,
  Polyfold.HalfSpaceBundle.admitsScPartitionsOfUnity_halfSEP,
  Polyfold.HalfSpaceBundle.hB_halfSEP,
  Polyfold.HalfSpaceBundle.zero_mem_boundary_halfSEP,
  Polyfold.HalfSpaceBundle.mem_boundary_halfSEP_iff,
  Polyfold.HalfSpaceBundle.nontrivial_fibre_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_charged_hypotheses_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_halfSEP,
  Polyfold.HalfSpaceBundle.isScPlusSectionOn_constSec,
  Polyfold.HalfSpaceBundle.isBoundaryStructurable_constMulti,
  Polyfold.HalfSpaceBundle.chargesBoundary_constMulti,
  Polyfold.HalfSpaceBundle.boundaryDomSupp_constMulti_nonempty,
  Polyfold.HalfSpaceBundle.pointwiseNorm_constMulti,
  Polyfold.HalfSpaceBundle.continuous_normW_constSec,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_constSec,
  Polyfold.SBLocalization.boundaryDomSupp_zero,
  Polyfold.SBLocalization.theorem_14_1_9_statement_hyp_witness,
  Polyfold.SBLocalization.theorem_14_1_9_hyp,
  Polyfold.SBLocalization.isOpen_pointwiseNorm_lt,
  Polyfold.SBLocalization.pointwiseNorm_tgt,
  Polyfold.SBLocalization.pointwiseNorm_src_le_tgt,
  Polyfold.SBLocalization.pointwiseNorm_nonneg,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn_normW,
  Polyfold.SBLocalization.normW_le_of_multisectionSmul_pos,
  Polyfold.SBLocalization.pointwiseNorm_smulFun_le,
  Polyfold.SBLocalization.multisectionSmulFun_of_eq_one,
  Polyfold.SBLocalization.domSupp_zeroMultisection,
  Polyfold.SBLocalization.isSaturated_boundary,
  Polyfold.SBLocalization.isSaturated_closure,
  Polyfold.SBLocalization.isSaturated_union,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_of_assembly,
  Polyfold.SBLocalization.theorem_14_1_9_of_assembly,
  Polyfold.SBLocalization.assemblyHyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.fibAct_eq_fiberZero_iff,
  Polyfold.SBLocalization.fibAct_comp_inv,
  Polyfold.SBLocalization.CriterionData.hasLocalSectionStructure,
  Polyfold.SBLocalization.AssemblyInput.mult_eq,
  Polyfold.SBLocalization.AssemblyInput.isWFunctor_mult,
  Polyfold.SBLocalization.AssemblyInput.crit_nonempty,
  Polyfold.SBLocalization.AssemblyInput.isStructurable_mult,
  Polyfold.SBLocalization.AssemblyInput.mult_boundary,
  Polyfold.SBLocalization.AssemblyInput.domSupp_mult_subset,
  Polyfold.SBLocalization.AssemblyInput.isSaturated_boundaryDomSupp,
  Polyfold.SBLocalization.AssemblyInput.exists_cutoff,
  Polyfold.SBLocalization.AssemblyInput.extension,
  Polyfold.SBLocalization.AssemblyInput.ssec_boundary,
  Polyfold.SBLocalization.AssemblyInput.s0_eq_zero,
  Polyfold.SBLocalization.AssemblyInput.mult_of_not_mem_C,
  Polyfold.SBLocalization.AssemblyInput.isOpen_critV]
#rt_check RoundTrip.V14_8.A_to_B_of_pu [Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.SBLocalization.assemblyHyp_holds,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_holds,
  Polyfold.SEP.exists_isTameChart,
  Polyfold.StrongBundle.exists_isTameChart,
  Polyfold.SBLocalization.IsBoundaryStructurable.chargesBoundary,
  Polyfold.SBLocalization.theorem_14_1_9_charged,
  Polyfold.SBLocalization.sizeControl,
  Polyfold.SBLocalization.theorem_14_1_9_iff,
  Polyfold.HalfSpaceBundle.isTame_halfSEP,
  Polyfold.HalfSpaceBundle.hasParacompactOrbitSpace_halfSEP,
  Polyfold.HalfSpaceBundle.admitsScPartitionsOfUnity_halfSEP,
  Polyfold.HalfSpaceBundle.hB_halfSEP,
  Polyfold.HalfSpaceBundle.zero_mem_boundary_halfSEP,
  Polyfold.HalfSpaceBundle.mem_boundary_halfSEP_iff,
  Polyfold.HalfSpaceBundle.nontrivial_fibre_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_charged_hypotheses_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_halfSEP,
  Polyfold.HalfSpaceBundle.isScPlusSectionOn_constSec,
  Polyfold.HalfSpaceBundle.isBoundaryStructurable_constMulti,
  Polyfold.HalfSpaceBundle.chargesBoundary_constMulti,
  Polyfold.HalfSpaceBundle.boundaryDomSupp_constMulti_nonempty,
  Polyfold.HalfSpaceBundle.pointwiseNorm_constMulti,
  Polyfold.HalfSpaceBundle.continuous_normW_constSec,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_constSec,
  Polyfold.SBLocalization.boundaryDomSupp_zero,
  Polyfold.SBLocalization.theorem_14_1_9_statement_hyp_witness,
  Polyfold.SBLocalization.theorem_14_1_9_hyp,
  Polyfold.SBLocalization.isOpen_pointwiseNorm_lt,
  Polyfold.SBLocalization.pointwiseNorm_tgt,
  Polyfold.SBLocalization.pointwiseNorm_src_le_tgt,
  Polyfold.SBLocalization.pointwiseNorm_nonneg,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn_normW,
  Polyfold.SBLocalization.normW_le_of_multisectionSmul_pos,
  Polyfold.SBLocalization.pointwiseNorm_smulFun_le,
  Polyfold.SBLocalization.multisectionSmulFun_of_eq_one,
  Polyfold.SBLocalization.domSupp_zeroMultisection,
  Polyfold.SBLocalization.isSaturated_boundary,
  Polyfold.SBLocalization.isSaturated_closure,
  Polyfold.SBLocalization.isSaturated_union,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_of_assembly,
  Polyfold.SBLocalization.theorem_14_1_9_of_assembly,
  Polyfold.SBLocalization.assemblyHyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.fibAct_eq_fiberZero_iff,
  Polyfold.SBLocalization.fibAct_comp_inv,
  Polyfold.SBLocalization.CriterionData.hasLocalSectionStructure,
  Polyfold.SBLocalization.AssemblyInput.mult_eq,
  Polyfold.SBLocalization.AssemblyInput.isWFunctor_mult,
  Polyfold.SBLocalization.AssemblyInput.crit_nonempty,
  Polyfold.SBLocalization.AssemblyInput.isStructurable_mult,
  Polyfold.SBLocalization.AssemblyInput.mult_boundary,
  Polyfold.SBLocalization.AssemblyInput.domSupp_mult_subset,
  Polyfold.SBLocalization.AssemblyInput.isSaturated_boundaryDomSupp,
  Polyfold.SBLocalization.AssemblyInput.exists_cutoff,
  Polyfold.SBLocalization.AssemblyInput.extension,
  Polyfold.SBLocalization.AssemblyInput.ssec_boundary,
  Polyfold.SBLocalization.AssemblyInput.s0_eq_zero,
  Polyfold.SBLocalization.AssemblyInput.mult_of_not_mem_C,
  Polyfold.SBLocalization.AssemblyInput.isOpen_critV]
#rt_overlap RoundTrip.V14_8.B_to_main [Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.SBLocalization.assemblyHyp_holds,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_holds,
  Polyfold.SEP.exists_isTameChart,
  Polyfold.StrongBundle.exists_isTameChart,
  Polyfold.SBLocalization.IsBoundaryStructurable.chargesBoundary,
  Polyfold.SBLocalization.theorem_14_1_9_charged,
  Polyfold.SBLocalization.sizeControl,
  Polyfold.SBLocalization.theorem_14_1_9_iff,
  Polyfold.HalfSpaceBundle.isTame_halfSEP,
  Polyfold.HalfSpaceBundle.hasParacompactOrbitSpace_halfSEP,
  Polyfold.HalfSpaceBundle.admitsScPartitionsOfUnity_halfSEP,
  Polyfold.HalfSpaceBundle.hB_halfSEP,
  Polyfold.HalfSpaceBundle.zero_mem_boundary_halfSEP,
  Polyfold.HalfSpaceBundle.mem_boundary_halfSEP_iff,
  Polyfold.HalfSpaceBundle.nontrivial_fibre_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_charged_hypotheses_halfSEP,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_halfSEP,
  Polyfold.HalfSpaceBundle.isScPlusSectionOn_constSec,
  Polyfold.HalfSpaceBundle.isBoundaryStructurable_constMulti,
  Polyfold.HalfSpaceBundle.chargesBoundary_constMulti,
  Polyfold.HalfSpaceBundle.boundaryDomSupp_constMulti_nonempty,
  Polyfold.HalfSpaceBundle.pointwiseNorm_constMulti,
  Polyfold.HalfSpaceBundle.continuous_normW_constSec,
  Polyfold.HalfSpaceBundle.theorem_14_1_9_constSec,
  Polyfold.SBLocalization.boundaryDomSupp_zero,
  Polyfold.SBLocalization.theorem_14_1_9_statement_hyp_witness,
  Polyfold.SBLocalization.theorem_14_1_9_hyp,
  Polyfold.SBLocalization.isOpen_pointwiseNorm_lt,
  Polyfold.SBLocalization.pointwiseNorm_tgt,
  Polyfold.SBLocalization.pointwiseNorm_src_le_tgt,
  Polyfold.SBLocalization.pointwiseNorm_nonneg,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn_normW,
  Polyfold.SBLocalization.normW_le_of_multisectionSmul_pos,
  Polyfold.SBLocalization.pointwiseNorm_smulFun_le,
  Polyfold.SBLocalization.multisectionSmulFun_of_eq_one,
  Polyfold.SBLocalization.domSupp_zeroMultisection,
  Polyfold.SBLocalization.isSaturated_boundary,
  Polyfold.SBLocalization.isSaturated_closure,
  Polyfold.SBLocalization.isSaturated_union,
  Polyfold.SBLocalization.theorem_14_1_9_extension_statement_of_assembly,
  Polyfold.SBLocalization.theorem_14_1_9_of_assembly,
  Polyfold.SBLocalization.assemblyHyp_of_boundary_eq_empty,
  Polyfold.SBLocalization.fibAct_eq_fiberZero_iff,
  Polyfold.SBLocalization.fibAct_comp_inv,
  Polyfold.SBLocalization.CriterionData.hasLocalSectionStructure,
  Polyfold.SBLocalization.AssemblyInput.mult_eq,
  Polyfold.SBLocalization.AssemblyInput.isWFunctor_mult,
  Polyfold.SBLocalization.AssemblyInput.crit_nonempty,
  Polyfold.SBLocalization.AssemblyInput.isStructurable_mult,
  Polyfold.SBLocalization.AssemblyInput.mult_boundary,
  Polyfold.SBLocalization.AssemblyInput.domSupp_mult_subset,
  Polyfold.SBLocalization.AssemblyInput.isSaturated_boundaryDomSupp,
  Polyfold.SBLocalization.AssemblyInput.exists_cutoff,
  Polyfold.SBLocalization.AssemblyInput.extension,
  Polyfold.SBLocalization.AssemblyInput.ssec_boundary,
  Polyfold.SBLocalization.AssemblyInput.s0_eq_zero,
  Polyfold.SBLocalization.AssemblyInput.mult_of_not_mem_C,
  Polyfold.SBLocalization.AssemblyInput.isOpen_critV]

end RoundTrip.V14_8
