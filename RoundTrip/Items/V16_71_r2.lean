import Polyfold
import Polyfold.Chapter7.ObjectPartitionsOfUnity
import Polyfold.Chapter16.Theorem1657Def1615
import RoundTrip.Check
import RoundTrip.Blind.V16_71

set_option maxSynthPendingDepth 3

/-! Round trip for V16_71_r2 (refresh of V16_71: 2021 Theorem 16.5.7, p. 735; 2017: Theorem
16.6).  `B` is the existing blind statement `RoundTrip.V16_71.B`.

`A` is the conjunction of the types of the six theorems of V16_71 (`theorem_16_5_7`,
`isStructurableNe_iff`, `SBLocalization.theorem_14_1_9`, `tsupport_comp_subset_preimage'`,
`theorem_16_5_7_hyp`, `theorem_16_5_7_hyp_witness`) and of the new
`theorem_16_5_7_def_16_1_5` (Theorem 16.5.7 with `c.polyfold.AdmitsScPartitionsOfUnity`,
Definition 16.1.5 (2)), `EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`
(Definition 7.5.5 ⇒ Definition 5.5.1 for the object M-polyfold) and
`theorem_16_5_7_def_16_1_5_witness` (the hypotheses hold over `|ℤ/3 × ℝ ⇉ ℝ|`), at universe `0`.

The partition-of-unity hypothesis of `theorem_16_5_7` (the object M-polyfold of every model
admits sc-smooth partitions of unity) follows from Definition 16.1.5 (2) by
`admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`, so the main conjunct
`theorem_16_5_7_def_16_1_5` has exactly `B`'s hypotheses and conclusion: `main_to_B` and
`B_to_main` are one application each, and `A_to_B` follows.

`B_to_A`: the two Theorem 16.5.7 conjuncts and `theorem_16_5_7_hyp` from `B` (Definition
16.1.5 (2) from the models' hypothesis by Theorem 7.5.7 in one model); the Chapter 7 lemma from
the non-item `exists_isScSmoothMap_urysohn_of_hasScPartitionsOfUnity` (its last step re-proved);
`isStructurableNe_iff`, `tsupport_comp_subset_preimage'`, `theorem_14_1_9` and the two witnesses
re-proved outright from non-item lemmas (the project's proofs). -/

namespace RoundTrip.V16_71_r2
open Set Function Topology Filter CategoryTheory
open Polyfold EPLocalization SBLocalization StrongPolyfoldBundle StrongPolyfoldBundleStructure

abbrev B : Prop := RoundTrip.V16_71.B

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage'.{0, 0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness)

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0},
    @Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff.{0},
    @Polyfold.SBLocalization.theorem_14_1_9.{0},
    @Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage'.{0, 0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5.{0},
    @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness⟩

/-- The main conjunct: Theorem 16.5.7 under Definition 16.1.5 (2). -/
def Amain : Prop := type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5.{0}

theorem main_to_B : Amain → B := by
  intro h Y Z _ _ p c hc hPU lam hl n hn U hU hd f hf hf0 hfU hlt
  exact h hc hPU hn lam hl hU hd hf hf0 hfU hlt

theorem B_to_main : B → Amain := by
  intro hB Y Z _ _ p c hc hPU n hn s hs U hU hdom f hf hf0 hfU hlt
  exact hB c hc hPU s hs n hn U hU hdom f hf hf0 hfU hlt

theorem A_to_B : A → B := fun h => main_to_B h.2.2.2.2.2.2.1

/-! ### `B ⇒ A` -/

/-- The models' hypothesis gives Definition 16.1.5 (2) (Theorem 7.5.7 in one model). -/
theorem admitsPU_of_models {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    {c : StrongPolyfoldBundle p}
    (hPU : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.PObj.AdmitsScPartitionsOfUnity) :
    c.polyfold.AdmitsScPartitionsOfUnity := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  exact ⟨S.toPolyfoldStructure, by rw [← hS]; rfl,
    S.A.X.theorem_7_5_7 S.paracompact (hPU S hS)⟩

theorem B_to_Aold : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0}) := by
  intro hB Y Z _ _ p c hc hPU n hn s hs U hU hdom f hf hf0 hfU hlt
  exact hB c hc (admitsPU_of_models hPU) s hs n hn U hU hdom f hf hf0 hfU hlt

theorem B_to_Ahyp : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0}) := by
  intro hB Y Z _ _ p c _ hc hPU n hn s hs U hU hdom f hf hf0 hfU hlt
  exact B_to_Aold hB hc hPU hn s hs hU hdom hf hf0 hfU hlt

/-- The Chapter 7 conjunct, from the (non-item) sc-smooth Urysohn functions. -/
theorem objectPU' :
    type_of% @Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity.{0} := by
  classical
  intro Obj Mor _ _ _ _ _ _ X hPU ι V hVo hVcov
  obtain ⟨b, hbp, hb⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : Obj → ℝ => X.PObj.IsScSmoothMap realPolyfold g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ :=
        EpGroupoid.exists_isScSmoothMap_urysohn_of_hasScPartitionsOfUnity hPU hs ht hst
      exact ⟨⟨F, continuousOn_univ.1 hF.continuousOn⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ V hVo (by rw [hVcov])
  refine ⟨b.toPartitionOfUnity, hb.toPartitionOfUnity, fun i => ?_⟩
  refine isScSmoothMap_real_of_eventuallyEq fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ⟨_, ?_, hT⟩
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact (hbp i).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
    (isScSmoothMap_real_const 1).real_sub (hbp j))

theorem isStructurableNe_iff' :
    type_of% @Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff.{0} := by
  intro Y Z _ _ p c s
  exact ⟨BoundaryMultisection.IsStructurableNe.isStructurable, fun ⟨a, ha, hs⟩ =>
    ⟨a, ha, hs, hs.chargesBoundary⟩⟩

theorem tsupport_comp_subset_preimage'' :
    type_of% @Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage'.{0, 0} := by
  intro α β _ _ g hg f
  rw [tsupport, tsupport, support_comp_eq_preimage]
  exact hg.closure_preimage_subset _

theorem theorem_14_1_9' : type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0} := by
  intro A hX hpara hpu Λ hΛ
  exact theorem_14_1_9_charged hX hpara hpu (A.exists_isTameChart hX) Λ hΛ hΛ.chargesBoundary

theorem witness' : type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness.{0} := by
  intro Y Z _ _ p c hc n
  set S := c.out
  have hX := (c.isTame_iff.1 hc) S (Quotient.out_eq c)
  set a : BoundaryMultisectionRep c := ⟨S, Quotient.out_eq c, zeroMultisection S.A,
    isBoundaryScPlusMultisection_zero hX, (ofFunctor S (Quotient.out_eq c) _
      (isScPlusMultisection_zeroMultisection S.A)).lam,
    fun w _ => (ofFunctor S (Quotient.out_eq c) _
      (isScPlusMultisection_zeroMultisection S.A)).comm w⟩
  have hempty : BoundaryMultisection.domSupp (c := c) ⟦a⟧ = ∅ := by
    have h := boundaryDomSupp_zero (A := S.A)
    rw [BoundaryMultisection.domSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
    rintro z ⟨hz, y, rfl, hy0, hpos⟩
    obtain ⟨ξ, rfl⟩ := S.Γ.surjective y
    obtain ⟨w, rfl⟩ := S.A.E.toEpGroupoid.surjective_π ξ
    have hw : S.A.P w ∈ S.A.X.PObj.boundary := by
      rw [S.p_Γ_π] at hz; exact (mem_boundary_iff_obj (Quotient.out_eq c) _).1 hz
    have hw0 : w ≠ fiberZero S.A.P (S.A.P w) := fun h' =>
      hy0 (by rw [zeroAt_eq_of_mem (Quotient.out_eq c)]; exact (S.Γ_π_eq_zeroAt_iff w).2 h')
    rw [BoundaryMultisection.toFun_mk_of_mem a hz, a.comm w hw] at hpos
    have : S.A.P w ∈ boundaryDomSupp (zeroMultisection S.A) :=
      subset_closure ⟨hw, w, rfl, hw0, hpos⟩
    rw [h] at this
    exact this
  refine ⟨⟦a⟧, ⟨a, rfl, isBoundaryStructurable_zero hX S.paracompact⟩, by rw [hempty], by simp,
    by simp [hempty]⟩

theorem witness_def' :
    type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness := by
  obtain ⟨n, hn⟩ := z3Bundle_exists_auxNorm 1
  obtain ⟨s, hs, hd, ht, hlt⟩ := witness' (n := n) (z3Bundle_isTame 1)
  exact ⟨z3Bundle_isTame 1, StrongBundleLocalizationExamples.z3Bundle_admitsScPartitionsOfUnity,
    n, hn, s, ∅, fun _ => 0, hs, isOpen_empty, hd, continuous_const, fun _ => le_rfl, ht, hlt⟩

theorem B_to_A : B → A := fun hB =>
  ⟨B_to_Aold hB, isStructurableNe_iff', theorem_14_1_9', tsupport_comp_subset_preimage'',
    B_to_Ahyp hB, witness', B_to_main hB, objectPU', witness_def'⟩

#rt_check RoundTrip.V16_71_r2.A_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness]
#rt_check RoundTrip.V16_71_r2.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness]
#rt_check RoundTrip.V16_71_r2.main_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity]
#rt_check RoundTrip.V16_71_r2.B_to_main [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity]
#rt_overlap RoundTrip.V16_71_r2.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5,
  Polyfold.EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_def_16_1_5_witness]

end RoundTrip.V16_71_r2
