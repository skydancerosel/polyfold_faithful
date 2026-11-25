import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_71

set_option maxSynthPendingDepth 3

/-! Round trip for V16_71 (2021 Theorem 16.5.7, p. 735; 2017: Theorem 16.6).

`A` is the conjunction of the types of `StrongPolyfoldBundle.theorem_16_5_7` (main conjunct),
`BoundaryMultisection.isStructurableNe_iff`, `SBLocalization.theorem_14_1_9` (the ep-level
Theorem 14.1.9 used by the proof), `tsupport_comp_subset_preimage'`, `theorem_16_5_7_hyp` (the
main form with Theorem 14.1.9 in the models as a hypothesis) and `theorem_16_5_7_hyp_witness`
(its hypotheses on `λ, Ũ, f` are satisfiable), all at universe `0`.

**The one difference: partitions of unity.**  The main conjunct assumes
`hPU : ∀ S ∈ c̄, S.A.X.PObj.AdmitsScPartitionsOfUnity`: the object M-polyfold of EVERY model
admits sc-smooth partitions of unity for arbitrary open covers (the M-polyfold notion).  `B`
assumes `c.polyfold.AdmitsScPartitionsOfUnity` (Definition 16.1.5 (2)): SOME model admits them
in the ep-groupoid sense (Definition 7.5.5: saturated covers, invariant partitions).  By
Theorem 7.5.7 (`EpGroupoid.theorem_7_5_7`, orbit space paracompact) the first gives the second, so
`B ⇒ A`'s main conjunct.  The converse (ep-groupoid partitions of unity in one model ⇒ M-polyfold
partitions of unity of the object space in every model) is not in the project, so `A ⇒ B` is not
proved; `A_to_Bpu` proves `A ⇒ B` with `B`'s hypothesis replaced by `A`'s (`Bpu`), so this is the
only gap.  All other hypotheses and the conclusion agree verbatim (both use `IsStructurable`, not
`IsStructurableNe`, the same `normLam`, `domSupp`, `tsupport`).

`B ⇒ A`: the main conjunct and `theorem_16_5_7_hyp` (whose extra hypothesis is not needed) from
`B`; `isStructurableNe_iff`, `tsupport_comp_subset_preimage'`, `theorem_14_1_9` and the witness
are re-proved outright from non-item lemmas (the project's proofs; `theorem_14_1_9` from
`theorem_14_1_9_charged` and `SEP.exists_isTameChart`). -/

namespace RoundTrip.V16_71
open Set Function Topology Filter CategoryTheory
open Polyfold EPLocalization SBLocalization StrongPolyfoldBundle StrongPolyfoldBundleStructure

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_14_1_9.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage'.{0, 0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0},
    @Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff.{0},
    @Polyfold.SBLocalization.theorem_14_1_9.{0},
    @Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage'.{0, 0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness.{0}⟩

/-- `A`'s partition-of-unity hypothesis gives `B`'s (Theorem 7.5.7 in one model). -/
theorem admitsPU_of_models {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    {c : StrongPolyfoldBundle p}
    (hPU : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.PObj.AdmitsScPartitionsOfUnity) :
    c.polyfold.AdmitsScPartitionsOfUnity := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  exact ⟨S.toPolyfoldStructure, by rw [← hS]; rfl,
    S.A.X.theorem_7_5_7 S.paracompact (hPU S hS)⟩

/-- `B` with its partition-of-unity hypothesis replaced by the main conjunct's. -/
def Bpu : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.IsTame →
    (∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.PObj.AdmitsScPartitionsOfUnity) →
    ∀ (lam : c.BoundaryMultisection), lam.IsStructurable →
    ∀ (n : Y → ℝ), c.IsAuxNorm n →
    ∀ (U : Set Z), IsOpen U → lam.domSupp ⊆ U →
    ∀ (f : Z → ℝ), Continuous f → (∀ z, 0 ≤ f z) → tsupport f ⊆ U →
      (∀ z ∈ lam.domSupp, c.normLam n lam.toFun z < f z) →
      ∃ lam' : c.ScPlusMultisection, lam'.IsStructurable ∧
        (∀ z, c.normLam n lam'.toFun z ≤ f z) ∧
        lam'.domSupp ⊆ U ∧
        ∀ y, p y ∈ c.polyfold.boundary → lam'.toFun y = lam.toFun y

/-- `B ⇒ Bpu` (B assumes less). -/
theorem B_to_Bpu : B → Bpu := by
  intro hB Y Z _ _ p c hc hPU lam hl n hn U hU hd f hf hf0 hfU hlt
  exact hB c hc (admitsPU_of_models hPU) lam hl n hn U hU hd f hf hf0 hfU hlt

/-- The main conjunct gives `Bpu`: the partition-of-unity hypothesis is the only gap in
`A ⇒ B`. -/
theorem Amain_to_Bpu : (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0}) → Bpu := by
  intro h Y Z _ _ p c hc hPU lam hl n hn U hU hd f hf hf0 hfU hlt
  exact h hc hPU hn lam hl hU hd hf hf0 hfU hlt

theorem A_to_Bpu : A → Bpu := fun h => Amain_to_Bpu h.1

/-- `B` gives the main conjunct. -/
theorem B_to_Amain : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7.{0}) := by
  intro hB Y Z _ _ p c hc hPU n hn s hs U hU hdom f hf hf0 hfU hlt
  exact hB c hc (admitsPU_of_models hPU) s hs n hn U hU hdom f hf hf0 hfU hlt

theorem B_to_Ahyp : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp.{0}) := by
  intro hB Y Z _ _ p c _ hc hPU n hn s hs U hU hdom f hf hf0 hfU hlt
  exact B_to_Amain hB hc hPU hn s hs hU hdom hf hf0 hfU hlt

/-! ### Side conjuncts, re-proved (the project's proofs) -/

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

theorem B_to_A : B → A := fun hB =>
  ⟨B_to_Amain hB, isStructurableNe_iff', theorem_14_1_9', tsupport_comp_subset_preimage'',
    B_to_Ahyp hB, witness'⟩

#rt_check RoundTrip.V16_71.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness]
#rt_check RoundTrip.V16_71.B_to_Amain [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness]
#rt_check RoundTrip.V16_71.A_to_Bpu [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness]
#rt_check RoundTrip.V16_71.B_to_Bpu [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness]
#rt_overlap RoundTrip.V16_71.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_5_7,
  Polyfold.StrongPolyfoldBundle.BoundaryMultisection.isStructurableNe_iff,
  Polyfold.SBLocalization.theorem_14_1_9,
  Polyfold.StrongPolyfoldBundle.tsupport_comp_subset_preimage',
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp,
  Polyfold.StrongPolyfoldBundle.theorem_16_5_7_hyp_witness]

end RoundTrip.V16_71
