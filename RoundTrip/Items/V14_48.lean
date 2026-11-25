import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_48

set_option maxSynthPendingDepth 3

/-! Round trip for V14_48 (2021 Lemma 14.5.2 and Remark 14.5.3, p. 672, `Λ̃ = ∑_a Λ_a` over
`∂X`; 2017: Lemma 14.11, Remark 14.7).

`A` is the conjunction of the types of the six listed theorems at universe `0`
(`lemma_14_5_2`, `definition_13_4_5_boundary`, `isFaceScPlusSectionOn_sectionSum` at `.{0,0}`,
the index type in `Type`; the half-space witness has no universe parameter).  `B` is on `SEP.{0}`.

* `main_to_B` / `A_to_B`: Lemma 14.5.2 part of `B` from the conjunct `lemma_14_5_2` with
  `ι = C.Aset` (local finiteness and `∑ᶠ β_a = 1` transferred from `C.BetaSpec β` to the
  subtype), the sections `smulOver T`; the class equality by `Quotient.sound`.  The Remark 14.5.3
  part of `B` (explicit formulas for `Λ_a`) is proved directly: the transport of the count along
  `φ` (`Sections.countAt_fibAct`) for points reached from `V_a`, and `β_a = 0` (so
  `Λ_a = 0 ⊙ Λ`, the trivial multisection) where nothing from `V̂_a` arrives
  (`tsupport β_a ⊆ saturation V̂_a`).  `A`'s `remark_14_5_3` is not used.
* `B_to_A` is not proved: `lemma_14_5_2` is for any structured tuple and any locally finite
  family of invariant sc-smooth `β` with `∑ β = 1` on `∂X`, while `B` only treats the cut-offs of
  Lemma 14.5.1 for the data of §14.3 under the standing hypotheses; `remark_14_5_3` (a uniqueness
  statement), `Over.s_eq_of_eqOn`, `definition_13_4_5_boundary`,
  `isFaceScPlusSectionOn_sectionSum` and the half-space witness are not consequences of `B`.
-/

namespace RoundTrip.V14_48
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.BoundaryCommData.definition_13_4_5_boundary.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.isFaceScPlusSectionOn_sectionSum.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.BoundaryCommData.remark_14_5_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.BoundaryCommData.Over.s_eq_of_eqOn.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.lemma_14_5_2_witness)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.BoundaryCommData.definition_13_4_5_boundary.{0,0},
   @Polyfold.SBLocalization.isFaceScPlusSectionOn_sectionSum.{0,0},
   @Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2.{0,0},
   @Polyfold.SBLocalization.BoundaryCommData.remark_14_5_3.{0},
   @Polyfold.SBLocalization.BoundaryCommData.Over.s_eq_of_eqOn.{0},
   @Polyfold.HalfSpaceBundle.lemma_14_5_2_witness⟩

open Classical in
theorem main_to_B
    (hL : type_of% @Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2.{0,0}) : B := by
  intro A _ _ _ T P E Q C β hβ
  obtain ⟨hsm, hinv, hsupp, hlf, hsum⟩ := hβ
  have hlf' : ∀ y, ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧
      {a : C.Aset | ∃ z ∈ O, β a z ≠ 0}.Finite := by
    intro y
    obtain ⟨O, hO, hyO, -, hfin⟩ := hlf y
    refine ⟨O, hO, hyO, ?_⟩
    have h' : (Subtype.val ⁻¹' {a | a ∈ C.Aset ∧ ∃ z ∈ O, β a z ≠ 0} : Set C.Aset).Finite :=
      hfin.preimage Subtype.val_injective.injOn
    exact h'.subset fun a ha => ⟨a.2, ha⟩
  have hsum' : ∀ y ∈ A.X.PObj.boundary, ∑ᶠ a : C.Aset, β a y = 1 := fun y hy => by
    rw [finsum_set_coe_eq_finsum_mem (f := fun a => β a y)]
    exact hsum y hy
  obtain ⟨hlfΛ, -, hmult, hequiv⟩ :=
    hL T (fun a : C.Aset => β a) (fun a => hinv a) (fun a => hsm a) hlf' hsum'
  refine ⟨⟨fun a => BoundaryCommData.smulOver T (hinv a) (hsm a), fun a x i y hy => ?_, hlfΛ,
    hmult, Quotient.sound hequiv⟩, fun a ha w hw => ⟨fun φ hφs hφt => ?_, fun hno => ?_⟩⟩
  · -- the sections are `β_a·s⁰ˣᵢ`
    rw [BoundaryCommData.smulOver_s_apply T (hinv a) (hsm a) i hy]
    unfold Polyfold.sectionSmul
    rw [dif_pos ((T.dec.S x).P_s i hy)]
  · -- Remark 14.5.3, at points reached from `V_a`
    set x := bdryRetr C.x₀ a
    set o := BoundaryCommData.smulOver T (hinv a) (hsm a)
    have hz : A.X.src φ ∈ T.dec.𝒰.U x :=
      C.mem_bdry ha ⟨C.toZData.V_subset a ha hφs.1, hφs.2⟩
    set x' : A.X.PObj.boundary := ⟨A.P w, hw⟩
    have hφ : φ ∈ (BoundaryCommData.ofTuple T).𝒰.mor x x' :=
      ⟨hz, by rw [hφt]; exact T.dec.𝒰.mem_U x'⟩
    have hPw : A.P w = A.X.src (A.X.inv φ) := by rw [A.X.src_inv, hφt]
    set v := fibAct (A.X.inv φ) w
    have hv : A.P v = A.X.src φ := by rw [P_fibAct hPw, A.X.tgt_inv]
    have hvw : fibAct φ v = w := by
      rw [← fibAct_comp hPw (A.X.tgt_inv φ).symm, A.X.comp_inv, fibAct_unit hφt.symm]
    have hsec : ∀ i, o.s x i (A.X.src φ) =
        Polyfold.sectionSmul A.P (β a) (C.toZSections.s a i) (A.X.src φ) := fun i => by
      rw [BoundaryCommData.smulOver_s_apply T (hinv a) (hsm a) i hz]
      unfold Polyfold.sectionSmul
      split_ifs with h
      · rfl
      · exact absurd ((T.dec.S x).P_s i hz) h
    have hiff : ∀ i, o.s x i (A.P v) = v ↔
        fibAct φ (Polyfold.sectionSmul A.P (β a) (C.toZSections.s a i) (A.X.src φ)) = w := by
      intro i
      rw [hv, hsec i]
      have hPu : A.P (Polyfold.sectionSmul A.P (β a) (C.toZSections.s a i) (A.X.src φ)) =
          A.X.src φ := by
        rw [← hsec i]; exact o.toSections.P_s i hz
      constructor
      · intro e; rw [e, hvw]
      · intro e
        calc _ = fibAct (A.X.inv φ) (fibAct φ _) := by
              rw [← fibAct_comp hPu (A.X.src_inv φ), A.X.inv_comp, fibAct_unit hPu]
          _ = v := by rw [e]
    have hrep := o.rep x' w (T.dec.𝒰.mem_U x')
    have hc : (BoundaryCommData.ofTuple T).countAt o.s x v =
        (BoundaryCommData.ofTuple T).countAt o.s x' w := by
      rw [o.toSections.countAt_fibAct hφ hv, hvw]
    show multisectionSmulFun (β a) T.Λ w = _
    rw [hrep, ← hc]
    unfold BoundaryCommData.countAt
    simp only [hiff]
    rfl
  · -- Remark 14.5.3, where nothing from `V_a` arrives: `β_a(P w) = 0`
    have h0 : β a (A.P w) = 0 := by
      by_contra hne
      obtain ⟨φ, hs, ht⟩ := exists_mor_of_ne_zero (hsupp a ha) hne
      exact hno ⟨φ, ⟨hs, (tgt_mem_boundary_iff_src φ).1 (ht ▸ hw)⟩, ht⟩
    unfold RoundTrip.V14_48.Λa multisectionSmulFun
    rw [h0, multisectionSmul_zero]
    rfl

theorem A_to_B (hA : A) : B := main_to_B hA.2.2.1

#rt_check_soft RoundTrip.V14_48.A_to_B [Polyfold.SBLocalization.BoundaryCommData.definition_13_4_5_boundary,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_sectionSum,
  Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2,
  Polyfold.SBLocalization.BoundaryCommData.remark_14_5_3,
  Polyfold.SBLocalization.BoundaryCommData.Over.s_eq_of_eqOn,
  Polyfold.HalfSpaceBundle.lemma_14_5_2_witness]
#rt_check_soft RoundTrip.V14_48.main_to_B [Polyfold.SBLocalization.BoundaryCommData.definition_13_4_5_boundary,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_sectionSum,
  Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2,
  Polyfold.SBLocalization.BoundaryCommData.remark_14_5_3,
  Polyfold.SBLocalization.BoundaryCommData.Over.s_eq_of_eqOn,
  Polyfold.HalfSpaceBundle.lemma_14_5_2_witness]
#rt_overlap RoundTrip.V14_48.A_to_B [Polyfold.SBLocalization.BoundaryCommData.definition_13_4_5_boundary,
  Polyfold.SBLocalization.isFaceScPlusSectionOn_sectionSum,
  Polyfold.SBLocalization.BoundaryCommData.lemma_14_5_2,
  Polyfold.SBLocalization.BoundaryCommData.remark_14_5_3,
  Polyfold.SBLocalization.BoundaryCommData.Over.s_eq_of_eqOn,
  Polyfold.HalfSpaceBundle.lemma_14_5_2_witness]

end RoundTrip.V14_48
