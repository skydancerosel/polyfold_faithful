import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_32

set_option maxSynthPendingDepth 3

/-! Round trip for V15_32 (2021 Theorem 15.3.9, p. 698; 2017: Theorem 15.5): the transversal
extension theorem.

`A` is the conjunction of the types of the 31 theorems of the item (definitions are vocabulary),
at universe `0` (`exists_scDeriv_eq_on_of_cover` at `0`; the `HalfSpaceBundle` examples have no
universe parameter).  The main conjunct is `theorem_15_3_9 : theorem_15_3_9_statement A`.

* `B_to_A` (main conjunct): proved (`B_to_main`).  `A`'s hypotheses give `B`'s: `B`'s boundary
  admissibility `{x ∈ ∂X | ∃ t ∈ [−1, 1], (tΛ)(f(x)) > 0} ⊆ U` follows from
  `boundaryDomSupp Λ ⊆ U` and `S_f ⊆ U` (`bd_eq_fiberZero`); `A`'s extra conclusion
  `IsAdmissible A f N U Λ̃` from `isAdmissible_of_domSupp_subset`.
* `A_to_B`: not proved.  The main conjunct assumes (i) the tame-germ hypothesis
  `A.B.IsScFredholmSectionTame f` and (ii) `boundaryDomSupp Λ ⊆ U`; `B` has neither: its
  admissibility over `∂X` only controls the points `x ∈ ∂X` where `f(x)` meets a multiple `tΛ`,
  not every boundary point carrying a non-zero branch.  (ii) is forced by `B`'s own conclusion
  (`Λ̃ = Λ` over `∂X` and `dom-supp Λ̃ ⊆ U` give `boundaryDomSupp Λ ⊆ dom-supp Λ̃ ⊆ U`), so `B`
  asks more than its hypotheses can give in that case.  With (i), (ii) added to `B` (`Bplus`),
  `A ⇒ Bplus` is proved (`main_to_Bplus`): `B`'s extra conclusion "`Λ̃ ∘ f` tame" comes from
  general position of `(f, Λ̃)` (at boundary points from `IsBoundaryFaceOnto`, at the other points,
  where `d_X = 0`, from transversality, `T^R_xX = T_xX`) and the project's
  `theorem_15_3_7_in_particular_tame_hyp`.
* `B_to_A` (all of `A`): not proved: the other conjuncts are proof steps (reduction to the
  relative statement, independence of the extension in `IsBoundaryFaceOnto`, the cut-off) and
  examples on the half disc, which `B` does not state.
-/

namespace RoundTrip.V15_32
open Set Function Polyfold Polyfold.SBLocalization

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_one_extension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isBoundaryFaceOnto_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_linearization_eqOn_reduced.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isReducedOntoAtPt_of_eqOn_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isReducedOntoAtPt_of_eq_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_scDeriv_eq_on_of_cover.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_local_families.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_charged_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_statement_of_charged.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_charged_of_local_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_charged_of_statement.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_charged_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_local_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_rel_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isInGeneralPosition_iff_forall_reducedOntoAtPt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsInGeneralPosition.isTransversal.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_9_of_extension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.lemma_15_3_9_cutoff_hyp.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_3_9_halfSEP) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc) ∧
  (type_of% @Polyfold.HalfSpaceBundle.hasCompactSolutionSetEp_halfDisc) ∧
  (type_of% @Polyfold.HalfSpaceBundle.not_isBoundaryFaceOnto_tangentDisc) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_constDatum) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_15_3_9_constDatum) ∧
  (type_of% @Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc_constMulti) ∧
  (type_of% @Polyfold.SBLocalization.isStructurable_sectionMulti.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mem_support_linearization_sectionMulti_iff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_3_9.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_one_extension.{0},
    @Polyfold.SBLocalization.isBoundaryFaceOnto_iff.{0},
    @Polyfold.SBLocalization.exists_linearization_eqOn_reduced.{0},
    @Polyfold.SBLocalization.isReducedOntoAtPt_of_eqOn_boundary.{0},
    @Polyfold.SBLocalization.isReducedOntoAtPt_of_eq_boundary.{0},
    @Polyfold.SBLocalization.exists_scDeriv_eq_on_of_cover.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_rel.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_local_families.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_charged_iff.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_statement_of_charged.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_charged_of_local_rel.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_charged_of_statement.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_charged_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_local_rel.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_rel_hyp.{0},
    @Polyfold.SBLocalization.isInGeneralPosition_iff_forall_reducedOntoAtPt.{0},
    @Polyfold.SBLocalization.IsInGeneralPosition.isTransversal.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_3_9_of_extension.{0},
    @Polyfold.SBLocalization.lemma_15_3_9_cutoff_hyp.{0},
    @Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_halfSEP,
    @Polyfold.HalfSpaceBundle.theorem_15_3_9_halfSEP,
    @Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc,
    @Polyfold.HalfSpaceBundle.hasCompactSolutionSetEp_halfDisc,
    @Polyfold.HalfSpaceBundle.not_isBoundaryFaceOnto_tangentDisc,
    @Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_constDatum,
    @Polyfold.HalfSpaceBundle.theorem_15_3_9_constDatum,
    @Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc_constMulti,
    @Polyfold.SBLocalization.isStructurable_sectionMulti.{0},
    @Polyfold.SBLocalization.mem_support_linearization_sectionMulti_iff.{0}⟩

/-- Over `∂X` off `boundaryDomSupp Λ`, `(tΛ)(w) > 0` forces `w = 0`. -/
theorem bd_eq_fiberZero {A : SEP.{0}} {Λ : A.W → ℚ≥0} {w : A.W}
    (hb : A.P w ∈ A.X.PObj.boundary) (hx : A.P w ∉ boundaryDomSupp Λ) {t : ℝ}
    (ht : 0 < multisectionSmul t Λ w) : w = fiberZero A.P (A.P w) := by
  unfold multisectionSmul smulAt at ht
  split_ifs at ht with h0 hu
  · exact congrArg Subtype.val hu
  · exact absurd ht (lt_irrefl 0)
  · by_contra hne
    set u : A.P ⁻¹' {A.P w} := t⁻¹ • toFib w
    have hu0 : u ≠ 0 := by
      intro hu
      apply hne
      have : toFib w = 0 := by
        have := congrArg (t • ·) hu
        simpa [u, smul_smul, mul_inv_cancel₀ h0] using this
      exact congrArg Subtype.val this
    have hz : Λ (u : A.W) = 0 := by
      by_contra hne'
      exact hx (subset_closure ⟨hb, (u : A.W), u.2, fun e => hu0 (Subtype.ext e),
        pos_iff_ne_zero.2 hne'⟩)
    rw [hz] at ht
    exact lt_irrefl 0 ht

/-- **B ⇒ the main conjunct** `theorem_15_3_9`. -/
theorem B_to_main : B → (type_of% @Polyfold.SBLocalization.theorem_15_3_9.{0}) := by
  intro hB A hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU hN1 h hc hfun hh hNh honto
  have hsec : IsSection A.P f := hf.1.1.1
  have hadm : IsBoundaryAdmissible A f N U Λ := by
    refine ⟨hΛ.1, hN1, ?_⟩
    rintro x ⟨hxb, t, -, ht⟩
    by_contra hxU
    have h0 := bd_eq_fiberZero (w := f x) (by rw [hsec x]; exact hxb)
      (by rw [hsec x]; exact fun hm => hxU (hdomU hm)) ht
    rw [hsec x] at h0
    exact hxU (hcc.2.2.2.1 h0)
  obtain ⟨Λt, hst, hbd, hdom, hN, htr, hbr, hK, -⟩ :=
    hB A hX hpara hPU f hf hS N U hcc h ⟨hc, hh, hfun⟩ Λ hadm hΛ hNh honto
  exact ⟨Λt, hst, hbd, hdom, hN, isAdmissible_of_domSupp_subset hsec hcc.2.2.2.1 hst.1
    (fun x => (hN x).le.trans (hh x).2) hdom, htr, hbr, hK⟩

/-- At a point with `d_X(x) = 0`, `T^R_xX = T_xX` in every chart and presentation. -/
theorem reducedTangentFiber_eq_top_of_deg0 {A : SEP.{0}} {x : A.X.PObj.Level 1}
    (hd : A.X.PObj.degIndex (A.X.PObj.levelVal 1 x) = 0) {φ : MChart A.Obj}
    (hφ : A.X.PObj.IsChart φ) (hxφ : A.X.PObj.levelVal 1 x ∈ φ.source) {k : ℕ} {V : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)) (hT : φ.model.C = T 0 ⁻¹' quadrant k V 0) :
    MPolyfold.reducedTangentFiber hφ hxφ T = ⊤ := by
  obtain ⟨χ, hχ, haχ, hdχ⟩ := A.X.PObj.exists_isChart_degIndex_eq (A.X.PObj.levelVal 1 x)
  obtain ⟨n', W', Tχ, hTχ⟩ := χ.model.isPartialQuadrant
  have h0 : degIndex χ.model.E χ.model.C (χ (A.X.PObj.levelVal 1 x)) = 0 := by
    have := hd; rw [hdχ] at this; exact this
  have hint : χ (A.X.PObj.levelVal 1 x) ∈ interior χ.model.C :=
    (degIndex_eq_zero_iff χ.model.isPartialQuadrant (χ.apply_mem_C haχ)).1 h0
  have htop : MPolyfold.reducedTangentFiber hχ haχ Tχ = ⊤ := by
    change (minimalSubspaceWith Tχ (χ _)).comap _ = ⊤
    rw [minimalSubspaceWith_eq_top_of_mem_interior Tχ hTχ hint, Submodule.comap_top]
  rw [MPolyfold.reducedTangentFiber_eq hφ hxφ T hχ haχ Tχ hT hTχ, htop]

/-- `B` with the main conjunct's added hypotheses: tame germ data and `boundaryDomSupp Λ ⊆ U`. -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
    ∀ Λ : A.W → ℚ≥0, IsBoundaryAdmissible A f N U Λ → IsBoundaryStructurable A Λ →
      boundaryDomSupp Λ ⊆ U →
      (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x) →
      IsBoundaryFaceOnto f Λ →
      ∃ Λt : A.W → ℚ≥0, IsStructurable A Λt ∧
        (∀ w : A.W, A.P w ∈ A.X.PObj.boundary → Λt w = Λ w) ∧
        domSupp Λt ⊆ U ∧
        (∀ x, pointwiseNorm N Λt x < h x) ∧
        IsTransversal f Λt ∧
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λt (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λt (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λt (f z) : ℚ≥0) : ℚ))

/-- **The main conjunct ⇒ `Bplus`.** -/
theorem main_to_Bplus : (type_of% @Polyfold.SBLocalization.theorem_15_3_9.{0}) → Bplus := by
  intro H A hX hpara hPU f hf hft hS N U hcc h hh Λ hadm hΛ hbdom hNh honto
  have hsec : IsSection A.P f := hf.1.1.1
  obtain ⟨Λt, hst, hbd, hdom, hN, -, htr, hbr, hK⟩ :=
    H hX hpara hPU f hf hft hS N U hcc Λ hΛ hbdom hadm.2.1 h hh.1 hh.2.2 hh.2.1 hNh honto
  have hgp : IsInGeneralPosition A f Λt := by
    intro x hpos L hL φ hφ hxφ k V T hT
    by_cases hxb : A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary
    · have hbdP : A.P (f (A.X.PObj.levelVal 1 x)) ∈ A.X.PObj.boundary := by
        rw [hsec]; exact hxb
      have hpos' : 0 < Λ (f (A.X.PObj.levelVal 1 x)) := by rwa [← hbd _ hbdP]
      exact honto Λt hst.1 hbd x hxb (mem_smoothSet_of_pos hft hst.1 hpos) hpos' L hL φ hφ hxφ
        k V T hT
    · have hd : A.X.PObj.degIndex (A.X.PObj.levelVal 1 x) = 0 := by
        simp only [MPolyfold.boundary, mem_ofPred_eq, not_le, Nat.lt_one_iff] at hxb
        exact hxb
      obtain ⟨-, hx1, hon⟩ := htr _ hpos
      have hLs : Surjective L := hon L hL
      have heq := reducedTangentFiber_eq_top_of_deg0 hd hφ hxφ T hT
      intro w
      obtain ⟨v, rfl⟩ := hLs w
      exact ⟨⟨v, by rw [heq]; trivial⟩, rfl⟩
  obtain ⟨-, -, hT⟩ := theorem_15_3_7_in_particular_tame_hyp hf hft hcc hst.1
    (fun x => (hN x).le.trans (hh.2.1 x).2) hdom hgp
  exact ⟨Λt, hst, hbd, hdom, hN, htr, hbr, hK, hT⟩

/-- `Bplus` is `B` with two more hypotheses. -/
theorem B_to_Bplus : B → Bplus := fun hB A hX hpara hPU f hf _ hS N U hcc h hh Λ hadm hΛ _ hNh
  honto => hB A hX hpara hPU f hf hS N U hcc h hh Λ hadm hΛ hNh honto

#rt_check RoundTrip.V15_32.B_to_main [Polyfold.SBLocalization.theorem_15_3_9, Polyfold.SBLocalization.theorem_15_3_9_of_one_extension, Polyfold.SBLocalization.isBoundaryFaceOnto_iff, Polyfold.SBLocalization.exists_linearization_eqOn_reduced, Polyfold.SBLocalization.isReducedOntoAtPt_of_eqOn_boundary, Polyfold.SBLocalization.isReducedOntoAtPt_of_eq_boundary, Polyfold.SBLocalization.exists_scDeriv_eq_on_of_cover, Polyfold.SBLocalization.theorem_15_3_9_of_rel, Polyfold.SBLocalization.theorem_15_3_9_of_local_families, Polyfold.SBLocalization.theorem_15_3_9_charged_iff, Polyfold.SBLocalization.theorem_15_3_9_statement_of_charged, Polyfold.SBLocalization.theorem_15_3_9_charged_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_charged_of_statement, Polyfold.SBLocalization.theorem_15_3_9_charged_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_of_rel_hyp, Polyfold.SBLocalization.isInGeneralPosition_iff_forall_reducedOntoAtPt, Polyfold.SBLocalization.IsInGeneralPosition.isTransversal, Polyfold.SBLocalization.theorem_15_3_9_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_extension, Polyfold.SBLocalization.lemma_15_3_9_cutoff_hyp, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_halfSEP, Polyfold.HalfSpaceBundle.theorem_15_3_9_halfSEP, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc, Polyfold.HalfSpaceBundle.hasCompactSolutionSetEp_halfDisc, Polyfold.HalfSpaceBundle.not_isBoundaryFaceOnto_tangentDisc, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_constDatum, Polyfold.HalfSpaceBundle.theorem_15_3_9_constDatum, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc_constMulti, Polyfold.SBLocalization.isStructurable_sectionMulti, Polyfold.SBLocalization.mem_support_linearization_sectionMulti_iff]
#rt_check RoundTrip.V15_32.main_to_Bplus [Polyfold.SBLocalization.theorem_15_3_9, Polyfold.SBLocalization.theorem_15_3_9_of_one_extension, Polyfold.SBLocalization.isBoundaryFaceOnto_iff, Polyfold.SBLocalization.exists_linearization_eqOn_reduced, Polyfold.SBLocalization.isReducedOntoAtPt_of_eqOn_boundary, Polyfold.SBLocalization.isReducedOntoAtPt_of_eq_boundary, Polyfold.SBLocalization.exists_scDeriv_eq_on_of_cover, Polyfold.SBLocalization.theorem_15_3_9_of_rel, Polyfold.SBLocalization.theorem_15_3_9_of_local_families, Polyfold.SBLocalization.theorem_15_3_9_charged_iff, Polyfold.SBLocalization.theorem_15_3_9_statement_of_charged, Polyfold.SBLocalization.theorem_15_3_9_charged_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_charged_of_statement, Polyfold.SBLocalization.theorem_15_3_9_charged_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_of_rel_hyp, Polyfold.SBLocalization.isInGeneralPosition_iff_forall_reducedOntoAtPt, Polyfold.SBLocalization.IsInGeneralPosition.isTransversal, Polyfold.SBLocalization.theorem_15_3_9_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_extension, Polyfold.SBLocalization.lemma_15_3_9_cutoff_hyp, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_halfSEP, Polyfold.HalfSpaceBundle.theorem_15_3_9_halfSEP, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc, Polyfold.HalfSpaceBundle.hasCompactSolutionSetEp_halfDisc, Polyfold.HalfSpaceBundle.not_isBoundaryFaceOnto_tangentDisc, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_constDatum, Polyfold.HalfSpaceBundle.theorem_15_3_9_constDatum, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc_constMulti, Polyfold.SBLocalization.isStructurable_sectionMulti, Polyfold.SBLocalization.mem_support_linearization_sectionMulti_iff]
#rt_overlap RoundTrip.V15_32.B_to_main [Polyfold.SBLocalization.theorem_15_3_9, Polyfold.SBLocalization.theorem_15_3_9_of_one_extension, Polyfold.SBLocalization.isBoundaryFaceOnto_iff, Polyfold.SBLocalization.exists_linearization_eqOn_reduced, Polyfold.SBLocalization.isReducedOntoAtPt_of_eqOn_boundary, Polyfold.SBLocalization.isReducedOntoAtPt_of_eq_boundary, Polyfold.SBLocalization.exists_scDeriv_eq_on_of_cover, Polyfold.SBLocalization.theorem_15_3_9_of_rel, Polyfold.SBLocalization.theorem_15_3_9_of_local_families, Polyfold.SBLocalization.theorem_15_3_9_charged_iff, Polyfold.SBLocalization.theorem_15_3_9_statement_of_charged, Polyfold.SBLocalization.theorem_15_3_9_charged_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_charged_of_statement, Polyfold.SBLocalization.theorem_15_3_9_charged_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_local_rel, Polyfold.SBLocalization.theorem_15_3_9_of_rel_hyp, Polyfold.SBLocalization.isInGeneralPosition_iff_forall_reducedOntoAtPt, Polyfold.SBLocalization.IsInGeneralPosition.isTransversal, Polyfold.SBLocalization.theorem_15_3_9_hyp, Polyfold.SBLocalization.theorem_15_3_9_of_extension, Polyfold.SBLocalization.lemma_15_3_9_cutoff_hyp, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_halfSEP, Polyfold.HalfSpaceBundle.theorem_15_3_9_halfSEP, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc, Polyfold.HalfSpaceBundle.hasCompactSolutionSetEp_halfDisc, Polyfold.HalfSpaceBundle.not_isBoundaryFaceOnto_tangentDisc, Polyfold.HalfSpaceBundle.theorem_15_3_9_hypotheses_constDatum, Polyfold.HalfSpaceBundle.theorem_15_3_9_constDatum, Polyfold.HalfSpaceBundle.isBoundaryFaceOnto_halfDisc_constMulti, Polyfold.SBLocalization.isStructurable_sectionMulti, Polyfold.SBLocalization.mem_support_linearization_sectionMulti_iff]

end RoundTrip.V15_32
