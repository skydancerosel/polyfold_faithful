import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_33

set_option maxSynthPendingDepth 3

/-! Round trip for V15_33 (2021 Corollary 15.3.10 (1), p. 699; 2017: Corollary 15.1 (1)):
regular perturbations exist.

`A` is the conjunction of the types of the six theorems of the item, at universe `0`
(`TrivialBundle.*` have no universe parameter).  The main conjunct is `corollary_15_3_10_1`.

* `A_to_B`: not proved.  The main conjunct assumes, besides `B`'s hypotheses, sc-smooth bump
  functions (pointwise reading, `AdmitsBumpFunctionsPointwise`) and the tame-germ hypothesis
  `A.B.IsScFredholmSectionTame f`; `B` has neither (its own comment flags the missing bump-function
  hypothesis).  With both added to `B` (`Bplus`), `A ⇒ Bplus` is proved (`main_to_Bplus`):
  "tame" of `Θ` comes from the project's `theorem_15_3_7_in_particular_tame_hyp` (not an item
  theorem here), `X` tame from `d_X ≡ 0`.
* `B_to_A` (main conjunct): proved (`B_to_main`).  `B` gives everything but general position;
  for `d_X ≡ 0` general position follows from transversality (`gp_of_transversal_deg0`: at every
  point a chart with the point interior has `T^R_xX = T_xX`, and `T^R_xX` is chart-independent,
  `MPolyfold.reducedTangentFiber_eq`).
* `B_to_A` (all of `A`): not proved, because of the conjunct `theorem_15_3_7_of_paracompact`
  (Theorem 15.3.7 for every `A` with paracompact `|X|`, without `d_X ≡ 0`), which `B` does not
  give.  The other five conjuncts follow from `B` (`B_to_A_rest`; the example on `ℝ × ℝ → ℝ`
  with its hypotheses re-proved from Part I/II lemmas).
-/

namespace RoundTrip.V15_33
open Set Function Polyfold Polyfold.SBLocalization
open scoped ContDiff

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_3_10_1.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_1_hyp.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_of_paracompact.{0},
    @Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP,
    @Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP⟩

/-- For `d_X ≡ 0` transversality gives general position (`T^R_xX = T_xX`). -/
theorem gp_of_transversal_deg0 {A : SEP.{0}} (hd : ∀ x : A.Obj, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} (htr : IsTransversal f Λ) : IsInGeneralPosition A f Λ := by
  intro x hx L hL φ hφ hxφ k V T hT
  obtain ⟨-, hx1, hon⟩ := htr _ hx
  have hLs : Surjective L := hon L hL
  obtain ⟨χ, hχ, haχ, hdχ⟩ := A.X.PObj.exists_isChart_degIndex_eq (A.X.PObj.levelVal 1 x)
  obtain ⟨n', W', Tχ, hTχ⟩ := χ.model.isPartialQuadrant
  have h0 : degIndex χ.model.E χ.model.C (χ (A.X.PObj.levelVal 1 x)) = 0 := by
    have := hd (A.X.PObj.levelVal 1 x); rw [hdχ] at this; exact this
  have hint : χ (A.X.PObj.levelVal 1 x) ∈ interior χ.model.C :=
    (degIndex_eq_zero_iff χ.model.isPartialQuadrant (χ.apply_mem_C haχ)).1 h0
  have htop : MPolyfold.reducedTangentFiber hχ haχ Tχ = ⊤ := by
    change (minimalSubspaceWith Tχ (χ _)).comap _ = ⊤
    rw [minimalSubspaceWith_eq_top_of_mem_interior Tχ hTχ hint, Submodule.comap_top]
  have heq : MPolyfold.reducedTangentFiber hφ hxφ T = ⊤ := by
    rw [MPolyfold.reducedTangentFiber_eq hφ hxφ T hχ haχ Tχ hT hTχ, htop]
  intro w
  obtain ⟨v, rfl⟩ := hLs w
  exact ⟨⟨v, by rw [heq]; trivial⟩, rfl⟩

/-- **B ⇒ the main conjunct** `corollary_15_3_10_1`. -/
theorem B_to_main : B → (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1.{0}) := by
  intro hB A hd hpara _ f hf _ hS N U hcc
  obtain ⟨Λ, hst, hdom, hN, htr, hbr, -, hK⟩ := hB A hd hpara f hf hS N U hcc
  exact ⟨Λ, ⟨hcc, hst, hdom, hN, htr⟩, gp_of_transversal_deg0 hd htr, hbr, hK⟩

/-- `B` with the main conjunct's added hypotheses (pointwise bump functions, tame germ data). -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}), (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    A.X.AdmitsBumpFunctionsPointwise →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ domSupp Λ ⊆ U ∧
        (∀ x, pointwiseNorm N Λ x < 1) ∧ IsTransversal f Λ ∧
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ))

/-- **The main conjunct ⇒ `Bplus`**. -/
theorem main_to_Bplus : (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1.{0}) → Bplus := by
  intro H A hd hpara hbump f hf hft hS N U hcc
  obtain ⟨Λ, ⟨-, hst, hdom, hN, htr⟩, hgp, hbr, hK⟩ := H hd hpara hbump hf hft hS hcc
  obtain ⟨-, -, hT⟩ := theorem_15_3_7_in_particular_tame_hyp hf hft hcc hst.1
    (fun x => (hN x).le) hdom hgp
  exact ⟨Λ, hst, hdom, hN, htr, hbr, hT, hK⟩

theorem A_to_Bplus : A → Bplus := fun hA => main_to_Bplus hA.1

/-- `Bplus` is `B` with two more hypotheses. -/
theorem B_to_Bplus : B → Bplus := fun hB A hd hpara _ f hf _ hS N U hcc =>
  hB A hd hpara f hf hS N U hcc

open StrongBundleEquivalenceExamples TrivialBundle in
/-- The hypotheses of the example on `ℝ × ℝ → ℝ` (re-proved). -/
theorem hypotheses_epSEP' : type_of% @Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP := by
  have hφ : ContDiff ℝ ∞ (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) := contDiff_id
  have hpara := (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn 1).2
  have hf : (epSEP 1 1).E.IsScFredholmSectionFunctor diagSection :=
    graphSection_mem_fredholmSectionFunctors_epBundle hφ
  have hS : (epSEP 1 1).E.HasCompactSolutionSetEp diagSection := by
    change IsCompact ((epSEP 1 1).X.π '' solutionSet (epSEP 1 1).P diagSection)
    rw [solutionSet_diagSection]
    exact isCompact_singleton.image (epSEP 1 1).X.continuous_π
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (epSEP 1 1).E hpara
  refine ⟨fun y => (fibEquiv (n := 1) (k := 1) y).nontrivial,
    ⟨_, by rw [solutionSet_diagSection]; exact mem_singleton _⟩, rnPolyfold_degIndex 1, hpara,
    (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn 1).1, hf,
    isScFredholmSectionTame_graphSection hφ, hS, N, exists_controlsCompactness hf hS hN⟩

/-- **B ⇒ the conjuncts of `A` other than `theorem_15_3_7_of_paracompact`.** -/
theorem B_to_A_rest : B →
    (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1.{0}) ∧
    (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1_hyp.{0}) ∧
    (type_of% @Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7.{0}) ∧
    (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP) ∧
    (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP) := by
  intro hB
  have hm := fun (A : SEP.{0}) => @B_to_main hB A
  refine ⟨B_to_main hB, fun _ hd hpara _ hbump _ hf hft hS _ _ hcc => hm _ hd hpara hbump hf hft hS hcc,
    fun _ hd hpara hbump _ hf hft hS _ _ hcc => hm _ hd hpara hbump hf hft hS hcc,
    hypotheses_epSEP', ?_⟩
  obtain ⟨-, -, hd, hpara, hbump, hf, hft, hS, N, U, hcc⟩ := hypotheses_epSEP'
  obtain ⟨Λ, h⟩ := hm _ hd hpara hbump hf hft hS hcc
  exact ⟨N, U, Λ, h⟩

#rt_check RoundTrip.V15_33.B_to_main [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]
#rt_check RoundTrip.V15_33.B_to_A_rest [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]
#rt_check RoundTrip.V15_33.main_to_Bplus [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]
#rt_check RoundTrip.V15_33.A_to_Bplus [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]
#rt_overlap RoundTrip.V15_33.B_to_main [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]
#rt_overlap RoundTrip.V15_33.B_to_A_rest [Polyfold.SBLocalization.corollary_15_3_10_1, Polyfold.SBLocalization.corollary_15_3_10_1_hyp, Polyfold.SBLocalization.corollary_15_3_10_1_of_theorem_15_3_7, Polyfold.SBLocalization.theorem_15_3_7_of_paracompact, Polyfold.TrivialBundle.corollary_15_3_10_1_hypotheses_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_1_epSEP]

end RoundTrip.V15_33
