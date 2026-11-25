import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_30

set_option maxSynthPendingDepth 3

/-! Round trip for V15_30 (2021 Theorem 15.3.7, last sentence, p. 694; 2017: Theorem 15.4):
"`Λ ∘ f` is a compact tame branched ep⁺-subgroupoid".

`A` is the conjunction of the types of the seven theorems of the item, at universe `0`.  The main
conjunct is `theorem_15_3_7_in_particular_tame_hyp`.

* `A_to_B`: not proved.  The main conjunct assumes `A.B.IsScFredholmSectionTame f` (germ data of
  the sc-Fredholm section in tame charts at every smooth point), which `B`'s hypotheses
  (`X` tame, sc-smooth bump functions, `f` an sc-Fredholm section functor) do not give; no project
  lemma derives it from tameness of `X`.  With that hypothesis added to `B` (`Btame`), `A ⇒ Btame`
  is proved (`A_to_Btame`, `main_to_Btame`): `N(Λ) < h ≤ 1` gives `N(Λ) ≤ 1`.
* `B_to_A`: not proved.  The main conjunct holds without `X` tame, without bump functions,
  without transversality, and with `N(Λ) ≤ 1` in place of `N(Λ) < h` for a continuous functor
  `h ≤ 1`; `B` cannot be applied when `X` is not tame or has no bump functions.  The other six
  conjuncts are proof steps (closedness and compactness of `|supp(Λ ∘ f)|`) that `B` does not
  state.
-/

namespace RoundTrip.V15_30
open Set Polyfold Polyfold.SBLocalization

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.pos_iff_exists_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isClosed_supp_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isClosed_orbitSupp_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.supp_comp_subset_controlled.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCompact_orbitSupp_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_in_particular_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_3_7_in_particular_tame_hyp.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.pos_iff_exists_eq.{0},
    @Polyfold.SBLocalization.isClosed_supp_comp.{0},
    @Polyfold.SBLocalization.isClosed_orbitSupp_comp.{0},
    @Polyfold.SBLocalization.supp_comp_subset_controlled.{0},
    @Polyfold.SBLocalization.isCompact_orbitSupp_comp.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_in_particular_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_3_7_in_particular_tame_hyp.{0}⟩

/-- `B` with the project's tame-germ hypothesis `A.B.IsScFredholmSectionTame f` added. -/
def Btame : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.AdmitsBumpFunctions →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
    ∀ (h : A.Obj → ℝ), IsUnitFunctor A h →
    ∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ →
      (∀ x, pointwiseNorm N Λ x < h x) → domSupp Λ ⊆ U → IsTransversal f Λ →
      IsInGeneralPosition A f Λ →
        A.X.IsBranchedEpSubgroupoid (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsCompactBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) ∧
        A.X.IsTameBranched (fun z => ((Λ (f z) : ℚ≥0) : ℚ))

/-- The main conjunct gives `Btame`. -/
theorem main_to_Btame :
    (type_of% @Polyfold.SBLocalization.theorem_15_3_7_in_particular_tame_hyp.{0}) → Btame := by
  intro H A _ _ f hf hft _ N U hcc h hh Λ hΛ hN hdom _ hgp
  exact H hf hft hcc hΛ (fun x => (hN x).le.trans (hh.2.1 x).2) hdom hgp

theorem A_to_Btame : A → Btame := fun hA => main_to_Btame hA.2.2.2.2.2.2

/-- `Btame` is `B` with one more hypothesis. -/
theorem B_to_Btame : B → Btame := by
  intro hB A ht hb f hf _ hS N U hcc h hh Λ hΛ hN hdom htr hgp
  exact hB A ht hb f hf hS N U hcc h hh Λ hΛ hN hdom htr hgp

#rt_check RoundTrip.V15_30.main_to_Btame [Polyfold.SBLocalization.pos_iff_exists_eq, Polyfold.SBLocalization.isClosed_supp_comp, Polyfold.SBLocalization.isClosed_orbitSupp_comp, Polyfold.SBLocalization.supp_comp_subset_controlled, Polyfold.SBLocalization.isCompact_orbitSupp_comp, Polyfold.SBLocalization.theorem_15_3_7_in_particular_hyp, Polyfold.SBLocalization.theorem_15_3_7_in_particular_tame_hyp]
#rt_check RoundTrip.V15_30.A_to_Btame [Polyfold.SBLocalization.pos_iff_exists_eq, Polyfold.SBLocalization.isClosed_supp_comp, Polyfold.SBLocalization.isClosed_orbitSupp_comp, Polyfold.SBLocalization.supp_comp_subset_controlled, Polyfold.SBLocalization.isCompact_orbitSupp_comp, Polyfold.SBLocalization.theorem_15_3_7_in_particular_hyp, Polyfold.SBLocalization.theorem_15_3_7_in_particular_tame_hyp]

end RoundTrip.V15_30
