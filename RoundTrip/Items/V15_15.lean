import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_15

set_option maxSynthPendingDepth 3

/-! Round trip for V15_15 (2021 Theorem 15.2.5, p. 690; 2017: Theorem 15.3: boundary local
perturbation).

`A` is the conjunction of the types of the sixteen theorems of the item (definitions
`IsReducedOntoAtLevel`, `IsInGeneralPositionAt` are vocabulary), at universe `0`
(`StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt` at `0, 0`; the witnesses have no
universe parameter).

* `A_to_B`: not proved.  Every perturbation statement of `A` (`theorem_15_2_5_hyp`,
  `theorem_15_2_5_tame_hyp`, `theorem_15_2_5_generalPosition_hyp`,
  `theorem_15_2_5_isTameBranched_hyp`, …) carries the added hypothesis
  `A.B.IsScFredholmSectionTame f` (germ data in tame charts at every smooth point), which `B`'s
  hypotheses (tame `X`, `f` sc-Fredholm functor, `Λ` sc⁺-multisection) do not give; the global
  statement `theorem_15_2_5_isTameBranched_hyp` moreover assumes `|supp(Λ ∘ f)|` paracompact, which
  `B`'s conclusion `IsBranchedEpSubgroupoid` asserts.  With these two hypotheses added to `B`
  (`Btame`), `A ⇒ Btame` is proved (`A_to_Btame`): the `Mᵢ` and weights of `LocalB` are those of the
  tame local branching structure of `theorem_15_2_5_tame_hyp` (reindexed by `Fin k`), cut down to a
  natural representation inside the `U(x)` of `theorem_15_2_5_hyp` (resp.
  `theorem_15_2_5_generalPosition_hyp`), which gives (2) on `M_{U(x)}`.
* `B_to_A`: not proved.  `B` assumes `X` tame and speaks only about boundary points, with `Mᵢ`
  not tied to a local sc⁺-section structure; `theorem_15_2_5_hyp` holds over any ep-groupoid at any
  point in good position and names the `Mᵢ` as the solution sets `{f = sᵢ}` of a local structure,
  with the formula for `T(f,Λ)` in a chart and only branches through `f(x)` meeting `f`.
-/

namespace RoundTrip.V15_15
open Set Polyfold Polyfold.SBLocalization Polyfold.MPolyfold

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_branch_goodPosition.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_hyp_witness) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_hyp_applies) ∧
  (type_of% @Polyfold.StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.isInGeneralPosition_iff_forall_at.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isGeneralPositionGerm_branch_at.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPositionAt.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_reduced_preimage_of_isGeneralPositionGerm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.surjective_reduced_toIntr_of_isGeneralPositionGerm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isReducedOntoAtLevel_of_isGeneralPositionGerm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp_witness) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_tame_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_isTameBranched_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_5_restricted_hyp.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_2_5_hyp.{0},
    @Polyfold.SBLocalization.exists_branch_goodPosition.{0},
    @Polyfold.SBLocalization.theorem_15_2_5_hyp_witness,
    @Polyfold.SBLocalization.theorem_15_2_5_hyp_applies,
    @Polyfold.StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt.{0, 0},
    @Polyfold.SBLocalization.isInGeneralPosition_iff_forall_at.{0},
    @Polyfold.SBLocalization.isGeneralPositionGerm_branch_at.{0},
    @Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPositionAt.{0},
    @Polyfold.SBLocalization.exists_reduced_preimage_of_isGeneralPositionGerm.{0},
    @Polyfold.SBLocalization.surjective_reduced_toIntr_of_isGeneralPositionGerm.{0},
    @Polyfold.SBLocalization.isReducedOntoAtLevel_of_isGeneralPositionGerm.{0},
    @Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp_witness,
    @Polyfold.SBLocalization.theorem_15_2_5_tame_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_2_5_isTameBranched_hyp.{0},
    @Polyfold.SBLocalization.theorem_15_2_5_restricted_hyp.{0}⟩

/-- `B` with the added hypotheses of the project's statements: `f` has tame germ data, and (for
the global conclusions) `|supp(Λ ∘ f)|` is paracompact. -/
def Btame : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0), A.X.IsTame →
    A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    IsScPlusMultisection A Λ →
      (∀ x ∈ A.X.PObj.boundary, IsGoodPositionAt f Λ x →
        LocalB A f Λ x (IsGoodPositionAt f Λ)) ∧
      (ParacompactSpace (A.X.orbitSupp fun z => ((Λ (f z) : ℚ≥0) : ℚ)) →
        (∀ x, 0 < Λ (f x) → IsGoodPositionAt f Λ x) → TameBranchedB A f Λ) ∧
      (∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsInGeneralPositionAt f Λ x →
        LocalB A f Λ x (IsInGeneralPositionAt f Λ)) ∧
      (ParacompactSpace (A.X.orbitSupp fun z => ((Λ (f z) : ℚ≥0) : ℚ)) →
        (∀ x, 0 < Λ (f x) → IsInGeneralPositionAt f Λ x) → TameBranchedB A f Λ)

/-- `LocalB` from a natural representation carrying `Good` on `supp(Λ ∘ f)` and a tame local
branching structure of `Λ ∘ f` at `x`. -/
theorem localB_of {Asep : SEP.{0}} {f : Asep.Obj → Asep.W} {Λ : Asep.W → ℚ≥0}
    (hft : Asep.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection Asep Λ) {x : Asep.Obj}
    {Good : Asep.Obj → Prop} (R : Asep.X.NaturalRep x)
    (hgood : ∀ y ∈ R.U, 0 < Λ (f y) → Good y)
    (T : Asep.X.TameBranchingStructure (fun z => ((Λ (f z) : ℚ≥0) : ℚ)) x) :
    LocalB Asep f Λ x Good := by
  classical
  obtain ⟨R', hR'U, -, -⟩ := Asep.X.exists_naturalRep_shrink R T.isOpen_U T.mem_U
  have hR'T : R'.U ⊆ T.U := fun y hy => (hR'U hy).1
  have hR'R : R'.U ⊆ R.U := fun y hy => (hR'U hy).2
  set e := Fintype.equivFin T.ι
  -- points of the `Mᵢ` are in `supp(Λ ∘ f)`
  have hpos : ∀ i, ∀ y ∈ T.M i, 0 < Λ (f y) := by
    intro i y hy
    have h := T.eq_sum y (T.subset_U i hy)
    have hle : T.σ i ≤ ∑ j with y ∈ T.M j, T.σ j :=
      Finset.single_le_sum (f := T.σ) (fun j _ => (T.σ_pos j).le)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩)
    have : (0 : ℚ) < ((Λ (f y) : ℚ≥0) : ℚ) := by
      rw [h]; exact lt_of_lt_of_le (T.σ_pos i) hle
    exact_mod_cast this
  refine ⟨R', Fintype.card T.ι, fun j => T.M (e.symm j) ∩ R'.U, fun j => T.σ (e.symm j),
    fun j => inter_subset_right, fun j y hy => mem_smoothSet_of_pos hft hΛ (hpos _ y hy.1),
    fun j => (T.isSmoothSubmanifold _).inter_isOpen R'.isOpen_U,
    fun j => HasTameInducedStructure.inter_isOpen (T.isSmoothSubmanifold _)
      (T.hasTameInducedStructure _) R'.isOpen_U,
    fun j => T.σ_pos _, fun j => ⟨inter_subset_right, ?_⟩,
    fun y hy hp => hgood y (hR'R hy) hp, fun y hy => ?_⟩
  · -- (1) properly embedded
    rw [isProperMap_inclusion_iff]
    have hcl := (isProperMap_inclusion_iff (T.subset_U (e.symm j))).1 (T.isProperMap _)
    convert hcl.preimage (continuous_inclusion hR'T) using 1
    ext p
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
  · -- (3)
    rw [T.eq_sum y (hR'T hy), Finset.sum_filter, Finset.sum_filter]
    rw [← Equiv.sum_comp e.symm (fun i => if y ∈ T.M i then T.σ i else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : y ∈ T.M (e.symm j)
    · rw [if_pos h, if_pos ⟨h, hy⟩]
    · rw [if_neg h, if_neg fun h' => h h'.1]

theorem main_A_to_Btame (h1 : type_of% @Polyfold.SBLocalization.theorem_15_2_5_hyp.{0})
    (h8 : type_of% @Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPositionAt.{0})
    (h12 : type_of% @Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp.{0})
    (h14 : type_of% @Polyfold.SBLocalization.theorem_15_2_5_tame_hyp.{0})
    (h15 : type_of% @Polyfold.SBLocalization.theorem_15_2_5_isTameBranched_hyp.{0}) :
    Btame := by
  intro Asep f Λ hX hf hft hΛ
  refine ⟨fun x _ hgp => ?_, fun hpar hgp => h15 hf hft hΛ hgp hpar,
    fun x _ hpos hgp => ?_, fun hpar hgp => h15 hf hft hΛ (fun y hy => h8 hf hft hΛ hy (hgp y hy))
      hpar⟩
  · obtain ⟨R, -, -, -, -, -, -, -, -, -, -, -, -, -, hgood, -⟩ := h1 hf hft hΛ hgp
    exact localB_of hft hΛ R hgood (h14 hf hft hgp).some
  · obtain ⟨R, -, -, -, -, -, -, -, -, -, -, -, -, -, hgood, -⟩ := h12 hX hf hft hΛ hpos hgp
    exact localB_of hft hΛ R (fun y hy hp => (hgood y hy hp).1)
      (h14 hf hft (h8 hf hft hΛ hpos hgp)).some

theorem A_to_Btame : A → Btame := fun h =>
  main_A_to_Btame h.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#rt_check RoundTrip.V15_15.A_to_Btame [Polyfold.SBLocalization.theorem_15_2_5_hyp,
  Polyfold.SBLocalization.exists_branch_goodPosition,
  Polyfold.SBLocalization.theorem_15_2_5_hyp_witness,
  Polyfold.SBLocalization.theorem_15_2_5_hyp_applies,
  Polyfold.StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt,
  Polyfold.SBLocalization.isInGeneralPosition_iff_forall_at,
  Polyfold.SBLocalization.isGeneralPositionGerm_branch_at,
  Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPositionAt,
  Polyfold.SBLocalization.exists_reduced_preimage_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.surjective_reduced_toIntr_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.isReducedOntoAtLevel_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp_witness,
  Polyfold.SBLocalization.theorem_15_2_5_tame_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_isTameBranched_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_restricted_hyp]
#rt_check RoundTrip.V15_15.main_A_to_Btame [Polyfold.SBLocalization.theorem_15_2_5_hyp,
  Polyfold.SBLocalization.exists_branch_goodPosition,
  Polyfold.SBLocalization.theorem_15_2_5_hyp_witness,
  Polyfold.SBLocalization.theorem_15_2_5_hyp_applies,
  Polyfold.StrongBundle.linKer_sup_reduced_eq_of_isGeneralPositionAt,
  Polyfold.SBLocalization.isInGeneralPosition_iff_forall_at,
  Polyfold.SBLocalization.isGeneralPositionGerm_branch_at,
  Polyfold.SBLocalization.isGoodPositionAt_of_isInGeneralPositionAt,
  Polyfold.SBLocalization.exists_reduced_preimage_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.surjective_reduced_toIntr_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.isReducedOntoAtLevel_of_isGeneralPositionGerm,
  Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_generalPosition_hyp_witness,
  Polyfold.SBLocalization.theorem_15_2_5_tame_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_isTameBranched_hyp,
  Polyfold.SBLocalization.theorem_15_2_5_restricted_hyp]

end RoundTrip.V15_15
