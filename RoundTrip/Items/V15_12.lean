import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_12

set_option maxSynthPendingDepth 3

/-! Round trip for V15_12 (2021 Theorem 15.2.2, pp. 688–689; 2017: Theorem 15.2: interior local
perturbation).

`A` is the conjunction of the types of `theorem_15_2_2_hyp` (the theorem), `exists_branch_interior`
(one branch), `isOpen_sep_ne`, `IsScPlusSectionOn.continuousOn` (at universe `0`) and the witness
`theorem_15_2_2_hyp_witness` (no universe parameter).

* `A_to_B`: not proved.  `theorem_15_2_2_hyp` carries the added hypothesis
  `A.B.IsScFredholmSectionTame f` (germ data in tame charts at every smooth point of `X`, a global
  condition that `B`'s hypotheses do not give).  With that hypothesis added to `B`
  (`Btame`), `A ⇒ Btame` is proved (`A_to_Btame`): (a) the sheet points are smooth by
  `mem_smoothSet_of_eq` (which uses the tame hypothesis), (e) for every chart by
  `linearization_eq`.
* `B_to_A`: proved.  From `B`'s `U(x)`, structure `(sᵢ, σᵢ)` on `O`: take a chart `c` at `x` with
  domain in `U(x)` (so in `O`), and shrink the natural representation (`exists_naturalRep_shrink`)
  into the chart domain and into `{y | f(y) ≠ sᵢ(y)}` for the branches with `sᵢ(x) ≠ f(x)` (the last
  conjunct of `theorem_15_2_2_hyp`); (1), (2), (a) (`IsSmoothSubmanifold.inter_isOpen`), (c), (d)
  and (e) come from `B` and restrict to the smaller set; (b) is closedness of the sheets.  The
  other conjuncts (one branch, two continuity facts and the witness) are not consequences of `B`:
  they are re-proved outright (the project's proofs, copied, from non-item lemmas such as
  `exists_solutionSet_interior`).
-/

namespace RoundTrip.V15_12
open Set Polyfold Polyfold.SBLocalization Polyfold.StrongBundle Polyfold.StrongRetr
  Polyfold.MPolyfold Polyfold.TrivialBundle

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_15_2_2_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_branch_interior.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isOpen_sep_ne.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_2_2_hyp_witness)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_15_2_2_hyp.{0},
    @Polyfold.SBLocalization.exists_branch_interior.{0},
    @Polyfold.SBLocalization.isOpen_sep_ne.{0},
    @Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn.{0},
    @Polyfold.SBLocalization.theorem_15_2_2_hyp_witness⟩

/-! ### Copies of the small conjuncts -/

theorem continuousOn' : type_of% @Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn.{0} := by
  intro Asep s O hs
  obtain ⟨-, G, hGs, hG⟩ := hs
  exact (Asep.B.continuous_oneVal.comp_continuousOn hG.continuousOn).congr fun y hy =>
    (hGs y hy).symm

theorem isOpen_sep_ne' : type_of% @Polyfold.SBLocalization.isOpen_sep_ne.{0} := by
  intro Asep f s hf O hO hs
  exact (hf.continuousOn.prodMk hs).isOpen_inter_preimage hO isClosed_diagonal.isOpen_compl

theorem exists_branch_interior' : type_of% @Polyfold.SBLocalization.exists_branch_interior.{0} := by
  intro Asep f hft s O hO hs c hc hsub x hx hx1 hd hon
  by_cases h : s x = f x
  · obtain ⟨V, hVo, hxV, hVc, hS, hall⟩ := exists_solutionSet_interior hft hO hs hc hsub hx h.symm
      hd (Asep.X.PObj.toBase_levelLift c.isChart hx hx1) (hon h)
    exact ⟨V, hVo, hxV, hVc, hS, hall, fun _ _ _ => h⟩
  · have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
    refine ⟨{y ∈ c.φ.source | f y ≠ s y},
      isOpen_sep_ne' hfc c.φ.isOpen_source ((continuousOn' hs).mono hsub), ⟨hx, fun e => h e.symm⟩,
      sep_subset _ _, fun a ha => absurd ha.2 ha.1.2, fun y hy hfs => absurd hfs hy.2,
      fun y hy hfs => absurd hfs hy.2⟩

theorem witness' : type_of% @Polyfold.SBLocalization.theorem_15_2_2_hyp_witness := by
  intro n
  classical
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) := contDiff_const
  have hpos : ∀ x : Fin n → ℝ, 0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
      (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) x) := fun x => by
    unfold zeroMultisection
    rw [if_pos]
    · exact one_pos
    · exact Prod.ext rfl (funext fun i => i.elim0)
  refine ⟨graphSection_mem_fredholmSectionFunctors_epBundle hφ,
    isScFredholmSectionTame_graphSection hφ,
    isScPlusMultisection_zeroMultisection _, fun x _ => ⟨hpos x, ?_⟩,
    fun x => ⟨rnPolyfold_degIndex n x, hpos x⟩⟩
  have hx1 : x ∈ (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.levelSet 1 := by
    have h : (x : Fin n → ℝ) ∈ (rnPolyfold n).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hx1, fun L _ w => ⟨0, ?_⟩⟩
  refine Subtype.ext (Prod.ext ?_ (funext fun i => i.elim0))
  exact ((L 0).2).trans w.2.symm

/-! ### `B ⇒ theorem_15_2_2_hyp` -/

theorem main_B_to_A : B → type_of% @Polyfold.SBLocalization.theorem_15_2_2_hyp.{0} := by
  classical
  intro hB Asep f hf hft Λ hΛ x hd htr
  obtain ⟨R, hdeg, honto, O, hO, hRO, k, s, σ, hrep, ha, -, hcU, hcount, he⟩ :=
    hB Asep f Λ hf hΛ x htr.1 hd htr
  have hsec : IsSection Asep.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  -- a chart at `x` with domain in `U(x)`
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem Asep.B x
  have hso : IsOpen (c₀.φ.source ∩ R.U) := c₀.φ.isOpen_source.inter R.isOpen_U
  obtain ⟨c, hc, hcsrc⟩ : ∃ c : StrongBundleChart Asep.X.PObj Asep.P, Asep.B.IsChart c ∧
      c.φ.source = c₀.φ.source ∩ R.U :=
    ⟨_, (StrongBundle.isChart_of_mem Asep.B hc₀).restrict inter_subset_left hso, rfl⟩
  have hcR : c.φ.source ⊆ R.U := hcsrc ▸ inter_subset_right
  have hcO : c.φ.source ⊆ O := hcR.trans hRO
  have hxc : x ∈ c.φ.source := hcsrc ▸ ⟨hxc₀, R.mem_U⟩
  -- the branches not through `f(x)` are avoided
  set W : Set Asep.Obj := c.φ.source ∩ ⋂ i, {y | y ∈ O ∧ (s i x = f x ∨ f y ≠ s i y)} with hW
  have hWo : IsOpen W := by
    refine c.φ.isOpen_source.inter (isOpen_iInter_of_finite fun i => ?_)
    by_cases hi : s i x = f x
    · simp only [hi, true_or, and_true, ofPred_mem_eq]; exact hO
    · simp only [hi, false_or]
      exact isOpen_sep_ne' hfc hO (continuousOn' (hrep.2.1 i))
  have hxW : x ∈ W := ⟨hxc, mem_iInter.2 fun i => ⟨hRO R.mem_U, by
    by_cases hi : s i x = f x
    · exact Or.inl hi
    · exact Or.inr fun e => hi e.symm⟩⟩
  obtain ⟨R', hR'U, -, -⟩ := Asep.X.exists_naturalRep_shrink R hWo hxW
  have hR'R : R'.U ⊆ R.U := fun y hy => (hR'U hy).2
  have hR'c : R'.U ⊆ c.φ.source := fun y hy => (hR'U hy).1.1
  have hR'W : ∀ i, ∀ y ∈ R'.U, s i x = f x ∨ f y ≠ s i y := fun i y hy =>
    (mem_iInter.1 (hR'U hy).1.2 i).2
  have hcount' : ∀ y ∈ R.U, Λ (f y) = ∑ i with f y = s i y, σ i := fun y hy => by
    rw [hcount y hy]
    exact Finset.sum_congr (Finset.filter_congr fun i _ =>
      ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩) fun _ _ => rfl
  refine ⟨R', O, k, s, σ, c, hO, hrep, hc, hR'c, hcO, fun y hy => hdeg y (hR'R hy),
    fun y hy hp => honto y (hR'R hy) hp, ?_, ?_, ?_, fun y hy => hcount' y (hR'R hy), ?_, ?_⟩
  · -- (a)
    intro i
    have e : {y ∈ R'.U | f y = s i y} = sheet R.U f (s i) ∩ R'.U := by
      ext y
      exact ⟨fun h => ⟨⟨hR'R h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
    rw [e]
    exact (ha i).2.1.inter_isOpen R'.isOpen_U
  · -- (b)
    intro i
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s i) R'.U := (continuousOn' (hrep.2.1 i)).mono (hR'R.trans hRO)
    have h1 : Continuous fun p : R'.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R'.U => s i p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  · -- (c)
    ext y
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hp⟩
      have : y ∈ ⋃ i, sheet R.U f (s i) := hcU ▸ ⟨hR'R hy, hp⟩
      obtain ⟨i, -, hi⟩ := mem_iUnion.1 this
      exact ⟨i, hy, hi⟩
    · rintro ⟨i, hy, hi⟩
      have : y ∈ {y | y ∈ R.U ∧ 0 < Λ (f y)} := hcU ▸ mem_iUnion.2 ⟨i, hR'R hy, hi⟩
      exact ⟨hy, this.2⟩
  · -- (e)
    intro y hy
    have hyR : Asep.X.PObj.levelVal 1 y ∈ R.U := hcR hy
    exact he y hyR c hc hcO hy
  · -- only branches through `f(x)` meet `f` in `U(x)`
    intro i y hy hi
    rcases hR'W i y hy with h | h
    · exact h
    · exact absurd hi h

theorem B_to_A : B → A := fun hB =>
  ⟨main_B_to_A hB, exists_branch_interior', isOpen_sep_ne', continuousOn', witness'⟩

/-! ### `A ⇒ B` with the tame hypothesis added to `B` -/

open Classical in
/-- `B` with the added hypothesis `A.B.IsScFredholmSectionTame f` of `theorem_15_2_2_hyp`. -/
def Btame : Prop :=
  ∀ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0),
    A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    IsScPlusMultisection A Λ →
    ∀ x : A.Obj, 0 < Λ (f x) → A.X.PObj.degIndex x = 0 → IsTransversalAt f Λ x →
    ∃ R : A.X.NaturalRep x,
      (∀ y ∈ R.U, A.X.PObj.degIndex y = 0) ∧
      (∀ y ∈ R.U, 0 < Λ (f y) → IsOntoAt f Λ y) ∧
      ∃ (O : Set A.Obj), IsOpen O ∧ R.U ⊆ O ∧
      ∃ (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ O s σ ∧
        (∀ i, sheet R.U f (s i) ⊆ A.X.PObj.smoothSet ∧
          A.X.PObj.IsSmoothSubmanifold (sheet R.U f (s i)) ∧
          ∀ y ∈ sheet R.U f (s i), A.X.PObj.degIndex y = 0) ∧
        (∀ i, ∃ h : sheet R.U f (s i) ⊆ R.U, IsProperMap (Set.inclusion h)) ∧
        ({y | y ∈ R.U ∧ 0 < Λ (f y)} = ⋃ i, sheet R.U f (s i)) ∧
        (∀ y ∈ R.U, Λ (f y) = ∑ i with y ∈ sheet R.U f (s i), σ i) ∧
        (∀ (y : A.X.PObj.Level 1), A.X.PObj.levelVal 1 y ∈ R.U →
          ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
          ∀ hy : A.X.PObj.levelVal 1 y ∈ c.φ.source,
            linearization f Λ y = linSumIntr c hy f s σ)

theorem main_A_to_Btame : type_of% @Polyfold.SBLocalization.theorem_15_2_2_hyp.{0} → Btame := by
  classical
  intro hA Asep f Λ hf hft hΛ x _ hd htr
  obtain ⟨R, O, k, s, σ, c, hO, hrep, hc, hRc, hcO, hdeg, honto, ha, hb, hcU, hcount, -, -⟩ :=
    hA hf hft hΛ hd htr
  have hRO : R.U ⊆ O := hRc.trans hcO
  refine ⟨R, hdeg, honto, O, hO, hRO, k, s, σ, hrep, fun i => ⟨?_, ha i, fun y hy => hdeg y hy.1⟩,
    fun i => ⟨sep_subset _ _, hb i⟩, hcU, fun y hy => ?_, ?_⟩
  · rintro y ⟨hy, hfs⟩
    exact mem_smoothSet_of_eq hft hO (hrep.2.1 i) (hRO hy) hfs
  · rw [hcount y hy]
    exact Finset.sum_congr (Finset.filter_congr fun i _ =>
      ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩) fun _ _ => rfl
  · intro y _ c' hc' hsub' hy
    exact linearization_eq hf ⟨O, hO, k, s, σ, hrep, c', hc', hsub', hy⟩

theorem A_to_Btame : A → Btame := fun h => main_A_to_Btame h.1

#rt_check RoundTrip.V15_12.B_to_A [Polyfold.SBLocalization.theorem_15_2_2_hyp,
  Polyfold.SBLocalization.exists_branch_interior, Polyfold.SBLocalization.isOpen_sep_ne,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn,
  Polyfold.SBLocalization.theorem_15_2_2_hyp_witness]
#rt_check RoundTrip.V15_12.main_B_to_A [Polyfold.SBLocalization.theorem_15_2_2_hyp,
  Polyfold.SBLocalization.exists_branch_interior, Polyfold.SBLocalization.isOpen_sep_ne,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn,
  Polyfold.SBLocalization.theorem_15_2_2_hyp_witness]
#rt_check RoundTrip.V15_12.A_to_Btame [Polyfold.SBLocalization.theorem_15_2_2_hyp,
  Polyfold.SBLocalization.exists_branch_interior, Polyfold.SBLocalization.isOpen_sep_ne,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn,
  Polyfold.SBLocalization.theorem_15_2_2_hyp_witness]
#rt_overlap RoundTrip.V15_12.B_to_A [Polyfold.SBLocalization.theorem_15_2_2_hyp,
  Polyfold.SBLocalization.exists_branch_interior, Polyfold.SBLocalization.isOpen_sep_ne,
  Polyfold.SBLocalization.IsScPlusSectionOn.continuousOn,
  Polyfold.SBLocalization.theorem_15_2_2_hyp_witness]

end RoundTrip.V15_12
