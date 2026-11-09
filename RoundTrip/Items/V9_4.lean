import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_4

/-! Round trip for V9_4 (Remark 9.1.3 (b), p. 403 [2017: Remark 9.2 (b), p. 292]: local branching
structures are not unique).

`A` is the conjunction of the types of the five listed theorems (no universe parameters):
`remark913Hyp_expNegInvGlue` (the hypotheses are satisfiable), `thetaGraphs_eq` (the two
descriptions of `Θ` agree), `Remark913Hyp.γ₂_pos`, `Remark913Hyp.eq_add_of_thetaGraphs_eq`
(`γ₂ = β₁ + β₂` is forced) and `remark_9_1_3_b` (`Θ` is a `1`-dimensional branched
ep⁺-subgroupoid, described by both families, and no sheet of `structureβ 0` agrees with a sheet of
`structureγ 0` on any neighbourhood of `0`).  `Remark913Hyp`, `thetaGraphs`, `structureβ`,
`structureγ` are definitions (vocabulary).

Dictionary: `HypB` is `Remark913Hyp` (same six fields, same order); `graphB = graph2`;
`countB G p = #{i | p ∈ Gᵢ} = ∑_{i : p ∈ Gᵢ} 1`, so `countB ![graphB β₁, graphB β₂] =
thetaGraphs β₁ β₂`; the blind `IsBranchedB` is the project's `IsBranchedEpSubgroupoid` (the
comparison of `RoundTrip/Items/V9_1.lean`, repeated here).

* `A → B`: (a) from `remark_9_1_3_b`; the structures at each `x` of the support are the project's
  `localBranchingStructure_sum_rn` (`U = {y | y ∈ Gᵢ ⇒ x ∈ Gᵢ}`, sheets `Gᵢ ∩ U` for the `i` with
  `x ∈ Gᵢ`), the two structures on `U = ℝ²` at `0` are checked directly; (b) with
  `γ₂ = β₁ + β₂` (`γ₂_pos`, `thetaGraphs_eq`); (c) from the last conjunct of `remark_9_1_3_b`
  (the domains of `structureβ 0`, `structureγ 0` are all of `ℝ²`): if the two pairs of sets agreed,
  `G₁ ∩ V` would be one of `Γ₁ ∩ V`, `Γ₂ ∩ V`.
* `B → A`: that `Θ` is branched comes from `B` (a); its `1`-dimensionality from the structures of
  `B` (a) at each point, with the dimension of graphs (`rnPolyfold_isSubmanifoldOfDim_graph2`), which
  `B` does not mention.  `B` (c) only says the two *pairs* of sets differ, which is weaker than
  `A`'s "no sheet of one equals a sheet of the other near `0`"; that conjunct, the satisfiability
  witness, `thetaGraphs_eq`, `γ₂_pos` and `eq_add_of_thetaGraphs_eq` are re-proved outright. -/

namespace RoundTrip.V9_4
open Polyfold EpGroupoid Set Filter Topology
open scoped ContDiff

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue) ∧
  (type_of% @Polyfold.EpGroupoid.thetaGraphs_eq) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.γ₂_pos) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq) ∧
  (type_of% @Polyfold.EpGroupoid.remark_9_1_3_b)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue, @Polyfold.EpGroupoid.thetaGraphs_eq,
    @Polyfold.EpGroupoid.Remark913Hyp.γ₂_pos,
    @Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq,
    @Polyfold.EpGroupoid.remark_9_1_3_b⟩

/-! ### Proper inclusions and the definition (as in `RoundTrip/Items/V9_1.lean`) -/

section Proper
variable {Z : Type} [TopologicalSpace Z]

theorem isProperMap_inclusion_iff' {A U : Set Z} (h : A ⊆ U) :
    IsProperMap (inclusion h) ↔ IsClosed ((↑) ⁻¹' A : Set U) := by
  have hr : ((↑) ⁻¹' A : Set U) = range (inclusion h) := (range_inclusion h).symm
  rw [hr]
  exact ⟨fun hp => hp.isClosedMap.isClosed_range,
    fun hc => (Topology.IsClosedEmbedding.mk (Topology.IsEmbedding.inclusion h) hc).isProperMap⟩

theorem properInclB_of_isClosed {A U : Set Z} (hc : IsClosed ((↑) ⁻¹' A : Set U)) :
    IsProperInclB A U := by
  intro K hKU hK
  have hK' : IsCompact ((↑) ⁻¹' K : Set U) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.2 hKU]
    exact hK
  have h2 := Subtype.isCompact_iff.1 (hK'.inter_right hc)
  have heq : (Subtype.val '' ((↑) ⁻¹' K ∩ (↑) ⁻¹' A : Set U)) = K ∩ A := by
    rw [← preimage_inter, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.2 fun y hy => hKU hy.1
  rwa [heq] at h2

theorem isClosed_of_properInclB [TopologicalSpace.MetrizableSpace Z] {A U : Set Z}
    (h : IsProperInclB A U) : IsClosed ((↑) ⁻¹' A : Set U) := by
  refine IsSeqClosed.isClosed fun u p hu hlim => ?_
  have hv : Tendsto (fun n => (u n : Z)) atTop (𝓝 (p : Z)) :=
    (continuous_subtype_val.tendsto p).comp hlim
  have hK : IsCompact (insert (p : Z) (range fun n => (u n : Z))) := hv.isCompact_insert_range
  have hKU : insert (p : Z) (range fun n => (u n : Z)) ⊆ U := by
    rintro _ (rfl | ⟨n, rfl⟩)
    · exact p.2
    · exact (u n).2
  have hKA := (h _ hKU hK).isClosed
  have hmem := hKA.mem_of_tendsto hv (Eventually.of_forall fun n => ⟨Or.inr ⟨n, rfl⟩, hu n⟩)
  exact hmem.2

/-- A closed set has the blind properness in every `U`. -/
theorem properInclB_of_isClosed' {A : Set Z} (hA : IsClosed A) (U : Set Z) :
    IsProperInclB A U := fun _ _ hK => hK.inter_right hA

end Proper

section Compare
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isLBSB_of {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (L : X.LocalBranchingStructure Θ x) : IsLBSB X Θ x L.U L.M L.σ :=
  ⟨L.isOpen_U, L.mem_U, fun i => ⟨L.subset_U i, L.isSmoothSubmanifold i, L.mem_M i,
    properInclB_of_isClosed ((isProperMap_inclusion_iff' _).1 (L.isProperMap i))⟩,
    L.σ_pos, L.eq_sum⟩

theorem isBranchedB_of (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    IsBranchedB X Θ := by
  refine ⟨hΘ.nonneg, hΘ.isFunctorial, hΘ.support_subset, hΘ.paracompactSpace_orbitSupp,
    fun x hx => ?_⟩
  obtain ⟨L⟩ := hΘ.localBranching x hx
  exact ⟨L.ι, L.fintype, L.U, L.M, L.σ, isLBSB_of L⟩

/-- A blind local branching structure as a project one. -/
def lbsOf (X : EpGroupoid Obj Mor) {Θ : Obj → ℚ} {x : Obj} {ι : Type} {inst : Fintype ι}
    {U : Set Obj} {M : ι → Set Obj} {σ : ι → ℚ} (h : @IsLBSB _ _ _ _ _ _ _ _ X Θ x ι inst U M σ) :
    X.LocalBranchingStructure Θ x :=
  have := X.PObj.metrizableSpace
  @EpGroupoid.LocalBranchingStructure.mk _ _ _ _ _ _ _ _ X Θ x U h.1 h.2.1 ι inst M
    (fun i => (h.2.2.1 i).1) (fun i => (h.2.2.1 i).2.1) (fun i => (h.2.2.1 i).2.2.1)
    (fun i => (isProperMap_inclusion_iff' _).2 (isClosed_of_properInclB (h.2.2.1 i).2.2.2))
    σ h.2.2.2.1 h.2.2.2.2

theorem isBranched_of (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (hΘ : IsBranchedB X Θ) :
    X.IsBranchedEpSubgroupoid Θ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hΘ
  refine ⟨h1, h2, h3, h4, fun x hx => ?_⟩
  obtain ⟨ι, inst, U, M, σ, h⟩ := h5 x hx
  exact ⟨lbsOf X h⟩

end Compare

/-! ### Dictionary for the counting function -/

open Classical in
theorem countB_eq_sum (G : Fin 2 → Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) :
    countB G p = ∑ i with p ∈ G i, (1 : ℚ) := by
  rw [countB, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem countB_eq_thetaGraphs (β₁ β₂ : ℝ → ℝ) :
    countB ![graphB β₁, graphB β₂] = thetaGraphs β₁ β₂ :=
  funext fun p => countB_eq_sum _ p

theorem hyp_of {β₁ β₂ : ℝ → ℝ} (h : HypB β₁ β₂) : Remark913Hyp β₁ β₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The structure on `U = ℝ²` at `0` given by two graphs through `0`. -/
theorem isLBSB_univ {β γ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hγ : ContDiff ℝ ∞ γ) (hβ0 : β 0 = 0)
    (hγ0 : γ 0 = 0) {Θ : (Fin 2 → ℝ) → ℚ} (hΘ : ∀ y, Θ y = countB ![graphB β, graphB γ] y) :
    IsLBSB X2 Θ 0 univ ![graphB β, graphB γ] (fun _ => 1) := by
  refine ⟨isOpen_univ, mem_univ _, fun i => ⟨subset_univ _, ?_, ?_, ?_⟩, fun _ => one_pos,
    fun y _ => by rw [hΘ y, countB_eq_sum]⟩
  · fin_cases i
    · exact (rnPolyfold_isSubmanifoldOfDim_graph2 hβ).1
    · exact (rnPolyfold_isSubmanifoldOfDim_graph2 hγ).1
  · fin_cases i
    · exact hβ0.symm
    · exact hγ0.symm
  · fin_cases i
    · exact properInclB_of_isClosed' (isClosed_graph2 hβ.continuous) _
    · exact properInclB_of_isClosed' (isClosed_graph2 hγ.continuous) _

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA β₁ β₂ hB
  have h := hyp_of hB
  obtain ⟨hbr, -, heq, hne⟩ := hA.2.2.2.2 h
  have hc := countB_eq_thetaGraphs β₁ β₂
  have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
  have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
  have hγ0 : (β₁ + β₂) 0 = 0 := by simp [h10, h20]
  refine ⟨?_, fun x _ => ?_, isLBSB_univ h.contDiff₁ h.contDiff₂ h10 h20 fun _ => rfl,
    β₁ + β₂, h.contDiff₁.add h.contDiff₂, fun s hs => hA.2.2.1 h hs, fun p => ?_, ?_,
    fun V hV h0V => ?_⟩
  · rw [hc]; exact isBranchedB_of X2 _ hbr
  · -- the graphs through `x`, cut down to `U`
    have L := localBranchingStructure_sum_rn ![graph2 β₁, graph2 β₂] 1 (fun _ => one_pos)
      (fun i => (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂ i).1)
      (graphs2_isClosed h.contDiff₁.continuous h.contDiff₂.continuous) x
    refine ⟨{y | ∀ i, y ∈ ![graph2 β₁, graph2 β₂] i → x ∈ ![graph2 β₁, graph2 β₂] i}, ?_⟩
    have hL := isLBSB_of (localBranchingStructure_sum_rn ![graph2 β₁, graph2 β₂] 1
      (fun _ => one_pos) (fun i => (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂ i).1)
      (graphs2_isClosed h.contDiff₁.continuous h.contDiff₂.continuous) x)
    rw [hc]
    exact hL
  · rw [countB_eq_thetaGraphs, countB_eq_thetaGraphs]; exact heq p
  · refine isLBSB_univ contDiff_const (h.contDiff₁.add h.contDiff₂) rfl hγ0 fun y => ?_
    rw [countB_eq_thetaGraphs, countB_eq_thetaGraphs]; exact heq y
  · -- (c)
    have hall : ∀ (β γ : ℝ → ℝ), β 0 = 0 → γ 0 = 0 → ∀ k,
        (0 : Fin 2 → ℝ) ∈ ![graph2 β, graph2 γ] k := fun β γ hβ hγ k => by
      fin_cases k
      · exact hβ.symm
      · exact hγ.symm
    have huniv : ∀ (β γ : ℝ → ℝ), β 0 = 0 → γ 0 = 0 →
        {y : Fin 2 → ℝ | ∀ k, y ∈ ![graph2 β, graph2 γ] k →
          (0 : Fin 2 → ℝ) ∈ ![graph2 β, graph2 γ] k} = univ := fun β γ hβ hγ =>
      eq_univ_of_forall fun _ k _ => hall β γ hβ hγ k
    have key : ∀ i j : Fin 2, ![graphB β₁, graphB β₂] i ∩ V ≠
        ![graphB 0, graphB (β₁ + β₂)] j ∩ V := by
      intro i j hij
      refine hne V hV h0V ⟨i, hall β₁ β₂ h10 h20 i⟩ ⟨j, hall 0 (β₁ + β₂) rfl hγ0 j⟩ ?_
      change (![graph2 β₁, graph2 β₂] i ∩ {y : Fin 2 → ℝ | ∀ k, y ∈ ![graph2 β₁, graph2 β₂] k →
          (0 : Fin 2 → ℝ) ∈ ![graph2 β₁, graph2 β₂] k}) ∩ V =
        (![graph2 0, graph2 (β₁ + β₂)] j ∩ {y : Fin 2 → ℝ | ∀ k,
          y ∈ ![graph2 0, graph2 (β₁ + β₂)] k →
          (0 : Fin 2 → ℝ) ∈ ![graph2 0, graph2 (β₁ + β₂)] k}) ∩ V
      rw [huniv β₁ β₂ h10 h20, huniv 0 (β₁ + β₂) rfl hγ0, inter_univ, inter_univ]
      exact hij
    intro hpair
    have hmem : graphB β₁ ∩ V ∈ ({graphB 0 ∩ V, graphB (β₁ + β₂) ∩ V} : Set (Set _)) :=
      hpair ▸ mem_insert _ _
    rcases hmem with h1 | h1
    · exact key 0 0 h1
    · exact key 0 1 h1

/-! ### `B → A` -/

open Classical in
theorem thetaGraphs_apply' (β₁ β₂ : ℝ → ℝ) (p : Fin 2 → ℝ) :
    thetaGraphs β₁ β₂ p =
      (if p 1 = β₁ (p 0) then 1 else 0) + (if p 1 = β₂ (p 0) then 1 else 0) := by
  rw [thetaGraphs, Finset.sum_filter, Fin.sum_univ_two]
  rfl

theorem B_to_A : B → A := by
  intro hB
  -- `thetaGraphs_eq`, re-proved
  have hteq : ∀ {β₁ β₂ : ℝ → ℝ}, (∀ s, β₁ s = 0 ∨ β₂ s = 0) → ∀ p : Fin 2 → ℝ,
      thetaGraphs β₁ β₂ p = thetaGraphs 0 (β₁ + β₂) p := by
    intro β₁ β₂ h p
    rw [thetaGraphs_apply', thetaGraphs_apply']
    simp only [Pi.zero_apply, Pi.add_apply]
    rcases h (p 0) with h1 | h2
    · simp only [h1, zero_add]
    · simp only [h2, add_zero]
      rw [add_comm]
  -- `γ₂_pos`, re-proved
  have hpos : ∀ {β₁ β₂ : ℝ → ℝ}, Remark913Hyp β₁ β₂ → ∀ {s : ℝ}, s ≠ 0 → 0 < (β₁ + β₂) s := by
    intro β₁ β₂ h s hs
    rcases hs.lt_or_gt with hs | hs
    · rw [Pi.add_apply, h.eq_zero₁ s hs.le, zero_add]; exact h.pos₂ s hs
    · rw [Pi.add_apply, h.eq_zero₂ s hs.le, add_zero]; exact h.pos₁ s hs
  have hor : ∀ {β₁ β₂ : ℝ → ℝ}, Remark913Hyp β₁ β₂ → ∀ s, β₁ s = 0 ∨ β₂ s = 0 :=
    fun h s => (le_total s 0).imp (h.eq_zero₁ s) (h.eq_zero₂ s)
  refine ⟨⟨expNegInvGlue.contDiff, expNegInvGlue.contDiff.comp contDiff_neg,
      fun _ hs => expNegInvGlue.zero_of_nonpos hs, fun _ hs => expNegInvGlue.pos_of_pos hs,
      fun _ hs => expNegInvGlue.pos_of_pos (neg_pos.2 hs),
      fun _ hs => expNegInvGlue.zero_of_nonpos (neg_nonpos.2 hs)⟩,
    fun h p => hteq h p, fun h _ hs => hpos h hs, fun {β₁ β₂} h γ hγ => ?_,
    fun {β₁ β₂} h => ?_⟩
  · -- `eq_add_of_thetaGraphs_eq`, re-proved
    funext s
    by_contra hne
    have hp := hγ (curve2 (β₁ + β₂) s)
    rw [thetaGraphs_apply', thetaGraphs_apply'] at hp
    change ((if β₁ s + β₂ s = β₁ s then 1 else 0) + if β₁ s + β₂ s = β₂ s then 1 else 0 : ℚ) =
      (if β₁ s + β₂ s = 0 then 1 else 0) + (if β₁ s + β₂ s = γ s then 1 else 0) at hp
    have hne' : β₁ s + β₂ s ≠ γ s := fun h' => hne h'.symm
    rcases hor h s with h1 | h2
    · rw [h1, zero_add] at hp hne'
      rw [if_pos rfl, if_neg hne'] at hp
      linarith
    · rw [h2, add_zero] at hp hne'
      rw [if_pos rfl, if_neg hne'] at hp
      linarith
  · -- `remark_9_1_3_b`
    have hb := hB β₁ β₂ ⟨h.contDiff₁, h.contDiff₂, h.eq_zero₁, h.pos₁, h.pos₂, h.eq_zero₂⟩
    obtain ⟨hbr, hloc, -, -⟩ := hb
    rw [countB_eq_thetaGraphs] at hbr hloc
    refine ⟨isBranched_of X2 _ hbr, fun x hx => ?_, hteq (hor h), fun V hV h0V i j => ?_⟩
    · -- `1`-dimensional: the structure of `B` at `x`, with the dimension of graphs
      obtain ⟨U, hU⟩ := hloc x hx
      refine ⟨lbsOf X2 hU, fun k => ?_⟩
      change (rnPolyfold 2).IsSubmanifoldOfDim (![graphB β₁, graphB β₂] k.1 ∩ U) 1
      refine MPolyfold.IsSubmanifoldOfDim.inter_isOpen ?_ hU.1
      rcases k with ⟨k, -⟩
      fin_cases k
      · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₁
      · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₂
    · -- no sheet of the one structure agrees with a sheet of the other near `0` (re-proved)
      intro heq
      have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
      have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
      have hall : ∀ (β γ : ℝ → ℝ), β 0 = 0 → γ 0 = 0 → ∀ k,
          (0 : Fin 2 → ℝ) ∈ ![graph2 β, graph2 γ] k := fun β γ hβ hγ k => by
        fin_cases k
        · exact hβ.symm
        · exact hγ.symm
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      have key : ∀ y, y ∈ V → y ∈ ![graph2 β₁, graph2 β₂] i →
          y ∈ ![graph2 0, graph2 (β₁ + β₂)] j := fun y hyV hy => by
        have hmem : y ∈ (h.structureβ 0).M ⟨i, hi⟩ ∩ V :=
          ⟨⟨hy, fun k _ => hall β₁ β₂ h10 h20 k⟩, hyV⟩
        rw [heq] at hmem
        exact hmem.1.1
      clear heq hi hj
      obtain ⟨s, hs, hV1, hV1'⟩ := exists_curve2_mem h.contDiff₁.continuous h10 hV h0V
      obtain ⟨t, ht, hV2, hV2'⟩ := exists_curve2_mem h.contDiff₂.continuous h20 hV h0V
      obtain ⟨r, hr, hV0, hV0'⟩ := exists_curve2_mem (β := 0) continuous_const rfl hV h0V
      fin_cases i <;> fin_cases j
      · have : β₁ s = 0 := key _ hV1 rfl
        exact (h.pos₁ s hs).ne' this
      · have := key _ hV0' (h.eq_zero₁ (-r) (neg_nonpos.2 hr.le)).symm
        exact (hpos h (neg_ne_zero.2 hr.ne')).ne this
      · have : β₂ (-t) = 0 := key _ hV2' rfl
        exact (h.pos₂ (-t) (neg_neg_iff_pos.2 ht)).ne' this
      · have := key _ hV0 (h.eq_zero₂ r hr.le).symm
        exact (hpos h hr.ne').ne this

#rt_check_soft RoundTrip.V9_4.A_to_B [Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue,
  Polyfold.EpGroupoid.thetaGraphs_eq, Polyfold.EpGroupoid.Remark913Hyp.γ₂_pos,
  Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq, Polyfold.EpGroupoid.remark_9_1_3_b]
#rt_check_soft RoundTrip.V9_4.B_to_A [Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue,
  Polyfold.EpGroupoid.thetaGraphs_eq, Polyfold.EpGroupoid.Remark913Hyp.γ₂_pos,
  Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq, Polyfold.EpGroupoid.remark_9_1_3_b]
#rt_overlap RoundTrip.V9_4.B_to_A [Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue,
  Polyfold.EpGroupoid.thetaGraphs_eq, Polyfold.EpGroupoid.Remark913Hyp.γ₂_pos,
  Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq, Polyfold.EpGroupoid.remark_9_1_3_b]

end RoundTrip.V9_4
