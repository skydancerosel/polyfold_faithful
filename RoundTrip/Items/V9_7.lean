import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_7

/-! Round trip for V9_7 (the restriction remark, p. 404, and Lemma 9.1.7, p. 405 [2017: Lemma 9.2,
p. 294]: symmetric local branching structures).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`LocalBranchingStructure.isClosed_M`, `isProperMap_inclusion_iff`, `IsFunctorial.apply_Φ`,
`EpGroupoid.lemma_9_1_7` (a symmetric structure with `U(x)` inside any given open `V ∋ x`) and
`EpGroupoid.lemma_9_1_7'`.  `LocalBranchingStructure.restrict`, `SymmetricBranchingStructure` and
`LocalBranchingStructure.symmetrize` are definitions (vocabulary).

Dictionary: the blind `IsBranchedB`, `IsLBSB` are the project's `IsBranchedEpSubgroupoid`,
`LocalBranchingStructure` (as in `RoundTrip/Items/V9_1.lean`: the properness of the inclusions is
"closed in `U`" on both sides, the blind ⇒ closed step using metrizability of the objects);
`B`'s `Gx X x` (a subtype) and the project's `X.Isotropy x` (a structure) are identified by
`toG`/`ofG`; a project `NaturalRep` gives `B`'s `IsNatRepData` (`natRepData_of`, as in
`RoundTrip/Items/V7_17.lean`), but not conversely (`NaturalRep` asks `U` connected).

* `A → B`.  (R) `B`'s restriction to an open `V ∋ x₀` with `x₀` arbitrary (the `Nᵢ` need not pass
  through a point) is more general than the project's `restrict` (`V ∋ x`, vocabulary only); it is
  proved directly (`Mᵢ ∩ V` is a submanifold, properness restricts).  (L) from `lemma_9_1_7'`.
  (C) `B` asks the construction `J = I × G_x` for an *arbitrary* natural-representation datum
  `IsNatRepData` on an open `U ⊆ U'` (not necessarily connected, inverses not given as `Φ(g⁻¹)`),
  while `A` only states the existence (`symmetrize` is vocabulary and takes a `NaturalRep`); the
  construction is re-proved here for `B`'s data (`constructionB`), following the project's
  `symmetrize`.
* `B → A`.  `lemma_9_1_7` from `B` (C) applied to a local branching structure and a natural
  representation `R ⊆ U(x) ∩ V` (Theorem 7.1); the symmetric structure is repackaged (the
  `G_x`-action on `I × G_x` from `B`'s `IsActionB`).  `lemma_9_1_7'` follows.  `isClosed_M`,
  `isProperMap_inclusion_iff` and `IsFunctorial.apply_Φ` are general facts, re-proved outright. -/

namespace RoundTrip.V9_7
open Polyfold EpGroupoid Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_M.{0}) ∧
  (type_of% @Polyfold.isProperMap_inclusion_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsFunctorial.apply_Φ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_1_7.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_1_7'.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_M.{0},
    @Polyfold.isProperMap_inclusion_iff.{0}, @Polyfold.EpGroupoid.IsFunctorial.apply_Φ.{0},
    @Polyfold.EpGroupoid.lemma_9_1_7.{0}, @Polyfold.EpGroupoid.lemma_9_1_7'.{0}⟩

/-! ### Proper inclusions (as in `RoundTrip/Items/V9_1.lean`) -/

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

end Proper

/-! ### Dictionary -/

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

variable {X : EpGroupoid Obj Mor} {x : Obj}

/-- The project's `G_x` element as `B`'s. -/
def toG (g : X.Isotropy x) : Gx X x := ⟨g.val, g.src_val, g.tgt_val⟩

/-- `B`'s `G_x` element as the project's. -/
def ofG (g : Gx X x) : X.Isotropy x := ⟨g.1, g.2.1, g.2.2⟩

/-- A project natural representation is `B`'s natural-representation datum. -/
theorem natRepData_of (R : X.NaturalRep x) :
    IsNatRepData X x R.U (fun g => R.Φ (ofG g)) (fun g => R.Γ (ofG g)) := by
  have hbij := R.bijOn_Γ
  refine ⟨fun g => ⟨_, R.isScDiffeoOn_Φ (ofG g)⟩, fun g h k hk y hy => ?_,
    fun g => R.isScSmoothOn_Γ (ofG g), fun g => R.Γ_self (ofG g),
    fun g y hy => ⟨R.src_Γ (ofG g) y hy, R.tgt_Γ (ofG g) y hy⟩, fun h hs ht => ?_, ?_⟩
  · have : ofG k = ofG g * ofG h := GroupoidStr.Isotropy.ext hk
    simp only [this]
    exact R.Φ_mul _ _ y hy
  · obtain ⟨g, hg, hu⟩ := R.existsUnique_Γ h hs ht
    exact ⟨toG g, hg, fun g' hg' => by
      have := hu (ofG g') hg'
      rw [← this]
      rfl⟩
  · refine ⟨fun p hp => hbij.mapsTo (show (ofG p.1, p.2) ∈ univ ×ˢ R.U from ⟨trivial, hp.2⟩),
      fun p hp q hq he => ?_, fun φ hφ => ?_⟩
    · have := hbij.injOn (show (ofG p.1, p.2) ∈ univ ×ˢ R.U from ⟨trivial, hp.2⟩)
        (show (ofG q.1, q.2) ∈ univ ×ˢ R.U from ⟨trivial, hq.2⟩) he
      exact Prod.ext (Subtype.ext (congrArg GroupoidStr.Isotropy.val (Prod.ext_iff.1 this).1))
        (Prod.ext_iff.1 this).2
    · obtain ⟨q, hq, hqe⟩ := hbij.surjOn hφ
      exact ⟨(toG q.1, q.2), ⟨trivial, hq.2⟩, hqe⟩

end Compare

/-! ### (R): the restriction, re-proved for an arbitrary `x₀` -/

theorem restrictB : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) (ι : Type) [Fintype ι] (U : Set Obj)
    (M : ι → Set Obj) (σ : ι → ℚ), IsLBSB X Θ x U M σ →
      ∀ x₀ ∈ U, ∀ V : Set Obj, IsOpen V → x₀ ∈ V → V ⊆ U →
        IsLocalRepB X Θ V (fun i => M i ∩ V) σ := by
  intro Obj Mor _ _ _ _ _ _ X Θ x ι _ U M σ h x₀ _ V hV _ hVU
  obtain ⟨-, -, hM, hσ, hsum⟩ := h
  refine ⟨hV, fun i => ⟨inter_subset_right, (hM i).2.1.inter_isOpen hV, fun K hKV hK => ?_⟩, hσ,
    fun y hy => ?_⟩
  · have : K ∩ (M i ∩ V) = K ∩ M i := by
      ext z
      constructor
      · rintro ⟨hz, hzM, -⟩; exact ⟨hz, hzM⟩
      · rintro ⟨hz, hzM⟩; exact ⟨hz, hzM, hKV hz⟩
    rw [this]
    exact (hM i).2.2.2 K (hKV.trans hVU) hK
  · rw [hsum y (hVU hy)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp [hy]

/-! ### (C): the construction `J = I × G_x`, re-proved for `B`'s data -/

open Classical in
theorem constructionB : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), IsBranchedB X Θ →
      ∀ (x : Obj) [Fintype (Gx X x)] (ι : Type) [Fintype ι] (U' : Set Obj)
        (M : ι → Set Obj) (σ : ι → ℚ), IsLBSB X Θ x U' M σ →
        ∀ (U : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor),
          IsOpen U → x ∈ U → U ⊆ U' → IsNatRepData X x U Φ Γ →
          IsSymB X Θ x U Φ Γ (fun j : ι × Gx X x => Φ j.2 '' (M j.1 ∩ U))
            (fun j => σ j.1 / (Fintype.card (Gx X x) : ℚ))
            (fun h j => (j.1, mulGx X x h j.2)) := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x _ ι _ U' M σ hL U Φ Γ hUo hxU hUU' hR
  have := X.PObj.metrizableSpace
  have hR0 := hR
  obtain ⟨hdiff, hmul, -, hself, hst, -, -⟩ := hR0
  choose ψ hψ using hdiff
  obtain ⟨-, -, hM, hσ, hsum⟩ := hL
  have hfun : ∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ) := hΘ.2.1
  have hΦx : ∀ g, Φ g x = x := fun g => by
    rw [← (hst g x hxU).2, hself g]; exact g.2.2
  have hmemΦ : ∀ g (A : Set Obj), A ⊆ U → ∀ y ∈ U, (y ∈ Φ g '' A ↔ ψ g y ∈ A) := by
    intro g A hA y hy
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [(hψ g).left_inv a (hA ha)]; exact ha
    · intro h; exact ⟨_, h, (hψ g).right_inv y hy⟩
  have hΘψ : ∀ g, ∀ y ∈ U, Θ (ψ g y) = Θ y := fun g y hy => by
    have hyU : ψ g y ∈ U := (hψ g).mapsTo_inv hy
    have h := hfun (Γ g (ψ g y))
    rw [(hst g _ hyU).1, (hst g _ hyU).2, (hψ g).right_inv y hy] at h
    exact h
  have hne : Nonempty (Gx X x) := ⟨⟨X.unit x, X.src_unit x, X.tgt_unit x⟩⟩
  have hcard : (Fintype.card (Gx X x) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨hR, ⟨hUo, hxU, fun j => ⟨?_, ?_, ?_, ?_⟩, fun j => div_pos (hσ j.1)
    (Nat.cast_pos.2 Fintype.card_pos), fun y hy => ?_⟩, ⟨fun g h k hk j => ?_, fun e he j => ?_⟩,
    fun g j => ?_, fun _ _ => rfl⟩
  · rintro _ ⟨a, ha, rfl⟩; exact (hψ j.2).mapsTo ha.2
  · exact ((hM j.1).2.1.inter_isOpen hUo).image_of_isScDiffeoOn (hψ j.2) inter_subset_right
  · exact ⟨x, ⟨(hM j.1).2.2.1, hxU⟩, hΦx j.2⟩
  · refine properInclB_of_isClosed ?_
    have hc1 : IsClosed ((↑) ⁻¹' M j.1 : Set U') := isClosed_of_properInclB (hM j.1).2.2.2
    have hc2 : IsClosed ((↑) ⁻¹' M j.1 : Set U) := hc1.preimage (continuous_inclusion hUU')
    have hc3 := hc2.preimage
      ((hψ j.2).isScSmoothOn_inv.continuousOn.mapsToRestrict (hψ j.2).mapsTo_inv)
    convert hc3 using 1
    ext y
    simp only [mem_preimage, MapsTo.val_restrict_apply]
    rw [hmemΦ j.2 _ inter_subset_right y y.2]
    exact ⟨fun h => h.1, fun h => ⟨h, (hψ j.2).mapsTo_inv y.2⟩⟩
  · -- the sum formula
    have hg : ∀ g : Gx X x, (∑ i : ι, if y ∈ Φ g '' (M i ∩ U) then
        σ i / (Fintype.card (Gx X x) : ℚ) else 0) = Θ y / Fintype.card (Gx X x) := by
      intro g
      have hy' : ψ g y ∈ U := (hψ g).mapsTo_inv hy
      rw [← hΘψ g y hy, hsum _ (hUU' hy'), Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hmemΦ g _ inter_subset_right y hy]
      by_cases h : ψ g y ∈ M i
      · simp [h, hy']
      · simp [h]
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    simp only [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · -- the action axioms
    refine Prod.ext rfl (Subtype.ext ?_)
    change X.comp k.1 j.2.1 = X.comp g.1 (X.comp h.1 j.2.1)
    rw [hk]
    exact X.comp_assoc g.1 h.1 j.2.1 (g.2.1.trans h.2.2.symm) (h.2.1.trans j.2.2.2.symm)
  · refine Prod.ext rfl (Subtype.ext ?_)
    change X.comp e.1 j.2.1 = j.2.1
    rw [he]
    exact GroupoidStr.unit_comp_of_eq (G := X.toGroupoidStr) j.2.2.2
  · -- `h ∗ M_{(i,g)} = M_{(i,hg)}`
    change Φ g '' (Φ j.2 '' (M j.1 ∩ U)) = Φ (mulGx X x g j.2) '' (M j.1 ∩ U)
    rw [image_image]
    exact image_congr fun y hy => (hmul g j.2 (mulGx X x g j.2) rfl y hy.2).symm

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA
  refine ⟨restrictB, fun Obj Mor _ _ _ _ _ _ X Θ hΘ x hx => ?_, constructionB⟩
  obtain ⟨S, hU, himg, hσ, -⟩ := hA.2.2.2.2 (isBranched_of X Θ hΘ) hx
  refine ⟨S.U, fun g => S.rep.Φ (ofG g), fun g => S.rep.Γ (ofG g), S.ι, S.fintype, S.M, S.σ,
    fun g i => ofG g • i, ?_, isLBSB_of S.toLocalBranchingStructure, ⟨?_, ?_⟩,
    fun g i => himg (ofG g) i, fun g i => hσ (ofG g) i⟩
  · rw [hU]; exact natRepData_of S.rep
  · intro g h k hk i
    have : ofG k = ofG g * ofG h := GroupoidStr.Isotropy.ext hk
    show ofG k • i = ofG g • (ofG h • i)
    rw [this, mul_smul]
  · intro e he i
    have : ofG e = 1 := GroupoidStr.Isotropy.ext he
    show ofG e • i = i
    rw [this, one_smul]

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  -- Lemma 9.1.7 from `B` (C)
  have h717 : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {Θ : Obj → ℚ}, X.IsBranchedEpSubgroupoid Θ → ∀ {x : Obj}, x ∈ supp Θ →
      ∀ {V : Set Obj}, IsOpen V → x ∈ V → ∃ S : X.SymmetricBranchingStructure Θ x, S.U ⊆ V := by
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ x hx V hV hxV
    obtain ⟨L⟩ := hΘ.localBranching x hx
    obtain ⟨R, hR⟩ := theorem_7_1 X x (L.isOpen_U.inter hV) ⟨L.mem_U, hxV⟩
    have : Finite (Gx X x) :=
      Finite.of_equiv (X.Isotropy x) ⟨toG, ofG, fun _ => rfl, fun _ => rfl⟩
    let _ : Fintype (Gx X x) := Fintype.ofFinite _
    have hS := hB.2.2 Obj Mor X Θ (isBranchedB_of X Θ hΘ) x L.ι L.U L.M L.σ (isLBSB_of L) R.U
      (fun g => R.Φ (ofG g)) (fun g => R.Γ (ofG g)) R.isOpen_U R.mem_U (fun y hy => (hR hy).1)
      (natRepData_of R)
    obtain ⟨-, hLB, hact, himg, hσ⟩ := hS
    let _inst : MulAction (X.Isotropy x) (L.ι × Gx X x) :=
      { smul := fun g j => (j.1, mulGx X x (toG g) j.2)
        one_smul := fun j => hact.2 (toG 1) rfl j
        mul_smul := fun g h j => hact.1 (toG g) (toG h) (toG (g * h)) rfl j }
    exact ⟨@SymmetricBranchingStructure.mk _ _ _ _ _ _ _ _ X Θ x (lbsOf X hLB) R rfl _inst
      (fun g i => himg (toG g) i) (fun g i => hσ (toG g) i), fun y hy => (hR hy).2⟩
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ {X Θ x} L i =>
      (isProperMap_inclusion_iff' (L.subset_U i)).1 (L.isProperMap i),
    fun {Z} _ {A U} h => isProperMap_inclusion_iff' h,
    fun {Obj Mor} _ _ _ _ _ _ {X Θ} hΘ {x} R g {y} hy => ?_, h717,
    fun {Obj Mor} _ _ _ _ _ _ {X Θ} hΘ {x} hx => ?_⟩
  · -- `IsFunctorial.apply_Φ`, re-proved
    have h := hΘ (R.Γ g y)
    rw [R.src_Γ g y hy, R.tgt_Γ g y hy] at h
    exact h.symm
  · -- `lemma_9_1_7'`
    obtain ⟨S, -⟩ := h717 hΘ hx isOpen_univ (mem_univ x)
    exact ⟨S, S.U_eq, S.image_M, S.σ_smul, S.eq_sum⟩

#rt_check RoundTrip.V9_7.A_to_B [Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_M,
  Polyfold.isProperMap_inclusion_iff, Polyfold.EpGroupoid.IsFunctorial.apply_Φ,
  Polyfold.EpGroupoid.lemma_9_1_7, Polyfold.EpGroupoid.lemma_9_1_7']
#rt_check RoundTrip.V9_7.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_M,
  Polyfold.isProperMap_inclusion_iff, Polyfold.EpGroupoid.IsFunctorial.apply_Φ,
  Polyfold.EpGroupoid.lemma_9_1_7, Polyfold.EpGroupoid.lemma_9_1_7']
#rt_overlap RoundTrip.V9_7.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_M,
  Polyfold.isProperMap_inclusion_iff, Polyfold.EpGroupoid.IsFunctorial.apply_Φ,
  Polyfold.EpGroupoid.lemma_9_1_7, Polyfold.EpGroupoid.lemma_9_1_7']

end RoundTrip.V9_7
