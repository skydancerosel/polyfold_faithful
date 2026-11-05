import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_62

/-! Round trip for V2_62 (Theorem 2.55: Smirnov's metrization theorem).

`A` is the conjunction of the types of `Polyfold.metrizableSpace_of_locally` (Smirnov),
`Polyfold.metrizableSpace_of_partition`, `Polyfold.metrizableSpace_of_pullback`,
`Polyfold.cone_triangle` and `Polyfold.paracompactSpace_of_metrizableSpace`, with all universes
instantiated at `0`.  `truncDist` is a definition (vocabulary).

`A → B`: `B` is literally the type of `metrizableSpace_of_locally.{0}`.

`B → A`: Smirnov (`metrizableSpace_of_locally`) is `B`.  The partition form
(`metrizableSpace_of_partition`) follows from `B` once the space is shown to be Hausdorff and
paracompact, which the partition hypotheses give: `t2_of_partition` (separate in a `V_i`, or by the
values of `ρ_i`), `paracompact_of_partition` (refine the cover inside each metrizable, hence
paracompact, `V_i` and cut with `{ρ_i > 0}`; local finiteness comes from that of the supports).
The pull-back form follows from the partition form exactly as in the project (pull back a partition
of unity of `X`).  `cone_triangle` (an elementary real inequality) and
`paracompactSpace_of_metrizableSpace` (A. H. Stone, in Mathlib) are proved directly, without `B`. -/

namespace RoundTrip.V2_62
open Polyfold Set Filter Topology TopologicalSpace

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.metrizableSpace_of_locally.{0}) ∧
    (type_of% @Polyfold.metrizableSpace_of_partition.{0, 0}) ∧
    (type_of% @Polyfold.metrizableSpace_of_pullback.{0, 0}) ∧
    (type_of% @Polyfold.cone_triangle) ∧
    (type_of% @Polyfold.paracompactSpace_of_metrizableSpace.{0})

theorem A_holds : A :=
  ⟨@Polyfold.metrizableSpace_of_locally.{0}, @Polyfold.metrizableSpace_of_partition.{0, 0},
    @Polyfold.metrizableSpace_of_pullback.{0, 0}, @Polyfold.cone_triangle,
    @Polyfold.paracompactSpace_of_metrizableSpace.{0}⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ h
  exact hA.1 h

section Partition

variable {Y ι : Type} [TopologicalSpace Y] (V : ι → Set Y) (hVo : ∀ i, IsOpen (V i))
  [hm : ∀ i, MetrizableSpace (V i)] (ρ : ι → Y → ℝ) (hρc : ∀ i, Continuous (ρ i))
  (hsupp : ∀ i, tsupport (ρ i) ⊆ V i) (hpos : ∀ y, ∃ i, 0 < ρ i y)

include hVo hρc hsupp hpos in
/-- A space with a partition as in `metrizableSpace_of_partition` is Hausdorff. -/
theorem t2_of_partition : T2Space Y := by
  constructor
  intro x y hxy
  obtain ⟨i, hi⟩ := hpos x
  have hxV : x ∈ V i := hsupp i (subset_tsupport _ hi.ne')
  by_cases hyV : y ∈ V i
  · let _ := metrizableSpaceMetric (V i)
    have hne : (⟨x, hxV⟩ : V i) ≠ ⟨y, hyV⟩ := fun h => hxy (congrArg Subtype.val h)
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
    exact ⟨Subtype.val '' u, Subtype.val '' v, (hVo i).isOpenMap_subtype_val u hu,
      (hVo i).isOpenMap_subtype_val v hv, ⟨_, hxu, rfl⟩, ⟨_, hyv, rfl⟩,
      (disjoint_image_iff Subtype.val_injective).2 huv⟩
  · have hy0 : ρ i y = 0 := image_eq_zero_of_notMem_tsupport fun h => hyV (hsupp i h)
    refine ⟨{z | ρ i x / 2 < ρ i z}, {z | ρ i z < ρ i x / 2},
      isOpen_lt continuous_const (hρc i), isOpen_lt (hρc i) continuous_const, ?_, ?_, ?_⟩
    · change ρ i x / 2 < ρ i x; linarith
    · change ρ i y < ρ i x / 2; rw [hy0]; linarith
    · rw [Set.disjoint_left]
      intro z h1 h2
      change ρ i x / 2 < ρ i z at h1
      change ρ i z < ρ i x / 2 at h2
      linarith

include hVo hρc hsupp hpos in
/-- A space with a partition as in `metrizableSpace_of_partition` is paracompact: refine the
cover inside each (metrizable, hence paracompact) `V_i`, and cut the pieces with `{ρ_i > 0}`. -/
theorem paracompact_of_partition (hlf : LocallyFinite fun i => tsupport (ρ i)) :
    ParacompactSpace Y := by
  classical
  have hpc : ∀ i, ParacompactSpace (V i) := fun i => by
    let _ := metrizableSpaceMetric (V i); infer_instance
  refine ⟨fun α s hso hsc => ?_⟩
  have hcov : ∀ i, ⋃ a, (Subtype.val ⁻¹' s a : Set (V i)) = univ := fun i => by
    rw [← preimage_iUnion, hsc, preimage_univ]
  choose v hvo hvc hvlf hvs using fun i =>
    @precise_refinement α (V i) _ (hpc i) (fun a => Subtype.val ⁻¹' s a)
      (fun a => (hso a).preimage continuous_subtype_val) (hcov i)
  let t : ι × α → Set Y := fun p => Subtype.val '' v p.1 p.2 ∩ {y | 0 < ρ p.1 y}
  refine ⟨ι × α, t, fun p => ?_, ?_, ?_, fun p => ⟨p.2, ?_⟩⟩
  · exact ((hVo p.1).isOpenMap_subtype_val _ (hvo p.1 p.2)).inter
      (isOpen_lt continuous_const (hρc p.1))
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := hpos y
    have hyV : y ∈ V i := hsupp i (subset_tsupport _ hi.ne')
    have : (⟨y, hyV⟩ : V i) ∈ ⋃ a, v i a := by rw [hvc i]; exact mem_univ _
    obtain ⟨a, ha⟩ := mem_iUnion.1 this
    exact mem_iUnion.2 ⟨(i, a), ⟨_, ha, rfl⟩, hi⟩
  · intro y
    obtain ⟨N, hN, hNfin⟩ := hlf y
    have hM : ∀ i, ∃ M ∈ 𝓝 y, {a | (t (i, a) ∩ M).Nonempty}.Finite := by
      intro i
      by_cases hyV : y ∈ V i
      · obtain ⟨M, hM, hMfin⟩ := hvlf i ⟨y, hyV⟩
        refine ⟨Subtype.val '' M, (hVo i).isOpenMap_subtype_val.image_mem_nhds hM,
          hMfin.subset ?_⟩
        rintro a ⟨z, ⟨⟨w, hw, rfl⟩, -⟩, ⟨w', hw', hww'⟩⟩
        rw [Subtype.val_injective hww'] at hw'
        exact ⟨w, hw, hw'⟩
      · refine ⟨(tsupport (ρ i))ᶜ,
          (isClosed_tsupport _).isOpen_compl.mem_nhds fun h => hyV (hsupp i h), ?_⟩
        convert Set.finite_empty
        ext a
        simp only [mem_empty_iff_false, iff_false]
        rintro ⟨z, ⟨-, hz⟩, hz'⟩
        exact hz' (subset_tsupport _ (ne_of_gt hz))
    choose M hMn hMfin using hM
    refine ⟨N ∩ ⋂ i ∈ hNfin.toFinset, M i,
      inter_mem hN ((biInter_finset_mem _).2 fun i _ => hMn i), ?_⟩
    refine (hNfin.biUnion fun i _ => (hMfin i).image (fun a => (i, a))).subset ?_
    rintro ⟨i, a⟩ ⟨z, hzt, hzN, hzM⟩
    have hiN : i ∈ {i | (tsupport (ρ i) ∩ N).Nonempty} :=
      ⟨z, subset_tsupport _ (ne_of_gt hzt.2), hzN⟩
    refine mem_iUnion₂.2 ⟨i, hiN, ⟨a, ⟨z, hzt, ?_⟩, rfl⟩⟩
    exact mem_iInter₂.1 hzM i (hNfin.mem_toFinset.2 hiN)
  · rintro z ⟨⟨w, hw, rfl⟩, -⟩
    exact hvs p.1 p.2 hw

end Partition

/-- `B` gives the partition form `metrizableSpace_of_partition`. -/
theorem partition_of_B (hB : B) : type_of% @Polyfold.metrizableSpace_of_partition.{0, 0} := by
  intro Y _ ι V hVo hm ρ hρc _ hsupp hlf hpos
  have := t2_of_partition V hVo ρ hρc hsupp hpos
  have := paracompact_of_partition V hVo ρ hρc hsupp hpos hlf
  refine hB Y fun y => ?_
  obtain ⟨i, hi⟩ := hpos y
  exact ⟨V i, hVo i, hsupp i (subset_tsupport _ hi.ne'), hm i⟩

/-- `B` gives the pull-back form `metrizableSpace_of_pullback`. -/
theorem pullback_of_B (hB : B) : type_of% @Polyfold.metrizableSpace_of_pullback.{0, 0} := by
  intro Y _ X _ _ _ π hπ h
  choose U hUo hxU hUm using h
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUo
    fun x _ => mem_iUnion.2 ⟨x, hxU x⟩
  have : ∀ x, MetrizableSpace (π ⁻¹' U x) := hUm
  exact partition_of_B hB (fun x => π ⁻¹' U x) (fun x => (hUo x).preimage hπ)
    (fun x => f x ∘ π) (fun x => (f x).continuous.comp hπ) (fun x y => f.nonneg x (π y))
    (fun x => (tsupport_comp_subset_preimage _ hπ).trans (preimage_mono (hf x)))
    ((f.locallyFinite.closure.preimage_continuous hπ).subset fun x =>
      tsupport_comp_subset_preimage _ hπ)
    fun y => f.exists_pos (mem_univ (π y))

/-- The elementary inequality `cone_triangle`, proved directly (it does not involve `B`). -/
theorem cone_triangle' : type_of% @Polyfold.cone_triangle := by
  intro a b c dxy dyz dxz ha hb hc h0xy h0yz h1xz htri
  have habs : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
  rcases le_or_gt (min a c) b with hmb | hbm
  · rcases eq_or_lt_of_le (le_min ha hc) with hm0 | hmpos
    · rw [← hm0, zero_mul, add_zero]
      nlinarith [mul_nonneg (le_min ha hb) h0xy, mul_nonneg (le_min hb hc) h0yz]
    · have hbpos : 0 < b := lt_of_lt_of_le hmpos hmb
      have ht := htri hmpos hbpos
      have h1 : min a c ≤ min a b := le_min (min_le_left _ _) (le_trans (le_refl _) hmb)
      have h2 : min a c ≤ min b c := le_min hmb (min_le_right _ _)
      have h3 : min a c * dxz ≤ min a c * dxy + min a c * dyz := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left ht (le_min ha hc)
      have h4 : min a c * dxy ≤ min a b * dxy := mul_le_mul_of_nonneg_right h1 h0xy
      have h5 : min a c * dyz ≤ min b c * dyz := mul_le_mul_of_nonneg_right h2 h0yz
      linarith
  · have hab : min a b = b := min_eq_right (le_of_lt (lt_of_lt_of_le hbm (min_le_left _ _)))
    have hbc : min b c = b := min_eq_left (le_of_lt (lt_of_lt_of_le hbm (min_le_right _ _)))
    rw [hab, hbc]
    have hba : b ≤ a := le_of_lt (lt_of_lt_of_le hbm (min_le_left _ _))
    have hbc' : b ≤ c := le_of_lt (lt_of_lt_of_le hbm (min_le_right _ _))
    rw [abs_of_nonneg (sub_nonneg.2 hba), abs_of_nonpos (sub_nonpos.2 hbc')]
    have hsum : |a - c| + 2 * min a c = a + c := by
      rcases le_total a c with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0]
      nlinarith [mul_le_mul_of_nonneg_left h1xz (le_min ha hc)]
    · have ht := htri (lt_of_le_of_lt hb hbm) hbpos
      have h6 : (min a c - b) * dxz ≤ (min a c - b) * 1 :=
        mul_le_mul_of_nonneg_left h1xz (by linarith)
      have h7 : b * dxz ≤ b * (dxy + dyz) := mul_le_mul_of_nonneg_left ht hb
      nlinarith

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun h => hB _ h, partition_of_B hB, pullback_of_B hB, cone_triangle', ?_⟩
  intro X _ _
  let _ := metrizableSpaceMetric X
  infer_instance

#rt_check RoundTrip.V2_62.A_to_B [Polyfold.metrizableSpace_of_locally,
  Polyfold.metrizableSpace_of_partition, Polyfold.metrizableSpace_of_pullback,
  Polyfold.cone_triangle, Polyfold.paracompactSpace_of_metrizableSpace]
#rt_check RoundTrip.V2_62.B_to_A [Polyfold.metrizableSpace_of_locally,
  Polyfold.metrizableSpace_of_partition, Polyfold.metrizableSpace_of_pullback,
  Polyfold.cone_triangle, Polyfold.paracompactSpace_of_metrizableSpace]
#rt_overlap RoundTrip.V2_62.B_to_A [Polyfold.metrizableSpace_of_locally,
  Polyfold.metrizableSpace_of_partition, Polyfold.metrizableSpace_of_pullback,
  Polyfold.cone_triangle, Polyfold.paracompactSpace_of_metrizableSpace]

end RoundTrip.V2_62
