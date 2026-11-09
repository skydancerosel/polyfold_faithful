import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_1

/-! Round trip for V9_1 (Definition 9.1.2, p. 402 [2017: Definition 9.1, p. 292]: branched
ep⁺-subgroupoids).

`A` is the conjunction of the types of the three listed theorems, universes at `0`:
`EpGroupoid.isBranchedEpSubgroupoid_zero` (`Θ = 0` is branched),
`EpGroupoid.isBranchedEpSubgroupoid_indicator` (the indicator of a point of `ℝⁿ` is branched) and
`rnPolyfold_isSmoothSubmanifold_singleton` (a point of `ℝⁿ` is a submanifold).  The listed
`IsFunctorial`, `supp`, `orbitSupp`, `LocalBranchingStructure`, `IsBranchedEpSubgroupoid` and
`localBranchingStructure_indicator` are definitions (vocabulary).

`B` says the project's `IsBranchedEpSubgroupoid` is the blind `IsBranchedB`.  It is proved
outright (`B_holds`): every field matches, except the properness of `Mᵢ → U(x)`, which is
Mathlib's (Bourbaki) `IsProperMap (inclusion _)` in the project and "compact sets have compact
preimages" (`IsProperInclB`) in `B`.  Both are equivalent to `Mᵢ` closed in `U(x)`:
`isProperMap_inclusion_iff'` (re-proved here, the project's lemma is not used), and
`properInclB_of_isClosed`, `isClosed_of_properInclB`; the last one uses that the object space is
metrizable (`MPolyfold.metrizableSpace`), so `U(x)` is sequential.  The universe of the index
type is `Type` on both sides.

* `A → B`: `B_holds`, without the hypothesis (`A` is a list of witnesses, `B` a definitional
  comparison).
* `B → A`: the zero functor and the indicator are shown to satisfy the blind `IsBranchedB` and
  transported through `B`; the singleton submanifold is re-proved outright (not a consequence of
  `B`). -/

namespace RoundTrip.V9_1
open Polyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator) ∧
  (type_of% @Polyfold.rnPolyfold_isSmoothSubmanifold_singleton)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isBranchedEpSubgroupoid_zero.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator,
    @Polyfold.rnPolyfold_isSmoothSubmanifold_singleton⟩

/-! ### Proper inclusions -/

section Proper
variable {Z : Type} [TopologicalSpace Z]

/-- The inclusion of `A ⊆ U` is proper (Mathlib) iff `A` is closed in `U`. -/
theorem isProperMap_inclusion_iff' {A U : Set Z} (h : A ⊆ U) :
    IsProperMap (inclusion h) ↔ IsClosed ((↑) ⁻¹' A : Set U) := by
  have hr : ((↑) ⁻¹' A : Set U) = range (inclusion h) := (range_inclusion h).symm
  rw [hr]
  exact ⟨fun hp => hp.isClosedMap.isClosed_range,
    fun hc => (Topology.IsClosedEmbedding.mk (Topology.IsEmbedding.inclusion h) hc).isProperMap⟩

/-- Closed in `U` implies the blind properness. -/
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

/-- In a metrizable space the blind properness implies closed in `U`. -/
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

/-! ### `B` holds -/

section Compare
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isBranchedB_of (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    IsBranchedB X Θ := by
  refine ⟨hΘ.nonneg, hΘ.isFunctorial, hΘ.support_subset, hΘ.paracompactSpace_orbitSupp,
    fun x hx => ?_⟩
  obtain ⟨L⟩ := hΘ.localBranching x hx
  exact ⟨L.ι, L.fintype, L.U, L.M, L.σ, L.isOpen_U, L.mem_U, fun i => ⟨L.subset_U i,
    L.isSmoothSubmanifold i, L.mem_M i,
    properInclB_of_isClosed ((isProperMap_inclusion_iff' _).1 (L.isProperMap i))⟩,
    L.σ_pos, L.eq_sum⟩

theorem isBranched_of (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (hΘ : IsBranchedB X Θ) :
    X.IsBranchedEpSubgroupoid Θ := by
  have := X.PObj.metrizableSpace
  obtain ⟨h1, h2, h3, h4, h5⟩ := hΘ
  refine ⟨h1, h2, h3, h4, fun x hx => ?_⟩
  obtain ⟨ι, inst, U, M, σ, hU, hxU, hM, hσ, hsum⟩ := h5 x hx
  exact ⟨@EpGroupoid.LocalBranchingStructure.mk _ _ _ _ _ _ _ _ X Θ x U hU hxU ι inst M
    (fun i => (hM i).1) (fun i => (hM i).2.1) (fun i => (hM i).2.2.1)
    (fun i => (isProperMap_inclusion_iff' _).2 (isClosed_of_properInclB (hM i).2.2.2))
    σ hσ hsum⟩

end Compare

theorem B_holds : B := fun _ _ _ _ _ _ _ _ X Θ => ⟨isBranchedB_of X Θ, isBranched_of X Θ⟩

theorem A_to_B : A → B := fun _ => B_holds

/-! ### `B → A` -/

/-- A point of `ℝⁿ` is a submanifold (re-proved outright). -/
theorem singleton_isSmoothSubmanifold (n : ℕ) (p : Fin n → ℝ) :
    (rnPolyfold n).IsSmoothSubmanifold {p} := by
  have hp : p ∈ (rnPolyfold n).smoothSet := by
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ p
  have hp1 : p ∈ (rnPolyfold n).levelSet 1 :=
    MPolyfold.smoothSet_subset_levelSet (P := rnPolyfold n) 1 hp
  intro a _
  refine ⟨univ, isOpen_univ, mem_univ a, fun _ => p,
    ⟨isScSmoothMap_const_of_mem_smoothSet hp, fun _ _ => mem_univ _, fun _ _ => rfl,
      fun _ _ => hp1, fun x₀ => ?_⟩, ?_⟩
  · refine isScSmoothMap_const_of_mem_smoothSet
      ((MPolyfold.mem_shift_smoothSet_iff ((rnPolyfold n).toLevelOne x₀ p)).2 ?_)
    rw [MPolyfold.levelVal_toLevelOne x₀ hp1]
    exact hp
  · ext y
    simp [eq_comm]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X => ?_, fun n p => ?_, singleton_isSmoothSubmanifold⟩
  · -- the zero functor
    refine (hB Obj Mor X 0).2 ⟨fun _ => le_rfl, fun _ => rfl,
      fun _ hx => (lt_irrefl (0 : ℚ) hx).elim, ?_, fun _ hx => (lt_irrefl (0 : ℚ) hx).elim⟩
    have h0 : suppB (0 : Obj → ℚ) = ∅ := eq_empty_iff_forall_notMem.2 fun _ hx => lt_irrefl (0 : ℚ) hx
    have hc : IsCompact (X.π '' suppB (0 : Obj → ℚ)) := by
      rw [h0, image_empty]; exact isCompact_empty
    have := isCompact_iff_compactSpace.1 hc
    infer_instance
  · -- the indicator of a point
    have hs : suppB (({p} : Set (Fin n → ℝ)).indicator (1 : (Fin n → ℝ) → ℚ)) = {p} := by
      ext y
      by_cases hy : y = p
      · subst hy; simp [suppB]
      · simp [suppB, hy]
    refine (hB _ _ (EpGroupoid.trivial (rnPolyfold n)) _).2 ⟨fun y => ?_, fun _ => rfl,
      fun y _ => ?_, ?_, fun y hy => ?_⟩
    · by_cases hy : y = p
      · subst hy; simp
      · simp [hy]
    · change y ∈ (rnPolyfold n).smoothSet
      rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ y
    · have hc : IsCompact ((EpGroupoid.trivial (rnPolyfold n)).π ''
          suppB (({p} : Set (Fin n → ℝ)).indicator (1 : (Fin n → ℝ) → ℚ))) := by
        rw [hs, image_singleton]; exact isCompact_singleton
      have := isCompact_iff_compactSpace.1 hc
      infer_instance
    · rw [hs] at hy
      rw [mem_singleton_iff] at hy
      subst hy
      refine ⟨Unit, inferInstance, univ, fun _ => {y}, fun _ => 1, isOpen_univ, mem_univ _,
        fun _ => ⟨subset_univ _, singleton_isSmoothSubmanifold n y, rfl, ?_⟩,
        fun _ => one_pos, fun z _ => ?_⟩
      · intro K _ _
        exact (finite_singleton y).subset inter_subset_right |>.isCompact
      · by_cases hz : z = y
        · subst hz; simp
        · simp [hz]

#rt_check RoundTrip.V9_1.A_to_B [Polyfold.EpGroupoid.isBranchedEpSubgroupoid_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator,
  Polyfold.rnPolyfold_isSmoothSubmanifold_singleton]
#rt_check RoundTrip.V9_1.B_to_A [Polyfold.EpGroupoid.isBranchedEpSubgroupoid_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator,
  Polyfold.rnPolyfold_isSmoothSubmanifold_singleton]
#rt_overlap RoundTrip.V9_1.B_to_A [Polyfold.EpGroupoid.isBranchedEpSubgroupoid_zero,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator,
  Polyfold.rnPolyfold_isSmoothSubmanifold_singleton]

end RoundTrip.V9_1
