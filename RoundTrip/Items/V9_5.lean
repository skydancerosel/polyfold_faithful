import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_5

/-! Round trip for V9_5 (Lemma 9.1.5, p. 403 [2017: Lemma 9.1, p. 293]: `|supp(Θ)|` is locally
closed).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`EpGroupoid.preimage_π_orbitSupp` (`supp Θ` is saturated for a functor `Θ`),
`LocalBranchingStructure.mem_supp_iff`, `LocalBranchingStructure.isClosed_preimage_val_supp`,
`EpGroupoid.isLocallyClosed_supp` (`supp Θ` locally closed in `X`) and
`EpGroupoid.lemma_9_1_5` (`|supp Θ|` locally closed in `|X|`).

Dictionary: the blind `IsBranchedB` is the project's `IsBranchedEpSubgroupoid` (the comparison of
`RoundTrip/Items/V9_1.lean`, repeated here: the only non-literal point is the properness of the
inclusions, both equivalent to `Mᵢ` closed in `U(x)`, using metrizability of the objects for the
blind ⇒ closed step).  `π '' suppB Θ` is `orbitSupp Θ` by definition.

* `A → B`: the blind hypothesis is converted (`isBranched_of`) and `lemma_9_1_5` applied.
* `B → A`: `lemma_9_1_5` is `B` after the (easy) conversion `isBranchedB_of`;
  `isLocallyClosed_supp` follows from `B` too, as `π⁻¹ |supp Θ| = supp Θ` and `π` is continuous.
  The three auxiliary facts (`preimage_π_orbitSupp`, `mem_supp_iff`,
  `isClosed_preimage_val_supp`) are general statements about functors and local branching
  structures, not consequences of `B`; they are re-proved outright. -/

namespace RoundTrip.V9_5
open Polyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.preimage_π_orbitSupp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.mem_supp_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_preimage_val_supp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isLocallyClosed_supp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_1_5.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.preimage_π_orbitSupp.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.mem_supp_iff.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_preimage_val_supp.{0},
    @Polyfold.EpGroupoid.isLocallyClosed_supp.{0}, @Polyfold.EpGroupoid.lemma_9_1_5.{0}⟩

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

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X Θ hΘ => hA.2.2.2.2 (isBranched_of X Θ hΘ)

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  -- the saturation of `supp Θ` (re-proved)
  have hsat : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {Θ : Obj → ℚ}, X.IsFunctorial Θ → X.π ⁻¹' X.orbitSupp Θ = EpGroupoid.supp Θ := by
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ
    ext y
    constructor
    · rintro ⟨a, ha, hay⟩
      obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
      change 0 < Θ (X.tgt φ)
      rw [← hΘ φ]
      exact ha
    · intro hy
      exact ⟨y, hy, rfl⟩
  -- `supp Θ ∩ U(x) = ⋃ Mᵢ` (re-proved)
  have hmem : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {Θ : Obj → ℚ} {x : Obj} (L : X.LocalBranchingStructure Θ x) {y : Obj}, y ∈ L.U →
      (y ∈ EpGroupoid.supp Θ ↔ ∃ i, y ∈ L.M i) := by
    intro Obj Mor _ _ _ _ _ _ X Θ x L y hy
    change 0 < Θ y ↔ _
    rw [L.eq_sum y hy]
    constructor
    · intro h
      by_contra hne
      simp only [not_exists] at hne
      simp [hne] at h
    · rintro ⟨i, hi⟩
      exact Finset.sum_pos' (fun j _ => (L.σ_pos j).le) ⟨i, by simp [hi], L.σ_pos i⟩
  refine ⟨fun hΘ => hsat hΘ, fun {_ _} _ _ _ _ _ _ {_ _ _} L {_} hy => hmem L hy, fun {Obj Mor} _ _ _ _ _ _ X Θ x L => ?_,
    fun {Obj Mor} _ _ _ _ _ _ X Θ hΘ => ?_, fun {Obj Mor} _ _ _ _ _ _ X Θ hΘ =>
      hB Obj Mor X Θ (isBranchedB_of X Θ hΘ)⟩
  · -- `supp Θ ∩ U(x)` is closed in `U(x)` (re-proved)
    have h : ((↑) ⁻¹' EpGroupoid.supp Θ : Set L.U) =
        ⋃ i, range (inclusion (L.subset_U i)) := by
      ext ⟨y, hy⟩
      simp only [mem_preimage, mem_iUnion, mem_range, hmem L hy]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, ⟨y, hi⟩, rfl⟩
      · rintro ⟨i, ⟨z, hz⟩, hzy⟩
        have h' : z = y := congrArg Subtype.val hzy
        exact ⟨i, h' ▸ hz⟩
    rw [h]
    exact isClosed_iUnion_of_finite fun i => (L.isProperMap i).isClosedMap.isClosed_range
  · -- `supp Θ` is locally closed in `X`: the preimage of `|supp Θ|`
    have h := (hB Obj Mor X Θ (isBranchedB_of X Θ hΘ)).preimage X.continuous_π
    change IsLocallyClosed (X.π ⁻¹' X.orbitSupp Θ) at h
    rwa [hsat hΘ.isFunctorial] at h

#rt_check RoundTrip.V9_5.A_to_B [Polyfold.EpGroupoid.preimage_π_orbitSupp,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_supp_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_preimage_val_supp,
  Polyfold.EpGroupoid.isLocallyClosed_supp, Polyfold.EpGroupoid.lemma_9_1_5]
#rt_check RoundTrip.V9_5.B_to_A [Polyfold.EpGroupoid.preimage_π_orbitSupp,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_supp_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_preimage_val_supp,
  Polyfold.EpGroupoid.isLocallyClosed_supp, Polyfold.EpGroupoid.lemma_9_1_5]
#rt_overlap RoundTrip.V9_5.B_to_A [Polyfold.EpGroupoid.preimage_π_orbitSupp,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_supp_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.isClosed_preimage_val_supp,
  Polyfold.EpGroupoid.isLocallyClosed_supp, Polyfold.EpGroupoid.lemma_9_1_5]

end RoundTrip.V9_5
