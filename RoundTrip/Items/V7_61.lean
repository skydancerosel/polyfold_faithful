import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_61

/-!
Round trip for V7_61 (Proposition 7.14: closed subsets of `|X|`).

`A` is the conjunction of the types of the eight theorems listed for the item, universes at `0`
(for `isProperSubset_iUnion_of_locallyFinite` also the index universe: `ι : Type`):
`isClosed_saturation_of_isProperSubset`, `proposition_7_14_one`, `IsProperSubset.of_subset`,
`IsProperSubset.union`, `isProperSubset_iUnion_of_locallyFinite`, `isProperSubset_of_isCompact`,
`exists_hasPropernessProperty_subset`, `proposition_7_14_two` (with
`[ParacompactSpace X.OrbitSpace]` as an instance argument).  `B` is the text's (1) and (2).

* `A → B`: (1) is `proposition_7_14_one`, (2) is `proposition_7_14_two` with the instance.
* `B → A`: `proposition_7_14_one`, `proposition_7_14_two` and the closedness of the saturation
  `π⁻¹(π(Q))` (preimage of the closed `π(Q)` under the continuous `π`) come from `B`.  The other
  five conjuncts are auxiliary lemmas of the project's proof that `B` does not state; they are
  re-proved here without `B`, from the compact-set form `isProperSubset_iff_isCompact` (item
  V7_59), `isProperSubset_biUnion`, the generic `isProperMap_domRestrict_of_subset_of_isClosed`
  and the field `exists_isProperMap` of `X`.
-/

namespace RoundTrip.V7_61
open Polyfold Set Topology

/-- The project's Proposition 7.14 and its auxiliary lemmas, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_14_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsProperSubset.of_subset.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsProperSubset.union.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.isProperSubset_of_isCompact.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_hasPropernessProperty_subset.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_14_two.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset.{0},
   @Polyfold.EpGroupoid.proposition_7_14_one.{0},
   @Polyfold.EpGroupoid.IsProperSubset.of_subset.{0},
   @Polyfold.EpGroupoid.IsProperSubset.union.{0},
   @Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite.{0, 0},
   @Polyfold.EpGroupoid.isProperSubset_of_isCompact.{0},
   @Polyfold.EpGroupoid.exists_hasPropernessProperty_subset.{0},
   @Polyfold.EpGroupoid.proposition_7_14_two.{0}⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  refine ⟨fun Q hQ => hA.2.1 X hQ, fun hpc A => ?_⟩
  exact @hA.2.2.2.2.2.2.2 Obj Mor _ _ _ _ _ _ X hpc A

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- A closed subset of a proper set is proper (re-proved from the generic lemma). -/
theorem of_subset' {X : EpGroupoid Obj Mor} {Q Q' : Set Obj} (hQ : X.IsProperSubset Q)
    (hQ'Q : Q' ⊆ Q) (hQ' : IsClosed Q') : X.IsProperSubset Q' :=
  isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src hQ hQ'Q hQ'

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the saturation `π⁻¹(π(Q))` is closed
    intro Obj Mor _ _ _ _ _ _ X Q hQ
    exact ((hB Obj Mor X).1 Q hQ).preimage X.continuous_π
  · intro Obj Mor _ _ _ _ _ _ X Q hQ
    exact (hB Obj Mor X).1 Q hQ
  · intro Obj Mor _ _ _ _ _ _ X Q Q' hQ hQ'Q hQ'
    exact of_subset' hQ hQ'Q hQ'
  · intro Obj Mor _ _ _ _ _ _ X Q Q' hQ hQ'
    rw [EpGroupoid.isProperSubset_iff_isCompact] at hQ hQ' ⊢
    intro K hK
    rw [preimage_union, union_inter_distrib_right]
    exact (hQ K hK).union (hQ' K hK)
  · intro Obj Mor _ _ _ _ _ _ X ι Q hQ hlf
    rw [EpGroupoid.isProperSubset_iff_isCompact]
    intro K hK
    have hfin := hlf.finite_nonempty_inter_compact (hK.image X.continuous_π)
    have heq : X.src ⁻¹' (⋃ i, Q i) ∩ X.tgt ⁻¹' K =
        ⋃ i ∈ {i | (X.π '' Q i ∩ X.π '' K).Nonempty}, X.src ⁻¹' Q i ∩ X.tgt ⁻¹' K := by
      ext φ
      simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨⟨i, hi⟩, hK'⟩
        exact ⟨i, ⟨X.π (X.src φ), mem_image_of_mem _ hi,
          X.π_src_eq_π_tgt φ ▸ mem_image_of_mem _ hK'⟩, hi, hK'⟩
      · rintro ⟨i, -, hi, hK'⟩
        exact ⟨⟨i, hi⟩, hK'⟩
    rw [heq]
    exact hfin.isCompact_biUnion fun i _ => (X.isProperSubset_iff_isCompact).1 (hQ i) K hK
  · intro Obj Mor _ _ _ _ _ _ X K hK
    have hV : ∀ x, ∃ V, x ∈ V ∧ X.HasPropernessProperty V := fun x => by
      obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
      exact ⟨V, hxV, hVo, hV⟩
    choose V hxV hV using hV
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover V (fun x => (hV x).1)
      fun x _ => mem_iUnion.2 ⟨x, hxV x⟩
    have heq : K = ⋃ x ∈ t, K ∩ closure (V x) := by
      refine Subset.antisymm (fun y hy => ?_) (iUnion₂_subset fun _ _ => inter_subset_left)
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
      exact mem_iUnion₂.2 ⟨x, hx, hy, subset_closure hyx⟩
    rw [heq]
    exact EpGroupoid.isProperSubset_biUnion t.finite_toSet fun x _ =>
      of_subset' (hV x).2 inter_subset_right (hK.isClosed.inter isClosed_closure)
  · intro Obj Mor _ _ _ _ _ _ X x W hW
    obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
    exact ⟨V ∩ W', ⟨hxV, hxW'⟩, inter_subset_right.trans hW'W, hVo.inter hW'o,
      of_subset' hV (closure_mono inter_subset_left) isClosed_closure⟩
  · intro Obj Mor _ _ _ _ _ _ X hpc A
    exact (hB Obj Mor X).2 hpc A

#rt_check RoundTrip.V7_61.A_to_B [Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset,
  Polyfold.EpGroupoid.proposition_7_14_one, Polyfold.EpGroupoid.IsProperSubset.of_subset,
  Polyfold.EpGroupoid.IsProperSubset.union,
  Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite,
  Polyfold.EpGroupoid.isProperSubset_of_isCompact,
  Polyfold.EpGroupoid.exists_hasPropernessProperty_subset, Polyfold.EpGroupoid.proposition_7_14_two]
#rt_check RoundTrip.V7_61.B_to_A [Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset,
  Polyfold.EpGroupoid.proposition_7_14_one, Polyfold.EpGroupoid.IsProperSubset.of_subset,
  Polyfold.EpGroupoid.IsProperSubset.union,
  Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite,
  Polyfold.EpGroupoid.isProperSubset_of_isCompact,
  Polyfold.EpGroupoid.exists_hasPropernessProperty_subset, Polyfold.EpGroupoid.proposition_7_14_two]
#rt_overlap RoundTrip.V7_61.B_to_A [Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset,
  Polyfold.EpGroupoid.proposition_7_14_one, Polyfold.EpGroupoid.IsProperSubset.of_subset,
  Polyfold.EpGroupoid.IsProperSubset.union,
  Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite,
  Polyfold.EpGroupoid.isProperSubset_of_isCompact,
  Polyfold.EpGroupoid.exists_hasPropernessProperty_subset, Polyfold.EpGroupoid.proposition_7_14_two]
#rt_overlap RoundTrip.V7_61.A_to_B [Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset,
  Polyfold.EpGroupoid.proposition_7_14_one, Polyfold.EpGroupoid.IsProperSubset.of_subset,
  Polyfold.EpGroupoid.IsProperSubset.union,
  Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite,
  Polyfold.EpGroupoid.isProperSubset_of_isCompact,
  Polyfold.EpGroupoid.exists_hasPropernessProperty_subset, Polyfold.EpGroupoid.proposition_7_14_two]

end RoundTrip.V7_61
