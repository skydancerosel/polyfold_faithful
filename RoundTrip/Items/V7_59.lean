import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_59

/-!
Round trip for V7_59 (Definition 7.17: proper subsets and the properness property).

`A` is the conjunction of the types of the four theorems listed with the definitions
`IsProperSubset`, `HasPropernessProperty` (universes at `0`):
`exists_hasPropernessProperty` (Definition 7.3 (3) in the vocabulary of Definition 7.17),
`HasPropernessProperty.mono`, `isProperSubset_iff_isCompact` (proper iff `s⁻¹(Q) ∩ t⁻¹(K)` is
compact for compact `K`) and `isProperSubset_iff_exists_tendsto_subseq` (the sequential form for
closed `Q`).  `B` says that the project's definitions agree with the classical notion
"continuous with compact preimages of compact sets" (`IsProperT`).

* `A → B`: the third conjunct of `A` plus the identification of compact subsets of the subtype
  `s⁻¹(Q)` with compact subsets of `𝐗` (an embedding) and the continuity of `t`.
* `B → A`: the third conjunct is `B` read the other way; `mono` follows from `B` (a closed subset
  of a compact set is compact); `exists_hasPropernessProperty` is the field `exists_isProperMap`
  of `X` (not from `B`); the sequential form is the project lemma
  `MPolyfold.isProperMap_domRestrict_iff_of_isClosed` (not from `B`).
-/

namespace RoundTrip.V7_59
open Polyfold Set

/-- The project's Definition 7.17 theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.exists_hasPropernessProperty.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.HasPropernessProperty.mono.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isProperSubset_iff_isCompact.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.exists_hasPropernessProperty.{0},
   @Polyfold.EpGroupoid.HasPropernessProperty.mono.{0},
   @Polyfold.EpGroupoid.isProperSubset_iff_isCompact.{0},
   @Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- Compact preimages under `t : s⁻¹(Q) → X` are the compact sets `s⁻¹(Q) ∩ t⁻¹(K)`. -/
theorem isCompact_domRestrict_preimage_iff (X : EpGroupoid Obj Mor) (Q K : Set Obj) :
    IsCompact ((X.src ⁻¹' Q).domRestrict X.tgt ⁻¹' K) ↔
      IsCompact (X.src ⁻¹' Q ∩ X.tgt ⁻¹' K) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, ← Subtype.image_preimage_coe]
  rfl

/-- `IsProperT` in the compact-set form. -/
theorem isProperT_iff (X : EpGroupoid Obj Mor) (Q : Set Obj) :
    IsProperT X Q ↔ ∀ K, IsCompact K → IsCompact (X.src ⁻¹' Q ∩ X.tgt ⁻¹' K) := by
  unfold IsProperT
  simp only [isCompact_domRestrict_preimage_iff]
  exact ⟨fun h => h.2, fun h => ⟨X.continuous_tgt.comp continuous_subtype_val, h⟩⟩

end

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  have h1 : ∀ Q : Set Obj, X.IsProperSubset Q ↔ IsProperT X Q := fun Q =>
    (hA.2.2.1 X).trans (isProperT_iff X Q).symm
  exact ⟨h1, fun U hU => ⟨fun h => (h1 _).1 h.2, fun h => ⟨hU, (h1 _).2 h⟩⟩⟩

theorem B_to_A : B → A := by
  intro hB
  have hC : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Q : Set Obj), X.IsProperSubset Q ↔
        ∀ K, IsCompact K → IsCompact (X.src ⁻¹' Q ∩ X.tgt ⁻¹' K) := fun X Q =>
    ((hB _ _ X).1 Q).trans (isProperT_iff X Q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x
    obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
    exact ⟨V, hxV, hVo, hV⟩
  · intro Obj Mor _ _ _ _ _ _ X V V' hV hV' hV'V
    refine ⟨hV', (hC X _).2 fun K hK => ?_⟩
    refine ((hC X _).1 hV.2 K hK).of_isClosed_subset ?_ ?_
    · exact (isClosed_closure.preimage X.continuous_src).inter
        (hK.isClosed.preimage X.continuous_tgt)
    · exact inter_subset_inter_left _ (preimage_mono (closure_mono hV'V))
  · intro Obj Mor _ _ _ _ _ _ X Q
    exact hC X Q
  · intro Obj Mor _ _ _ _ _ _ X Q hQ
    exact MPolyfold.isProperMap_domRestrict_iff_of_isClosed X.PMor X.PObj X.continuous_src
      X.continuous_tgt hQ

#rt_check RoundTrip.V7_59.A_to_B [Polyfold.EpGroupoid.exists_hasPropernessProperty,
  Polyfold.EpGroupoid.HasPropernessProperty.mono, Polyfold.EpGroupoid.isProperSubset_iff_isCompact,
  Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq]
#rt_check RoundTrip.V7_59.B_to_A [Polyfold.EpGroupoid.exists_hasPropernessProperty,
  Polyfold.EpGroupoid.HasPropernessProperty.mono, Polyfold.EpGroupoid.isProperSubset_iff_isCompact,
  Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq]
#rt_overlap RoundTrip.V7_59.B_to_A [Polyfold.EpGroupoid.exists_hasPropernessProperty,
  Polyfold.EpGroupoid.HasPropernessProperty.mono, Polyfold.EpGroupoid.isProperSubset_iff_isCompact,
  Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq]
#rt_overlap RoundTrip.V7_59.A_to_B [Polyfold.EpGroupoid.exists_hasPropernessProperty,
  Polyfold.EpGroupoid.HasPropernessProperty.mono, Polyfold.EpGroupoid.isProperSubset_iff_isCompact,
  Polyfold.EpGroupoid.isProperSubset_iff_exists_tendsto_subseq]

end RoundTrip.V7_59
