import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_46

/-!
Round trip for V7_46 (Lemma 7.7: `|X|` is regular).

`A` is the type of `Polyfold.EpGroupoid.lemma_7_3_5` at universe `0`: for every ep-groupoid
`X : EpGroupoid Obj Mor` (`Obj Mor : Type`), Mathlib's `RegularSpace X.OrbitSpace`.
`B` is the text's definition of regularity, stated literally (a point and a nonempty closed set
not containing it have disjoint open neighbourhoods).  The two notions agree in every topological
space: `RegularSpace` is `Disjoint (𝓝ˢ A) (𝓝 z)` for closed `A ∌ z`, which unfolds through the
bases of open sets of `𝓝ˢ A` and `𝓝 z`; the empty case is automatic (`𝓝ˢ ∅ = ⊥`).
-/

namespace RoundTrip.V7_46
open Polyfold Set Filter Topology

/-- The project's Lemma 7.7, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_7_3_5.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.lemma_7_3_5.{0}

/-- Mathlib's regularity is the text's. -/
theorem regular_iff_text (Y : Type) [TopologicalSpace Y] :
    RegularSpace Y ↔ IsRegularText Y := by
  constructor
  · intro h S _ hS z hz
    have hd : Disjoint (𝓝ˢ S) (𝓝 z) := RegularSpace.regular hS hz
    obtain ⟨V, ⟨hVo, hSV⟩, U, ⟨hzU, hUo⟩, hVU⟩ :=
      ((hasBasis_nhdsSet S).disjoint_iff (nhds_basis_opens z)).1 hd
    exact ⟨U, V, hUo, hVo, hzU, hSV, by rw [inter_comm]; exact hVU.inter_eq⟩
  · intro h
    refine ⟨fun {S z} hS hz => ?_⟩
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨U, V, hUo, hVo, hzU, hSV, hUV⟩ := h S hne hS z hz
    exact Filter.disjoint_iff.2 ⟨V, hVo.mem_nhdsSet.2 hSV, U, hUo.mem_nhds hzU,
      Set.disjoint_iff_inter_eq_empty.2 (by rw [inter_comm]; exact hUV)⟩

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X =>
  (regular_iff_text X.OrbitSpace).1 (hA X)

theorem B_to_A : B → A := fun hB {Obj Mor} _ _ _ _ _ _ X =>
  (regular_iff_text X.OrbitSpace).2 (hB Obj Mor X)

#rt_check RoundTrip.V7_46.A_to_B [Polyfold.EpGroupoid.lemma_7_3_5]
#rt_check RoundTrip.V7_46.B_to_A [Polyfold.EpGroupoid.lemma_7_3_5]
#rt_overlap RoundTrip.V7_46.B_to_A [Polyfold.EpGroupoid.lemma_7_3_5]
#rt_overlap RoundTrip.V7_46.A_to_B [Polyfold.EpGroupoid.lemma_7_3_5]

end RoundTrip.V7_46
