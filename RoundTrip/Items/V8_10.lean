import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_10

/-! Round trip for V8_10 (Lemma 8.1.8 (2017: 8.7): the properness property of `T(X, 𝐗)`).

`A` is the type of `EpGroupoid.lemma_8_7`, universe instantiated at `0` (`B` lives in `Type`):
every `a ∈ TX` has an open `V' ∋ a` with `t_T : s_T⁻¹(cl V') → TX` a proper map (Mathlib's
`IsProperMap`).  `B` asks the same with "proper" read as continuous with compact preimages of
compact sets (`IsProperB`).  The two readings of "proper" agree because `TX` is Hausdorff and
metrizable (Part I's `MPolyfold.metrizableSpace_tangentSpace`), hence compactly generated:
Mathlib's `isProperMap_iff_isCompact_preimage`.  `B`'s `tangentMap hs`, `tangentMap ht` are the
project's `tSrc`, `tTgt` (proof irrelevance). -/

namespace RoundTrip.V8_10
open Polyfold

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_8_7.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.lemma_8_7.{0}

/-- On maps into `TX`, Mathlib's `IsProperMap` is `B`'s `IsProperB`. -/
theorem isProperMap_iff_isProperB {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) {α : Type 1} [TopologicalSpace α]
    (f : α → P.TangentSpace) : IsProperMap f ↔ IsProperB f := by
  have := P.metrizableSpace_tangentSpace
  rw [isProperMap_iff_isCompact_preimage]
  exact ⟨fun h => ⟨h.1, fun K hK => h.2 hK⟩, fun h => ⟨h.1, fun K hK => h.2 K hK⟩⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, fun a => ?_⟩
  obtain ⟨V, hV, ha, hp⟩ := hA X a
  exact ⟨V, hV, ha, (isProperMap_iff_isProperB X.PObj _).1 hp⟩

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X a
  obtain ⟨hs, ht, h⟩ := hB Obj Mor X
  obtain ⟨V, hV, ha, hp⟩ := h a
  exact ⟨V, hV, ha, (isProperMap_iff_isProperB X.PObj _).2 hp⟩

#rt_check RoundTrip.V8_10.A_to_B [Polyfold.EpGroupoid.lemma_8_7]
#rt_check RoundTrip.V8_10.B_to_A [Polyfold.EpGroupoid.lemma_8_7]
#rt_overlap RoundTrip.V8_10.B_to_A [Polyfold.EpGroupoid.lemma_8_7]

end RoundTrip.V8_10
