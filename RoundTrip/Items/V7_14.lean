import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_14

/-! Round trip for V7_14 (Lemma 7.1, p. 230: finitely many morphisms from `x` into `U(x₀)`).

`A` is the conjunction of the types of the six listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.lemma_7_1_11`, `lemma_7_1_11_swap`, `lemma_7_1_11_of_isProperMap`,
`lemma_7_1_11_swap_of_isProperMap` (one universe each) and the two abstract topological lemmas
`finite_setOf_mem_of_isProperMap_domRestrict`,
`IsProperMap.finite_preimage_singleton_of_isLocallyInjective` (two universes each).

* `A → B`: `B` is literally `lemma_7_1_11` (same setting, same hypotheses `IsOpen U`, `x₀ ∈ U`,
  `IsProperMap ((s⁻¹(cl U)).domRestrict t)`, same conclusion), only the binders are reordered.
* `B → A`: `lemma_7_1_11` is `B`; `lemma_7_1_11_swap` follows from `B` through the inverse map `ι`
  (which exchanges `s` and `t`).  The other four conjuncts are not consequences of `B`:
  the `_of_isProperMap` forms have `t(ψ) ∈ cl U` (resp. `s(ψ) ∈ cl U`) instead of `∈ U` and no
  openness, and the two abstract lemmas are about arbitrary maps `s, t : M → X`; they are
  re-proved outright here (compact discrete fibres are finite). -/

namespace RoundTrip.V7_14
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_7_1_11.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_1_11_swap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_1_11_of_isProperMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_7_1_11_swap_of_isProperMap.{0}) ∧
  (type_of% @Polyfold.finite_setOf_mem_of_isProperMap_domRestrict.{0, 0}) ∧
  (type_of% @Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_7_1_11.{0}, @Polyfold.EpGroupoid.lemma_7_1_11_swap.{0},
    @Polyfold.EpGroupoid.lemma_7_1_11_of_isProperMap.{0},
    @Polyfold.EpGroupoid.lemma_7_1_11_swap_of_isProperMap.{0},
    @Polyfold.finite_setOf_mem_of_isProperMap_domRestrict.{0, 0},
    @Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective.{0, 0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x x₀ U hU hx₀ hp
  exact hA.1 X hU hx₀ hp

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- Inversion exchanges `{ψ | s ψ = x ∧ t ψ ∈ K}` and `{ψ | t ψ = x ∧ s ψ ∈ K}`. -/
theorem finite_swap_of_finite {x : Obj} {K : Set Obj}
    (h : {ψ | X.src ψ = x ∧ X.tgt ψ ∈ K}.Finite) : {ψ | X.tgt ψ = x ∧ X.src ψ ∈ K}.Finite := by
  refine (h.image X.inv).subset fun ψ hψ => ?_
  refine ⟨X.inv ψ, ⟨?_, ?_⟩, GroupoidStr.inv_inv ψ⟩
  · rw [X.src_inv]; exact hψ.1
  · rw [X.tgt_inv]; exact hψ.2

theorem finite_of_finite_swap {x : Obj} {K : Set Obj}
    (h : {ψ | X.tgt ψ = x ∧ X.src ψ ∈ K}.Finite) : {ψ | X.src ψ = x ∧ X.tgt ψ ∈ K}.Finite := by
  refine (h.image X.inv).subset fun ψ hψ => ?_
  refine ⟨X.inv ψ, ⟨?_, ?_⟩, GroupoidStr.inv_inv ψ⟩
  · rw [X.tgt_inv]; exact hψ.1
  · rw [X.src_inv]; exact hψ.2

end

/-- `IsProperMap.finite_preimage_singleton_of_isLocallyInjective`, re-proved outright. -/
theorem finite_preimage' {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y] {f : M → Y}
    (hf : IsProperMap f) (hi : IsLocallyInjective f) (y : Y) : (f ⁻¹' {y}).Finite :=
  (hf.isCompact_preimage isCompact_singleton).finite
    (IsLocallyInjective.isDiscrete_preimage_singleton hi y)

/-- `finite_setOf_mem_of_isProperMap_domRestrict`, re-proved outright. -/
theorem finite_setOf_mem' {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y] {s t : M → Y}
    (ht : IsLocallyInjective t) {K : Set Y} (hK : IsProperMap ((s ⁻¹' K).domRestrict t)) (y : Y) :
    {ψ | s ψ ∈ K ∧ t ψ = y}.Finite := by
  refine ((finite_preimage' hK
    (ht.comp_right continuous_subtype_val Subtype.val_injective) y).image Subtype.val).subset ?_
  rintro ψ ⟨hψK, hψx⟩
  exact ⟨⟨ψ, hψK⟩, hψx, rfl⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, @finite_setOf_mem', @finite_preimage'⟩
  · -- `lemma_7_1_11` is `B`
    intro Obj Mor _ _ _ _ _ _ X x x₀ U hU hx₀ hp
    exact hB Obj Mor X x x₀ U hU hx₀ hp
  · -- `lemma_7_1_11_swap` from `B` by inversion
    intro Obj Mor _ _ _ _ _ _ X x x₀ U hU hx₀ hp
    exact finite_swap_of_finite X (hB Obj Mor X x x₀ U hU hx₀ hp)
  · -- `lemma_7_1_11_of_isProperMap` (outright)
    intro Obj Mor _ _ _ _ _ _ X U hp x
    refine finite_of_finite_swap X ((finite_setOf_mem' X.isLocalScDiffeo_tgt.isLocallyInjective
      hp x).subset fun ψ hψ => ⟨hψ.2, hψ.1⟩)
  · -- `lemma_7_1_11_swap_of_isProperMap` (outright)
    intro Obj Mor _ _ _ _ _ _ X U hp x
    exact (finite_setOf_mem' X.isLocalScDiffeo_tgt.isLocallyInjective hp x).subset
      fun ψ hψ => ⟨hψ.2, hψ.1⟩

#rt_check RoundTrip.V7_14.A_to_B [Polyfold.EpGroupoid.lemma_7_1_11, Polyfold.EpGroupoid.lemma_7_1_11_swap,
  Polyfold.EpGroupoid.lemma_7_1_11_of_isProperMap, Polyfold.EpGroupoid.lemma_7_1_11_swap_of_isProperMap,
  Polyfold.finite_setOf_mem_of_isProperMap_domRestrict,
  Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective]
#rt_check RoundTrip.V7_14.B_to_A [Polyfold.EpGroupoid.lemma_7_1_11, Polyfold.EpGroupoid.lemma_7_1_11_swap,
  Polyfold.EpGroupoid.lemma_7_1_11_of_isProperMap, Polyfold.EpGroupoid.lemma_7_1_11_swap_of_isProperMap,
  Polyfold.finite_setOf_mem_of_isProperMap_domRestrict,
  Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective]
#rt_overlap RoundTrip.V7_14.B_to_A [Polyfold.EpGroupoid.lemma_7_1_11,
  Polyfold.EpGroupoid.lemma_7_1_11_swap, Polyfold.EpGroupoid.lemma_7_1_11_of_isProperMap,
  Polyfold.EpGroupoid.lemma_7_1_11_swap_of_isProperMap,
  Polyfold.finite_setOf_mem_of_isProperMap_domRestrict,
  Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective]

end RoundTrip.V7_14
