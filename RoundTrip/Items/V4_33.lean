import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_33

/-!
Round trip for V4_33 (Proposition 4.15 (1)).  `A` is the conjunction of the types of
`Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet`,
`Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff` and
`Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one`, universe instantiated at `0`.

Glue:
* B's `IsSmoothSubmanifoldB` is the project's `IsSmoothSubmanifold` (V4_29: the sc⁺-retraction
  notions agree, `retractionOn_iff` copied from V4_9).
* B's existential paracompactness of `A` is `MPolyfold.paracompactSpace_subtype`; B's `hA` is
  `IsSmoothSubmanifold.isSubMPolyfold` (any proof gives the same structure).
* `B → A`: B says only `(subPolyfold hA).levelSet 1 = univ`; A's level-trace lemma is stated for
  every `m`.  It is a general fact about the induced structure (charts `subChart`), re-proved here
  (`levelSet_sub_iff`, the project's three-line chart argument, for any sub-M-polyfold); with it,
  B's `A ⊆ X_∞` gives that every point of `A` is smooth for the induced structure.
-/

namespace RoundTrip.V4_33
open Polyfold

def A : Prop :=
  type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet.{0} ∧
    type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff.{0} ∧
    type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet.{0},
    @Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff.{0},
    @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9). -/
theorem retractionOn_iff (P : MPolyfold X) (r : X → X) (V : Set X) :
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V := by
  constructor
  · intro h
    refine ⟨h.isScSmoothOn.isOpen, h.isScSmoothOn, h.mapsTo, h.idem, h.mem_levelSet,
      fun g hg => ?_⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact MPolyfold.IsScSmoothOn.of_exists_charts h.isScSmoothOn.isOpen
        (fun y _ => (IsEmpty.false y).elim) (fun y _ => (IsEmpty.false y).elim)
    · refine (h.isScSmoothOn_one (g x)).congr fun y hy => ?_
      change P.toLevelOne (g x) (r y) = g y
      rw [← hg y hy, MPolyfold.toLevelOne_levelVal]
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x₀ =>
      h5 _ fun x hx => MPolyfold.levelVal_toLevelOne x₀ (h4 x hx)⟩

/-- Definition 4.13: the project's notion is B's (V4_29). -/
theorem smooth_iff (P : MPolyfold X) (S : Set X) :
    P.IsSmoothSubmanifold S ↔ IsSmoothSubmanifoldB P S := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, s, hs, himg⟩ := h a ha
    exact ⟨V, s, hV, haV, (retractionOn_iff P s V).1 hs, himg⟩
  · intro h a ha
    obtain ⟨V, s, hV, haV, hs, himg⟩ := h a ha
    exact ⟨V, hV, haV, s, (retractionOn_iff P s V).2 hs, himg⟩

/-- The level sets of the induced structure of ANY sub-M-polyfold are the traces of those of `X`
(re-proved: the chart argument with `subChart`). -/
theorem levelSet_sub_iff {P : MPolyfold X} {S : Set X} (hS : P.IsSubMPolyfold S)
    [ParacompactSpace S] (a : S) (m : ℕ) :
    a ∈ (MPolyfold.subPolyfold hS).levelSet m ↔ a.1 ∈ P.levelSet m := by
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
  set d := hS.data a.2
  have hsrc : a ∈ (MPolyfold.subChart d hφ a).source :=
    d.mem_shrink φ a.2 (hS.mem_data_V a.2) haφ
  rw [(MPolyfold.subPolyfold hS).mem_levelSet_iff
    (MPolyfold.subPolyfold_isChart hS d hφ a) hsrc, P.mem_levelSet_iff hφ haφ]
  rfl

end Glue

theorem A_to_B : A → B := by
  rintro ⟨h1, h2, -⟩ X _ _ _ P S hSB
  have hS : P.IsSmoothSubmanifold S := (smooth_iff P S).2 hSB
  have : ParacompactSpace S := P.paracompactSpace_subtype S
  refine ⟨h1 hS, hS.isSubMPolyfold, inferInstance, ?_⟩
  ext a
  simp only [Set.mem_univ, iff_true]
  exact (h2 hS a 1).2 (MPolyfold.smoothSet_subset_levelSet 1 (h1 hS a.2))

theorem B_to_A : B → A := by
  intro hB
  have hsm : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      {P : MPolyfold X} {S : Set X}, P.IsSmoothSubmanifold S → S ⊆ P.smoothSet :=
    fun {X} _ _ _ {P} {S} hS => (hB X P S ((smooth_iff P S).1 hS)).1
  refine ⟨fun {X} _ _ _ {P} {S} hS => hsm hS,
    fun {X} _ _ _ {P} {S} hS _ a m => levelSet_sub_iff hS.isSubMPolyfold a m,
    fun {X} _ _ _ {P} {S} hS _ => ⟨hsm hS, fun a => ?_⟩⟩
  simp only [MPolyfold.smoothSet, Set.mem_iInter]
  intro m
  exact (levelSet_sub_iff hS.isSubMPolyfold a m).2 (MPolyfold.smoothSet_subset_levelSet m (hsm hS a.2))

#rt_check RoundTrip.V4_33.A_to_B [Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet,
  Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one]
#rt_check RoundTrip.V4_33.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet,
  Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one]
#rt_overlap RoundTrip.V4_33.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet,
  Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_one]

end RoundTrip.V4_33
