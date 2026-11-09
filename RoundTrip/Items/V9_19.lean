import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_19

/-! Round trip for V9_19 (Definition 9.2.6, p. 411 of the 2021 book; 2017: Definition 9.5,
p. 300: the good set `S^g_Θ` and the bad set `S^b_Θ`).

The item lists two definitions (`EpGroupoid.goodSet`, `EpGroupoid.badSet`: vocabulary) and two
theorems.  `A` is the conjunction of the types of the theorems, universes instantiated at `0`:
`EpGroupoid.preimage_π_image_goodSet` and `EpGroupoid.preimage_π_image_badSet`, i.e.
`π⁻¹(π(S^g_Θ)) = S^g_Θ` and `π⁻¹(π(S^b_Θ)) = S^b_Θ` for every branched `Θ`.

* `B` (1)–(2): the project's `goodSet` is `{y ∈ supp Θ | y good}` and its `badSet` is
  `{y ∈ supp Θ | y not good}`.  `B`'s `IsGoodPt` is the project's "good for some structure
  whose domain contains `y`" up to `inter_comm`, and `badSet = supp Θ \ goodSet`.  These two
  parts are definitional (`goodSet_eq`, `badSet_eq`) and use no hypothesis.
* `B` (3)–(4) (both sets are unions of isomorphism classes) are `A`'s saturation statements,
  read along a morphism.
* `A_to_B`: proved.  (1)–(2) are definitional; (3)–(4) follow from `A` and `π(s φ) = π(t φ)`.
* `B → A`: not proved; a genuine difference in generality.  `A` is for every branched `Θ`,
  `B` (the text, §9.2's standing hypothesis) only for equidimensional ones.
* `B_to_A_equidim`: proved.  For branched equidimensional `Θ`, `A`'s two equalities follow
  from `B` (3)–(4) and `π_eq_π_iff`. -/

namespace RoundTrip.V9_19
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.preimage_π_image_goodSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.preimage_π_image_badSet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.preimage_π_image_goodSet.{0},
    @Polyfold.EpGroupoid.preimage_π_image_badSet.{0}⟩

section Glue

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- `B`'s good point is the project's. -/
theorem isGoodAt_iff {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) :
    IsGoodAt B y ↔ B.IsGoodPoint y := by
  constructor
  · rintro ⟨hy, V, hV, hyV, hVU, h⟩
    exact ⟨hy, V, hV, hyV, hVU, fun i j hi hj => by
      rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]⟩
  · rintro ⟨hy, V, hV, hyV, hVU, h⟩
    exact ⟨hy, V, hV, hyV, hVU, fun i j hij => by
      rw [inter_comm, h i j hij.1 hij.2, inter_comm]⟩

theorem goodSet_eq : X.goodSet Θ = {y | y ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ y} := by
  ext y
  constructor
  · rintro ⟨hys, x, B, hyU, hg⟩
    exact ⟨hys, x, B, hyU, (isGoodAt_iff B y).2 hg⟩
  · rintro ⟨hys, x, B, hyU, hg⟩
    exact ⟨hys, x, B, hyU, (isGoodAt_iff B y).1 hg⟩

theorem badSet_eq : X.badSet Θ = {y | y ∈ EpGroupoid.supp Θ ∧ ¬ IsGoodPt X Θ y} := by
  ext y
  change y ∈ EpGroupoid.supp Θ ∧ y ∉ X.goodSet Θ ↔ _
  rw [goodSet_eq]
  simp only [mem_ofPred_eq, not_and]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

/-- A subset `S` with `π⁻¹(π(S)) = S` is closed under morphisms. -/
theorem mem_iff_of_preimage_image {S : Set Obj} (hS : X.π ⁻¹' (X.π '' S) = S) (φ : Mor) :
    X.src φ ∈ S ↔ X.tgt φ ∈ S := by
  constructor
  · intro h
    rw [← hS]
    exact ⟨X.src φ, h, X.π_src_eq_π_tgt φ⟩
  · intro h
    rw [← hS]
    exact ⟨X.tgt φ, h, (X.π_src_eq_π_tgt φ).symm⟩

/-- A subset closed under morphisms has `π⁻¹(π(S)) = S`. -/
theorem preimage_image_of_mem_iff {S : Set Obj} (hS : ∀ φ : Mor, X.src φ ∈ S ↔ X.tgt φ ∈ S) :
    X.π ⁻¹' (X.π '' S) = S := by
  refine Subset.antisymm (fun y hy => ?_) (subset_preimage_image _ _)
  obtain ⟨a, ha, hay⟩ := hy
  obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
  exact (hS φ).1 ha

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ _
  exact ⟨goodSet_eq, badSet_eq, mem_iff_of_preimage_image (hA.1 hΘ),
    mem_iff_of_preimage_image (hA.2 hΘ)⟩

/-- `B` gives `A` for every branched equidimensional `Θ`. -/
theorem B_to_A_equidim (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      (∃ n : ℕ, X.IsNDimensional Θ n) →
      X.π ⁻¹' (X.π '' X.goodSet Θ) = X.goodSet Θ ∧
        X.π ⁻¹' (X.π '' X.badSet Θ) = X.badSet Θ := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ hdim
  obtain ⟨-, -, hg, hb⟩ := hB Obj Mor X Θ hΘ hdim
  exact ⟨preimage_image_of_mem_iff hg, preimage_image_of_mem_iff hb⟩

#rt_check RoundTrip.V9_19.A_to_B [Polyfold.EpGroupoid.preimage_π_image_goodSet,
  Polyfold.EpGroupoid.preimage_π_image_badSet]
#rt_check RoundTrip.V9_19.B_to_A_equidim [Polyfold.EpGroupoid.preimage_π_image_goodSet,
  Polyfold.EpGroupoid.preimage_π_image_badSet]
#rt_overlap RoundTrip.V9_19.B_to_A_equidim [Polyfold.EpGroupoid.preimage_π_image_goodSet,
  Polyfold.EpGroupoid.preimage_π_image_badSet]

end RoundTrip.V9_19
