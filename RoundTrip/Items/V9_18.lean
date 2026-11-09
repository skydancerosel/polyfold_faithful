import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_18

/-! Round trip for V9_18 (Lemma 9.2.5, p. 411 of the 2021 book; 2017: Lemma 9.4, p. 300: `s(φ)`
is good iff `t(φ)` is good).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`:
* `EpGroupoid.Sheet.apply_hat`: for a functorial `Θ` and a sheet `S`, `Θ ∘ φ̂ = Θ` on `S.srcSet`;
* `EpGroupoid.src_mem_goodSet_of_tgt`: for branched `Θ`, `t φ ∈ goodSet → s φ ∈ goodSet`;
* `EpGroupoid.lemma_9_2_5`: for branched `Θ`, `s φ ∈ goodSet ↔ t φ ∈ goodSet`.

`B`'s `IsGoodPt X Θ y` (good for some structure whose domain contains `y`) is the project's
`y ∈ goodSet X Θ`: `isGoodPt_iff`.  The `y ∈ supp Θ` in `goodSet` is automatic.

* `A_to_B`: proved, from `lemma_9_2_5` through `isGoodPt_iff`.
* `B → A`: not proved; a genuine difference in generality.  `B` (the text) is for equidimensional
  branched `Θ`, `A`'s two good-point statements are for every branched `Θ`.  `Sheet.apply_hat`
  (any functorial `Θ`) is a lemma that `B` does not state.
* `B_to_A_equidim`: proved, for branched equidimensional `Θ`.  The two good-point statements
  come from `B`.  `Sheet.apply_hat` is re-proved outright (two lines: `Θ(t ψ) = Θ(s ψ)` for
  `ψ = (s|S)⁻¹ z`). -/

namespace RoundTrip.V9_18
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.Sheet.apply_hat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.src_mem_goodSet_of_tgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_2_5.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.Sheet.apply_hat.{0}, @Polyfold.EpGroupoid.src_mem_goodSet_of_tgt.{0},
    @Polyfold.EpGroupoid.lemma_9_2_5.{0}⟩

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

/-- `B`'s good points of `Θ` are the project's `goodSet`. -/
theorem isGoodPt_iff (y : Obj) : IsGoodPt X Θ y ↔ y ∈ X.goodSet Θ := by
  constructor
  · rintro ⟨x, B, hyU, hg⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hg.1
    exact ⟨(B.mem_supp_iff hyU).2 ⟨i, hi⟩, x, B, hyU, (isGoodAt_iff B y).1 hg⟩
  · rintro ⟨-, x, B, hyU, hg⟩
    exact ⟨x, B, hyU, (isGoodAt_iff B y).2 hg⟩

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ _ φ
  rw [isGoodPt_iff, isGoodPt_iff]
  exact hA.2.2 hΘ φ

/-- `B` gives `A` for every branched equidimensional `Θ` (`Sheet.apply_hat` re-proved). -/
theorem B_to_A_equidim (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
      -- `Sheet.apply_hat` (for every functorial `Θ`)
      (X.IsFunctorial Θ → ∀ (S : X.Sheet) {z : Obj}, z ∈ S.srcSet → Θ (S.hat z) = Θ z) ∧
      (X.IsBranchedEpSubgroupoid Θ → (∃ n : ℕ, X.IsNDimensional Θ n) →
        -- `src_mem_goodSet_of_tgt`
        (∀ φ : Mor, X.tgt φ ∈ X.goodSet Θ → X.src φ ∈ X.goodSet Θ) ∧
        -- `lemma_9_2_5`
        (∀ φ : Mor, X.src φ ∈ X.goodSet Θ ↔ X.tgt φ ∈ X.goodSet Θ)) := by
  intro Obj Mor _ _ _ _ _ _ X Θ
  refine ⟨fun hΘ S z hz => ?_, fun hΘ hdim => ?_⟩
  · change Θ (X.tgt (S.srcInv z)) = Θ z
    rw [← hΘ (S.srcInv z), S.isScDiffeoOn_src.right_inv z hz]
  · have h : ∀ φ : Mor, X.src φ ∈ X.goodSet Θ ↔ X.tgt φ ∈ X.goodSet Θ := fun φ => by
      rw [← isGoodPt_iff, ← isGoodPt_iff]
      exact hB Obj Mor X Θ hΘ hdim φ
    exact ⟨fun φ => (h φ).2, h⟩

#rt_check RoundTrip.V9_18.A_to_B [Polyfold.EpGroupoid.Sheet.apply_hat,
  Polyfold.EpGroupoid.src_mem_goodSet_of_tgt, Polyfold.EpGroupoid.lemma_9_2_5]
#rt_check RoundTrip.V9_18.B_to_A_equidim [Polyfold.EpGroupoid.Sheet.apply_hat,
  Polyfold.EpGroupoid.src_mem_goodSet_of_tgt, Polyfold.EpGroupoid.lemma_9_2_5]
#rt_overlap RoundTrip.V9_18.B_to_A_equidim [Polyfold.EpGroupoid.Sheet.apply_hat,
  Polyfold.EpGroupoid.src_mem_goodSet_of_tgt, Polyfold.EpGroupoid.lemma_9_2_5]

end RoundTrip.V9_18
