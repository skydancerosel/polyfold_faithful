import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_17

/-! Round trip for V9_17 (Remark 9.2.4 (a), (b), p. 411 of the 2021 book; 2017: Remark 9.4,
p. 300).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`:
* `EpGroupoid.remark_9_2_4_a`: for ANY `Θ` (no hypothesis), `y ∈ goodSet X Θ` and a structure
  `B` (at any point) whose domain contains `y` give `B.IsGoodPoint y`;
* `EpGroupoid.mem_goodSet_iff`: for branched `Θ`, `y ∈ goodSet` iff `y ∈ supp Θ` and `Θ` is
  constant on `supp Θ` near `y`;
* `EpGroupoid.remark_9_2_4_b`: for branched `Θ` and `y ∈ goodSet`: an open `V ∋ y` and a
  submanifold `M ∋ y`, properly embedded in `V`, with `Θ = Θ(y) · 1_M` on `V` and `Θ(y) > 0`.

* `A_to_B`: proved.  (a) A point good for `B₁` lies in `goodSet`, and `remark_9_2_4_a` makes
  it good for `B₂`.  (b) The data of `remark_9_2_4_b` are a structure at `y` with one
  submanifold and weight `Θ(y)`.
* `B → A`: not proved; a genuine difference in generality.  `B` (the text, §9.2's standing
  hypothesis) covers only equidimensional branched `Θ`.  `A`'s (a) holds for every `Θ`, its
  other two parts for every branched `Θ`.  `A` also has the converse half of `mem_goodSet_iff`
  (`Θ` constant on `supp Θ` near `y` ⇒ `y` good), which `B` does not state.
* `B_to_A_equidim`: proved, for branched equidimensional `Θ`.  `remark_9_2_4_a`,
  `remark_9_2_4_b` and the forward half of `mem_goodSet_iff` come from `B`.  The converse half
  is re-proved outright from `isGoodPoint_iff`, a lemma of V9_15 that is not banned here. -/

namespace RoundTrip.V9_17
open Polyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.remark_9_2_4_a.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_goodSet_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.remark_9_2_4_b.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.remark_9_2_4_a.{0}, @Polyfold.EpGroupoid.mem_goodSet_iff.{0},
    @Polyfold.EpGroupoid.remark_9_2_4_b.{0}⟩

section Glue

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- `B`'s good point is the project's. -/
theorem isGoodAt_iff (B : X.LocalBranchingStructure Θ x) (y : Obj) :
    IsGoodAt B y ↔ B.IsGoodPoint y := by
  constructor
  · rintro ⟨hy, V, hV, hyV, hVU, h⟩
    exact ⟨hy, V, hV, hyV, hVU, fun i j hi hj => by
      rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]⟩
  · rintro ⟨hy, V, hV, hyV, hVU, h⟩
    exact ⟨hy, V, hV, hyV, hVU, fun i j hij => by
      rw [inter_comm, h i j hij.1 hij.2, inter_comm]⟩

theorem mem_U_of_isGoodAt (B : X.LocalBranchingStructure Θ x) {y : Obj} (h : IsGoodAt B y) :
    y ∈ B.U := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 h.1
  exact B.subset_U i hi

/-- A point good for some structure lies in the project's `goodSet`. -/
theorem mem_goodSet_of_isGoodAt (B : X.LocalBranchingStructure Θ x) {y : Obj}
    (h : IsGoodAt B y) : y ∈ X.goodSet Θ := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 h.1
  exact ⟨(B.mem_supp_iff (B.subset_U i hi)).2 ⟨i, hi⟩, x, B, mem_U_of_isGoodAt B h,
    (isGoodAt_iff B y).1 h⟩

open scoped Classical in
/-- A structure with one index: `Θ = σ` on its submanifolds and `0` off them. -/
theorem eq_of_card_eq_one {y : Obj} (B : X.LocalBranchingStructure Θ y)
    (hcard : Fintype.card B.ι = 1) {z : Obj} (hz : z ∈ B.U) (i₀ : B.ι) :
    Θ z = if z ∈ B.M i₀ then B.σ i₀ else 0 := by
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.1 hcard
  have hi : ∀ i, i = i₀ := fun i => (hj i).trans (hj i₀).symm
  rw [B.eq_sum z hz, Finset.sum_filter]
  rw [Finset.sum_eq_single i₀ (fun b _ hb => (hb (hi b)).elim) (fun h => (h (Finset.mem_univ _)).elim)]

open scoped Classical in
/-- The structure at `y` with the single submanifold `M` and weight `Θ(y)`. -/
def single {y : Obj} {V M : Set Obj} (hV : IsOpen V) (hyV : y ∈ V) (hMV : M ⊆ V)
    (hM : X.PObj.IsSmoothSubmanifold M) (hyM : y ∈ M) (hprop : IsProperMap (inclusion hMV))
    (hpos : 0 < Θ y) (hΘV : ∀ z ∈ V, Θ z = if z ∈ M then Θ y else 0) :
    X.LocalBranchingStructure Θ y where
  U := V
  isOpen_U := hV
  mem_U := hyV
  ι := Unit
  M _ := M
  subset_U _ := hMV
  isSmoothSubmanifold _ := hM
  mem_M _ := hyM
  isProperMap _ := hprop
  σ _ := Θ y
  σ_pos _ := hpos
  eq_sum z hz := by
    rw [hΘV z hz, Finset.sum_filter, Fintype.sum_unique]

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ _
  refine ⟨fun x₁ x₂ B₁ B₂ y hy₁ hy₂ => ?_, fun x B y hg => ?_⟩
  · constructor
    · intro h
      exact (isGoodAt_iff B₂ y).2 (hA.1 (mem_goodSet_of_isGoodAt B₁ h) B₂ hy₂)
    · intro h
      exact (isGoodAt_iff B₁ y).2 (hA.1 (mem_goodSet_of_isGoodAt B₂ h) B₁ hy₁)
  · classical
    obtain ⟨V, hV, hyV, M, hMV, hM, hyM, hprop, hpos, hΘV⟩ :=
      hA.2.2 hΘ (mem_goodSet_of_isGoodAt B hg)
    exact ⟨single hV hyV hMV hM hyM hprop hpos hΘV, rfl, fun _ => rfl⟩

open scoped Classical in
/-- `B` gives `A` for every branched equidimensional `Θ` (the converse half of
`mem_goodSet_iff` re-proved from `isGoodPoint_iff`). -/
theorem B_to_A_equidim (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      (∃ n : ℕ, X.IsNDimensional Θ n) →
      -- `remark_9_2_4_a`
      (∀ y ∈ X.goodSet Θ, ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U →
        B.IsGoodPoint y) ∧
      -- `mem_goodSet_iff`
      (∀ y, y ∈ X.goodSet Θ ↔ y ∈ EpGroupoid.supp Θ ∧
        ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ EpGroupoid.supp Θ → Θ z = Θ y) ∧
      -- `remark_9_2_4_b`
      (∀ y ∈ X.goodSet Θ, ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ ∃ (M : Set Obj) (hMV : M ⊆ V),
        X.PObj.IsSmoothSubmanifold M ∧ y ∈ M ∧ IsProperMap (inclusion hMV) ∧ 0 < Θ y ∧
          ∀ z ∈ V, Θ z = if z ∈ M then Θ y else 0) := by
  classical
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ hdim
  obtain ⟨ha, hb⟩ := hB Obj Mor X Θ hΘ hdim
  -- the single-sheet structure at a good point, from `B` (b)
  have hsingle : ∀ y ∈ X.goodSet Θ, ∃ B' : X.LocalBranchingStructure Θ y,
      Fintype.card B'.ι = 1 ∧ ∀ i, B'.σ i = Θ y := by
    rintro y ⟨-, x', B', hyU', hg'⟩
    exact hb x' B' y ((isGoodAt_iff B' y).2 hg')
  refine ⟨fun y hy x B hyU => ?_, fun y => ⟨fun hy => ?_, fun ⟨hys, h⟩ => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨-, x', B', hyU', hg'⟩ := hy
    exact (isGoodAt_iff B y).1 ((ha x' x B' B y hyU' hyU).1 ((isGoodAt_iff B' y).2 hg'))
  · obtain ⟨B', hcard, hσ⟩ := hsingle y hy
    obtain ⟨i₀⟩ : Nonempty B'.ι := Fintype.card_pos_iff.1 (by omega)
    refine ⟨hy.1, B'.U, B'.isOpen_U.mem_nhds B'.mem_U, fun z hz hzs => ?_⟩
    have hz' := eq_of_card_eq_one B' hcard hz i₀
    obtain ⟨j, hj⟩ := (B'.mem_supp_iff hz).1 hzs
    have hji : j = i₀ := by
      obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.1 hcard
      exact (hk j).trans (hk i₀).symm
    rw [hji] at hj
    rw [hz', if_pos hj, hσ]
  · -- re-proved outright, through `isGoodPoint_iff` (V9_15, not banned here)
    obtain ⟨B⟩ := hΘ.localBranching y hys
    exact ⟨hys, y, B, B.mem_U, (B.isGoodPoint_iff B.mem_U).2 ⟨hys, h⟩⟩
  · obtain ⟨B', hcard, hσ⟩ := hsingle y hy
    obtain ⟨i₀⟩ : Nonempty B'.ι := Fintype.card_pos_iff.1 (by omega)
    refine ⟨B'.U, B'.isOpen_U, B'.mem_U, B'.M i₀, B'.subset_U i₀, B'.isSmoothSubmanifold i₀,
      B'.mem_M i₀, B'.isProperMap i₀, hy.1, fun z hz => ?_⟩
    rw [eq_of_card_eq_one B' hcard hz i₀, hσ]

#rt_check RoundTrip.V9_17.A_to_B [Polyfold.EpGroupoid.remark_9_2_4_a,
  Polyfold.EpGroupoid.mem_goodSet_iff, Polyfold.EpGroupoid.remark_9_2_4_b]
#rt_check RoundTrip.V9_17.B_to_A_equidim [Polyfold.EpGroupoid.remark_9_2_4_a,
  Polyfold.EpGroupoid.mem_goodSet_iff, Polyfold.EpGroupoid.remark_9_2_4_b]
#rt_overlap RoundTrip.V9_17.B_to_A_equidim [Polyfold.EpGroupoid.remark_9_2_4_a,
  Polyfold.EpGroupoid.mem_goodSet_iff, Polyfold.EpGroupoid.remark_9_2_4_b]

end RoundTrip.V9_17
