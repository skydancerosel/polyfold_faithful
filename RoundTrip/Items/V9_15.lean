import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_15

/-! Round trip for V9_15 (Definition 9.2.2, p. 410 of the 2021 book; 2017: Definition 9.4,
p. 299: good points of a local branching structure).

The item lists three definitions (`LocalBranchingStructure.MU`, `IsGoodPoint`, `nbhdAt`:
vocabulary) and two theorems.  `A` is the conjunction of the types of the theorems,
universes instantiated at `0` (`B` lives in `Type`):
`LocalBranchingStructure.isGoodPoint_iff` (the intrinsic form: for `y ∈ U(x)`, `y` is good iff
`y ∈ supp Θ` and `Θ` is constant on `supp Θ` near `y`) and
`LocalBranchingStructure.eq_iff_of_mem_nbhdAt` (on `nbhdAt y`, `Θ z = Θ y` iff `I_y ⊆ I_z`).

* `B` says that the project's `MU` is `⋃ᵢ Mᵢ` and that `IsGoodPoint` is the text's good point
  (`IsGoodAt`), bad = not good.  This is definitional (`rfl` and `inter_comm`): `B_holds`,
  so `A_to_B` does not use `A`.
* `A`'s two theorems are characterizations that `B` does not state; `B_to_A` re-proves them
  outright (from `MU_eq`, `mem_supp_iff`, `isOpen_nbhdAt`, `eq_sum`, none of them banned), so
  it does not use `B` either.  The comparison that matters is `B_holds`: the definitions agree
  with the text's. -/

namespace RoundTrip.V9_15
open Polyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.eq_iff_of_mem_nbhdAt.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.eq_iff_of_mem_nbhdAt.{0}⟩

/-- `B` holds by unfolding the project's definitions. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ _ _ x B
  refine ⟨rfl, fun y => ?_, fun y _ => ?_⟩
  · constructor
    · rintro ⟨hy, V, hV, hyV, hVU, h⟩
      exact ⟨hy, V, hV, hyV, hVU, fun i j hij => by
        rw [inter_comm, h i j hij.1 hij.2, inter_comm]⟩
    · rintro ⟨hy, V, hV, hyV, hVU, h⟩
      exact ⟨hy, V, hV, hyV, hVU, fun i j hi hj => by
        rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]⟩
  · constructor
    · intro h
      refine ⟨‹y ∈ B.MU›, fun hg => h ?_⟩
      obtain ⟨hy, V, hV, hyV, hVU, h'⟩ := hg
      exact ⟨hy, V, hV, hyV, hVU, fun i j hi hj => by
        rw [inter_comm, h' i j ⟨hi, hj⟩, inter_comm]⟩
    · rintro ⟨-, h⟩ hg
      apply h
      obtain ⟨hy, V, hV, hyV, hVU, h'⟩ := hg
      exact ⟨hy, V, hV, hyV, hVU, fun i j hij => by
        rw [inter_comm, h' i j hij.1 hij.2, inter_comm]⟩

/-- `A → B`: `B` is definitional (does not use `A`). -/
theorem A_to_B : A → B := fun _ => B_holds

section Reproof

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)

open scoped Classical in
/-- `eq_iff_of_mem_nbhdAt`, re-proved. -/
theorem eqIff {y z : Obj} (hy : y ∈ B.U) (hz : z ∈ B.nbhdAt y) :
    Θ z = Θ y ↔ ∀ i, y ∈ B.M i → z ∈ B.M i := by
  constructor
  · intro h i hyi
    by_contra hzi
    have hlt : Θ z < Θ y := by
      rw [B.eq_sum z hz.1, B.eq_sum y hy]
      refine Finset.sum_lt_sum_of_subset (i := i) (fun j hj => ?_) ?_ ?_ (B.σ_pos i)
        fun j _ _ => (B.σ_pos j).le
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hz.2 j hj
      · simpa using hyi
      · simpa using hzi
    exact (ne_of_lt hlt) h
  · intro h
    rw [B.eq_sum z hz.1, B.eq_sum y hy]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hz.2 i, h i⟩

/-- `isGoodPoint_iff`, re-proved. -/
theorem goodIff {y : Obj} (hy : y ∈ B.U) :
    B.IsGoodPoint y ↔ y ∈ EpGroupoid.supp Θ ∧
      ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ EpGroupoid.supp Θ → Θ z = Θ y := by
  constructor
  · rintro ⟨hyM, V, hV, hyV, -, hVM⟩
    rw [B.MU_eq] at hyM
    refine ⟨hyM.1, V ∩ B.nbhdAt y, (hV.inter (B.isOpen_nbhdAt y)).mem_nhds
      ⟨hyV, B.mem_nbhdAt_self hy⟩, fun z hz hzs => ?_⟩
    obtain ⟨k, hzk⟩ := (B.mem_supp_iff hz.2.1).1 hzs
    have hyk : y ∈ B.M k := hz.2.2 k hzk
    refine (eqIff B hy hz.2).2 fun i hyi => ?_
    have h' : z ∈ V ∩ B.M k := ⟨hz.1, hzk⟩
    rw [hVM k i hyk hyi] at h'
    exact h'.2
  · rintro ⟨hys, V, hV, hc⟩
    obtain ⟨V₁, hV₁V, hV₁, hyV₁⟩ := mem_nhds_iff.1 hV
    refine ⟨B.MU_eq ▸ ⟨hys, hy⟩, V₁ ∩ B.nbhdAt y, hV₁.inter (B.isOpen_nbhdAt y),
      ⟨hyV₁, B.mem_nbhdAt_self hy⟩, fun z hz => (B.nbhdAt_subset y) hz.2,
      fun i j hyi hyj => ?_⟩
    have key : ∀ i j, y ∈ B.M i → y ∈ B.M j →
        V₁ ∩ B.nbhdAt y ∩ B.M i ⊆ V₁ ∩ B.nbhdAt y ∩ B.M j := by
      intro i j _ hyj z hz
      have hzs : z ∈ EpGroupoid.supp Θ := (B.mem_supp_iff hz.1.2.1).2 ⟨i, hz.2⟩
      have hΘz := hc z (hV₁V hz.1.1) hzs
      exact ⟨hz.1, (eqIff B hy hz.1.2).1 hΘz j hyj⟩
    exact Subset.antisymm (key i j hyi hyj) (key j i hyj hyi)

end Reproof

/-- `B → A`: `A`'s characterizations re-proved outright (does not use `B`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨fun B _ hy => goodIff B hy, fun B _ _ hy hz => eqIff B hy hz⟩

#rt_check RoundTrip.V9_15.A_to_B [Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_iff_of_mem_nbhdAt]
#rt_check RoundTrip.V9_15.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_iff_of_mem_nbhdAt]
#rt_overlap RoundTrip.V9_15.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_iff_of_mem_nbhdAt]

end RoundTrip.V9_15
