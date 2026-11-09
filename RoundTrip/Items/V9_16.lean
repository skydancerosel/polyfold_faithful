import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_16

/-! Round trip for V9_16 (Lemma 9.2.3, p. 410 of the 2021 book; 2017: Lemma 9.3, p. 299:
being good does not depend on the local branching structure).

`A` is the type of `EpGroupoid.LocalBranchingStructure.lemma_9_2_3`, universe at `0`: for ANY
`Θ : Obj → ℚ` (no branched, no dimension hypothesis), any structure `B` at `x`, any structure
`B'` at any `x'`, and any `y ∈ U ∩ U'`, `B.IsGoodPoint y → B'.IsGoodPoint y`.

* `A_to_B`: proved.  `IsGoodAt` (`B`'s good point) is the project's `IsGoodPoint` up to
  `inter_comm`; `y ∈ U(x)` follows from `y ∈ ⋃ Mᵢ`.
* `B → A`: not proved; a genuine difference in generality.  `B` is the text's statement: an
  equidimensional branched `Θ`, two structures at the same `x` with the same domain.  `A`
  holds for every `Θ` with local branching structures, for structures at different points and
  with different domains.  `B` says nothing about a `Θ` that is not branched or not
  equidimensional.
* `B_to_A_branched_equidim`: proved.  The extra generality in the points and domains is only
  glue.  For a branched equidimensional `Θ`, `B` gives `A`'s conclusion for structures at any
  two points whose domains contain `y`: restrict both to `y` (`restrictAt`) and then to the
  common domain (`restrict`), apply `B`, and read the goodness back. -/

namespace RoundTrip.V9_16
open Polyfold Set

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3.{0}

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

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ _ _ x B₁ B₂ hU y hg
  have hyU := mem_U_of_isGoodAt B₁ hg
  exact (isGoodAt_iff B₂ y).2
    (hA B₁ B₂ hyU (hU ▸ hyU) ((isGoodAt_iff B₁ y).1 hg))

/-- `B` gives `A`'s conclusion for every branched equidimensional `Θ`, for structures at
different points and with different domains. -/
theorem B_to_A_branched_equidim (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      (∃ n : ℕ, X.IsNDimensional Θ n) →
      ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (x' : Obj)
        (B' : X.LocalBranchingStructure Θ x') (y : Obj), y ∈ B.U → y ∈ B'.U →
        B.IsGoodPoint y → B'.IsGoodPoint y := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ hdim x B₁ x' B₂ y hy₁ hy₂ hg
  set C₁ := B₁.restrictAt hy₁
  set C₂ := B₂.restrictAt hy₂
  have hW : IsOpen (C₁.U ∩ C₂.U) := C₁.isOpen_U.inter C₂.isOpen_U
  have hyW : y ∈ C₁.U ∩ C₂.U := ⟨C₁.mem_U, C₂.mem_U⟩
  set D₁ := C₁.restrict hW hyW inter_subset_left
  set D₂ := C₂.restrict hW hyW inter_subset_right
  -- the good point of `B₁` is a good point of `D₁`
  have h1 : IsGoodAt D₁ y := by
    obtain ⟨hyM, V, hV, hyV, -, hVM⟩ := hg
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 hyM
    refine ⟨mem_iUnion.2 ⟨⟨i₀, hi₀⟩, D₁.mem_M _⟩, V ∩ (C₁.U ∩ C₂.U), hV.inter hW, ⟨hyV, hyW⟩,
      inter_subset_right, fun i j _ => ?_⟩
    have key : ∀ z ∈ V, (z ∈ B₁.M i.1 ↔ z ∈ B₁.M j.1) := fun z hz => by
      have h := Set.ext_iff.1 (hVM i.1 j.1 i.2 j.2) z
      simp only [mem_inter_iff] at h
      exact ⟨fun hi => (h.1 ⟨hz, hi⟩).2, fun hj => (h.2 ⟨hz, hj⟩).2⟩
    ext z
    change z ∈ ((B₁.M i.1 ∩ B₁.nbhdAt y) ∩ (C₁.U ∩ C₂.U)) ∩ (V ∩ (C₁.U ∩ C₂.U)) ↔
      z ∈ ((B₁.M j.1 ∩ B₁.nbhdAt y) ∩ (C₁.U ∩ C₂.U)) ∩ (V ∩ (C₁.U ∩ C₂.U))
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄, h₅⟩
      exact ⟨⟨⟨(key z h₄).1 h₁, h₂⟩, h₃⟩, h₄, h₅⟩
    · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄, h₅⟩
      exact ⟨⟨⟨(key z h₄).2 h₁, h₂⟩, h₃⟩, h₄, h₅⟩
  have h2 : IsGoodAt D₂ y := hB Obj Mor X Θ hΘ hdim y D₁ D₂ rfl y h1
  -- a good point of `D₂` is a good point of `B₂`
  obtain ⟨hyM, V, hV, hyV, hVU, hVM⟩ := h2
  obtain ⟨i₀, -⟩ := mem_iUnion.1 hyM
  have hVW : V ⊆ C₁.U ∩ C₂.U := hVU
  refine ⟨mem_iUnion.2 ⟨i₀.1, i₀.2⟩, V, hV, hyV,
    fun z hz => B₂.nbhdAt_subset y (hVW hz).2, fun i j hi hj => ?_⟩
  have h := hVM ⟨i, hi⟩ ⟨j, hj⟩ ⟨D₂.mem_M _, D₂.mem_M _⟩
  have key : ∀ z ∈ V, z ∈ B₂.M i → z ∈ B₂.M j := fun z hz hzi => by
    have hz' : z ∈ D₂.M ⟨i, hi⟩ ∩ V := ⟨⟨⟨hzi, (hVW hz).2⟩, hVW hz⟩, hz⟩
    rw [h] at hz'
    exact hz'.1.1.1
  have key' : ∀ z ∈ V, z ∈ B₂.M j → z ∈ B₂.M i := fun z hz hzj => by
    have hz' : z ∈ D₂.M ⟨j, hj⟩ ∩ V := ⟨⟨⟨hzj, (hVW hz).2⟩, hVW hz⟩, hz⟩
    rw [← h] at hz'
    exact hz'.1.1.1
  ext z
  exact ⟨fun hz => ⟨hz.1, key z hz.1 hz.2⟩, fun hz => ⟨hz.1, key' z hz.1 hz.2⟩⟩

#rt_check RoundTrip.V9_16.A_to_B [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3]
#rt_check RoundTrip.V9_16.B_to_A_branched_equidim
  [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3]
#rt_overlap RoundTrip.V9_16.B_to_A_branched_equidim
  [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3]

end RoundTrip.V9_16
