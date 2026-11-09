import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_60

/-! Round trip for V9_60 (2021 Definition 9.6.3, p. 455: top-good and top-bad points).

The item lists the definitions `LocalBranchingStructure.IsTopGoodPoint`, `IsTopBadPoint`
(vocabulary) and one theorem, `dimPart_topDim_eq_of_isTopGoodPoint` (p. 456: at a point of
`U ∩ U'` top-good for two labelled structures the top-dimensional parts `Θ_k` agree); `A` is its
type, universes at `0`.

`B` says that the project's `IsTopGoodPoint`, `IsTopBadPoint` are the blind notions
(`IsTopGoodB`, `IsTopBadB`) at every `y ∈ M^k_U`, for branched `Θ` and labelled structures.

* `B_holds`: `B` holds outright.  On `M^k_U` the two definitions differ only in that the project
  asks `y ∈ M_U` (implied by `y ∈ M^k_U`) and `V ⊆ U` (replace `V` by `V ∩ U`); `M^k_U`, the top
  dimension and the top-bad clause agree by `rfl`.  The branched hypothesis and the labels are
  not used.  So `A_to_B` is proved without its hypothesis (vacuous).
* `B_to_A`: `A` is not a consequence of `B` (a definitional statement); it is re-proved outright
  below (`A_outright`, the project's proof copied, from the non-item lemmas `lemma_9_6_1`,
  `lemma_9_6_2`, `exists_isGeneric`, `dimPart_topDim_eq_of_isGeneric`, `nbhdAt`), so `B_to_A` is
  also vacuous.  The content of the round trip is the agreement of the definitions. -/

namespace RoundTrip.V9_60
open Polyfold EpGroupoid MPolyfold Set
open Polyfold.EpGroupoid.LocalBranchingStructure

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint.{0}

theorem A_holds : A :=
  @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint.{0}

section Defs
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

/-- On `M^k_U`, the project's top-good point is the blind "the top sheets coincide near `y`". -/
theorem isTopGoodPoint_iff_topCoincideB (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ)
    {y : Obj} (hy : y ∈ MkB L dim (topDimB L dim)) :
    L.IsTopGoodPoint dim y ↔ TopCoincideB L dim y := by
  have hy' : ∃ i, dim i = topDimB L dim ∧ y ∈ L.M i := by
    simpa [MkB] using hy
  obtain ⟨i₀, -, hyi₀⟩ := hy'
  constructor
  · rintro ⟨-, V, hV, hyV, -, hVeq⟩
    exact ⟨V, hV, hyV, hVeq⟩
  · rintro ⟨V, hV, hyV, hVeq⟩
    refine ⟨mem_iUnion.2 ⟨i₀, hyi₀⟩, V ∩ L.U, hV.inter L.isOpen_U,
      ⟨hyV, L.subset_U i₀ hyi₀⟩, inter_subset_right, fun i j hi hj hyi hyj => ?_⟩
    have h := hVeq i j hi hj hyi hyj
    calc V ∩ L.U ∩ L.M i = L.U ∩ (V ∩ L.M i) := by ext; simp only [mem_inter_iff]; tauto
      _ = L.U ∩ (V ∩ L.M j) := by rw [h]
      _ = V ∩ L.U ∩ L.M j := by ext; simp only [mem_inter_iff]; tauto

end Defs

/-- **`B` holds outright** (no use of the branched hypothesis or of the labels). -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ _ x L dim _ y hy
  have hg := isTopGoodPoint_iff_topCoincideB L dim hy
  refine ⟨⟨fun h => ⟨hy, hg.1 h⟩, fun h => hg.2 h.2⟩, ?_⟩
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hy, fun h' => h (hg.2 h')⟩
  · rintro ⟨-, h⟩
    exact ⟨hy, fun h' => h (hg.1 h')⟩

theorem A_to_B : A → B := fun _ => B_holds

/-! ### `A` outright (the project's proof, from non-item lemmas) -/

open scoped Classical in
theorem A_outright : A := by
  intro Obj Mor _ _ _ _ _ _ X Θ x L L' dim dim' hdim hdim' y hyU hyU' h h'
  have hK : L'.topDim dim' = L.topDim dim := (lemma_9_6_1 hdim hdim').symm
  have h962 := lemma_9_6_2 hdim hdim'
  by_cases hyT : y ∈ L.topUnion dim (L.topDim dim)
  · obtain ⟨i₀, hi₀, hyi₀⟩ := L.mem_topUnion.1 hyT
    obtain ⟨-, V, hV, hyV, -, hVeq⟩ := h
    obtain ⟨-, V', hV', hyV', -, hV'eq⟩ := h'
    set W := V ∩ V' ∩ (L.nbhdAt y ∩ L'.nbhdAt y)
    have hW : IsOpen W := (hV.inter hV').inter ((L.isOpen_nbhdAt y).inter (L'.isOpen_nbhdAt y))
    have hWU : W ⊆ L.U ∩ L'.U := fun z hz => ⟨hz.2.1.1, hz.2.2.1⟩
    have hyW : y ∈ W := ⟨⟨hyV, hyV'⟩, L.mem_nbhdAt_self hyU, L'.mem_nbhdAt_self hyU'⟩
    obtain ⟨z, ⟨hzi₀, hzW⟩, hgen⟩ := exists_isGeneric hdim hdim' (hdim i₀) hW hWU hyi₀ hyW
    have c1 : ∀ i, dim i = L.topDim dim → (z ∈ L.M i ↔ y ∈ L.M i) := fun i hi =>
      ⟨hzW.2.1.2 i, fun hyi => by
        have : z ∈ V ∩ L.M i₀ := ⟨hzW.1.1, hzi₀⟩
        rw [← hVeq i i₀ hi hi₀ hyi hyi₀] at this
        exact this.2⟩
    have hzT' : z ∈ L'.topUnion dim' (L'.topDim dim') := by
      have : z ∈ L.topUnion dim (L.topDim dim) ∩ L'.U :=
        ⟨L.mem_topUnion.2 ⟨i₀, hi₀, hzi₀⟩, (hWU hzW).2⟩
      rw [h962] at this
      exact this.1
    obtain ⟨j₀, hj₀, hzj₀⟩ := L'.mem_topUnion.1 hzT'
    have hyj₀ : y ∈ L'.M j₀ := hzW.2.2.2 j₀ hzj₀
    have c2 : ∀ j, dim' j = L'.topDim dim' → (z ∈ L'.M j ↔ y ∈ L'.M j) := fun j hj =>
      ⟨hzW.2.2.2 j, fun hyj => by
        have : z ∈ V' ∩ L'.M j₀ := ⟨hzW.1.2, hzj₀⟩
        rw [← hV'eq j j₀ hj hj₀ hyj hyj₀] at this
        exact this.2⟩
    have e1 : L.dimPart dim (L.topDim dim) y = L.dimPart dim (L.topDim dim) z := by
      unfold dimPart
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1, (c1 i h.1).2 h.2⟩, fun h => ⟨h.1, (c1 i h.1).1 h.2⟩⟩
    have e2 : L'.dimPart dim' (L'.topDim dim') y = L'.dimPart dim' (L'.topDim dim') z := by
      unfold dimPart
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1, (c2 j h.1).2 h.2⟩, fun h => ⟨h.1, (c2 j h.1).1 h.2⟩⟩
    rw [e1, e2, dimPart_topDim_eq_of_isGeneric hdim hdim' (hWU hzW).1 (hWU hzW).2 (hi₀ ▸ hgen)]
  · have hyT' : y ∉ L'.topUnion dim' (L'.topDim dim') := fun hy' => by
      have : y ∈ L'.topUnion dim' (L'.topDim dim') ∩ L.U := ⟨hy', hyU⟩
      rw [← h962] at this
      exact hyT this.1
    rw [L.dimPart_eq_zero_of_notMem_topUnion hyT, L'.dimPart_eq_zero_of_notMem_topUnion hyT']

theorem B_to_A : B → A := fun _ => A_outright

#rt_check RoundTrip.V9_60.A_to_B
  [Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint]
#rt_check RoundTrip.V9_60.B_to_A
  [Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint]
#rt_overlap RoundTrip.V9_60.B_to_A
  [Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint]

end RoundTrip.V9_60
