import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_43

/-! Round trip for V9_43 (Definition 9.4.5, 2021 p. 431; 2017: Definition 9.13: sets of measure
zero).

The item lists the definition `IsMeasureZero` (vocabulary) and three theorems.  `A` is the
conjunction of their types, universes at `0`: `isMeasureZero_iUnion` (countable unions),
`isMeasureZero_of_forall_mem` (the chart criterion: one null chart image around each point
suffices) and `not_isMeasureZero_univ` (`ℝ²` is not null: the definition is not vacuous).

`B` says that the project's `IsMeasureZero (Q n) K` is the text's notion for an `n`-dimensional
manifold with corners modelled on the quadrant `[0, ∞)ⁿ ⊆ ℝⁿ = EuclideanSpace ℝ (Fin n)`:
`volume (φ(U ∩ K)) = 0` for every chart of the maximal `C^∞` atlas.

* `B` holds by `Iff.rfl` (`B_holds`): the project's `chartImage I e K` is `e.extend I '' (e.source ∩
  K)` and both sides use the instance `volume` of `EuclideanSpace ℝ (Fin n)` (the project's
  `IsMeasureZero` takes `[MeasureSpace E]` as an instance argument, which `B`'s statement fills
  with the same instance as `IsMeasureZeroB`).  So `A ⇒ B` is vacuous (`B` is proved outright).
* `B ⇒ A` is vacuous too: `A`'s three theorems are general facts about the project's definition
  for an arbitrary model with corners `I : H → E` and an arbitrary `MeasureSpace E`; `B` (quadrant
  models only, and an iff of definitions) does not give them.  They are re-proved outright here
  from non-item lemmas (`iUnion_re`, `of_forall_mem_re`, `not_univ_re`, copies of the project's
  proofs).
-/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V9_43
open Polyfold Set Filter Topology MeasureTheory Manifold
open scoped ContDiff

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isMeasureZero_iUnion.{0, 0, 0, 0} ∧
  type_of% @Polyfold.isMeasureZero_of_forall_mem.{0, 0, 0} ∧
  type_of% @Polyfold.not_isMeasureZero_univ

theorem A_holds : A :=
  ⟨@Polyfold.isMeasureZero_iUnion, @Polyfold.isMeasureZero_of_forall_mem,
    Polyfold.not_isMeasureZero_univ⟩

/-- **`B` holds outright**: the two definitions are the same term. -/
theorem B_holds : B := by
  intro n M _ _ _ K
  exact Iff.rfl

theorem A_to_B : A → B := fun _ => B_holds

/-! ### Outright re-proofs of `A`'s three theorems (copies of the project's proofs) -/

section Reproofs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [MeasureSpace E]

theorem iUnion_re {ι : Type} [Countable ι] {K : ι → Set M}
    (h : ∀ i, IsMeasureZero I (K i)) : IsMeasureZero I (⋃ i, K i) := fun e he => by
  rw [chartImage, inter_iUnion, image_iUnion]
  exact measure_iUnion_null fun i => h i e he

theorem of_forall_mem_re [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [IsManifold I ∞ M] {K : Set M}
    (h : ∀ z ∈ K, ∃ e ∈ IsManifold.maximalAtlas I ∞ M, z ∈ e.source ∧
      volume (chartImage I e K) = 0) :
    IsMeasureZero I K := by
  intro e' he'
  set S' := chartImage I e' K with hS'
  choose c hc hzc hc0 using h
  let W : ↥(e'.source ∩ K) → Set S' := fun z =>
    ((↑) : S' → E) ⁻¹' ((e'.extend I).symm ⁻¹' (c z.1 z.2.2).source)
  have hS'sub : S' ⊆ (e'.extend I).target := by
    rintro _ ⟨w, hw, rfl⟩
    exact (e'.extend I).map_source (by rw [e'.extend_source]; exact hw.1)
  have hW : ∀ z, IsOpen (W z) := by
    intro z
    have hcont : Continuous fun q : S' => (e'.extend I).symm q :=
      (e'.continuousOn_extend_symm (I := I)).comp_continuous continuous_subtype_val
        fun q => hS'sub q.2
    exact (c z.1 z.2.2).open_source.preimage hcont
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hcover : S' ⊆ ⋃ z ∈ T, I.extendCoordChange (c z.1 z.2.2) e' ''
      (chartImage I (c z.1 z.2.2) K ∩ (I.extendCoordChange (c z.1 z.2.2) e').source) := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := hq
    have hmem : (⟨e'.extend I w, ⟨w, hw, rfl⟩⟩ : S') ∈ ⋃ z, W z := by
      refine mem_iUnion.2 ⟨⟨w, hw⟩, ?_⟩
      change (e'.extend I).symm (e'.extend I w) ∈ (c w hw.2).source
      rw [e'.extend_left_inv hw.1]
      exact hzc w hw.2
    rw [← hTU] at hmem
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.1 hmem
    change (e'.extend I).symm (e'.extend I w) ∈ (c z.1 z.2.2).source at hz
    rw [e'.extend_left_inv hw.1] at hz
    exact mem_iUnion₂.2 ⟨z, hzT, (c z.1 z.2.2).extend I w, ⟨⟨w, ⟨hz, hw.2⟩, rfl⟩,
      extend_mem_extendCoordChange_source hz hw.1⟩, extendCoordChange_apply_of_mem hz⟩
  refine measure_mono_null hcover ((measure_biUnion_null_iff hT).2 fun z _ => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left (hc0 z.1 z.2.2))
  exact ((I.contDiffOn_extendCoordChange (hc z.1 z.2.2) he').differentiableOn
    (by simp)).mono inter_subset_right

end Reproofs

theorem not_univ_re : ¬ IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) (univ : Set (Fin 2 → ℝ)) := by
  intro h
  have h0 := h (chartAt (Fin 2 → ℝ) (0 : Fin 2 → ℝ))
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin 2 → ℝ)) (n := ∞) 0)
  rw [chartImage_chartAt_self] at h0
  exact (Metric.measure_closedBall_pos volume (0 : Fin 2 → ℝ) one_pos).ne'
    (measure_mono_null (subset_univ _) h0)

/-- `B ⇒ A`, vacuously: `A`'s three theorems are re-proved outright. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@iUnion_re, @of_forall_mem_re, not_univ_re⟩

#rt_check RoundTrip.V9_43.A_to_B [Polyfold.isMeasureZero_iUnion,
  Polyfold.isMeasureZero_of_forall_mem, Polyfold.not_isMeasureZero_univ]
#rt_check RoundTrip.V9_43.B_to_A [Polyfold.isMeasureZero_iUnion,
  Polyfold.isMeasureZero_of_forall_mem, Polyfold.not_isMeasureZero_univ]
#rt_overlap RoundTrip.V9_43.B_to_A [Polyfold.isMeasureZero_iUnion,
  Polyfold.isMeasureZero_of_forall_mem, Polyfold.not_isMeasureZero_univ]
#print axioms RoundTrip.V9_43.B_to_A

end RoundTrip.V9_43
