import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_21

/-! Round trip for V9_21 (Lemma 9.2.7 (2), p. 412 of the 2021 book; 2017: Lemma 9.5 (2)): at a
bad point `x` of an equidimensional `Θ`, every `Mᵢ` of a local branching structure at `x`
contains good points converging to `x`.

`A` is the conjunction of the types of the five listed theorems, universe instantiated at `0`
where there is one (`B` lives in `Type`): `MPolyfold.hasDomainInvarianceAt_rn` (invariance of
domain for equidimensional submanifolds of `ℝᵐ`), `EpGroupoid.lemma_9_2_7_2` (the lemma, for a
structure whose `Mᵢ` are all `n`-dimensional, under the hypothesis `HasDomainInvarianceAt y n`
at every `y ∈ U(x)`; any `Θ`, any `x`), `EpGroupoid.lemma_9_2_7_2_rn` (the same over `ℝᵐ`, no
invariance hypothesis), `Remark913Hyp.zero_mem_badSet` and
`Remark913Hyp.exists_seq_goodSet_structureβ` (a nontrivial instance in `ℝ²`).

* `A_to_B` is not proved.  `B` covers every local branching structure at `x` of every
  equidimensional `Θ` on every M-polyfold; `A`'s general lemma needs two things `B`'s hypotheses
  do not supply: (i) the structure is `n`-dimensional (`B.IsOfDim n`; `IsNDimensional Θ n` only
  gives SOME `n`-dimensional structure at each point), and (ii) `HasDomainInvarianceAt y n` at
  the points of `U(x)`, a Part I fact the project proves only in `ℝᵐ`.  Both are satisfiable
  (e.g. over `ℝᵐ`) and believed true in general, but proving (ii) for M-polyfolds is real
  mathematics.  `A_gives_B_of` proves `B`'s conclusion from `A` under (i) and (ii), and
  `A_gives_B_rn` over `ℝᵐ` under (i) alone.
* `B_to_A` is not proved: `A` contains invariance of domain in `ℝᵐ`
  (`hasDomainInvarianceAt_rn`) and the Remark 9.1.3 (b) example, which `B` does not state, and
  `lemma_9_2_7_2` holds at every `x` (good or bad) for every `Θ` (not necessarily branched or
  equidimensional), outside `B`'s scope. -/

namespace RoundTrip.V9_21
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.hasDomainInvarianceAt_rn) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_2_7_2.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_2_7_2_rn) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.zero_mem_badSet) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.exists_seq_goodSet_structureβ)

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.hasDomainInvarianceAt_rn, @Polyfold.EpGroupoid.lemma_9_2_7_2.{0},
    @Polyfold.EpGroupoid.lemma_9_2_7_2_rn, @Polyfold.EpGroupoid.Remark913Hyp.zero_mem_badSet,
    @Polyfold.EpGroupoid.Remark913Hyp.exists_seq_goodSet_structureβ⟩

section glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ}

/-- B's good point is the project's `IsGoodPoint`. -/
theorem isGoodAt_iff {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) :
    IsGoodAt B y ↔ B.IsGoodPoint y := by
  unfold IsGoodAt EpGroupoid.LocalBranchingStructure.IsGoodPoint
  refine and_congr Iff.rfl (exists_congr fun V => and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl ?_)))
  refine ⟨fun h i j hi hj => ?_, fun h i j hij => ?_⟩
  · rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]
  · rw [inter_comm, h i j hij.1 hij.2, inter_comm]

/-- B's "good point of `supp Θ`" is membership in the project's `goodSet`. -/
theorem mem_goodSet_iff' (y : Obj) :
    y ∈ X.goodSet Θ ↔ y ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ y := by
  simp only [EpGroupoid.goodSet, IsGoodPt, isGoodAt_iff, mem_ofPred_eq]

end glue

/-- `B`'s conclusion from `A` for an `n`-dimensional structure under invariance of domain. -/
theorem A_gives_B_of (hA : A) {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) {n : ℕ}
    (hdim : B.IsOfDim n) (hDI : ∀ y ∈ B.U, X.PObj.HasDomainInvarianceAt y n) (i : B.ι) :
    ∃ y : ℕ → Obj, (∀ k, y k ∈ B.M i ∧ y k ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ (y k)) ∧
      Filter.Tendsto y Filter.atTop (nhds x) := by
  obtain ⟨u, hu, hlim⟩ := hA.2.1 B hdim hDI i
  exact ⟨u, fun k => ⟨(hu k).1, (mem_goodSet_iff' _).1 (hu k).2⟩, hlim⟩

/-- `B`'s conclusion from `A` over `ℝᵐ` for an `n`-dimensional structure. -/
theorem A_gives_B_rn (hA : A) {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor]
    [ParacompactSpace Mor] {X : EpGroupoid (Fin m → ℝ) Mor} (hX : X.PObj = rnPolyfold m)
    {Θ : (Fin m → ℝ) → ℚ} {x : Fin m → ℝ} (B : X.LocalBranchingStructure Θ x) {n : ℕ}
    (hdim : B.IsOfDim n) (i : B.ι) :
    ∃ y : ℕ → Fin m → ℝ, (∀ k, y k ∈ B.M i ∧ y k ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ (y k)) ∧
      Filter.Tendsto y Filter.atTop (nhds x) := by
  obtain ⟨u, hu, hlim⟩ := hA.2.2.1 hX B hdim i
  exact ⟨u, fun k => ⟨(hu k).1, (mem_goodSet_iff' _).1 (hu k).2⟩, hlim⟩

#rt_check RoundTrip.V9_21.A_gives_B_of [Polyfold.MPolyfold.hasDomainInvarianceAt_rn,
  Polyfold.EpGroupoid.lemma_9_2_7_2, Polyfold.EpGroupoid.lemma_9_2_7_2_rn,
  Polyfold.EpGroupoid.Remark913Hyp.zero_mem_badSet,
  Polyfold.EpGroupoid.Remark913Hyp.exists_seq_goodSet_structureβ]
#rt_check RoundTrip.V9_21.A_gives_B_rn [Polyfold.MPolyfold.hasDomainInvarianceAt_rn,
  Polyfold.EpGroupoid.lemma_9_2_7_2, Polyfold.EpGroupoid.lemma_9_2_7_2_rn,
  Polyfold.EpGroupoid.Remark913Hyp.zero_mem_badSet,
  Polyfold.EpGroupoid.Remark913Hyp.exists_seq_goodSet_structureβ]

end RoundTrip.V9_21
