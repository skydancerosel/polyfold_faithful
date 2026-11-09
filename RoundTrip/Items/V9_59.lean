import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_59

/-! Round trip for V9_59 (2021 Lemma 9.6.2, p. 454: the union `M^k_U` of the top-dimensional
sheets does not depend on the structure).

The item lists the definition `LocalBranchingStructure.topUnion` (vocabulary) and two theorems;
`A` is the conjunction of their types, universes at `0`: `lemma_9_6_2`
(`M_U^k ∩ U' = M'^k_U ∩ U` for two labelled structures at `x`) and `mem_topUnion_iff_of_mem` (the
same pointwise on `U ∩ U'`).  Neither has a hypothesis on `Θ` or on `x`.

`B`: for a branched ep⁺-subgroupoid `Θ`, `x ∈ supp Θ` and two structures at `x` with dimension
labels in the blind sense (`IsDimLabelB`: `HasDimB`, `T_mMᵢ` read in a chart has dimension
`dim i` at every `m ∈ Mᵢ`), `MkB ∩ U' = MkB' ∩ U`.

Glue: the blind dimension is the project's on submanifolds (`hasDimB_of`, `hasDimAt_of`, copied
from `RoundTrip/Items/V9_2.lean`), so `IsDimLabelB B dim ↔ ∀ i, IsSubmanifoldOfDim (Mᵢ) (dim i)`;
`MkB`/`topDimB` are `topUnion`/`topDim` by `rfl`.

* `A_to_B` (proved): `lemma_9_6_2` on the translated labels.
* `B → A` (not proved as a whole): `A` has no branched hypothesis on `Θ`; `B` has.  Proved on
  `B`'s domain: `B_to_A_of_branched` (both conjuncts of `A` for branched `Θ`; off `supp Θ` both
  structures are empty).  For general `Θ` `B` says nothing; `A`'s proof does not use the
  branched hypothesis (it is the non-item `topUnion_inter_subset`, a covering argument), so the
  gap is generality only. -/

namespace RoundTrip.V9_59
open Polyfold EpGroupoid MPolyfold Set

/-- The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2.{0}
def A2 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem.{0}
def A : Prop := A1 ∧ A2

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem.{0}⟩

/-! ### The two dimension notions agree on submanifolds (from `RoundTrip/Items/V9_2.lean`) -/

section Dim
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

theorem tyMB_eq {A : Set Z} {y : Z} (hyA : y ∈ A) : TyMB P A y = P.submanifoldTangent A y := by
  ext α
  constructor
  · rintro ⟨d, hyV, β, hβ, rfl⟩
    have hβ' : P.levelVal 1 (P.tangentProj β) = y := hβ
    have hβV : β ∈ P.tangentPreimage d.V := by
      change P.levelVal 1 (P.tangentProj β) ∈ d.V
      rw [hβ']; exact hyV
    have := d.tmap_mem_submanifoldTangent hβV
    rwa [hβ', d.apply_eq_self ⟨hyA, hyV⟩] at this
  · rintro ⟨hαy, d, hyV, hfix⟩
    exact ⟨d, hyV, α, hαy, hfix⟩

theorem chartImgB_eq {φ : MChart Z} (hφ : P.IsChart φ) {A : Set Z} {y : Z} (hyA : y ∈ A) :
    chartImgB hφ (TyMB P A y) = P.chartTangent hφ A y := by
  rw [chartImgB, tyMB_eq hyA]
  rfl

theorem hasDimB_of {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} {n : ℕ}
    (h : P.HasDimAt A y n) : HasDimB P A y n := by
  have hyA := h.1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hA hyA hyφ
  refine ⟨φ, hφ, hyφ, N, hfin, ?_, ?_⟩
  · rw [chartImgB_eq hφ hyA, hN]
  · set d := hA.data hyA
    have hyV := hA.mem_data_V hyA
    have hy1 := d.mem_levelSet_one hyA hyV
    have hz := P.toBase_levelLift hφ hyφ hy1
    have h1 := h.finrank_eq d hφ hyV hyφ hz
    rw [← chartTangent_eq hφ d hyA hyV hyφ, ← hN, Submodule.span_eq] at h1
    exact h1

theorem hasDimAt_of {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} (hyA : y ∈ A) {n : ℕ}
    (h : HasDimB P A y n) : P.HasDimAt A y n := by
  obtain ⟨φ, hφ, hyφ, S, -, hS, hn⟩ := h
  set d := hA.data hyA
  have hyV := hA.mem_data_V hyA
  have hy1 := d.mem_levelSet_one hyA hyV
  have hz := P.toBase_levelLift hφ hyφ hy1
  refine ⟨hyA, d, φ, levelLift φ 1 y, hyV, hφ, hyφ, hz, ?_⟩
  rw [← chartTangent_eq hφ d hyA hyV hyφ, ← chartImgB_eq hφ hyA, hS, Submodule.span_eq]
  exact hn

end Dim

section Labels
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

theorem isSubmanifoldOfDim_of_label {L : X.LocalBranchingStructure Θ x} {dim : L.ι → ℕ}
    (h : IsDimLabelB L dim) : ∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i) := fun i =>
  ⟨L.isSmoothSubmanifold i, fun m hm => hasDimAt_of (L.isSmoothSubmanifold i) hm (h i m hm)⟩

theorem label_of_isSubmanifoldOfDim {L : X.LocalBranchingStructure Θ x} {dim : L.ι → ℕ}
    (h : ∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) : IsDimLabelB L dim := fun i m hm =>
  hasDimB_of (L.isSmoothSubmanifold i) ((h i).2 m hm)

theorem mkB_eq (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) :
    MkB L dim (topDimB L dim) = L.topUnion dim (L.topDim dim) := rfl

/-- Off `supp Θ` a structure at `x` has no sheets. -/
theorem isEmpty_of_notMem_supp (L : X.LocalBranchingStructure Θ x) (hx : x ∉ supp Θ) :
    IsEmpty L.ι :=
  ⟨fun i => hx ((L.mem_supp_iff L.mem_U).2 ⟨i, L.mem_M i⟩)⟩

theorem topUnion_eq_empty (L : X.LocalBranchingStructure Θ x) (hx : x ∉ supp Θ)
    (dim : L.ι → ℕ) (k : ℕ) : L.topUnion dim k = ∅ := by
  have := isEmpty_of_notMem_supp L hx
  ext y
  simp [LocalBranchingStructure.topUnion]

end Labels

theorem A_to_B : A → B := by
  rintro ⟨h1, -⟩
  intro Obj Mor _ _ _ _ _ _ X Θ _ x _ L L' dim dim' hl hl'
  exact h1 (isSubmanifoldOfDim_of_label hl) (isSubmanifoldOfDim_of_label hl')

/-! ### What `B` gives of `A`: `A` for branched `Θ` -/

/-- `A1` for branched `Θ`, from `B`. -/
theorem B_to_A1_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L L' : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (dim' : L'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (L'.M j) (dim' j)) →
      L.topUnion dim (L.topDim dim) ∩ L'.U = L'.topUnion dim' (L'.topDim dim') ∩ L.U := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L L' dim dim' hd hd'
  by_cases hx : x ∈ supp Θ
  · exact hB Obj Mor X Θ hΘ x hx L L' dim dim' (label_of_isSubmanifoldOfDim hd)
      (label_of_isSubmanifoldOfDim hd')
  · rw [topUnion_eq_empty L hx, topUnion_eq_empty L' hx, empty_inter, empty_inter]

/-- `A2` for branched `Θ`, from `B`. -/
theorem B_to_A2_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L L' : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (dim' : L'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (L'.M j) (dim' j)) →
      ∀ y ∈ L.U, y ∈ L'.U →
        (y ∈ L.topUnion dim (L.topDim dim) ↔ y ∈ L'.topUnion dim' (L'.topDim dim')) := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L L' dim dim' hd hd' y hyU hyU'
  have h := B_to_A1_of_branched hB Obj Mor X Θ hΘ x L L' dim dim' hd hd'
  constructor
  · intro hy
    have : y ∈ L.topUnion dim (L.topDim dim) ∩ L'.U := ⟨hy, hyU'⟩
    rw [h] at this
    exact this.1
  · intro hy
    have : y ∈ L'.topUnion dim' (L'.topDim dim') ∩ L.U := ⟨hy, hyU⟩
    rw [← h] at this
    exact this.1

#rt_check RoundTrip.V9_59.A_to_B [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem]
#rt_check RoundTrip.V9_59.B_to_A1_of_branched [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem]
#rt_check RoundTrip.V9_59.B_to_A2_of_branched [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem]
#rt_overlap RoundTrip.V9_59.B_to_A2_of_branched [Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_topUnion_iff_of_mem]

end RoundTrip.V9_59
