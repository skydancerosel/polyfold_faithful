import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_58

/-! Round trip for V9_58 (2021 Lemma 9.6.1, p. 453, and `dim_Θ`, p. 454: the top dimension).

The item lists the definitions `LocalBranchingStructure.topDim`, `EpGroupoid.localTopDim`
(vocabulary) and five theorems; `A` is the conjunction of their types, universes at `0`:
`MPolyfold.HasDimAt.le_of_inter_subset` (`A1`) and `MPolyfold.exists_mem_forall_notMem` (`A2`,
the covering lemma replacing "measure zero"), `lemma_9_6_1` (`A3`: two structures at `x` whose
sheets carry constant-dimension labels `dim`, `IsSubmanifoldOfDim (Mᵢ) (dim i)`, have the same
top dimension `maxᵢ dim i`; no hypothesis on `Θ` or `x`), `localTopDim_eq` (`A4`: on `supp Θ`,
`dim_Θ(x)` is the top dimension of every labelled structure) and `localTopDim_eq_bot` (`A5`).

`B` (branched `Θ`, `x ∈ supp Θ`, arbitrary structures, no labels): (a) every structure has a top
dimension in the pointwise sense `IsTopDimAtB` (`maxᵢ dim T_xMᵢ`, the dimension of each sheet *at
`x`*, read with the blind `HasDimB`); (b) two structures have the same one; (c) it is the
project's `localTopDim`.

Glue: the blind dimension is the project's `HasDimAt` on submanifolds (`hasDimB_of`,
`hasDimAt_of`, copied from `RoundTrip/Items/V9_2.lean`).

* `A → B` fails on (b), (c): `A3`, `A4` need constant-dimension labels on all sheets, `B` gives a
  structure whose sheets only have a dimension at `x`.  To label them one shrinks the structure
  to a neighbourhood where each sheet has constant dimension, i.e. needs **local constancy of the
  dimension** (Remark 9.1.1), which the project proves only in `ℝᵐ`
  (`hasLocallyConstantDimAt_rn`; see V9_2).  Proved:
  - `A_to_Ba`: (a) holds (outright: each sheet has a dimension at `x`, `HasDimAt.unique`);
  - `A_to_B_of_hasLocallyConstantDimAt`: all of `B` at the points where the dimension is locally
    constant (the non-item `exists_restrict_labelled` shrinks to a labelled structure; then `A3`,
    `A4`), in particular for every ep-groupoid over `ℝᵐ`.
* `B → A` fails: `A3`, `A4` hold for every `Θ` (no branched hypothesis), `B` only for branched
  `Θ`; `A1`, `A2` (general M-polyfold lemmas) and `A5` (the convention off `supp Θ`) are not in
  `B`.  Proved: `B_to_A3_of_branched`, `B_to_A4_of_branched` (labels give the pointwise top
  dimension). -/

namespace RoundTrip.V9_58
open Polyfold EpGroupoid MPolyfold Set

/-- The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.MPolyfold.HasDimAt.le_of_inter_subset.{0}
def A2 : Prop := type_of% @Polyfold.MPolyfold.exists_mem_forall_notMem.{0, 0}
def A3 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1.{0}
def A4 : Prop := type_of% @Polyfold.EpGroupoid.localTopDim_eq.{0}
def A5 : Prop := type_of% @Polyfold.EpGroupoid.localTopDim_eq_bot.{0}
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.HasDimAt.le_of_inter_subset.{0},
    @Polyfold.MPolyfold.exists_mem_forall_notMem.{0, 0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1.{0},
    @Polyfold.EpGroupoid.localTopDim_eq.{0}, @Polyfold.EpGroupoid.localTopDim_eq_bot.{0}⟩

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

section Top
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

theorem hasDimB_iff_of_hasDimAt {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} (hy : y ∈ A)
    {n : ℕ} (h : P.HasDimAt A y n) {j : ℕ} : HasDimB P A y j ↔ j = n :=
  ⟨fun hj => (hasDimAt_of hA hy hj).unique h, fun hj => hj ▸ hasDimB_of hA h⟩

end Top

section Labels
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

theorem nonempty_of_mem_supp (L : X.LocalBranchingStructure Θ x) (hx : x ∈ supp Θ) :
    Nonempty L.ι := by
  obtain ⟨i, -⟩ := (L.mem_supp_iff L.mem_U).1 hx
  exact ⟨i⟩

theorem isEmpty_of_notMem_supp (L : X.LocalBranchingStructure Θ x) (hx : x ∉ supp Θ) :
    IsEmpty L.ι :=
  ⟨fun i => hx ((L.mem_supp_iff L.mem_U).2 ⟨i, L.mem_M i⟩)⟩

/-- If the dimension of `Mᵢ` at `x` is `dim i`, the pointwise top dimension is `maxᵢ dim i`. -/
theorem isTopDimAtB_iff (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ)
    (hd : ∀ i j, HasDimB X.PObj (L.M i) x j ↔ j = dim i) [Nonempty L.ι] (k : ℕ) :
    IsTopDimAtB L k ↔ k = L.topDim dim := by
  constructor
  · rintro ⟨⟨i, hi⟩, hle⟩
    refine le_antisymm ?_ (Finset.sup_le fun i' _ => hle i' (dim i') ((hd i' _).2 rfl))
    rw [(hd i k).1 hi]
    exact L.dim_le_topDim dim i
  · rintro rfl
    obtain ⟨i, hi⟩ := L.exists_dim_eq_topDim dim
    refine ⟨⟨i, (hd i _).2 hi.symm⟩, fun i' j hj => ?_⟩
    rw [(hd i' j).1 hj]
    exact L.dim_le_topDim dim i'

/-- Labels give the dimension at `x`. -/
theorem hd_of_labels (L : X.LocalBranchingStructure Θ x) {dim : L.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) (i : L.ι) (j : ℕ) :
    HasDimB X.PObj (L.M i) x j ↔ j = dim i :=
  hasDimB_iff_of_hasDimAt (L.isSmoothSubmanifold i) (L.mem_M i) ((hdim i).2 x (L.mem_M i))

/-- The dimension at `x` of the sheets of a restriction with labels. -/
theorem hd_of_restrict (L : X.LocalBranchingStructure Θ x) {V : Set Obj} (hV : IsOpen V)
    (hxV : x ∈ V) (hVU : V ⊆ L.U) {dim : L.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim ((L.restrict hV hxV hVU).M i) (dim i)) (i : L.ι)
    (j : ℕ) : HasDimB X.PObj (L.M i) x j ↔ j = dim i := by
  have h : X.PObj.HasDimAt (L.M i ∩ V) x (dim i) := (hdim i).2 x ⟨L.mem_M i, hxV⟩
  exact hasDimB_iff_of_hasDimAt (L.isSmoothSubmanifold i) (L.mem_M i)
    ((hasDimAt_inter_isOpen_iff (L.isSmoothSubmanifold i) hV hxV).1 h)

end Labels

/-! ### What `A` gives of `B` -/

/-- **(a) holds** (outright: every sheet has a dimension at `x`). -/
theorem A_to_Ba : A →
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ L : X.LocalBranchingStructure Θ x, ∃ k, IsTopDimAtB L k := by
  intro _ Obj Mor _ _ _ _ _ _ X Θ _ x hx L
  have := nonempty_of_mem_supp L hx
  have h : ∀ i, ∃ n, X.PObj.HasDimAt (L.M i) x n := fun i =>
    (L.isSmoothSubmanifold i).exists_hasDimAt (L.mem_M i)
  choose dim hdim using h
  exact ⟨L.topDim dim, (isTopDimAtB_iff L dim (fun i j => hasDimB_iff_of_hasDimAt
    (L.isSmoothSubmanifold i) (L.mem_M i) (hdim i)) _).2 rfl⟩

/-- **All of `B` where the dimension is locally constant** (Remark 9.1.1; e.g. over `ℝᵐ`,
`hasLocallyConstantDimAt_rn`). -/
theorem A_to_B_of_hasLocallyConstantDimAt : A →
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      ∀ x ∈ EpGroupoid.supp Θ, X.PObj.HasLocallyConstantDimAt x →
      (∀ B : X.LocalBranchingStructure Θ x, ∃ k, IsTopDimAtB B k) ∧
      (∀ (B B' : X.LocalBranchingStructure Θ x) (k k' : ℕ),
        IsTopDimAtB B k → IsTopDimAtB B' k' → k = k') ∧
      (∀ (B : X.LocalBranchingStructure Θ x) (k : ℕ), IsTopDimAtB B k →
        X.localTopDim Θ x = (k : WithBot ℕ)) := by
  rintro hA Obj Mor _ _ _ _ _ _ X Θ hΘ x hx hLC
  -- every structure: its pointwise top dimension is the top dimension of a labelled restriction
  have key : ∀ L : X.LocalBranchingStructure Θ x, ∃ (L₀ : X.LocalBranchingStructure Θ x)
      (dim : L₀.ι → ℕ), (∀ i, X.PObj.IsSubmanifoldOfDim (L₀.M i) (dim i)) ∧
      ∀ k, IsTopDimAtB L k ↔ k = L₀.topDim dim := by
    intro L
    have := nonempty_of_mem_supp L hx
    obtain ⟨V, hV, hxV, hVU, dim, hdim⟩ := L.exists_restrict_labelled hLC
    exact ⟨L.restrict hV hxV hVU, dim, hdim,
      isTopDimAtB_iff L dim (hd_of_restrict L hV hxV hVU hdim)⟩
  refine ⟨A_to_Ba hA Obj Mor X Θ hΘ x hx, fun L L' k k' hk hk' => ?_, fun L k hk => ?_⟩
  · obtain ⟨L₀, dim, hdim, hL⟩ := key L
    obtain ⟨L₀', dim', hdim', hL'⟩ := key L'
    rw [(hL k).1 hk, (hL' k').1 hk']
    exact hA.2.2.1 hdim hdim'
  · obtain ⟨L₀, dim, hdim, hL⟩ := key L
    rw [(hL k).1 hk]
    exact hA.2.2.2.1 L₀ hdim hx

/-! ### What `B` gives of `A`: `A3`, `A4` for branched `Θ` -/

theorem B_to_A3_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L L' : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (dim' : L'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (L'.M j) (dim' j)) → L.topDim dim = L'.topDim dim' := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L L' dim dim' hd hd'
  by_cases hx : x ∈ supp Θ
  · have := nonempty_of_mem_supp L hx
    have := nonempty_of_mem_supp L' hx
    exact (hB Obj Mor X Θ hΘ x hx).2.1 L L' _ _
      ((isTopDimAtB_iff L dim (hd_of_labels L hd) _).2 rfl)
      ((isTopDimAtB_iff L' dim' (hd_of_labels L' hd') _).2 rfl)
  · have := isEmpty_of_notMem_supp L hx
    have := isEmpty_of_notMem_supp L' hx
    simp [LocalBranchingStructure.topDim]

theorem B_to_A4_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) → x ∈ supp Θ →
      X.localTopDim Θ x = (L.topDim dim : WithBot ℕ) := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L dim hd hx
  have := nonempty_of_mem_supp L hx
  exact (hB Obj Mor X Θ hΘ x hx).2.2 L _ ((isTopDimAtB_iff L dim (hd_of_labels L hd) _).2 rfl)

#rt_check RoundTrip.V9_58.A_to_Ba [Polyfold.MPolyfold.HasDimAt.le_of_inter_subset,
  Polyfold.MPolyfold.exists_mem_forall_notMem,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1, Polyfold.EpGroupoid.localTopDim_eq,
  Polyfold.EpGroupoid.localTopDim_eq_bot]
#rt_check RoundTrip.V9_58.A_to_B_of_hasLocallyConstantDimAt [Polyfold.MPolyfold.HasDimAt.le_of_inter_subset,
  Polyfold.MPolyfold.exists_mem_forall_notMem,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1, Polyfold.EpGroupoid.localTopDim_eq,
  Polyfold.EpGroupoid.localTopDim_eq_bot]
#rt_check RoundTrip.V9_58.B_to_A3_of_branched [Polyfold.MPolyfold.HasDimAt.le_of_inter_subset,
  Polyfold.MPolyfold.exists_mem_forall_notMem,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1, Polyfold.EpGroupoid.localTopDim_eq,
  Polyfold.EpGroupoid.localTopDim_eq_bot]
#rt_check RoundTrip.V9_58.B_to_A4_of_branched [Polyfold.MPolyfold.HasDimAt.le_of_inter_subset,
  Polyfold.MPolyfold.exists_mem_forall_notMem,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1, Polyfold.EpGroupoid.localTopDim_eq,
  Polyfold.EpGroupoid.localTopDim_eq_bot]
#rt_overlap RoundTrip.V9_58.B_to_A3_of_branched [Polyfold.MPolyfold.HasDimAt.le_of_inter_subset,
  Polyfold.MPolyfold.exists_mem_forall_notMem,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1, Polyfold.EpGroupoid.localTopDim_eq,
  Polyfold.EpGroupoid.localTopDim_eq_bot]

end RoundTrip.V9_58
