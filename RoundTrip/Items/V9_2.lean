import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_2

/-! Round trip for V9_2 (Remark 9.1.1, p. 402 [2017: Remark 9.1, p. 291] and the last paragraph of
Definition 9.1.2, p. 402: the dimension of a submanifold, `n`-dimensional `Θ`).

`A` is the conjunction of the types of the nine listed theorems, universes at `0`:
`finrank_tangentSpace_chart_change`, `HasDimAt.finrank_eq`, `HasDimAt.unique`,
`IsSmoothSubmanifold.exists_hasDimAt`, `hasDimAt_inter_isOpen_iff`, `hasDimAt_image_iff` (the
dimension `HasDimAt` is chart independent, unique, exists, is a germ, invariant under
sc-diffeomorphisms), `LocalBranchingStructure.dim_unique`, `isNDimensional_zero` and
`hasLocallyConstantDimAt_rn` (local constancy of the dimension, in `ℝᵐ` only).  The listed
`HasDimAt`, `IsSubmanifoldOfDim`, `LocalBranchingStructure.IsOfDim`, `IsNDimensional`,
`HasLocallyConstantDimAt` are definitions (vocabulary).

`B` = (a) local constancy of the dimension on every submanifold of every M-polyfold, (b) the
project's `IsNDimensional` is the blind `IsNDimB`, (c) the footnote: a branched `Θ` with nonempty
support that is `n`- and `m`-dimensional has `m = n`.

Neither direction is proved.

* `A → B` fails on (a) and (c), which are not in `A` (the project says so: local constancy is
  proved only in `ℝᵐ`, the footnote is not formalized).  (a) needs the local constancy of the
  rank of `T_yM` on an sc⁺-retract in an infinite-dimensional sc-Banach space; (c) needs that a
  piece of an `n`-dimensional submanifold is not covered by finitely many submanifolds of another
  dimension (a dimension / Baire argument).  Both are new mathematics, not glue.
  What *is* proved from `A`:
  - `A_to_Bb`: (b) holds.  The two dimension notions agree on submanifolds
    (`hasDimB_of`, `hasDimAt_of`): the blind `T_yM` (images `Ts(β)` over `y`) is the project's
    `submanifoldTangent` (fixed points of `Ts`), its chart image is `chartTangent`, the tangent
    space of the chart retract, a finite-dimensional subspace (`exists_submodule_chartTangent`),
    and its `finrank` is the project's dimension (with `A`'s `HasDimAt.finrank_eq`); the blind
    properness is the project's (as in `RoundTrip/Items/V9_1.lean`).
  - `A_to_Ba_rn`: (a) for the M-polyfolds `ℝᵐ`, from `hasLocallyConstantDimAt_rn` and
    `hasDimAt_inter_isOpen_iff`.
* `B → A` fails: `A` consists of chart-independence and invariance theorems about the project's
  `HasDimAt` (and its `ℝᵐ` local constancy) that `B` does not imply; they would have to be
  re-proved outright (the project's Part I tangent machinery), which `B` does not help with.
  (`B` (a) for `ℝᵐ` would give `hasLocallyConstantDimAt_rn` through `hasDimAt_of`, but the other
  eight conjuncts stay.) -/

namespace RoundTrip.V9_2
open Polyfold EpGroupoid MPolyfold Set Filter Topology Module

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.finrank_tangentSpace_chart_change.{0}) ∧
  (type_of% @Polyfold.MPolyfold.HasDimAt.finrank_eq.{0}) ∧
  (type_of% @Polyfold.MPolyfold.HasDimAt.unique.{0}) ∧
  (type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.exists_hasDimAt.{0}) ∧
  (type_of% @Polyfold.MPolyfold.hasDimAt_inter_isOpen_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.hasDimAt_image_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dim_unique.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isNDimensional_zero.{0}) ∧
  (type_of% @Polyfold.MPolyfold.hasLocallyConstantDimAt_rn)

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.finrank_tangentSpace_chart_change.{0},
    @Polyfold.MPolyfold.HasDimAt.finrank_eq.{0}, @Polyfold.MPolyfold.HasDimAt.unique.{0},
    @Polyfold.MPolyfold.IsSmoothSubmanifold.exists_hasDimAt.{0},
    @Polyfold.MPolyfold.hasDimAt_inter_isOpen_iff.{0}, @Polyfold.MPolyfold.hasDimAt_image_iff.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dim_unique.{0},
    @Polyfold.EpGroupoid.isNDimensional_zero.{0}, @Polyfold.MPolyfold.hasLocallyConstantDimAt_rn⟩

/-- Part (a) of `B`. -/
def Ba : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z), P.IsSmoothSubmanifold M → ∀ m ∈ M,
      ∃ (n : ℕ) (W : Set Z), IsOpen W ∧ m ∈ W ∧ ∀ m' ∈ M ∩ W, HasDimB P M m' n

/-- Part (b) of `B`. -/
def Bb : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
      X.IsNDimensional Θ n ↔ IsNDimB X Θ n

/-- Part (c) of `B`. -/
def Bc : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n m : ℕ),
      IsBranchedB X Θ → (suppB Θ).Nonempty → IsNDimB X Θ n → IsNDimB X Θ m → m = n

theorem B_iff : B ↔ Ba ∧ Bb ∧ Bc := Iff.rfl

/-! ### Proper inclusions (as in `RoundTrip/Items/V9_1.lean`) -/

section Proper
variable {Z : Type} [TopologicalSpace Z]

theorem isProperMap_inclusion_iff' {A U : Set Z} (h : A ⊆ U) :
    IsProperMap (inclusion h) ↔ IsClosed ((↑) ⁻¹' A : Set U) := by
  have hr : ((↑) ⁻¹' A : Set U) = range (inclusion h) := (range_inclusion h).symm
  rw [hr]
  exact ⟨fun hp => hp.isClosedMap.isClosed_range,
    fun hc => (Topology.IsClosedEmbedding.mk (Topology.IsEmbedding.inclusion h) hc).isProperMap⟩

theorem properInclB_of_isClosed {A U : Set Z} (hc : IsClosed ((↑) ⁻¹' A : Set U)) :
    IsProperInclB A U := by
  intro K hKU hK
  have hK' : IsCompact ((↑) ⁻¹' K : Set U) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.2 hKU]
    exact hK
  have h2 := Subtype.isCompact_iff.1 (hK'.inter_right hc)
  have heq : (Subtype.val '' ((↑) ⁻¹' K ∩ (↑) ⁻¹' A : Set U)) = K ∩ A := by
    rw [← preimage_inter, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.2 fun y hy => hKU hy.1
  rwa [heq] at h2

theorem isClosed_of_properInclB [TopologicalSpace.MetrizableSpace Z] {A U : Set Z}
    (h : IsProperInclB A U) : IsClosed ((↑) ⁻¹' A : Set U) := by
  refine IsSeqClosed.isClosed fun u p hu hlim => ?_
  have hv : Tendsto (fun n => (u n : Z)) atTop (𝓝 (p : Z)) :=
    (continuous_subtype_val.tendsto p).comp hlim
  have hK : IsCompact (insert (p : Z) (range fun n => (u n : Z))) := hv.isCompact_insert_range
  have hKU : insert (p : Z) (range fun n => (u n : Z)) ⊆ U := by
    rintro _ (rfl | ⟨n, rfl⟩)
    · exact p.2
    · exact (u n).2
  have hKA := (h _ hKU hK).isClosed
  have hmem := hKA.mem_of_tendsto hv (Eventually.of_forall fun n => ⟨Or.inr ⟨n, rfl⟩, hu n⟩)
  exact hmem.2

end Proper

section Compare
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isLBSB_of {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (L : X.LocalBranchingStructure Θ x) : IsLBSB X Θ x L.U L.M L.σ :=
  ⟨L.isOpen_U, L.mem_U, fun i => ⟨L.subset_U i, L.isSmoothSubmanifold i, L.mem_M i,
    properInclB_of_isClosed ((isProperMap_inclusion_iff' _).1 (L.isProperMap i))⟩,
    L.σ_pos, L.eq_sum⟩

/-- A blind local branching structure as a project one. -/
def lbsOf (X : EpGroupoid Obj Mor) {Θ : Obj → ℚ} {x : Obj} {ι : Type} {inst : Fintype ι}
    {U : Set Obj} {M : ι → Set Obj} {σ : ι → ℚ} (h : @IsLBSB _ _ _ _ _ _ _ _ X Θ x ι inst U M σ) :
    X.LocalBranchingStructure Θ x :=
  have := X.PObj.metrizableSpace
  @EpGroupoid.LocalBranchingStructure.mk _ _ _ _ _ _ _ _ X Θ x U h.1 h.2.1 ι inst M
    (fun i => (h.2.2.1 i).1) (fun i => (h.2.2.1 i).2.1) (fun i => (h.2.2.1 i).2.2.1)
    (fun i => (isProperMap_inclusion_iff' _).2 (isClosed_of_properInclB (h.2.2.1 i).2.2.2))
    σ h.2.2.2.1 h.2.2.2.2

end Compare

/-! ### The two dimension notions agree on submanifolds -/

section Dim
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- The blind `T_yM` (images of `Ts` over `y`) is the project's `submanifoldTangent` (fixed
points of `Ts` over `y`). -/
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

/-- The project's dimension gives the blind one (with `A`'s `HasDimAt.finrank_eq`). -/
theorem hasDimB_of (hfe : type_of% @Polyfold.MPolyfold.HasDimAt.finrank_eq.{0}) {A : Set Z}
    (hA : P.IsSmoothSubmanifold A) {y : Z} {n : ℕ} (h : P.HasDimAt A y n) : HasDimB P A y n := by
  have hyA := h.1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hA hyA hyφ
  refine ⟨φ, hφ, hyφ, N, hfin, ?_, ?_⟩
  · rw [chartImgB_eq hφ hyA, hN]
  · set d := hA.data hyA
    have hyV := hA.mem_data_V hyA
    have hy1 := d.mem_levelSet_one hyA hyV
    have hz := P.toBase_levelLift hφ hyφ hy1
    have h1 := hfe h d hφ hyV hyφ hz
    rw [← chartTangent_eq hφ d hyA hyV hyφ, ← hN, Submodule.span_eq] at h1
    exact h1

/-- The blind dimension gives the project's. -/
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

/-! ### What `A` gives of `B` -/

/-- **(b) holds**: the project's `n`-dimensional `Θ` is the blind one. -/
theorem A_to_Bb : A → Bb := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ n
  have hfe : type_of% @Polyfold.MPolyfold.HasDimAt.finrank_eq.{0} := hA.2.1
  constructor
  · intro h x hx
    obtain ⟨L, hL⟩ := h x hx
    exact ⟨L.ι, L.fintype, L.U, L.M, L.σ, isLBSB_of L,
      fun i m hm => hasDimB_of hfe (L.isSmoothSubmanifold i) ((hL i).2 m hm)⟩
  · intro h x hx
    obtain ⟨ι, inst, U, M, σ, hLB, hdim⟩ := h x hx
    exact ⟨lbsOf X hLB, fun i => ⟨(hLB.2.2.1 i).2.1,
      fun m hm => hasDimAt_of (hLB.2.2.1 i).2.1 hm (hdim i m hm)⟩⟩

/-- **(a) in `ℝᵐ`** (the only case `A` has). -/
theorem A_to_Ba_rn : A → ∀ (k : ℕ) (M : Set (Fin k → ℝ)), (rnPolyfold k).IsSmoothSubmanifold M →
    ∀ m ∈ M, ∃ (n : ℕ) (W : Set (Fin k → ℝ)), IsOpen W ∧ m ∈ W ∧
      ∀ m' ∈ M ∩ W, HasDimB (rnPolyfold k) M m' n := by
  intro hA k M hM m hm
  obtain ⟨V, hV, hmV, n, hn⟩ := hA.2.2.2.2.2.2.2.2 m M hM hm
  refine ⟨n, V, hV, hmV, fun m' hm' => hasDimB_of hA.2.1 hM ?_⟩
  exact (hA.2.2.2.2.1 hM hV hm'.2).1 (hn.2 m' hm')

#rt_check RoundTrip.V9_2.A_to_Bb [Polyfold.MPolyfold.finrank_tangentSpace_chart_change,
  Polyfold.MPolyfold.HasDimAt.finrank_eq, Polyfold.MPolyfold.HasDimAt.unique,
  Polyfold.MPolyfold.IsSmoothSubmanifold.exists_hasDimAt,
  Polyfold.MPolyfold.hasDimAt_inter_isOpen_iff, Polyfold.MPolyfold.hasDimAt_image_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.dim_unique, Polyfold.EpGroupoid.isNDimensional_zero,
  Polyfold.MPolyfold.hasLocallyConstantDimAt_rn]
#rt_check RoundTrip.V9_2.A_to_Ba_rn [Polyfold.MPolyfold.finrank_tangentSpace_chart_change,
  Polyfold.MPolyfold.HasDimAt.finrank_eq, Polyfold.MPolyfold.HasDimAt.unique,
  Polyfold.MPolyfold.IsSmoothSubmanifold.exists_hasDimAt,
  Polyfold.MPolyfold.hasDimAt_inter_isOpen_iff, Polyfold.MPolyfold.hasDimAt_image_iff,
  Polyfold.EpGroupoid.LocalBranchingStructure.dim_unique, Polyfold.EpGroupoid.isNDimensional_zero,
  Polyfold.MPolyfold.hasLocallyConstantDimAt_rn]

end RoundTrip.V9_2
