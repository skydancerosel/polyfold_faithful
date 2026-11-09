import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_13

/-! Round trip for V9_13 (Theorem 9.2.1, p. 409; 2017: Theorem 9.1, p. 298: the tangent section
`T_Θ`).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`LocalBranchingStructure.tangentSum_transport`, `tangentValue_eq`, `grPush_tangentValue`,
`theorem_9_2_1` (`tangentSum`, `transport`, `HasIndependentTangentSums`, `tangentValue`,
`tangentSection` are vocabulary).  The last three assume `HasIndependentTangentSums Θ`: the
independence of `∑ σᵢ T_xMᵢ` from the local branching structure, which is the difficult part of
Theorem 9.2.1 (1) and is a **hypothesis** of the project's theorem.

`B` asserts, for every branched `Θ`: (1) the independence, `∑ σᵢ T_xMᵢ ∈ Gr(x)` (`B`'s `GrB`:
chart subspaces), and (2) `φ_*(T_Θ(s φ)) = T_Θ(t φ)` for any structures at `s φ`, `t φ`.

Dictionary: `B`'s local branching structures (`IsLBSB`, with "proper" read as compact traces
`K ∩ M`) are the project's (`lbsOf`, `isLBSB_of_lbs`; the hard direction uses that M-polyfolds
are metrizable, hence `U` sequential, so compact traces make `M` closed in `U`), and `B`'s
`T_xM = ⋃_d Tr(T_xX)` is the project's fixed-vector `T_xM` (`tyMB_eq`), so `tsumB = tangentSum`.

* `A → B`: not proved.  `A` gives `B` only under the independence hypothesis:
  `A_to_B_of_hyp : A → Hind → B`, where `Hind` is `HasIndependentTangentSums` for every branched
  `Θ` of every ep-groupoid in `Type`.  Conversely `B → Hind` (`B_to_hyp`).  So `B ⇔ A ∧ Hind`
  and the gap is exactly `Hind` (Theorem 9.2.1 (1) proper), which the project proves only in
  special cases (good points, equidimensional with tangent slices, `ℝᵐ`, from Proposition
  9.1.12).
* `B → A`: proved.  `grPush_tangentValue` is derived from `B (2)`; `tangentSum_transport` (stated
  for any functorial `Θ`, not only branched ones), `tangentValue_eq` and `theorem_9_2_1` are
  conditional facts about the construction, re-proved outright (the proofs follow the
  project's). -/

namespace RoundTrip.V9_13
open Polyfold Polyfold.EpGroupoid Polyfold.MPolyfold Set Filter Topology CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentValue_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.grPush_tangentValue.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.theorem_9_2_1.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport.{0},
    @Polyfold.EpGroupoid.tangentValue_eq.{0}, @Polyfold.EpGroupoid.grPush_tangentValue.{0},
    @Polyfold.EpGroupoid.theorem_9_2_1.{0}⟩

/-! ### Dictionary -/

section DictZ
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- `B`'s `T_yM` (union over the data of `Tr(T_yX)`) is the project's `T_yM` (fixed vectors). -/
theorem tyMB_eq {M : Set Z} {y : Z} (hy : y ∈ M) : TyMB P M y = P.submanifoldTangent M y := by
  ext α
  constructor
  · rintro ⟨d, hyV, β, hβ, rfl⟩
    have hβy : P.levelVal 1 (P.tangentProj β) = y := hβ
    have hβV : β ∈ P.tangentPreimage d.V := by
      change P.levelVal 1 (P.tangentProj β) ∈ d.V
      rw [hβy]; exact hyV
    have := d.tmap_mem_submanifoldTangent hβV
    rwa [hβy, d.apply_eq_self ⟨hy, hyV⟩] at this
  · rintro ⟨hα, d, hyV, hfix⟩
    exact ⟨d, hyV, α, hα, hfix⟩

end DictZ

section Dict
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

omit [T2Space Obj] [ParacompactSpace Obj] in
/-- A proper inclusion has compact traces on compact subsets of `U`. -/
theorem isProperInclB_of_isProperMap {M U : Set Obj} (h : M ⊆ U)
    (hp : IsProperMap (Set.inclusion h)) : IsProperInclB M U := by
  intro K hKU hK
  have hc : IsClosed ((↑) ⁻¹' M : Set U) := (isProperMap_inclusion_iff h).1 hp
  have hK0 : IsCompact ((↑) ⁻¹' K : Set U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]; exact hK
  have := (hK0.inter_right hc).image continuous_subtype_val
  convert this using 1
  ext z
  constructor
  · rintro ⟨hzK, hzM⟩; exact ⟨⟨z, h hzM⟩, ⟨hzK, hzM⟩, rfl⟩
  · rintro ⟨w, ⟨hwK, hwM⟩, rfl⟩; exact ⟨hwK, hwM⟩

/-- Conversely, compact traces make the inclusion proper (the M-polyfold is metrizable, so `U`
is sequential and `M` is sequentially closed in `U`). -/
theorem isProperMap_of_isProperInclB (P : MPolyfold Obj) {M U : Set Obj} (h : M ⊆ U)
    (hp : IsProperInclB M U) : IsProperMap (Set.inclusion h) := by
  have := P.metrizableSpace
  rw [isProperMap_inclusion_iff]
  refine IsSeqClosed.isClosed fun u p hu hlim => ?_
  have hK : IsCompact ((↑) '' insert p (range u) : Set Obj) :=
    hlim.isCompact_insert_range.image continuous_subtype_val
  have hKU : ((↑) '' insert p (range u) : Set Obj) ⊆ U := by
    rintro _ ⟨w, -, rfl⟩; exact w.2
  have hc : IsClosed (((↑) '' insert p (range u) : Set Obj) ∩ M) := (hp _ hKU hK).isClosed
  have hmem : ∀ n, ((u n : U) : Obj) ∈ ((↑) '' insert p (range u) : Set Obj) ∩ M := fun n =>
    ⟨⟨u n, Or.inr ⟨n, rfl⟩, rfl⟩, hu n⟩
  have hlim' : Tendsto (fun n => (u n : Obj)) atTop (𝓝 (p : Obj)) :=
    (continuous_subtype_val.tendsto p).comp hlim
  exact (hc.mem_of_tendsto hlim' (Eventually.of_forall hmem)).2

theorem isLBSB_of_lbs {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x) :
    IsLBSB X Θ x Bs.U Bs.M Bs.σ :=
  ⟨Bs.isOpen_U, Bs.mem_U, fun i => ⟨Bs.subset_U i, Bs.isSmoothSubmanifold i, Bs.mem_M i,
    isProperInclB_of_isProperMap _ (Bs.isProperMap i)⟩, Bs.σ_pos, fun y hy => by
      rw [Bs.eq_sum y hy]⟩

/-- `B`'s local branching structure as the project's. -/
noncomputable def lbsOf {Θ : Obj → ℚ} {x : Obj} {ι : Type} [Fintype ι] {U : Set Obj}
    {M : ι → Set Obj} {σ : ι → ℚ} (h : IsLBSB X Θ x U M σ) : X.LocalBranchingStructure Θ x where
  U := U
  isOpen_U := h.1
  mem_U := h.2.1
  ι := ι
  M := M
  subset_U i := (h.2.2.1 i).1
  isSmoothSubmanifold i := (h.2.2.1 i).2.1
  mem_M i := (h.2.2.1 i).2.2.1
  isProperMap i := isProperMap_of_isProperInclB X.PObj _ (h.2.2.1 i).2.2.2
  σ := σ
  σ_pos := h.2.2.2.1
  eq_sum := h.2.2.2.2

theorem isBranchedB_of {Θ : Obj → ℚ} (h : X.IsBranchedEpSubgroupoid Θ) : IsBranchedB X Θ :=
  ⟨h.nonneg, h.isFunctorial, h.support_subset, h.paracompactSpace_orbitSupp, fun x hx => by
    obtain ⟨Bs⟩ := h.localBranching x hx
    exact ⟨Bs.ι, inferInstance, Bs.U, Bs.M, Bs.σ, isLBSB_of_lbs Bs⟩⟩

theorem isBranched_of_B {Θ : Obj → ℚ} (h : IsBranchedB X Θ) : X.IsBranchedEpSubgroupoid Θ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => by
    obtain ⟨ι, _, U, M, σ, hl⟩ := h.2.2.2.2 x hx
    exact ⟨lbsOf hl⟩⟩

/-- `B`'s `∑ σᵢ T_xMᵢ` is the project's `tangentSum`. -/
theorem tsumB_eq {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x) :
    tsumB X.PObj Bs.M Bs.σ x = Bs.tangentSum := by
  unfold tsumB LocalBranchingStructure.tangentSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tyMB_eq (Bs.mem_M i)]

end Dict

/-! ### The gap: the independence hypothesis -/

/-- The independence of `∑ σᵢ T_xMᵢ` for every branched ep⁺-subgroupoid (the hypothesis of the
project's `theorem_9_2_1`, for all ep-groupoids in `Type`). -/
def Hind : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → X.HasIndependentTangentSums Θ

theorem A_to_B_of_hyp : A → Hind → B := by
  intro hA hind Obj Mor _ _ _ _ _ _ X Θ hΘB
  have hΘ := isBranched_of_B hΘB
  have hi := hind Obj Mor X Θ hΘ
  refine ⟨fun x ι ι' _ _ U U' M σ M' σ' hl hl' => ?_, fun x ι _ U M σ hl => ?_,
    fun φ ι ι' _ _ U U' M σ M' σ' hl hl' => ?_⟩
  · have e1 := tsumB_eq (lbsOf hl)
    have e2 := tsumB_eq (lbsOf hl')
    exact e1.trans ((hi x _ _).trans e2.symm)
  · have e1 : tsumB X.PObj M σ x = (lbsOf hl).tangentSum := tsumB_eq (lbsOf hl)
    rw [e1]
    intro L hL
    refine ⟨fun α hα => (lbsOf hl).tangentSum_mem.2 L hL α hα, ?_⟩
    obtain ⟨φ, hφ, hxφ⟩ := X.PObj.exists_isChart_mem_source x
    obtain ⟨N, hfin, hN, -⟩ := (lbsOf hl).exists_submodule_of_mem_support hL hφ hxφ
    exact ⟨φ, hφ, hxφ, N, hfin, hN.symm⟩
  · have e1 : tsumB X.PObj M σ (X.src φ) = (lbsOf hl).tangentSum := tsumB_eq (lbsOf hl)
    have e2 : tsumB X.PObj M' σ' (X.tgt φ) = (lbsOf hl').tangentSum := tsumB_eq (lbsOf hl')
    rw [e1, e2, ← hA.2.1 hi (lbsOf hl), ← hA.2.1 hi (lbsOf hl')]
    exact hA.2.2.1 hΘ hi φ

theorem B_to_hyp : B → Hind := by
  intro hB Obj Mor _ _ _ _ _ _ X Θ hΘ x Bs Bs'
  have h := (hB Obj Mor X Θ (isBranchedB_of hΘ)).1 x Bs.ι Bs'.ι Bs.U Bs'.U Bs.M Bs.σ Bs'.M Bs'.σ
    (isLBSB_of_lbs Bs) (isLBSB_of_lbs Bs')
  rwa [tsumB_eq, tsumB_eq] at h

/-! ### `B → A` -/

section Reproofs
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

theorem tangentSum_transport' {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) {φ : Mor}
    (hφ : φ ∈ X.PMor.levelSet 1) (B : X.LocalBranchingStructure Θ (X.src φ)) :
    (B.transport hΘ φ).tangentSum = X.grPush φ B.tangentSum := by
  rw [LocalBranchingStructure.tangentSum, LocalBranchingStructure.tangentSum, grPush,
    Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.mapDomain_single]
  congr 1
  have hd := X.isScDiffeoOn_hat' φ
  have hS := hd.isScSmoothOn.isOpen
  have h := MPolyfold.submanifoldTangent_image hd ((B.isSmoothSubmanifold i).inter_isOpen hS)
    inter_subset_right ⟨B.mem_M i, X.src_mem_sheetAt φ⟩
  rw [X.hat_src φ, MPolyfold.submanifoldTangent_inter_isOpen hS (X.src_mem_sheetAt φ)] at h
  change X.PObj.submanifoldTangent (X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet)) (X.tgt φ) = _
  rw [h]
  exact image_congr fun α hα =>
    (X.tangentMor_eq_tangentMapOn_hat hφ (MPolyfold.levelVal_tangentProj_of_mem hα)).symm

theorem tangentValue_eq' {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) : X.tangentValue Θ x = B.tangentSum := by
  rw [tangentValue, dif_pos ⟨B⟩]
  exact hind x _ B

/-- `grPush_tangentValue` from `B (2)`. -/
theorem grPush_tangentValue_of_B (hB : B) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (φ : Mor) :
    X.grPush φ (X.tangentValue Θ (X.src φ)) = X.tangentValue Θ (X.tgt φ) := by
  by_cases hs : X.src φ ∈ supp Θ
  · have ht : X.tgt φ ∈ supp Θ := by
      change 0 < Θ (X.tgt φ); rw [← hΘ.isFunctorial φ]; exact hs
    obtain ⟨Bs⟩ := hΘ.localBranching _ hs
    obtain ⟨Bt⟩ := hΘ.localBranching _ ht
    rw [tangentValue_eq' hind Bs, tangentValue_eq' hind Bt]
    have h := (hB Obj Mor X Θ (isBranchedB_of hΘ)).2.2 φ Bs.ι Bt.ι Bs.U Bt.U Bs.M Bs.σ Bt.M Bt.σ
      (isLBSB_of_lbs Bs) (isLBSB_of_lbs Bt)
    rw [tsumB_eq, tsumB_eq] at h
    exact h
  · have ht : X.tgt φ ∉ supp Θ := fun h => hs (by
      change 0 < Θ (X.src φ); rw [hΘ.isFunctorial φ]; exact h)
    rw [X.tangentValue_eq_zero hs, X.tangentValue_eq_zero ht, grPush, Finsupp.mapDomain_zero]

theorem theorem_9_2_1' {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) :
    X.tangentSection hΘ hind ⋙ X.grProj = 𝟭 X.SmoothCat ∧
      (∀ (x : X.SmoothCat), x.pt ∈ supp Θ → ∀ B : X.LocalBranchingStructure Θ x.pt,
        ((X.tangentSection hΘ hind).obj x).sum =
          ∑ i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) x.pt) (B.σ i)) ∧
      (∀ (x : X.SmoothCat), x.pt ∉ supp Θ → ((X.tangentSection hΘ hind).obj x).sum = 0) ∧
      (∀ {x y : X.SmoothCat} (f : x ⟶ y),
        ((X.tangentSection hΘ hind).obj x).pt = X.src (SmoothCat.mor f) ∧
          ((X.tangentSection hΘ hind).map f).1 = SmoothCat.mor f) :=
  ⟨rfl, fun _ _ B => tangentValue_eq' hind B, fun _ hx => X.tangentValue_eq_zero hx,
    fun f => ⟨(SmoothCat.src_mor f).symm, rfl⟩⟩

end Reproofs

theorem B_to_A : B → A := fun hB =>
  ⟨@tangentSum_transport', @tangentValue_eq', fun hΘ hind φ => grPush_tangentValue_of_B hB hΘ hind φ,
    @theorem_9_2_1'⟩

#rt_check_soft RoundTrip.V9_13.A_to_B_of_hyp [
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport,
  Polyfold.EpGroupoid.tangentValue_eq, Polyfold.EpGroupoid.grPush_tangentValue,
  Polyfold.EpGroupoid.theorem_9_2_1]
#rt_check RoundTrip.V9_13.B_to_hyp [
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport,
  Polyfold.EpGroupoid.tangentValue_eq, Polyfold.EpGroupoid.grPush_tangentValue,
  Polyfold.EpGroupoid.theorem_9_2_1]
#rt_check_soft RoundTrip.V9_13.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport,
  Polyfold.EpGroupoid.tangentValue_eq, Polyfold.EpGroupoid.grPush_tangentValue,
  Polyfold.EpGroupoid.theorem_9_2_1]
#rt_overlap RoundTrip.V9_13.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_transport,
  Polyfold.EpGroupoid.tangentValue_eq, Polyfold.EpGroupoid.grPush_tangentValue,
  Polyfold.EpGroupoid.theorem_9_2_1]

end RoundTrip.V9_13
