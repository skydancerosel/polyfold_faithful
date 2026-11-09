import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_10

/-! Round trip for V9_10 (Proposition 9.1.12, p. 408, proof in §9.6.1: the dimensional
decomposition does not depend on the structure).

`A` is the conjunction of the types of the eleven listed theorems (universes at `0` where there
are any): `DimPartsAgreeNear.exists_naturalRep`, `dimPartsAgreeNear_of_isOfDim` (equidimensional
case), `dimPartsAgreeNear_of_topMultiplicity` / `proposition_9_1_12_of_topMultiplicity` and
`dimPartsAgreeNear_of_hasGraphChartAt` / `proposition_9_1_12_of_hasGraphChartAt` (the
proposition under a hypothesis on the M-polyfold), `proposition_9_1_12_rn` (every ep-groupoid
with object M-polyfold `ℝᵐ`), `proposition_9_1_12_rn_zero`, `proposition_9_1_12_rn_one`, and the
mixed-dimension witnesses `exists_mixed_rn_one`, `Remark913Hyp.exists_mixed_rn_two`.
`DimPartsAgreeNear`, `Proposition_9_1_12` are vocabulary.

`B` is the proposition for **every** ep-groupoid and branched `Θ`, two structures on the same
`U`, with the pointwise dimension `Θ_k(y) = ∑_{y ∈ Mᵢ, dim T_yMᵢ = k} σᵢ` and a `V` carrying
`B`'s natural-representation data.

* `A → B`: not proved, a genuine difference.  `A` proves the proposition only for `ℝᵐ` or under
  `TopMultiplicity` / `HasGraphChartAt` (the graph representation of Lemmas 9.2.9–9.2.11 /
  the "measure zero" steps of §9.6.1), which the project establishes only for `ℝᵐ`; for a general
  M-polyfold the proposition is not in `A`.  Also `A` works with labellings `dim` of constant
  dimension, while `B`'s `Mᵢ` are arbitrary submanifolds: matching them needs the local constancy
  of the dimension (Remark 9.1.1), not proved in general in the project.
* `B → A`: proved.  The key lemma `local_of_B` derives the project's `DimPartsAgreeNear` for
  **any** `Θ` with two labelled structures (no branchedness needed, as in
  `dimPartsAgreeNear_of_topMultiplicity`): restrict both structures to `W = U ∩ U'`, and apply
  `B` to the *trivial* ep-groupoid of `X.PObj` and the auxiliary branched
  `Θ_W(y) = ∑_{y ∈ Mᵢ ∩ W} σᵢ` (`isBranchedB_thetaW`: at each point of its support a structure
  is cut out by removing the `Mⱼ` not through the point; paracompactness from metrizability).
  `B`'s pointwise `dimPartB` is the labelled `dimPart` (`dimPartB_eq`: `HasDimB` at `y` forces
  the label by `finrank_chartTangent`).  All six "proposition" conjuncts follow.  The rest
  (`exists_naturalRep`, the equidimensional case, the two witnesses) are re-proved outright,
  the `ℝ²` witness with its Proposition 9.1.12 step replaced by `local_of_B` and its tangent-sum
  step by the fibre count with `ℝᵐ` tangent slices. -/

namespace RoundTrip.V9_10
open Polyfold Polyfold.EpGroupoid Polyfold.MPolyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.DimPartsAgreeNear.exists_naturalRep.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_isOfDim.{0}) ∧
  (type_of%
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_topMultiplicity.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_1_12_of_topMultiplicity.{0}) ∧
  (type_of%
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_1_12_of_hasGraphChartAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_1_12_rn) ∧
  (type_of% @Polyfold.proposition_9_1_12_rn_zero) ∧
  (type_of% @Polyfold.proposition_9_1_12_rn_one) ∧
  (type_of% @Polyfold.exists_mixed_rn_one) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.exists_mixed_rn_two)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.DimPartsAgreeNear.exists_naturalRep.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_isOfDim.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_topMultiplicity.{0},
    @Polyfold.EpGroupoid.proposition_9_1_12_of_topMultiplicity.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt.{0},
    @Polyfold.EpGroupoid.proposition_9_1_12_of_hasGraphChartAt.{0},
    @Polyfold.EpGroupoid.proposition_9_1_12_rn, @Polyfold.proposition_9_1_12_rn_zero,
    @Polyfold.proposition_9_1_12_rn_one, @Polyfold.exists_mixed_rn_one,
    @Polyfold.EpGroupoid.Remark913Hyp.exists_mixed_rn_two⟩

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

/-- `HasDimAt` (some data and chart) gives `B`'s `HasDimB`. -/
theorem hasDimB_of_hasDimAt {M : Set Z} {m : Z} {n : ℕ} (hM : P.IsSmoothSubmanifold M)
    (h : P.HasDimAt M m n) : HasDimB P M m n := by
  obtain ⟨-, φ, -, -, hφ, hmφ, -, -⟩ := h.2
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hM h.1 hmφ
  refine ⟨φ, hφ, hmφ, N, hfin, ?_, finrank_chartTangent hφ h hM hmφ hN⟩
  rw [chartImgB, tyMB_eq h.1, hN]
  rfl

/-- The trivial ep-groupoid of an M-polyfold: `|supp|` of anything is paracompact. -/
theorem paracompact_trivial (S : Set Z) : ParacompactSpace ((EpGroupoid.trivial P).π '' S) := by
  have := P.metrizableSpace
  set Y := EpGroupoid.trivial P
  have hinj : Function.Injective Y.π := fun a b h => by
    obtain ⟨φ, h1, h2⟩ := Y.π_eq_π_iff.1 h
    exact h1.symm.trans h2
  let e : Z ≃ₜ Y.OrbitSpace := Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective _ ⟨hinj, Y.surjective_π⟩) Y.continuous_π Y.proposition_7_1_8
  have : ParacompactSpace S := paracompactSpace_of_metrizableSpace _
  exact (e.image S).paracompactSpace_iff.1 inferInstance

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

/-- A structure restricted to an open `W ∋ x` inside its domain, for a function `Θ'` agreeing
with `Θ` on `W`, as `B`'s local branching structure of any ep-groupoid with the same objects. -/
theorem isLBSB_restrict {Mor' : Type} [TopologicalSpace Mor'] [T2Space Mor']
    [ParacompactSpace Mor'] (Y : EpGroupoid Obj Mor') (hY : Y.PObj = X.PObj) {Θ Θ' : Obj → ℚ}
    {x : Obj} (Bs : X.LocalBranchingStructure Θ x) {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W)
    (hWU : W ⊆ Bs.U) (hΘ' : ∀ y ∈ W, Θ' y = Θ y) :
    IsLBSB Y Θ' x W (fun i => Bs.M i ∩ W) Bs.σ := by
  refine ⟨hW, hxW, fun i => ⟨inter_subset_right, ?_, ⟨Bs.mem_M i, hxW⟩, ?_⟩, Bs.σ_pos,
    fun y hy => ?_⟩
  · rw [hY]; exact (Bs.isSmoothSubmanifold i).inter_isOpen hW
  · intro K hKW hK
    have := isProperInclB_of_isProperMap _ (Bs.isProperMap i) K (hKW.trans hWU) hK
    convert this using 1
    ext z
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hKW h.1⟩⟩
  · rw [hΘ' y hy, Bs.eq_sum y (hWU hy)]
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : y ∈ Bs.M i
    · rw [if_pos h1, if_pos (show y ∈ Bs.M i ∩ W from ⟨h1, hy⟩)]
    · rw [if_neg h1, if_neg (show ¬ y ∈ Bs.M i ∩ W from fun h => h1 h.1)]

/-- `B`'s pointwise `Θ_k` of the restricted structure is the project's labelled `Θ_k`. -/
theorem dimPartB_eq {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x)
    {dim : Bs.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (Bs.M i) (dim i)) {W : Set Obj}
    (hW : IsOpen W) (k : ℕ) {y : Obj} (hyW : y ∈ W) :
    dimPartB X.PObj (fun i => Bs.M i ∩ W) Bs.σ k y = Bs.dimPart dim k y := by
  unfold dimPartB LocalBranchingStructure.dimPart
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdW : X.PObj.IsSubmanifoldOfDim (Bs.M i ∩ W) (dim i) := (hdim i).inter_isOpen hW
  have hiff : (y ∈ Bs.M i ∩ W ∧ HasDimB X.PObj (Bs.M i ∩ W) y k) ↔ (dim i = k ∧ y ∈ Bs.M i) := by
    constructor
    · rintro ⟨⟨hyM, -⟩, φ, hφ, hyφ, S, -, hS, hrank⟩
      refine ⟨?_, hyM⟩
      rw [← hrank]
      refine (finrank_chartTangent hφ (hdW.2 y ⟨hyM, hyW⟩) hdW.1 hyφ ?_).symm
      rw [← hS, chartImgB, tyMB_eq (show y ∈ Bs.M i ∩ W from ⟨hyM, hyW⟩)]
      rfl
    · rintro ⟨rfl, hyM⟩
      exact ⟨⟨hyM, hyW⟩, hasDimB_of_hasDimAt hdW.1 (hdW.2 y ⟨hyM, hyW⟩)⟩
  by_cases h1 : dim i = k ∧ y ∈ Bs.M i
  · rw [if_pos h1, if_pos (hiff.2 h1)]
  · rw [if_neg h1, if_neg (mt hiff.1 h1)]

open Classical in
/-- The auxiliary functor `Θ_W(y) = ∑_{y ∈ Mᵢ ∩ W} σᵢ`. -/
noncomputable def thetaW {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x)
    (W : Set Obj) : Obj → ℚ :=
  fun y => ∑ i with y ∈ Bs.M i ∩ W, Bs.σ i

theorem thetaW_eq {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x) {W : Set Obj}
    (hWU : W ⊆ Bs.U) {y : Obj} (hy : y ∈ W) : thetaW Bs W y = Θ y := by
  unfold thetaW
  rw [Bs.eq_sum y (hWU hy)]
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : y ∈ Bs.M i
  · rw [if_pos h1, if_pos (show y ∈ Bs.M i ∩ W from ⟨h1, hy⟩)]
  · rw [if_neg h1, if_neg (show ¬ y ∈ Bs.M i ∩ W from fun h => h1 h.1)]

/-- `Θ_W` is a branched ep⁺-subgroupoid (in `B`'s sense) of the trivial ep-groupoid of
`X.PObj`. -/
theorem isBranchedB_thetaW {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x)
    {W : Set Obj} (hW : IsOpen W) (hWU : W ⊆ Bs.U) :
    IsBranchedB (EpGroupoid.trivial X.PObj) (thetaW Bs W) := by
  classical
  have hex : ∀ y, 0 < thetaW Bs W y → ∃ i, y ∈ Bs.M i ∩ W := fun y hy => by
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy.ne'
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  refine ⟨fun y => Finset.sum_nonneg fun i _ => (Bs.σ_pos i).le, fun φ => rfl,
    fun y hy => ?_, paracompact_trivial _, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := hex y hy
    exact (Bs.isSmoothSubmanifold i).subset_smoothSet hi.1
  · obtain ⟨i₀, hi₀⟩ := hex y hy
    have hyW : y ∈ W := hi₀.2
    -- remove the `Mⱼ` not through `y`
    have hopen : ∀ j, IsOpen (Bs.U \ Bs.M j) := fun j => by
      have h1 := Bs.isOpen_U.isOpenMap_subtype_val _ (Bs.isClosed_M j).isOpen_compl
      convert h1 using 1
      ext z
      exact ⟨fun h => ⟨⟨z, h.1⟩, h.2, rfl⟩, fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.2, hw⟩⟩
    let J := Finset.univ.filter fun j => y ∉ Bs.M j
    let Uy : Set Obj := W ∩ ⋂ j ∈ J, (Bs.U \ Bs.M j)
    have hUy : IsOpen Uy := hW.inter (isOpen_biInter_finset fun j _ => hopen j)
    have hyUy : y ∈ Uy := ⟨hyW, mem_iInter₂.2 fun j hj => ⟨hWU hyW, (Finset.mem_filter.1 hj).2⟩⟩
    have hkey : ∀ z ∈ Uy, ∀ j, z ∈ Bs.M j → y ∈ Bs.M j := fun z hz j hzj => by
      by_contra hyj
      exact (mem_iInter₂.1 hz.2 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hyj⟩)).2 hzj
    refine ⟨{i // y ∈ Bs.M i}, inferInstance, Uy, fun i => Bs.M i.1 ∩ Uy, fun i => Bs.σ i.1,
      hUy, hyUy, fun i => ⟨inter_subset_right, (Bs.isSmoothSubmanifold i.1).inter_isOpen hUy,
        ⟨i.2, hyUy⟩, ?_⟩, fun i => Bs.σ_pos i.1, fun z hz => ?_⟩
    · intro K hKU hK
      have hKBU : K ⊆ Bs.U := hKU.trans (inter_subset_left.trans hWU)
      have := isProperInclB_of_isProperMap _ (Bs.isProperMap i.1) K hKBU hK
      convert this using 1
      ext w
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hKU h.1⟩⟩
    · have hzW : z ∈ W := hz.1
      unfold thetaW
      rw [Finset.sum_filter, Finset.sum_filter]
      have h0 : ∑ i : {i // ¬ y ∈ Bs.M i}, (if z ∈ Bs.M i.1 ∩ W then Bs.σ i.1 else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => if_neg fun h => i.2 (hkey z hz i.1 h.1)
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => y ∈ Bs.M i), h0, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hiff : z ∈ Bs.M i.1 ∩ W ↔ z ∈ Bs.M i.1 ∩ Uy :=
        ⟨fun h => ⟨h.1, hz⟩, fun h => ⟨h.1, hzW⟩⟩
      by_cases h1 : z ∈ Bs.M i.1 ∩ W
      · rw [if_pos h1, if_pos (hiff.1 h1)]
      · rw [if_neg h1, if_neg (mt hiff.2 h1)]

/-- **The key lemma**: `B` gives the project's `DimPartsAgreeNear` for any `Θ` and any two
labelled local branching structures at `x`. -/
theorem local_of_B (hB : B) {Θ : Obj → ℚ} {x : Obj} (Bs Bs' : X.LocalBranchingStructure Θ x)
    {dim : Bs.ι → ℕ} {dim' : Bs'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (Bs.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (Bs'.M j) (dim' j)) :
    LocalBranchingStructure.DimPartsAgreeNear Bs Bs' dim dim' := by
  have hW : IsOpen (Bs.U ∩ Bs'.U) := Bs.isOpen_U.inter Bs'.isOpen_U
  have hxW : x ∈ Bs.U ∩ Bs'.U := ⟨Bs.mem_U, Bs'.mem_U⟩
  have hWU : Bs.U ∩ Bs'.U ⊆ Bs.U := inter_subset_left
  have hWU' : Bs.U ∩ Bs'.U ⊆ Bs'.U := inter_subset_right
  have hT := isBranchedB_thetaW Bs hW hWU
  have h1 := isLBSB_restrict (X := X) (EpGroupoid.trivial X.PObj) rfl Bs hW hxW hWU
    (fun y hy => thetaW_eq Bs hWU hy)
  have h2 := isLBSB_restrict (X := X) (EpGroupoid.trivial X.PObj) rfl Bs' hW hxW hWU'
    (fun y hy => thetaW_eq Bs hWU hy)
  obtain ⟨V, -, -, hV, hxV, hVW, -, hagree⟩ :=
    hB Obj Obj (EpGroupoid.trivial X.PObj) (thetaW Bs (Bs.U ∩ Bs'.U)) hT x Bs.ι Bs'.ι
      (Bs.U ∩ Bs'.U) _ _ _ _ h1 h2
  exact ⟨V, hV, hxV, hVW, fun k y hy => (dimPartB_eq Bs hdim hW k (hVW hy)).symm.trans
    ((hagree k y hy).trans (dimPartB_eq Bs' hdim' hW k (hVW hy)))⟩

theorem prop_of_B (hB : B) : X.Proposition_9_1_12 := fun _ _ _ Bs Bs' _ _ hd hd' =>
  local_of_B hB Bs Bs' hd hd'

/-! ### The outright re-proofs -/

theorem exists_naturalRep' {Θ : Obj → ℚ} {x : Obj} {B B' : X.LocalBranchingStructure Θ x}
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ} (h : LocalBranchingStructure.DimPartsAgreeNear B B' dim dim') :
    ∃ R : X.NaturalRep x, R.U ⊆ B.U ∩ B'.U ∧
      ∀ k, ∀ y ∈ R.U, B.dimPart dim k y = B'.dimPart dim' k y := by
  obtain ⟨V, hV, hxV, hVU, hk⟩ := h
  obtain ⟨R, hR⟩ := theorem_7_1_13 X x hV hxV
  exact ⟨R, hR.trans hVU, fun k y hy => hk k y (hR hy)⟩

theorem isOfDim' {Θ : Obj → ℚ} {x : Obj} {n : ℕ} (B B' : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ} (hdim : ∀ i, dim i = n) (hdim' : ∀ j, dim' j = n) :
    LocalBranchingStructure.DimPartsAgreeNear B B' dim dim' := by
  refine ⟨B.U ∩ B'.U, B.isOpen_U.inter B'.isOpen_U, ⟨B.mem_U, B'.mem_U⟩, subset_rfl,
    fun k y hy => ?_⟩
  by_cases hk : k = n
  · subst hk
    rw [B.dimPart_eq_of_isOfDim hdim hy.1, B'.dimPart_eq_of_isOfDim hdim' hy.2]
  · rw [B.dimPart_eq_zero (fun i h => hk (h.symm.trans (hdim i))),
      B'.dimPart_eq_zero (fun j h => hk (h.symm.trans (hdim' j)))]

end Dict

open scoped Classical in
theorem mixed_one : ∃ (Θ : (Fin 1 → ℝ) → ℚ)
    (B : (EpGroupoid.trivial (rnPolyfold 1)).LocalBranchingStructure Θ 0) (dim : B.ι → ℕ),
    (EpGroupoid.trivial (rnPolyfold 1)).IsBranchedEpSubgroupoid Θ ∧
      (∀ i, (rnPolyfold 1).IsSubmanifoldOfDim (B.M i) (dim i)) ∧ (∃ i, dim i = 0) ∧
        ∃ i, dim i = 1 := by
  set M : Fin 2 → Set (Fin 1 → ℝ) := ![univ, {0}]
  have hMd : ∀ i, (rnPolyfold 1).IsSubmanifoldOfDim (M i) (![1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_univ 1
    · exact EpGroupoid.rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hc : ∀ i, IsClosed (M i) := by
    intro i
    fin_cases i
    · exact isClosed_univ
    · exact isClosed_singleton
  set B := EpGroupoid.localBranchingStructure_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1)
    hc 0
  refine ⟨_, B, fun i => ![1, 0] i.1,
    EpGroupoid.isBranchedEpSubgroupoid_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc,
    fun i => (hMd i.1).inter_isOpen B.isOpen_U, ⟨⟨1, rfl⟩, rfl⟩, ⟨⟨0, mem_univ _⟩, rfl⟩⟩

section Two
open Polyfold.EpGroupoid.Remark913Hyp
variable {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂)
include h

open scoped Classical in
theorem mixed_two (hB : B) :
    ∃ (Θ : (Fin 2 → ℝ) → ℚ) (B B' : (trivial (rnPolyfold 2)).LocalBranchingStructure Θ 0)
      (dim : B.ι → ℕ) (dim' : B'.ι → ℕ),
      (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid Θ ∧
      (∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (B.M i) (dim i)) ∧
      (∀ j, (rnPolyfold 2).IsSubmanifoldOfDim (B'.M j) (dim' j)) ∧
      (∃ i, dim i = 0) ∧ (∃ i, dim i = 1) ∧
      (∀ i, ∃ s, B.M i = ![graph2 β₁, graph2 β₂, ({0} : Set (Fin 2 → ℝ))] s ∩ B.U) ∧
      (∀ j, ∃ s, B'.M j = ![graph2 0, graph2 (β₁ + β₂), ({0} : Set (Fin 2 → ℝ))] s ∩ B'.U) ∧
      LocalBranchingStructure.DimPartsAgreeNear B B' dim dim' ∧
      B.tangentSum = B'.tangentSum := by
  set M : Fin 3 → Set (Fin 2 → ℝ) := ![graph2 β₁, graph2 β₂, {0}] with hMdef
  set M' : Fin 3 → Set (Fin 2 → ℝ) := ![graph2 0, graph2 (β₁ + β₂), {0}] with hM'def
  have hMd : ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (M i) (![1, 1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₁
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₂
    · exact rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hM'd : ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (M' i) (![1, 1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 (h.contDiff₁.add h.contDiff₂)
    · exact rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hc : ∀ i, IsClosed (M i) := by
    intro i
    fin_cases i
    · exact isClosed_graph2 h.contDiff₁.continuous
    · exact isClosed_graph2 h.contDiff₂.continuous
    · exact isClosed_singleton
  have hc' : ∀ i, IsClosed (M' i) := by
    intro i
    fin_cases i
    · exact isClosed_graph2 continuous_const
    · exact isClosed_graph2 (h.contDiff₁.continuous.add h.contDiff₂.continuous)
    · exact isClosed_singleton
  have hΘ : ∀ y, (∑ i with y ∈ M' i, (1 : ℚ)) = ∑ i with y ∈ M i, (1 : ℚ) := fun y => by
    rw [hMdef, hM'def, sum_three_eq, sum_three_eq, thetaGraphs_eq h.eq_zero_or y]
  set B := localBranchingStructure_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc 0
  set B' := (localBranchingStructure_sum_rn M' 1 (fun _ => one_pos) (fun i => (hM'd i).1) hc'
    0).ofEq hΘ
  have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
  have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
  have h0M : ∀ i, (0 : Fin 2 → ℝ) ∈ M i := by
    intro i
    fin_cases i
    · change (0 : Fin 2 → ℝ) 1 = β₁ ((0 : Fin 2 → ℝ) 0); simp [h10]
    · change (0 : Fin 2 → ℝ) 1 = β₂ ((0 : Fin 2 → ℝ) 0); simp [h20]
    · exact mem_singleton _
  have hd : ∀ i : B.ι, (rnPolyfold 2).IsSubmanifoldOfDim (B.M i) (![1, 1, 0] i.1) :=
    fun i => (hMd i.1).inter_isOpen B.isOpen_U
  have hd' : ∀ j : B'.ι, (rnPolyfold 2).IsSubmanifoldOfDim (B'.M j) (![1, 1, 0] j.1) :=
    fun j => (hM'd j.1).inter_isOpen B'.isOpen_U
  have hagree := local_of_B hB B B' hd hd'
  refine ⟨_, B, B', fun i => ![1, 1, 0] i.1, fun j => ![1, 1, 0] j.1,
    isBranchedEpSubgroupoid_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc,
    hd, hd', ⟨⟨2, h0M 2⟩, rfl⟩, ⟨⟨0, h0M 0⟩, rfl⟩, fun i => ⟨i.1, rfl⟩, fun j => ⟨j.1, rfl⟩,
    hagree, B.tangentSum_eq_of_dimPartsAgreeNear B' hd hd' hagree
      (fun n => MPolyfold.hasTangentSlicesAt_rn 0 n)⟩

end Two

theorem B_to_A : B → A := fun hB =>
  ⟨@exists_naturalRep', @isOfDim', fun _ Bs Bs' _ _ hd hd' => local_of_B hB Bs Bs' hd hd',
    fun _ => prop_of_B hB, fun _ Bs Bs' _ _ hd hd' => local_of_B hB Bs Bs' hd hd',
    fun _ => prop_of_B hB, fun _ => prop_of_B hB, prop_of_B hB, prop_of_B hB, mixed_one,
    fun h => mixed_two h hB⟩

#rt_check RoundTrip.V9_10.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.DimPartsAgreeNear.exists_naturalRep,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_isOfDim,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_topMultiplicity,
  Polyfold.EpGroupoid.proposition_9_1_12_of_topMultiplicity,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt,
  Polyfold.EpGroupoid.proposition_9_1_12_of_hasGraphChartAt,
  Polyfold.EpGroupoid.proposition_9_1_12_rn, Polyfold.proposition_9_1_12_rn_zero,
  Polyfold.proposition_9_1_12_rn_one, Polyfold.exists_mixed_rn_one,
  Polyfold.EpGroupoid.Remark913Hyp.exists_mixed_rn_two]
#rt_overlap RoundTrip.V9_10.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.DimPartsAgreeNear.exists_naturalRep,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_isOfDim,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_topMultiplicity,
  Polyfold.EpGroupoid.proposition_9_1_12_of_topMultiplicity,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt,
  Polyfold.EpGroupoid.proposition_9_1_12_of_hasGraphChartAt,
  Polyfold.EpGroupoid.proposition_9_1_12_rn, Polyfold.proposition_9_1_12_rn_zero,
  Polyfold.proposition_9_1_12_rn_one, Polyfold.exists_mixed_rn_one,
  Polyfold.EpGroupoid.Remark913Hyp.exists_mixed_rn_two]

end RoundTrip.V9_10
