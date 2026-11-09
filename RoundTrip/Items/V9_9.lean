import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_9

/-! Round trip for V9_9 (Proposition 9.1.11, pp. 407–408; 2017: Proposition 9.2, p. 297: the
dimensional decomposition).

`A` is the conjunction of the types of the nine listed theorems (universes at `0` where there
are any): the local construction of the proof (`dimPartStructure_isOfDim`, `eq_sum_dimPart`,
`dimPart_eq_zero`, `dimPart_eq_of_isOfDim`, `SymmetricBranchingStructure.dim_smul`,
`SymmetricBranchingStructure.dimPart_Φ`) and the counterexample to the uniqueness
(`decompA_isDimDecomposition`, `decompB_isDimDecomposition`, `not_proposition_9_1_11_rn`).
`dimPart`, `dimPartStructure`, `IsDimDecomposition`, `IsLocallyFiniteFamily`,
`Proposition_9_1_11`, `axis2`, `decompA`, `decompB` are vocabulary.

* `B` is the literal statement (`∃!` of a locally finite family of `k`-dimensional branched
  ep⁺-subgroupoids summing to `Θ`), which its author already expected to be false.  It is false
  (`not_B`): the project's two decompositions `decompA` (`Θ₀ = 1_{0}`, `Θ₁ = 1_{L ∖ 0}`) and
  `decompB` (`Θ₁ = 1_L`) of the indicator of the `x`-axis `L ⊆ ℝ²` are both decompositions in
  `B`'s sense.  For that, the project's notions are translated into `B`'s (`isBranchedB_of`,
  `isNDimB_of`): a local branching structure is an `IsLBSB` (a proper inclusion has compact
  traces `K ∩ M`), and `IsSubmanifoldOfDim M k` gives `B`'s `HasDimB` at every point of `M` (the
  chart of `HasDimAt`, `exists_submodule_chartTangent`, `finrank_chartTangent`, and `B`'s
  `T_yM = ⋃_d Tr(T_yX)` is the project's fixed-vector `T_yM`, `tyMB_eq`).  The two
  decompositions are re-proved outright here (the proofs follow the project's, from
  `isBranchedEpSubgroupoid_indicator_rn` etc.), plus their local finiteness.
* Hence `A → B` is false (`not_A_to_B`) and `B → A` holds only ex falso.  Both sides agree that
  the literal uniqueness fails; `A` additionally has the local construction, `B` (being false)
  nothing usable. -/

namespace RoundTrip.V9_9
open Polyfold Polyfold.EpGroupoid Polyfold.MPolyfold Set Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPartStructure_isOfDim.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_of_isOfDim.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.SymmetricBranchingStructure.dim_smul.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.decompA_isDimDecomposition) ∧
  (type_of% @Polyfold.EpGroupoid.decompB_isDimDecomposition) ∧
  (type_of% @Polyfold.EpGroupoid.not_proposition_9_1_11_rn)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.dimPartStructure_isOfDim.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_zero.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_of_isOfDim.{0},
    @Polyfold.EpGroupoid.SymmetricBranchingStructure.dim_smul.{0},
    @Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ.{0},
    @Polyfold.EpGroupoid.decompA_isDimDecomposition,
    @Polyfold.EpGroupoid.decompB_isDimDecomposition,
    @Polyfold.EpGroupoid.not_proposition_9_1_11_rn⟩

/-! ### Dictionary: the project's notions give `B`'s -/

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

theorem isLBSB_of_lbs {Θ : Obj → ℚ} {x : Obj} (Bs : X.LocalBranchingStructure Θ x) :
    IsLBSB X Θ x Bs.U Bs.M Bs.σ :=
  ⟨Bs.isOpen_U, Bs.mem_U, fun i => ⟨Bs.subset_U i, Bs.isSmoothSubmanifold i, Bs.mem_M i,
    isProperInclB_of_isProperMap _ (Bs.isProperMap i)⟩, Bs.σ_pos, fun y hy => by
      rw [Bs.eq_sum y hy]⟩

theorem isBranchedB_of {Θ : Obj → ℚ} (h : X.IsBranchedEpSubgroupoid Θ) : IsBranchedB X Θ :=
  ⟨h.nonneg, h.isFunctorial, h.support_subset, h.paracompactSpace_orbitSupp, fun x hx => by
    obtain ⟨Bs⟩ := h.localBranching x hx
    exact ⟨Bs.ι, inferInstance, Bs.U, Bs.M, Bs.σ, isLBSB_of_lbs Bs⟩⟩

theorem isNDimB_of {Θ : Obj → ℚ} {k : ℕ} (h : X.IsNDimensional Θ k) : IsNDimB X Θ k :=
  fun x hx => by
    obtain ⟨Bs, hB⟩ := h x hx
    exact ⟨Bs.ι, inferInstance, Bs.U, Bs.M, Bs.σ, isLBSB_of_lbs Bs,
      fun i m hm => hasDimB_of_hasDimAt (hB i).1 ((hB i).2 m hm)⟩

theorem isDimDecompB_of {Θ : Obj → ℚ} {Θk : ℕ → Obj → ℚ} (h : X.IsDimDecomposition Θ Θk)
    (hlf : IsLocFinB Θk) : IsDimDecompB X Θ Θk :=
  ⟨fun k => ⟨isBranchedB_of (h.isBranched k), isNDimB_of (h.isNDimensional k)⟩, hlf,
    h.eq_finsum⟩

end Dict

/-! ### The two decompositions (re-proved outright; the proofs follow the project's) -/

section Counterexample
open scoped ContDiff Classical

theorem decompA_dd :
    (trivial (rnPolyfold 2)).IsDimDecomposition (axis2.indicator 1) decompA where
  isBranched k := by
    rcases k with _ | _ | k
    · exact indicator_singleton_zero_branched.1
    · exact indicator_axis2_diff_branched.1
    · exact isBranchedEpSubgroupoid_zero _
  isNDimensional k := by
    rcases k with _ | _ | k
    · exact indicator_singleton_zero_branched.2
    · exact indicator_axis2_diff_branched.2
    · exact isNDimensional_zero _
  finite_support y := by
    refine (finite_le_nat 1).subset fun k hk => ?_
    by_contra hk'
    have hk2 : ¬ k ≤ 1 := hk'
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    exact hk (by
      change decompA k y = 0
      unfold decompA
      rw [if_neg h0, if_neg h1]
      rfl)
  eq_finsum y := by
    rw [finsum_eq_sum_of_support_subset (s := {0, 1}) _ fun k hk => by
      by_contra hk'
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
        not_or] at hk'
      exact hk (by simp [decompA, hk'.1, hk'.2])]
    rw [Finset.sum_pair zero_ne_one]
    simp only [decompA, if_true, one_ne_zero, if_false]
    by_cases hy0 : y = 0
    · subst hy0; simp [zero_mem_axis2]
    · by_cases hyL : y ∈ axis2
      · simp [hy0, hyL]
      · simp [hy0, hyL]

theorem decompB_dd :
    (trivial (rnPolyfold 2)).IsDimDecomposition (axis2.indicator 1) decompB where
  isBranched k := by
    by_cases hk : k = 1
    · subst hk; exact indicator_axis2_branched.1
    · simp only [decompB, hk, if_false]; exact isBranchedEpSubgroupoid_zero _
  isNDimensional k := by
    by_cases hk : k = 1
    · subst hk; exact indicator_axis2_branched.2
    · simp only [decompB, hk, if_false]; exact isNDimensional_zero _
  finite_support y := by
    refine (finite_singleton 1).subset fun k hk => ?_
    by_contra hk'
    exact hk (by
      change decompB k y = 0
      unfold decompB
      rw [if_neg (fun h => hk' (mem_singleton_iff.2 h))]
      rfl)
  eq_finsum y := by
    rw [finsum_eq_single _ 1 fun k hk => by simp [decompB, hk]]
    simp [decompB]

theorem locFinA : IsLocFinB decompA := fun _ => ⟨univ, univ_mem, by
  refine (finite_le_nat 1).subset fun k hk => ?_
  obtain ⟨z, -, hz⟩ := hk
  by_contra hk'
  have h0 : k ≠ 0 := by intro h; exact hk' (by simp [h])
  have h1 : k ≠ 1 := by intro h; exact hk' (by simp [h])
  exact hz (by unfold decompA; rw [if_neg h0, if_neg h1]; rfl)⟩

theorem locFinB : IsLocFinB decompB := fun _ => ⟨univ, univ_mem, by
  refine (finite_singleton 1).subset fun k hk => ?_
  obtain ⟨z, -, hz⟩ := hk
  by_contra hk'
  exact hz (by unfold decompB; rw [if_neg (fun h => hk' (mem_singleton_iff.2 h))]; rfl)⟩

end Counterexample

/-! ### `B` is false -/

theorem not_B : ¬ B := by
  intro hB
  obtain ⟨Θk, -, huniq⟩ := hB _ _ (EpGroupoid.trivial (rnPolyfold 2)) (axis2.indicator 1)
    (isBranchedB_of indicator_axis2_branched.1)
  have e := (huniq _ (isDimDecompB_of decompA_dd locFinA)).trans
    (huniq _ (isDimDecompB_of decompB_dd locFinB)).symm
  have := congrFun (congrFun e 0) 0
  simp [decompA, decompB] at this

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

theorem B_to_A : B → A := fun h => absurd h not_B

#rt_check RoundTrip.V9_9.not_B [
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartStructure_isOfDim,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_zero,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_of_isOfDim,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dim_smul,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ,
  Polyfold.EpGroupoid.decompA_isDimDecomposition, Polyfold.EpGroupoid.decompB_isDimDecomposition,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]
#rt_check RoundTrip.V9_9.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartStructure_isOfDim,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_zero,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_of_isOfDim,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dim_smul,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ,
  Polyfold.EpGroupoid.decompA_isDimDecomposition, Polyfold.EpGroupoid.decompB_isDimDecomposition,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]
#rt_overlap RoundTrip.V9_9.B_to_A [
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPartStructure_isOfDim,
  Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_zero,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_eq_of_isOfDim,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dim_smul,
  Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ,
  Polyfold.EpGroupoid.decompA_isDimDecomposition, Polyfold.EpGroupoid.decompB_isDimDecomposition,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]

end RoundTrip.V9_9
