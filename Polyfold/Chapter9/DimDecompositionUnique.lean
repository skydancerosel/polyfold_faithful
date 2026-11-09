import Polyfold.Chapter9.AppendixSlices

/-!
# Proposition 9.1.11: uniqueness for the decomposition the proof constructs

2021 Proposition 9.1.11, pp. 407–408 (2017: Proposition 9.2, p. 297), says that a branched
ep⁺-subgroupoid `Θ` has a family `(Θ_k)` of `k`-dimensional branched ep⁺-subgroupoids with
`Θ = Θ_0 + Θ_1 + ⋯`, "uniquely characterized" by these two properties.  As we read it, the
uniqueness does not hold (`not_proposition_9_1_11_rn`): the indicator of a line `L` in `ℝ²` has
the decompositions `Θ_0 = 1_{0}`, `Θ_1 = 1_{L ∖ 0}` and `Θ_0 = 0`, `Θ_1 = 1_L`.

The proof of the text builds `Θ_k` near each point `x` as the `k`-dimensional part of a local
branching structure at `x`: the sum of the weights of its `k`-dimensional submanifolds
(`LocalBranchingStructure.dimPart`).  Call a decomposition **local** when it has this form near
every point of `supp(Θ)` (`IsLocalDimDecomposition`).  This file proves that a local
decomposition is unique, given Proposition 9.1.12 (2021, p. 408: the dimensional parts of any
two local branching structures at `x` agree near `x`):

* `isDimDecomposition_unique`: two local dimensional decompositions of `Θ` are equal;
* `proposition_9_1_11_unique_rn` and `proposition_9_1_11_unique_of_hasGraphChartAt`: the same with
  no hypothesis over `ℝᵐ`, and under the graph representation in general (where Proposition
  9.1.12 is proved, `proposition_9_1_12_rn`, `proposition_9_1_12_of_hasGraphChartAt`);
* `decompB_isLocalDimDecomposition`: the decomposition `Θ_1 = 1_L` of the counterexample is local
  (so the condition can be met), and `decompA_not_isLocalDimDecomposition`: the other one is not.

So the uniqueness of Proposition 9.1.11 holds once "uniquely" is read among local decompositions,
which are what its proof produces.  The gluing of the local `Θ_k` into functors on all of `X`
(gap G.96) is not formalized here.
-/

open Set Filter Topology

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

variable (X) in
/-- A family `(Θ_k)` is a **local dimensional decomposition** of `Θ`: near every point `x` of
`supp(Θ)` there are a local branching structure `B` of `Θ` at `x` and a labelling `dim` of its
submanifolds by their dimensions with `Θ_k = B.dimPart dim k` near `x` for every `k`.  This is the
form of the decomposition built in the proof of Proposition 9.1.11 (2021, pp. 407–408). -/
def IsLocalDimDecomposition (Θ : Obj → ℚ) (Θk : ℕ → Obj → ℚ) : Prop :=
  ∀ x ∈ supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ),
    (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) ∧
      ∀ᶠ y in 𝓝 x, ∀ k, Θk k y = B.dimPart dim k y

/-- Off `supp(Θ)` every member of a dimensional decomposition vanishes: the `Θ_k` are
nonnegative and sum to `Θ(y) = 0`. -/
theorem IsDimDecomposition.eq_zero_of_not_mem_supp {Θk : ℕ → Obj → ℚ}
    (h : X.IsDimDecomposition Θ Θk) (hΘ : X.IsBranchedEpSubgroupoid Θ) {y : Obj}
    (hy : y ∉ supp Θ) (k : ℕ) : Θk k y = 0 := by
  have hy0 : Θ y = 0 := le_antisymm (not_lt.1 hy) (hΘ.nonneg y)
  have hsum : ∑ᶠ j, Θk j y = 0 := (h.eq_finsum y).symm.trans hy0
  have hnn : ∀ j, 0 ≤ Θk j y := fun j => (h.isBranched j).nonneg y
  have hfin := h.finite_support y
  rw [finsum_eq_sum _ hfin] at hsum
  by_cases hk : k ∈ hfin.toFinset
  · exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 hsum k hk
  · simpa using hk

/-- **Uniqueness of the local dimensional decomposition** (Proposition 9.1.11, 2021 p. 407, in the
reading of its proof): given Proposition 9.1.12, two local dimensional decompositions of a
branched ep⁺-subgroupoid are equal. -/
theorem isDimDecomposition_unique (h912 : X.Proposition_9_1_12)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {Θk Θk' : ℕ → Obj → ℚ} (h : X.IsDimDecomposition Θ Θk)
    (h' : X.IsDimDecomposition Θ Θk') (hl : X.IsLocalDimDecomposition Θ Θk)
    (hl' : X.IsLocalDimDecomposition Θ Θk') : Θk = Θk' := by
  funext k y
  by_cases hy : y ∈ supp Θ
  · obtain ⟨B, dim, hd, hev⟩ := hl y hy
    obtain ⟨B', dim', hd', hev'⟩ := hl' y hy
    obtain ⟨V, -, hyV, -, hagree⟩ := h912 Θ hΘ y B B' dim dim' hd hd'
    rw [hev.self_of_nhds k, hev'.self_of_nhds k]
    exact hagree k y hyV
  · rw [h.eq_zero_of_not_mem_supp hΘ hy k, h'.eq_zero_of_not_mem_supp hΘ hy k]

/-- **Proposition 9.1.11, uniqueness, under the graph representation**: local dimensional
decompositions are unique when every point has a graph chart (Proposition 9.1.12 holds there,
`proposition_9_1_12_of_hasGraphChartAt`). -/
theorem proposition_9_1_11_unique_of_hasGraphChartAt (hG : ∀ y, X.PObj.HasGraphChartAt y)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {Θk Θk' : ℕ → Obj → ℚ} (h : X.IsDimDecomposition Θ Θk)
    (h' : X.IsDimDecomposition Θ Θk') (hl : X.IsLocalDimDecomposition Θ Θk)
    (hl' : X.IsLocalDimDecomposition Θ Θk') : Θk = Θk' :=
  isDimDecomposition_unique (proposition_9_1_12_of_hasGraphChartAt hG) hΘ h h' hl hl'

end EpGroupoid

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor} {Θ : (Fin m → ℝ) → ℚ}

/-- **Proposition 9.1.11, uniqueness, over `ℝᵐ`**, with no further hypothesis: two local
dimensional decompositions of a branched ep⁺-subgroupoid are equal. -/
theorem proposition_9_1_11_unique_rn (hX : X.PObj = rnPolyfold m)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) {Θk Θk' : ℕ → (Fin m → ℝ) → ℚ}
    (h : X.IsDimDecomposition Θ Θk) (h' : X.IsDimDecomposition Θ Θk')
    (hl : X.IsLocalDimDecomposition Θ Θk) (hl' : X.IsLocalDimDecomposition Θ Θk') : Θk = Θk' :=
  isDimDecomposition_unique (proposition_9_1_12_rn hX) hΘ h h' hl hl'

/-- **The condition can be met**: in the example of `not_proposition_9_1_11_rn`, the decomposition
`Θ_0 = 0`, `Θ_1 = 1_L` of the indicator of the `x`-axis `L` of `ℝ²` is local (one submanifold
`L`, of dimension `1`, with weight `1`). -/
theorem decompB_isLocalDimDecomposition :
    (trivial (rnPolyfold 2)).IsLocalDimDecomposition (axis2.indicator 1) decompB := by
  intro x hx
  rw [supp_indicator_one] at hx
  refine ⟨localBranchingStructure_indicator_rn isOpen_univ (subset_univ _)
    (isClosed_axis2.preimage continuous_subtype_val) axis2_isSubmanifoldOfDim.1 hx,
    fun _ => 1, fun _ => axis2_isSubmanifoldOfDim, Eventually.of_forall fun y k => ?_⟩
  classical
  simp only [LocalBranchingStructure.dimPart, localBranchingStructure_indicator_rn, decompB]
  by_cases hk : k = 1
  · subst hk
    by_cases hy : y ∈ axis2
    · simp [hy]; rfl
    · simp [hy]
  · simp [hk, Ne.symm hk]

/-- **The other decomposition of the counterexample is not local**: `Θ_0 = 1_{0}`,
`Θ_1 = 1_{L ∖ 0}` is a dimensional decomposition of `1_L` but not of the form the proof of
Proposition 9.1.11 constructs. -/
theorem decompA_not_isLocalDimDecomposition :
    ¬ (trivial (rnPolyfold 2)).IsLocalDimDecomposition (axis2.indicator 1) decompA := by
  intro hA
  have e := proposition_9_1_11_unique_rn rfl indicator_axis2_branched.1
    decompA_isDimDecomposition decompB_isDimDecomposition hA decompB_isLocalDimDecomposition
  have := congrFun (congrFun e 0) 0
  simp [decompA, decompB] at this

end EpGroupoid

end Polyfold
