import Polyfold.Chapter9.GeneralCorollaries
import Polyfold.Chapter9.GoodPoints
import Polyfold.Chapter9.PropertyTShrinking2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.1, Definition 9.1.2, last paragraph and its footnote, p. 402 (2017: Definition 9.1, p. 291;
the footnote is new in 2021).

# The dimension of a branched ep⁺-subgroupoid

The last paragraph of Definition 9.1.2 calls `Θ` `n`-dimensional if at every point of its support
the sheets of a local branching structure can be taken `n`-dimensional, and *locally
equidimensional* if the sheets of a sufficiently small local branching structure at every point of
the support have one dimension.  A footnote says that an `n`-dimensional `Θ` is not
`m`-dimensional for `m ≠ n`, a proof being left to the reader after the chapter.

## What is formalized

* `LocalBranchingStructure.exists_submanifoldTangent_eq`: every tangent space `T_xM'_j` of one
  local branching structure at `x` is a tangent space `T_xMᵢ` of any other one at `x` (from the
  independence of the tangent sums, Theorem 9.2.1 (1), `hasIndependentTangentSums`, and the
  positivity of the weights); hence the sheets of any two structures at `x` have the same
  dimensions at `x` (`hasDimAt_of_isOfDim`, `isOfDim_unique`).
* **The footnote** (`definition_9_1_2_footnote`, and `definition_9_1_2_footnote_of_ne_zero` for
  `Θ ≠ 0` with values in `ℚ⁺`): an `n`-dimensional `Θ` with nonempty support is not
  `m`-dimensional for `m ≠ n`.  For `Θ = 0` it does not hold as we read it: the zero functor is
  `n`-dimensional for every `n` (`definition_9_1_2_footnote_zero`).
* **Locally equidimensional** (`IsLocallyEquidimensional`): at every point of `supp(Θ)` some local
  branching structure has sheets of one dimension.  Equivalently, for a branched
  ep⁺-subgroupoid (`isLocallyEquidimensional_iff`): at every `x ∈ supp(Θ)` there is an `n` such
  that **every** local branching structure at `x`, restricted to a small enough neighbourhood of
  `x`, has only `n`-dimensional sheets — the reading "sufficiently small" of the book.
* `IsNDimensional.isLocallyEquidimensional`, and the local constancy of the dimension
  (`IsLocallyEquidimensional.exists_isOpen_isNDimensionalAt`): near a point of the support the
  structures at nearby points of the support have the same dimension.
-/

open Set

universe u

namespace Polyfold

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace LocalBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj}

/-- At a point of the support, a local branching structure has at least one sheet. -/
theorem nonempty_ι_of_mem_supp (B : X.LocalBranchingStructure Θ x) (hx : x ∈ supp Θ) :
    Nonempty B.ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hx' : 0 < Θ x := hx
  rw [B.eq_sum x B.mem_U] at hx'
  exact hx'.ne' (Finset.sum_eq_zero fun i _ => (IsEmpty.false i).elim)

/-- **The tangent spaces at `x` of two local branching structures at `x` agree as sets**: every
`T_xM'_j` is some `T_xMᵢ`.  (The tangent sums `∑ σᵢ · T_xMᵢ` agree, Theorem 9.2.1 (1), and all
weights are positive.) -/
theorem exists_submanifoldTangent_eq (B B' : X.LocalBranchingStructure Θ x) (j : B'.ι) :
    ∃ i, X.PObj.submanifoldTangent (B.M i) x = X.PObj.submanifoldTangent (B'.M j) x := by
  classical
  by_contra h
  push Not at h
  set L := X.PObj.submanifoldTangent (B'.M j) x
  have h1 : B.tangentSum L = 0 := by
    rw [tangentSum_apply]
    exact Finset.sum_eq_zero fun i _ => if_neg (h i)
  have h2 : 0 < B'.tangentSum L := by
    rw [tangentSum_apply]
    refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · split_ifs
      · exact (B'.σ_pos i).le
      · exact le_rfl
    · rw [if_pos rfl]
      exact B'.σ_pos j
  rw [← hasIndependentTangentSums Θ x B B'] at h2
  exact h2.ne' h1

/-- If one local branching structure at `x` has only `n`-dimensional sheets, every sheet of any
other local branching structure at `x` is `n`-dimensional at `x`. -/
theorem hasDimAt_of_isOfDim (B B' : X.LocalBranchingStructure Θ x) {n : ℕ} (hB : B.IsOfDim n)
    (j : B'.ι) : X.PObj.HasDimAt (B'.M j) x n := by
  obtain ⟨i, hi⟩ := B.exists_submanifoldTangent_eq B' j
  obtain ⟨k, hk⟩ := (B'.isSmoothSubmanifold j).exists_hasDimAt (B'.mem_M j)
  have hnk := HasDimAt.eq_of_submanifoldTangent_eq (hB i).1 (B'.isSmoothSubmanifold j)
    ((hB i).2 x (B.mem_M i)) hk hi
  rwa [← hnk] at hk

/-- **The dimension of a local branching structure at a point of the support is determined**: if
`B` and `B'` at `x ∈ supp(Θ)` have only `n`- resp. `m`-dimensional sheets, then `n = m`. -/
theorem isOfDim_unique (B B' : X.LocalBranchingStructure Θ x) (hx : x ∈ supp Θ) {n m : ℕ}
    (hB : B.IsOfDim n) (hB' : B'.IsOfDim m) : n = m := by
  obtain ⟨j⟩ := B'.nonempty_ι_of_mem_supp hx
  exact ((hB' j).eq_of_hasDimAt (B.hasDimAt_of_isOfDim B' hB j)).symm

/-- An `n`-dimensional structure restricted to a point `y ∈ U(x)` is `n`-dimensional. -/
theorem IsOfDim.restrictAt {B : X.LocalBranchingStructure Θ x} {n : ℕ} (hB : B.IsOfDim n)
    {y : Obj} (hy : y ∈ B.U) : (B.restrictAt hy).IsOfDim n := fun i =>
  (hB i.1).inter_isOpen (B.isOpen_nbhdAt y)

/-- An `n`-dimensional structure restricted to an open `V ∋ x` is `n`-dimensional. -/
theorem IsOfDim.restrict {B : X.LocalBranchingStructure Θ x} {n : ℕ} (hB : B.IsOfDim n)
    {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) :
    (B.restrict hV hxV hVU).IsOfDim n := fun i =>
  (hB i).inter_isOpen hV

/-- **Every local branching structure at `x`, restricted near `x`, is `n`-dimensional**, if one
structure at `x` is (the dimension is locally constant on every M-polyfold,
`MPolyfold.hasLocallyConstantDimAt`, and is `n` at `x` by `hasDimAt_of_isOfDim`). -/
theorem exists_restrict_isOfDim (B₀ B : X.LocalBranchingStructure Θ x) {n : ℕ}
    (hB₀ : B₀.IsOfDim n) : ∃ (V : Set Obj) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U),
      (B.restrict hV hxV hVU).IsOfDim n := by
  obtain ⟨V, hV, hxV, hVU, dim, hdim⟩ :=
    B.exists_restrict_labelled (MPolyfold.hasLocallyConstantDimAt x)
  refine ⟨V, hV, hxV, hVU, fun i => ?_⟩
  have h := (hdim i).eq_of_hasDimAt (B₀.hasDimAt_of_isOfDim (B.restrict hV hxV hVU) hB₀ i)
  rw [← h]
  exact hdim i

end LocalBranchingStructure

open LocalBranchingStructure

variable {Θ : Obj → ℚ}

/-- **The footnote to Definition 9.1.2, 2021 p. 402** (new in 2021): an `n`-dimensional `Θ` with
nonempty support is not `m`-dimensional for `m ≠ n`.  As in the book, for `Θ ≠ 0` (the zero
functor is `n`-dimensional for every `n`, `isNDimensional_zero`); proved from the independence of
the tangent sums (Theorem 9.2.1 (1)), as the footnote suggests ("after reading the relevant parts
of this chapter"). -/
theorem definition_9_1_2_footnote {n m : ℕ} (hn : X.IsNDimensional Θ n)
    (hm : X.IsNDimensional Θ m) (hΘ : (supp Θ).Nonempty) : n = m := by
  obtain ⟨x, hx⟩ := hΘ
  obtain ⟨B, hB⟩ := hn x hx
  obtain ⟨B', hB'⟩ := hm x hx
  exact B.isOfDim_unique B' hx hB hB'

/-- **The footnote to Definition 9.1.2, 2021 p. 402**, for `Θ : X → ℚ⁺` with `Θ ≠ 0`: an
`n`-dimensional `Θ` is not `m`-dimensional for `m ≠ n`. -/
theorem definition_9_1_2_footnote_of_ne_zero (hΘ : ∀ x, 0 ≤ Θ x) (h0 : Θ ≠ 0) {n m : ℕ}
    (hn : X.IsNDimensional Θ n) (hm : X.IsNDimensional Θ m) : n = m := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  exact definition_9_1_2_footnote hn hm ⟨x, lt_of_le_of_ne (hΘ x) (Ne.symm hx)⟩

/-- For `Θ = 0` the footnote to Definition 9.1.2 does not hold as we read it: the zero functor is
both `0`- and `1`-dimensional (`isNDimensional_zero`); hence the hypothesis `Θ ≠ 0` above. -/
theorem definition_9_1_2_footnote_zero : X.IsNDimensional 0 0 ∧ X.IsNDimensional 0 1 :=
  ⟨isNDimensional_zero 0, isNDimensional_zero 1⟩

variable (X) in
/-- **`Θ` is locally equidimensional** (Definition 9.1.2, last paragraph, 2021 p. 402): at every
point of `supp(Θ)` the sheets of some local branching structure all have one dimension.  By
`isLocallyEquidimensional_iff`, then every local branching structure at that point, restricted
to a sufficiently small neighbourhood, has sheets of that one dimension (the book's wording). -/
def IsLocallyEquidimensional (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (n : ℕ), B.IsOfDim n

/-- An `n`-dimensional `Θ` is locally equidimensional. -/
theorem IsNDimensional.isLocallyEquidimensional {n : ℕ} (h : X.IsNDimensional Θ n) :
    X.IsLocallyEquidimensional Θ := fun x hx => by
  obtain ⟨B, hB⟩ := h x hx
  exact ⟨B, n, hB⟩

/-- **"Sufficiently small" structures**: for a locally equidimensional `Θ` and `x ∈ supp(Θ)` there
is an `n` such that every local branching structure at `x`, restricted to a small neighbourhood
of `x`, has only `n`-dimensional sheets. -/
theorem IsLocallyEquidimensional.exists_restrict_isOfDim (h : X.IsLocallyEquidimensional Θ)
    {x : Obj} (hx : x ∈ supp Θ) : ∃ n, ∀ B : X.LocalBranchingStructure Θ x,
      ∃ (V : Set Obj) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U),
        (B.restrict hV hxV hVU).IsOfDim n := by
  obtain ⟨B₀, n, hB₀⟩ := h x hx
  exact ⟨n, fun B => B₀.exists_restrict_isOfDim B hB₀⟩

/-- **Locally equidimensional, the two readings** (Definition 9.1.2, 2021 p. 402): for a branched
ep⁺-subgroupoid, "some local branching structure at every `x ∈ supp(Θ)` has sheets of one
dimension" iff "at every `x ∈ supp(Θ)`, every sufficiently small local branching structure has
sheets of one dimension `n(x)`". -/
theorem isLocallyEquidimensional_iff (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.IsLocallyEquidimensional Θ ↔ ∀ x ∈ supp Θ, ∃ n, ∀ B : X.LocalBranchingStructure Θ x,
      ∃ (V : Set Obj) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U),
        (B.restrict hV hxV hVU).IsOfDim n := by
  refine ⟨fun h x hx => h.exists_restrict_isOfDim hx, fun h x hx => ?_⟩
  obtain ⟨n, hn⟩ := h x hx
  obtain ⟨B⟩ := hΘ.localBranching x hx
  obtain ⟨V, hV, hxV, hVU, hB⟩ := hn B
  exact ⟨B.restrict hV hxV hVU, n, hB⟩

/-- **The local dimension is locally constant on the support**: for a locally equidimensional `Θ`
and `x ∈ supp(Θ)` there are an open `U ∋ x` and an `n` such that at every `y ∈ U ∩ supp(Θ)` some
(hence, after restriction, every) local branching structure is `n`-dimensional. -/
theorem IsLocallyEquidimensional.exists_isOpen_isNDimensionalAt (h : X.IsLocallyEquidimensional Θ)
    {x : Obj} (hx : x ∈ supp Θ) : ∃ (U : Set Obj) (n : ℕ), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U ∩ supp Θ, ∃ B : X.LocalBranchingStructure Θ y, B.IsOfDim n := by
  obtain ⟨B, n, hB⟩ := h x hx
  exact ⟨B.U, n, B.isOpen_U, B.mem_U, fun y hy => ⟨B.restrictAt hy.1, hB.restrictAt hy.1⟩⟩

end EpGroupoid

end Polyfold
