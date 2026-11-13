import Polyfold.Chapter9.BoundaryNotNull
import Polyfold.Chapter9.BoundaryFaceNullSets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.5, Definition 9.5.14, p. 448 (2017: Definition 9.17, p. 327), with Definition 9.4.5, p. 431.

# The `(n-1)`-dimensional null sets of the boundaries `∂Mᵢ` and the σ-algebra `L(∂S)`

## What is formalized

* `MPolyfold.tameBoundaries n`: the class of the boundaries `∂M` of the `n`-dimensional
  submanifolds `M` with tame induced structure (the sheets of tame branching structures).
* `MPolyfold.boundaryNullSets n : SheetNullSets (tameBoundaries n)`: the `(n-1)`-dimensional null
  sets, `IsNull B A ↔ IsHNull (n-1) (A ∩ B)`, with no hypothesis (a nonempty boundary is not
  null: `not_isHNull_submanifoldBoundary`).
* `MPolyfold.isHNull_zero_iff`, `MPolyfold.boundaryNullSets_one_isNull_iff`: for `n = 1` these
  are the counting null sets `SheetNullSets.point` of `BoundaryFaceNullSets`.
* `EpGroupoid.isMeasureZeroBoundary_boundaryNullSets_iff`: for an `n`-dimensional `Θ`, `K` has
  measure zero in `∂S` iff near each `x ∈ supp(∂Θ)` a tame local branching structure has
  `∂Mᵢ ∩ π⁻¹(K)` of `(n-1)`-dimensional measure zero for all `i`;
  `EpGroupoid.isHNull_boundary_of_isMeasureZeroBoundary`: then this holds for every tame
  structure (the notion is well defined).
* `EpGroupoid.lebesgueSigmaBoundaryH X n Θ`: **Definition 9.5.14**, the σ-algebra `L(∂S)`, with
  these null sets.
* Corners: `hNull_setOf_two_coord_eq_zero` (a codimension-`2` coordinate subspace of `ℝⁿ` is
  `(n-1)`-null), `MPolyfold.HasCornerStructureOfDim.isHNull_two_le_degIndex`,
  `MPolyfold.isHNull_two_le_subDegIndex` (the points with `d_M ≥ 2` of a tame `n`-dimensional `M`
  are `(n-1)`-null), `MPolyfold.isHNull_submanifoldBoundary_diff_boundaryStratum` (`∂M` minus the
  stratum `{d_M = 1}` is `(n-1)`-null: the stratum carries the boundary integral).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace
open scoped NNReal ENNReal

noncomputable section

namespace Polyfold

universe u

/-! ### Codimension two in `ℝⁿ` -/

/-- Inserting a `0` at the place `i` is `1`-Lipschitz `ℝᵐ → ℝᵐ⁺¹`. -/
theorem lipschitzWith_insertNth_zero {m : ℕ} (i : Fin (m + 1)) :
    LipschitzWith 1 fun u : Fin m → ℝ => (i.insertNth (0 : ℝ) u : Fin (m + 1) → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun u u' => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro l
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same, dist_self]; exact dist_nonneg
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    exact dist_le_pi_dist u u' j

/-- A coordinate hyperplane of `ℝᵐ` is `m`-null. -/
theorem hNull_setOf_coord_eq_zero {m : ℕ} (j : Fin m) :
    HNull (m : ℝ) {u : Fin m → ℝ | u j = 0} := by
  rw [hNull_iff]
  have e : (μH[(m : ℝ)] : Measure (Fin m → ℝ)) = volume := by
    have := hausdorffMeasure_pi_real (ι := Fin m)
    rwa [Fintype.card_fin] at this
  rw [e]
  have hs : LinearMap.ker (LinearMap.proj j : (Fin m → ℝ) →ₗ[ℝ] ℝ) ≠ ⊤ := fun h => by
    have : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈
        LinearMap.ker (LinearMap.proj j : (Fin m → ℝ) →ₗ[ℝ] ℝ) := h ▸ Submodule.mem_top
    simp at this
  exact Measure.addHaar_submodule volume _ hs

/-- **A codimension-`2` coordinate subspace of `ℝⁿ` is `(n-1)`-null.** -/
theorem hNull_setOf_two_coord_eq_zero {n : ℕ} {i j : Fin n} (hij : j ≠ i) :
    HNull ((n - 1 : ℕ) : ℝ) {v : Fin n → ℝ | v i = 0 ∧ v j = 0} := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij
    have h := (hNull_setOf_coord_eq_zero j').image_lipschitzOn (Nat.cast_nonneg m)
      (lipschitzWith_insertNth_zero i).lipschitzOnWith
    refine h.mono fun v hv => ⟨fun k => v (i.succAbove k), hv.2, funext fun l => ?_⟩
    change (i.insertNth (0 : ℝ) (fun k => v (i.succAbove k)) : Fin (m + 1) → ℝ) l = v l
    rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨k, rfl⟩
    · rw [Fin.insertNth_apply_same]; exact hv.1.symm
    · rw [Fin.insertNth_apply_succAbove]

namespace MPolyfold

/-! ### The corners are null in the boundary -/

section Corner

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}

/-- **The corners are `(n-1)`-null** (2021 p. 448): for `Q` with a corner structure of dimension
`n`, the points with `d_Q ≥ 2` have `(n-1)`-dimensional measure zero. -/
theorem HasCornerStructureOfDim.isHNull_two_le_degIndex {n : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) : Q.IsHNull (n - 1) {z | 2 ≤ Q.degIndex z} := by
  refine isHNull_of_forall_exists_chart hcs.hasCornerStructure.isSmoothSubmanifold_univ
    (subset_univ _) fun z _ => ?_
  obtain ⟨κ, hzκ⟩ := hcs.exists_cornerCoords z
  refine ⟨κ.χ, κ.isChart, κ.s_subset hzκ, κ.s, κ.isOpen_s, hzκ, ?_⟩
  rw [← hNull_image_affine_iff κ.Ψ κ.c (Nat.cast_nonneg _)]
  have hU : HNull ((n - 1 : ℕ) : ℝ)
      (⋃ p : {p : Fin n × Fin n // p.2 ≠ p.1}, {v : Fin n → ℝ | v p.1.1 = 0 ∧ v p.1.2 = 0}) :=
    hNull_iUnion fun p => hNull_setOf_two_coord_eq_zero p.2
  refine hU.mono ?_
  rintro _ ⟨_, ⟨w, ⟨⟨hw2, hws⟩, -⟩, rfl⟩, rfl⟩
  have h2 : 1 < (Finset.univ.filter fun l => κ.coord w l = 0).card := by
    rw [← κ.degIndex_eq_card hws]; exact hw2
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
  exact mem_iUnion.2 ⟨⟨(a, b), hab.symm⟩, (Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2⟩

end Corner

section Sheet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The corners of a tame sheet are null in its boundary** (2021 p. 448): for an
`n`-dimensional submanifold `M` with tame induced structure, the points with `d_M ≥ 2` have
`(n-1)`-dimensional measure zero. -/
theorem isHNull_two_le_subDegIndex {M : Set X} {n : ℕ} (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) :
    P.IsHNull (n - 1) {y | ∃ hy : y ∈ M, 2 ≤ P.subDegIndex hM.1.isSubMPolyfold ⟨y, hy⟩} := by
  have := P.paracompactSpace_subtype M
  have hcs := hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  refine (isHNull_iff_subPolyfold hM.1 (fun y hy => hy.1) (n - 1)).2
    (hcs.isHNull_two_le_degIndex.mono ?_)
  rintro a ⟨_, ha⟩
  exact ha

/-- **`∂M` minus the stratum `{d_M = 1}` is `(n-1)`-null** (2021 p. 448 with p. 427): the
boundary of a tame `n`-dimensional sheet is, up to an `(n-1)`-dimensional null set, the stratum on
which the boundary orientation is defined (Definition 9.3.8). -/
theorem isHNull_submanifoldBoundary_diff_boundaryStratum {M : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (ht : P.HasTameInducedStructure M) :
    P.IsHNull (n - 1) (P.submanifoldBoundary M \ P.boundaryStratum M) := by
  refine (isHNull_two_le_subDegIndex hM ht).mono ?_
  rintro y ⟨⟨_, hyM, h1⟩, hns⟩
  refine ⟨hyM, ?_⟩
  have hne : P.subDegIndex hM.1.isSubMPolyfold ⟨y, hyM⟩ ≠ 1 := fun h =>
    hns ((mem_boundaryStratum_iff_subDegIndex hM.1 ht hyM).2 h)
  have h1' : 1 ≤ P.subDegIndex hM.1.isSubMPolyfold ⟨y, hyM⟩ := h1
  omega

/-! ### The null-set system of the boundaries -/

variable (P) in
/-- The class of the boundaries `∂M` of the `n`-dimensional submanifolds `M` with tame induced
structure (the sheets of the tame branching structures of dimension `n`, Definition 9.3.6). -/
def tameBoundaries (n : ℕ) : Set (Set X) :=
  {B | ∃ M, P.IsSubmanifoldOfDim M n ∧ P.HasTameInducedStructure M ∧
    B = P.submanifoldBoundary M}

theorem submanifoldBoundary_mem_tameBoundaries {M : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (ht : P.HasTameInducedStructure M) :
    P.submanifoldBoundary M ∈ P.tameBoundaries n := ⟨M, hM, ht, rfl⟩

variable (P) in
/-- **The `(n-1)`-dimensional null sets in the boundaries `∂Mᵢ`** (Definition 9.5.14, 2021
p. 448; Definition 9.4.5 in dimension `n - 1`): a null-set system on the class of the boundaries
of the tame `n`-dimensional sheets, with no hypothesis; `A` is null in `∂M` iff `A ∩ ∂M` has
`(n-1)`-dimensional measure zero in the M-polyfold charts. -/
def boundaryNullSets (n : ℕ) : SheetNullSets (P.tameBoundaries n) :=
  P.hNullSets (n - 1) _ fun B hB hne => by
    obtain ⟨M, hM, ht, rfl⟩ := hB
    exact not_isHNull_submanifoldBoundary hM ht hne

theorem boundaryNullSets_isNull_iff {n : ℕ} {B A : Set X} :
    (P.boundaryNullSets n).IsNull B A ↔ P.IsHNull (n - 1) (A ∩ B) := Iff.rfl

/-- **`0`-dimensional measure zero**: only the empty set (the `0`-dimensional Hausdorff measure
is the counting measure). -/
theorem isHNull_zero_iff {C : Set X} : P.IsHNull 0 C ↔ C = ∅ := by
  refine ⟨fun h => eq_empty_of_forall_notMem fun z hz => ?_, fun h => h ▸ isHNull_empty 0⟩
  obtain ⟨ψ, hψ, hzψ⟩ := P.exists_isChart_mem_source z
  have h1 := h ψ hψ {z} (singleton_subset_iff.2 hz) (singleton_subset_iff.2 hzψ)
    ((countable_singleton z).image ψ).isSeparable
  let : MeasurableSpace (ψ.model.E 0) := borel _
  have : BorelSpace (ψ.model.E 0) := ⟨rfl⟩
  have h2 := hNull_iff.1 h1
  rw [image_singleton, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton] at h2
  exact one_ne_zero h2

/-- **The case `n = 1`**: the null sets of the boundaries of `1`-dimensional sheets are the
counting null sets `SheetNullSets.point` (`A` is null in `∂M` iff `A ∩ ∂M = ∅`). -/
theorem boundaryNullSets_one_isNull_iff {B A : Set X} :
    (P.boundaryNullSets 1).IsNull B A ↔ (SheetNullSets.point (P.tameBoundaries 1)).IsNull B A := by
  rw [boundaryNullSets_isNull_iff, SheetNullSets.point_isNull_iff, isHNull_zero_iff,
    disjoint_iff_inter_eq_empty]

end Sheet

end MPolyfold

/-! ### Definition 9.5.14 -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {n : ℕ}

/-- The boundaries of the sheets of a tame local branching structure of an `n`-dimensional `Θ`
lie in the class `tameBoundaries n`. -/
theorem TameBranchingStructure.submanifoldBoundary_mem (hΘ : X.IsNDimensional Θ n) {x : Obj}
    (B : X.TameBranchingStructure Θ x) (i : B.ι) :
    X.PObj.submanifoldBoundary (B.M i) ∈ X.PObj.tameBoundaries n :=
  submanifoldBoundary_mem_tameBoundaries
    (B.toLocalBranchingStructure.isOfDim_of_isNDimensional hΘ i) (B.hasTameInducedStructure i)

/-- **`(n-1)`-dimensional measure zero in `∂S`** (2021 p. 448, before Definition 9.5.14), for an
`n`-dimensional `Θ`: `K` has measure zero in `∂S = |supp(∂Θ)|` iff every `x ∈ supp(∂Θ)` has a
tame local branching structure with `∂Mᵢ ∩ π⁻¹(K)` of `(n-1)`-dimensional measure zero for all
`i` (Definition 9.4.5 in dimension `n - 1`, in the M-polyfold charts). -/
theorem isMeasureZeroBoundary_boundaryNullSets_iff (hΘ : X.IsNDimensional Θ n)
    {K : Set X.OrbitSpace} :
    X.IsMeasureZeroBoundary (X.PObj.boundaryNullSets n) Θ K ↔
      ∀ x ∈ supp (X.boundaryTheta Θ), ∃ B : X.TameBranchingStructure Θ x,
        ∀ i, X.PObj.IsHNull (n - 1) (X.PObj.submanifoldBoundary (B.M i) ∩ X.π ⁻¹' K) := by
  have e : ∀ A C : Set Obj, A ∩ C ∩ A = A ∩ C := fun A C => by
    rw [inter_right_comm, inter_self]
  constructor
  · intro h x hx
    obtain ⟨B, -, hB⟩ := h x hx
    exact ⟨B, fun i => by have := hB i; rwa [boundaryNullSets_isNull_iff, e] at this⟩
  · intro h x hx
    obtain ⟨B, hB⟩ := h x hx
    exact ⟨B, fun i => B.submanifoldBoundary_mem hΘ i, fun i => by
      rw [boundaryNullSets_isNull_iff, e]; exact hB i⟩

/-- **The notion is well defined** (2021 p. 448): if `K` has measure zero in `∂S`, then for
every tame local branching structure of the `n`-dimensional `Θ` at a point of `supp(∂Θ)` the
sets `∂Mᵢ ∩ π⁻¹(K)` have `(n-1)`-dimensional measure zero (given the independence of
Theorem 9.2.1, through which `∂Θ` is defined). -/
theorem isHNull_boundary_of_isMeasureZeroBoundary (hind : X.HasIndependentTangentSums Θ)
    (hΘ : X.IsNDimensional Θ n) {K : Set X.OrbitSpace}
    (h : X.IsMeasureZeroBoundary (X.PObj.boundaryNullSets n) Θ K) {x : Obj}
    (hx : x ∈ supp (X.boundaryTheta Θ)) (B : X.TameBranchingStructure Θ x) (i : B.ι) :
    X.PObj.IsHNull (n - 1) (X.PObj.submanifoldBoundary (B.M i) ∩ X.π ⁻¹' K) := by
  have h1 := isMeasureZeroBoundaryAll_of _ hind h x hx B.toLocalBranchingStructure
    (fun i => B.submanifoldBoundary_mem hΘ i) i
  rw [boundaryNullSets_isNull_iff, inter_right_comm, inter_self] at h1
  exact h1

variable (X) in
/-- **Definition 9.5.14, 2021 p. 448 (2017: Definition 9.17, p. 327) (the canonical σ-algebra
`L(∂S)`)**, for `Θ` of dimension `n`: the smallest σ-algebra on `∂S = |supp(∂Θ)|` containing the
Borel sets and the sets of `(n-1)`-dimensional measure zero (`boundaryNullSets`). -/
@[instance_reducible] def lebesgueSigmaBoundaryH (n : ℕ) (Θ : Obj → ℚ) :
    MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) :=
  X.lebesgueSigmaBoundary (X.PObj.boundaryNullSets n) Θ

/-- Every Borel set of `∂S` lies in `L(∂S)`. -/
theorem borel_le_lebesgueSigmaBoundaryH (n : ℕ) (Θ : Obj → ℚ) :
    borel (X.orbitSupp (X.boundaryTheta Θ)) ≤ X.lebesgueSigmaBoundaryH n Θ :=
  borel_le_borelNullSigma _

/-- Every subset of `∂S` of `(n-1)`-dimensional measure zero lies in `L(∂S)`. -/
theorem measurableSet_lebesgueSigmaBoundaryH {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : X.IsMeasureZeroBoundary (X.PObj.boundaryNullSets n) Θ (Subtype.val '' K)) :
    MeasurableSet[X.lebesgueSigmaBoundaryH n Θ] K :=
  measurableSet_borelNullSigma_of_mem hK

end EpGroupoid

end Polyfold
