import Polyfold.Chapter9.GapP1_Stokes2021
import Polyfold.Chapter9.BoundaryOrientationContinuity2021
import Polyfold.Chapter4.GapP1_Remark422One

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, the paragraph before Definition 9.3.8, p. 427 (2017: before Definition 9.9, p. 313).

# The points with `d_M = 1` are open and dense in `∂M`

The text: for a tame `Mᵢ`, a smooth manifold with boundary with corners, "the set of points with
`d_{Mᵢ}(y) = 1` is open and dense in `∂Mᵢ` and has the structure of a smooth manifold".

## What is formalized

* `MPolyfold.setOf_degIndex_eq_one`, `MPolyfold.isOpen_degIndex_le_one`: `{d_Q = 1}` is
  `∂Q ∩ {d_Q ≤ 1}`, and `{d_Q ≤ 1}` is open (Lemma 2.4.3); so `{d_Q = 1}` is open in `∂Q`, for
  every M-polyfold.
* `MPolyfold.HasCornerStructureOfDim.boundary_subset_closure_degIndex_eq_one`: for `Q` with a
  corner structure, `{d_Q = 1}` is dense in `∂Q` (in corner coordinates a point with a vanishing
  coordinate is a limit of points with exactly that coordinate vanishing).
* For an `n`-dimensional submanifold `A` of an M-polyfold with tame induced structure (a sheet of
  a tame branching structure, Definition 9.3.6): the stratum `boundaryStratum A = {d_A = 1}` on
  which `o_{∂A}` is defined (Definition 9.3.8) is open in `∂A`
  (`exists_isOpen_boundaryStratum_eq`) and dense in `∂A`
  (`submanifoldBoundary_subset_closure_boundaryStratum`).

## Relation to the text

"Has the structure of a smooth manifold": the open piece `{d_A ≤ 1}` of `A` is a smooth manifold
with boundary (`remark_4_2_2_dA_one`, `Chapter4/GapP1_Remark422One.lean`), with boundary the
stratum; the tangent space of the stratum is read as `T^R_yA` (`boundaryCarrier`).  The stratum is
not built here as a submanifold of its own.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

section Corner

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}

/-- `{d_Q ≤ 1}` is open (Lemma 2.4.3). -/
theorem isOpen_degIndex_le_one (Q : MPolyfold Z) : IsOpen {x | Q.degIndex x ≤ 1} :=
  isOpen_degIndex_le Q 1

/-- `{d_Q = 1} = ∂Q ∩ {d_Q ≤ 1}`: the points of degeneracy index `1` are open in `∂Q`. -/
theorem setOf_degIndex_eq_one (Q : MPolyfold Z) :
    {x | Q.degIndex x = 1} = {x | 1 ≤ Q.degIndex x} ∩ {x | Q.degIndex x ≤ 1} := by
  ext x
  exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

/-- **The points with `d_Q = 1` are dense in `∂Q`** (2021 p. 427, for a manifold with boundary
with corners): for `Q` with a corner structure of dimension `n`, every point with `d_Q ≥ 1` is a
limit of points with `d_Q = 1`. -/
theorem HasCornerStructureOfDim.boundary_subset_closure_degIndex_eq_one {n : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) :
    {x | 1 ≤ Q.degIndex x} ⊆ closure {y | Q.degIndex y = 1} := by
  intro x hx
  rw [mem_closure_iff]
  intro G hG hxG
  obtain ⟨κ, hxκ⟩ := hcs.exists_cornerCoords x
  have hpos : 0 < (Finset.univ.filter fun j => κ.coord x j = 0).card := by
    rw [← κ.degIndex_eq_card hxκ]; exact hx
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  obtain ⟨y, hyG, hys, hyi, hyl⟩ :=
    κ.exists_coord_one_zero hG hxG hxκ (Finset.mem_filter.1 hi).2
  exact ⟨y, hyG, κ.degIndex_eq_one hys hyi fun j hj => (hyl j hj).ne'⟩

end Corner

section Sheet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The stratum `{d_A = 1}` is open in `∂A`** (2021 p. 427), for a smooth submanifold `A` with
tame induced structure: `boundaryStratum A = ∂A ∩ V` for an open `V`. -/
theorem exists_isOpen_boundaryStratum_eq {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) :
    ∃ V, IsOpen V ∧ P.boundaryStratum A = P.submanifoldBoundary A ∩ V := by
  have := P.paracompactSpace_subtype A
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1
    (isOpen_degIndex_le_one (subPolyfold hA.isSubMPolyfold))
  refine ⟨V, hV, ?_⟩
  ext y
  constructor
  · intro hy
    have hyA : y ∈ A := hy.1
    have h1 : P.subDegIndex hA.isSubMPolyfold ⟨y, hyA⟩ = 1 :=
      (mem_boundaryStratum_iff_subDegIndex hA ht hyA).1 hy
    refine ⟨(mem_submanifoldBoundary_iff_subDegIndex hA hyA).2 h1.ge, ?_⟩
    have : (⟨y, hyA⟩ : A) ∈ Subtype.val ⁻¹' V := by rw [hVe]; exact h1.le
    exact this
  · rintro ⟨⟨_, hyA, h1⟩, hyV⟩
    have h2 : (⟨y, hyA⟩ : A) ∈ {x : A | (subPolyfold hA.isSubMPolyfold).degIndex x ≤ 1} := by
      rw [← hVe]; exact hyV
    exact (mem_boundaryStratum_iff_subDegIndex hA ht hyA).2 (le_antisymm h2 h1)

/-- **The stratum `{d_A = 1}` is dense in `∂A`** (2021 p. 427), for an `n`-dimensional
submanifold `A` with tame induced structure (a sheet of a tame branching structure, Definition
9.3.6): every point of `∂A` is a limit of points of the stratum on which `o_{∂A}` is defined. -/
theorem submanifoldBoundary_subset_closure_boundaryStratum {A : Set X} {n : ℕ}
    (hA : P.IsSubmanifoldOfDim A n) (ht : P.HasTameInducedStructure A) :
    P.submanifoldBoundary A ⊆ closure (P.boundaryStratum A) := by
  have := P.paracompactSpace_subtype A
  have hcs := hA.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  rintro y ⟨_, hyA, h1⟩
  have hmem : (⟨y, hyA⟩ : A) ∈
      closure {a : A | (subPolyfold hA.1.isSubMPolyfold).degIndex a = 1} :=
    hcs.boundary_subset_closure_degIndex_eq_one h1
  have h2 := image_closure_subset_closure_image continuous_subtype_val (mem_image_of_mem _ hmem)
  refine closure_mono ?_ h2
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_boundaryStratum_iff_subDegIndex hA.1 ht a.2).2 ha

end Sheet

end MPolyfold

end Polyfold
