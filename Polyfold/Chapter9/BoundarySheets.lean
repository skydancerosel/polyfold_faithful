import Polyfold.Chapter9.BoundaryOrientation
import Polyfold.Chapter9.IntegralCovering

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, Definition 9.3.10, p. 427, and §9.5, Theorem 9.5.15, p. 448 (2017: Theorem 9.4).

# The boundary sheets of an oriented tame branching structure

For an oriented tame local branching structure `C` of dimension `m + 1` (sheets `Mᵢ`, weights
`σᵢ`, orientations `oᵢ`), the local expression of the boundary measure of Theorem 9.5.15
integrates over the `∂Mᵢ` with the orientations `o_{∂Mᵢ}`.

## What is formalized

* `OrientedTameStructure.boundarySheet C i = {d_{Mᵢ} = 1}`, an `m`-dimensional submanifold
  (`isSubmanifoldOfDim_boundarySheet`), with the orientation `C.boundaryOrient i = o_{∂Mᵢ}` of
  Definition 9.3.8 (`boundaryOrient_tangent`).
* **`OrientedTameStructure.boundaryOrientation_eq_sum`**: if `C` describes `T̂_Θ = T`, then
  `T̂_{∂Θ}(y) = ∑_{y ∈ ∂₁Mᵢ} σᵢ T_y(∂₁Mᵢ, o_{∂Mᵢ})` ((9.12)), with the oriented tangent spaces of
  the boundary sheets as submanifolds; the left side depends on `T` only, so the oriented
  weighted family of the boundary sheets is the same for all structures describing `T`.
* `OrientedTameStructure.exists_boundarySheet_mem_sheets`: near each of its points a boundary
  sheet lies in the class of sheets of the concrete integration of `m`-forms
  (`FormEval.sheets`), so `∫_K ω|(∂Mᵢ, o_{∂Mᵢ})` is defined for measurable `K` in such a piece.

Not formalized: the local expressions as signed measures on `(∂S, L(∂S))` and their agreement on
overlaps (Theorems 9.5.15, 9.5.16).  (2026-11-13) They are in the `GapP2_E7_*` files
(`existsUnique_familyMeasure`, `theorem_9_5_15_msheets`).
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {m : ℕ} {x : Obj}

namespace OrientedTameStructure

variable (C : X.OrientedTameStructure (m + 1) Θ x)

/-- **The boundary sheet `∂₁Mᵢ = {d_{Mᵢ} = 1}`** of the sheet `Mᵢ`. -/
def boundarySheet (i : C.ι) : Set Obj := X.PObj.boundaryStratum (C.M i)

theorem boundarySheet_subset (i : C.ι) : C.boundarySheet i ⊆ C.M i := fun _ h => h.1

/-- The boundary sheets are `m`-dimensional submanifolds. -/
theorem isSubmanifoldOfDim_boundarySheet (i : C.ι) :
    X.PObj.IsSubmanifoldOfDim (C.boundarySheet i) m :=
  isSubmanifoldOfDim_boundaryStratum (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i)

/-- **The boundary orientation `o_{∂Mᵢ}`** of the boundary sheet (Definition 9.3.8). -/
def boundaryOrient (i : C.ι) : X.PObj.SubmanifoldOrientation (C.boundarySheet i) m :=
  (C.orient i).stratumOrientation (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i)

theorem boundaryOrient_tangent (i : C.ι) {y : Obj} (hy : y ∈ C.boundarySheet i) :
    (C.boundaryOrient i).tangent y = X.PObj.boundaryOp ((C.orient i).tangent y) :=
  (C.orient i).stratumOrientation_tangent (C.isSubmanifoldOfDim i)
    (C.hasTameInducedStructure i) hy

open scoped Classical in
/-- **(9.12), Definition 9.3.10 (2021 p. 427), for the boundary sheets as oriented
submanifolds**: if `C` describes `T̂_Θ = T` on `U(x)`, then at a smooth `y ∈ U(x)`
`T̂_{∂Θ}(y) = ∑_{y ∈ ∂₁Mᵢ} σᵢ · T_y(∂₁Mᵢ, o_{∂Mᵢ})`.  The left side is a function of `T(y)`. -/
theorem boundaryOrientation_eq_sum {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : C.Represents T)
    {y : Obj} (hyU : y ∈ C.U) (hys : y ∈ X.PObj.smoothSet) :
    X.boundaryOrientation T y =
      ∑ i with y ∈ C.boundarySheet i,
        Finsupp.single ((C.boundaryOrient i).tangent y) (C.σ i) := by
  have hf : (Finset.univ.filter fun i : C.toOriented.ι => y ∈ C.toOriented.M i ∧
      X.PObj.HasReducedCodim y 1 ((C.toOriented.orient i).tangent y)) =
      Finset.univ.filter fun i : C.toOriented.ι => y ∈ C.boundarySheet i := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · rintro ⟨hy, h⟩
      exact ((C.orient i).hasReducedCodim_iff_mem_boundaryStratum hy).1 h
    · intro h
      exact ⟨h.1, ((C.orient i).hasReducedCodim_iff_mem_boundaryStratum h.1).2 h⟩
  have h1 := reducedCodimPart_orientedSum C.toOriented y 1
  rw [boundaryOrientation, hT y hyU hys, h1]
  refine (Finsupp.mapDomain_finsetSum (f := X.PObj.boundaryOp) (s := Finset.univ.filter
    fun i : C.toOriented.ι => y ∈ C.toOriented.M i ∧
      X.PObj.HasReducedCodim y 1 ((C.toOriented.orient i).tangent y))
    (v := fun i => Finsupp.single ((C.toOriented.orient i).tangent y)
      (C.toOriented.σ i))).trans ?_
  refine Finset.sum_congr hf fun i hi => ?_
  rw [Finsupp.mapDomain_single]
  exact congrArg (fun g => Finsupp.single g (C.σ i))
    (C.boundaryOrient_tangent i (Finset.mem_filter.1 hi).2).symm

/-- **The boundary sheets are locally in the class of the concrete integration**: every point of
`∂₁Mᵢ` has a neighbourhood `V` with `∂₁Mᵢ ∩ V ∈ F.sheets` (one graph chart, forms absolutely
integrable), for the values `F` of a space of `m`-forms. -/
theorem exists_boundarySheet_mem_sheets {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (F : X.FormEval m Ω) (i : C.ι) {y : Obj} (hy : y ∈ C.boundarySheet i) :
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ C.boundarySheet i ∩ V ∈ F.sheets :=
  F.exists_mem_sheets (C.isSubmanifoldOfDim_boundarySheet i) hy

end OrientedTameStructure

end EpGroupoid

end Polyfold
