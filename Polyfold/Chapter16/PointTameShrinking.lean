import Polyfold.Chapter16.PointCountEquivalence
import Polyfold.Chapter9.MathlibManifoldBridge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
**Definition 9.3.6** (p. 425) and **Definition 9.5.6** (p. 446) for dimension `n = 0`, as used
for Theorem 16.6.6 (p. 739) with Fredholm index `0`.  Numbers and pages are the 2021 text's.

# Tame structures of dimension `0` have point sheets

## The text, paraphrased

(Definition 9.3.6) A tame local branching structure at `x` has sheets `Mᵢ ∋ x` that are tame
finite-dimensional submanifolds; "in particular every `Mᵢ` is a manifold with boundary with
corners".  (Definition 9.5.6) Integration of `n`-forms is over tame oriented `Θ̂` of dimension
`n`.  For `n = 0` a sheet is a `0`-dimensional manifold, a discrete set, so after shrinking
`U(x)` every sheet is the point `{x}`.

## What is formalized

* `EpGroupoid.TameBranchingStructure.exists_isOpen_inter_subset_singleton`: a sheet of a tame
  local branching structure of dimension `0` meets some open `V ∋ x` only in `x` (the corner
  structure of dimension `0` of the sheet, `TameBranchingStructure.hasCornerStructureOfDim`, has
  charts with values in `ℝ⁰`, a point).
* **`EpGroupoid.OrientedTameStructure.exists_restrictRep_mem_pointSheets`**: every oriented
  tame structure of dimension `0` restricts to a smaller natural representation on which all
  sheets are `{x}` (point sheets), describing the same orientations.
* **`EpGroupoid.isPointTame_iff`**: `Θ̂` is tame of dimension `0` with point sheets
  (`IsPointTame`) iff it is tame of dimension `0` in the form of Chapter 9 (oriented tame
  structures of dimension `0` describing `T̂`).
* `PolyfoldClass.OrientedRep.isPointTame_iff_isTameOriented`,
  **`PolyfoldClass.OrientedSuborbifold.isPointTame_iff_isTameOriented`**: the same for the
  representatives and the oriented branched suborbifolds of a polyfold, so the counts
  `OrientedSuborbifold.pointIntegral`, `pointIntegralEff` are defined for every compact
  `θ̂` tame of dimension `0` in the sense of Chapter 16 (`IsTameOriented θ 0`):
  `OrientedSuborbifold.pointIntegralOfTame`, `pointIntegralEffOfTame`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- **A sheet of a tame local branching structure of dimension `0` is discrete at `x`**: some
open `V ∋ x` meets `Mᵢ` only in `x`.  The sheet carries a corner structure of dimension `0`
(Definition 9.3.6, last sentence), whose coordinate charts take values in `ℝ⁰`; a chart domain
around `x` is therefore `{x}`, open in `Mᵢ`. -/
theorem TameBranchingStructure.exists_isOpen_inter_subset_singleton
    (C : X.TameBranchingStructure Θ x) (hdim : C.toLocalBranchingStructure.IsOfDim 0)
    (i : C.ι) : ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ C.M i ∩ V ⊆ {x} := by
  let _ := X.PObj.paracompactSpace_subtype (C.M i)
  have h := C.hasCornerStructureOfDim hdim i
  have hx : x ∈ C.M i := C.mem_M i
  obtain ⟨κ, hκ⟩ := h.exists_cornerCoords ⟨x, hx⟩
  obtain ⟨V, hV, hVs⟩ := isOpen_induced_iff.1 κ.isOpen_s
  refine ⟨V, hV, ?_, ?_⟩
  · have h' : (⟨x, hx⟩ : C.M i) ∈ Subtype.val ⁻¹' V := by rw [hVs]; exact hκ
    exact h'
  · rintro y ⟨hyM, hyV⟩
    have hy : (⟨y, hyM⟩ : C.M i) ∈ κ.s := by
      rw [← hVs]; exact hyV
    have e : κ.coord ⟨y, hyM⟩ = κ.coord ⟨x, hx⟩ := Subsingleton.elim _ _
    have e' := congrArg κ.coordInv e
    rw [κ.coordInv_coord hy, κ.coordInv_coord hκ] at e'
    exact congrArg Subtype.val e'

namespace OrientedTameStructure

/-- **An oriented tame structure of dimension `0` restricts to one with point sheets**: on a
natural representation `R` with `R.U` inside `U(x)` and inside the open sets of
`TameBranchingStructure.exists_isOpen_inter_subset_singleton`, every sheet `Mᵢ ∩ R.U` is
`{x}` (and `x` is smooth, a point of a submanifold); the restriction describes every
orientation the original structure describes. -/
theorem exists_restrictRep_mem_pointSheets (C : X.OrientedTameStructure 0 Θ x) :
    ∃ C' : X.OrientedTameStructure 0 Θ x, (∀ i, C'.M i ∈ pointSheets X) ∧
      ∀ T : Obj → X.PObj.OrTangent →₀ ℚ, C.Represents T → C'.Represents T := by
  have hdim : C.toLocalBranchingStructure.IsOfDim 0 := C.isSubmanifoldOfDim
  choose V hV hxV hMV using fun i =>
    C.toTameBranchingStructure.exists_isOpen_inter_subset_singleton hdim i
  have : Fintype C.ι := C.fintype
  have hWo : IsOpen (⋂ i, V i) := isOpen_iInter_of_finite hV
  have hxW : x ∈ ⋂ i, V i := mem_iInter.2 hxV
  obtain ⟨R, hRW, -, -⟩ := X.exists_naturalRep_shrink C.rep hWo hxW
  have hRU : R.U ⊆ C.U := fun y hy => C.U_eq ▸ (hRW hy).2
  refine ⟨C.restrictRep R hRU, fun i => Or.inr ⟨x, ?_, ?_⟩,
    fun T hT => C.represents_restrictRep R hRU hT⟩
  · exact (C.isSubmanifoldOfDim i).1.subset_smoothSet (C.mem_M i)
  · change C.M i ∩ R.U = {x}
    refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 ⟨C.mem_M i, R.mem_U⟩)
    exact hMV i ⟨hy.1, mem_iInter.1 (hRW hy.2).1 i⟩

end OrientedTameStructure

/-- **Tame of dimension `0` with point sheets is tame of dimension `0`** (Definition 9.5.6 for
`n = 0`): `IsPointTame Θ T` iff at every point of `supp Θ` some oriented tame structure of
dimension `0` describes `T`. -/
theorem isPointTame_iff {T : Obj → X.PObj.OrTangent →₀ ℚ} :
    X.IsPointTame Θ T ↔
      ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure 0 Θ x, C.Represents T := by
  refine ⟨fun h x hx => (h x hx).imp fun _ hC => hC.2, fun h x hx => ?_⟩
  obtain ⟨C, hC⟩ := h x hx
  obtain ⟨C', hS, hR⟩ := C.exists_restrictRep_mem_pointSheets
  exact ⟨C', hS, hR T hC⟩

end EpGroupoid

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-- A representative is tame of dimension `0` with point sheets iff it is tame of dimension `0`
in the form of Chapter 16 (`OrientedRep.IsTameOriented a 0`). -/
theorem OrientedRep.isPointTame_iff_isTameOriented (a : OrientedRep c) :
    a.p.X.X.IsPointTame a.A.Θ a.A.T ↔ a.IsTameOriented 0 :=
  EpGroupoid.isPointTame_iff

namespace OrientedSuborbifold

/-- **`θ̂` is tame of dimension `0` with point sheets iff it is tame of dimension `0`**
(`IsTameOriented θ 0`, Definition 16.4.4 with Definition 9.5.6): the reading "point sheets" is
no restriction. -/
theorem isPointTame_iff_isTameOriented (θ : OrientedSuborbifold c) :
    θ.IsPointTame ↔ θ.IsTameOriented 0 :=
  ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, (a.isPointTame_iff_isTameOriented).1 h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, (a.isPointTame_iff_isTameOriented).2 h⟩⟩

/-- **The weighted signed count `∫_θ̂ τ`** of a `0`-form over a compact oriented branched
suborbifold tame of dimension `0` (2021 p. 732 for dimension `0`). -/
def pointIntegralOfTame (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented 0) (τ : ScForm c 0) : ℝ :=
  θ.pointIntegral hcpt ((isPointTame_iff_isTameOriented θ).2 htame) τ

/-- **The effective weighted count `∮_θ̂ τ`** over a compact `θ̂` tame of dimension `0`. -/
def pointIntegralEffOfTame (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented 0) (τ : ScForm c 0) : ℝ :=
  θ.pointIntegralEff hcpt ((isPointTame_iff_isTameOriented θ).2 htame) τ

/-- `∫_θ̂ τ` is computed on every representative. -/
theorem pointIntegralOfTame_eq (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented 0) (τ : ScForm c 0) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.pointIntegralOfTame hcpt htame τ = a.pointIntegral (isCompactBranched_of_mk hcpt a ha)
      ((a.isPointTame_iff_isTameOriented).2 ((isTameOriented_iff θ).1 htame a ha)) τ :=
  θ.pointIntegral_eq hcpt _ τ a ha

/-- `∮_θ̂ τ` is computed on every representative. -/
theorem pointIntegralEffOfTame_eq (θ : OrientedSuborbifold c) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented 0) (τ : ScForm c 0) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.pointIntegralEffOfTame hcpt htame τ =
      a.pointIntegralEff (isCompactBranched_of_mk hcpt a ha)
        ((a.isPointTame_iff_isTameOriented).2 ((isTameOriented_iff θ).1 htame a ha)) τ :=
  θ.pointIntegralEff_eq hcpt _ τ a ha

end OrientedSuborbifold

end PolyfoldClass

end Polyfold
