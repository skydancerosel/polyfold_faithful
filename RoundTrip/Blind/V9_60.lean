import Polyfold
/-! Blind formalization of V9_60 (the Springer 2021 book, Part II, §9.6, Definition 9.6.3,
p. 455; new in the 2021 edition): top-good and top-bad points.

Text: `y ∈ M^k_U` is top-good if near `y` the top-dimensional `Mᵢ` through `y` coincide,
top-bad otherwise.

Choices:
- Setting as in my `RoundTrip/Blind/V9_59.lean` (prelude copied): the project's ep-groupoid `X`,
  `Θ` a branched ep⁺-subgroupoid, a project `LocalBranchingStructure` `B` at `x` with sheets of
  constant dimensions `dim i` (`IsDimLabelB`), `k = maxᵢ dim i`, `M^k_U = ⋃_{dim i = k} Mᵢ`.
- "near `y` the top-dimensional `Mᵢ` through `y` coincide": some open `V ∋ y` has
  `V ∩ Mᵢ = V ∩ Mⱼ` for all `i, j` with `dim i = dim j = k` and `y ∈ Mᵢ ∩ Mⱼ` (`TopCoincideB`;
  `V` need not lie in `U`, the sheets do).  Top-good: `y ∈ M^k_U` and this holds; top-bad:
  `y ∈ M^k_U` and it fails.
- The item is a definition: B says that the project's `IsTopGoodPoint`, `IsTopBadPoint` are my
  notions at every `y ∈ M^k_U`, where the text defines them (off `M^k_U` the text defines
  nothing, so no comparison is made there).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_60
open Polyfold
open Classical

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `T_yX`: the tangent vectors over `y` (copied from `RoundTrip/Blind/V9_2.lean`). -/
def TxXB (P : MPolyfold Z) (y : Z) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) = y}

/-- `T_yM = Tr(y)(T_yX)` for the sc⁺-retractions `r` of the data of Definition 4.13 of `M` at
`y` (copied from `RoundTrip/Blind/V9_2.lean`). -/
def TyMB (P : MPolyfold Z) (M : Set Z) (y : Z) : Set P.TangentSpace :=
  {α | ∃ d : P.SubmanifoldData M, y ∈ d.V ∧ ∃ β ∈ TxXB P y, d.tmap β = α}

/-- The chart image of a set of tangent vectors (copied from `RoundTrip/Blind/V9_2.lean`). -/
def chartImgB {P : MPolyfold Z} {φ : MChart Z} (hφ : P.IsChart φ) (S : Set P.TangentSpace) :
    Set (φ.model.E.lvl 0) :=
  (fun α => (MPolyfold.tangentChartMap hφ α).2) '' S

/-- Remark 9.1.1: `M` has dimension `n` at `y` (copied from `RoundTrip/Blind/V9_2.lean`). -/
def HasDimB (P : MPolyfold Z) (M : Set Z) (y : Z) (n : ℕ) : Prop :=
  ∃ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source ∧
    ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
      chartImgB hφ (TyMB P M y) = (S : Set (φ.model.E.lvl 0)) ∧ Module.finrank ℝ S = n

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

/-- `dim` labels the sheets of `B` by their dimensions: `Mᵢ` has dimension `dim i` at each of
its points (the text's "`dim Mᵢ`", sheets of constant dimension). -/
def IsDimLabelB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) : Prop :=
  ∀ i, ∀ m ∈ B.M i, HasDimB X.PObj (B.M i) m (dim i)

/-- The top dimension `k = maxᵢ dim Mᵢ`. -/
def topDimB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) : ℕ :=
  Finset.univ.sup dim

/-- `M^k_U`, the union of the `Mᵢ` of dimension `k`. -/
def MkB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (k : ℕ) : Set Obj :=
  ⋃ i, ⋃ (_ : dim i = k), B.M i

/-- `Θ_k(y) = ∑_{dim Mᵢ = k, y ∈ Mᵢ} σᵢ`, the `k`-dimensional part (as in the proof of
Proposition 9.1.11). -/
noncomputable def dimPartB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (k : ℕ) (y : Obj) : ℚ :=
  ∑ i with dim i = k ∧ y ∈ B.M i, B.σ i

/-- Near `y` the top-dimensional `Mᵢ` through `y` coincide. -/
def TopCoincideB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (y : Obj) : Prop :=
  ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ ∀ i j, dim i = topDimB B dim → dim j = topDimB B dim →
    y ∈ B.M i → y ∈ B.M j → V ∩ B.M i = V ∩ B.M j

/-- **Definition 9.6.3**: `y ∈ M^k_U` is top-good. -/
def IsTopGoodB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (y : Obj) : Prop :=
  y ∈ MkB B dim (topDimB B dim) ∧ TopCoincideB B dim y

/-- **Definition 9.6.3**: `y ∈ M^k_U` is top-bad. -/
def IsTopBadB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (y : Obj) : Prop :=
  y ∈ MkB B dim (topDimB B dim) ∧ ¬ TopCoincideB B dim y

end

/-- **Definition 9.6.3**: the project's top-good and top-bad points are the text's, on
`M^k_U`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ), IsDimLabelB B dim →
      ∀ y ∈ MkB B dim (topDimB B dim),
        (B.IsTopGoodPoint dim y ↔ IsTopGoodB B dim y) ∧
        (B.IsTopBadPoint dim y ↔ IsTopBadB B dim y)

end RoundTrip.V9_60
