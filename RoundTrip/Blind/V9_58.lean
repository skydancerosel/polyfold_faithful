import Polyfold
/-! Blind formalization of V9_58 (the Springer 2021 book, Part II, §9.6, Lemma 9.6.1, p. 453,
new in the 2021 edition, and `dim_Θ`, p. 454): the top dimension.

Text: two local branching structures at `x` have the same top dimension, by a measure zero
argument; this defines `dim_Θ(x)`.

Choices:
- Setting (§9.6.1, the proof of Proposition 9.1.12): `Obj Mor : Type` (universe 0), the
  project's ep-groupoid `X`, `Θ` a branched ep⁺-subgroupoid (project's
  `IsBranchedEpSubgroupoid`, compared in `RoundTrip/Blind/V9_1.lean`), `x ∈ supp Θ`, local
  branching structures the project's `LocalBranchingStructure Θ x` (arbitrary domains).  No
  dimension hypothesis on `Θ` (the point of §9.6.1 is that the sheets may have several dimensions).
- "dimension of `Mᵢ`": the dimension of `T_xMᵢ`, my `HasDimB` (copied from
  `RoundTrip/Blind/V9_2.lean`: `T_xMᵢ` read in a chart is an `n`-dimensional subspace), at the
  point `x` that every sheet passes through.  "The top dimension of `B` is `k`" (`IsTopDimAtB`):
  some sheet has dimension `k` at `x` and none has a larger one.
- B: (a) every structure at `x` has a top dimension (presupposed by "the top dimension");
  (b) Lemma 9.6.1: two structures at `x` have the same one; (c) "this defines `dim_Θ(x)`": the
  project's `X.localTopDim Θ x` (`WithBot ℕ`) is this number at every `x ∈ supp Θ`.  Off the
  support no claim is made.
- The measure zero argument is the proof, not part of B.  The prelude also contains the labelled
  notions of my V9_59–V9_62 (unused here).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_58
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

/-- The top dimension of the local branching structure `B` at `x` is `k`: `maxᵢ dim T_xMᵢ = k`. -/
def IsTopDimAtB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (k : ℕ) : Prop :=
  (∃ i, HasDimB X.PObj (B.M i) x k) ∧ ∀ i j, HasDimB X.PObj (B.M i) x j → j ≤ k

/-- **Lemma 9.6.1 and `dim_Θ`**: at `x ∈ supp Θ` every local branching structure has a top
dimension, two of them have the same one, and it is the project's `dim_Θ(x)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ x ∈ EpGroupoid.supp Θ,
      -- (a) a top dimension exists
      (∀ B : X.LocalBranchingStructure Θ x, ∃ k, IsTopDimAtB B k) ∧
      -- (b) Lemma 9.6.1
      (∀ (B B' : X.LocalBranchingStructure Θ x) (k k' : ℕ),
        IsTopDimAtB B k → IsTopDimAtB B' k' → k = k') ∧
      -- (c) `dim_Θ(x)`
      (∀ (B : X.LocalBranchingStructure Θ x) (k : ℕ), IsTopDimAtB B k →
        X.localTopDim Θ x = (k : WithBot ℕ))

end RoundTrip.V9_58
