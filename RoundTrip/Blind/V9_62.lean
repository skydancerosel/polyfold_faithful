import Polyfold
/-! Blind formalization of V9_62 (the Springer 2021 book, Part II, §9.6, Proposition 9.6.5,
p. 456, and the formula on p. 457; new in the 2021 edition): approximating a top-bad point.

Text: at a top-bad `x`, for a class `Ξ` of top-dimensional indices with one tangent space there
are `i_1, …, i_p`, a partition (printed `I_k = I^1 ⊔ ⋯ ⊔ I^p`) and sequences of top-good points
with `x^e_j ∈ Mᵢ` iff `i ∈ I^e`; then `Θ_k(x) = ∑_Ξ ∑_e Θ_k(x^k_e)`.

Choices:
- Setting and notions as in my `RoundTrip/Blind/V9_59.lean`–`V9_61.lean` (prelude copied): the
  project's ep-groupoid `X`, `Θ` a branched ep⁺-subgroupoid, a project `LocalBranchingStructure`
  `B` at `x` with sheets of constant dimensions `dim i` (`IsDimLabelB`), `k = maxᵢ dim i`,
  top-good/top-bad points (`IsTopGoodB`, `IsTopBadB`, Definition 9.6.3, at the point `x` itself:
  `IsTopBadB B dim x`).
- `I_k = {i | dim i = k}` (`IkB`).  "A class of top-dimensional indices with one tangent space":
  a class of `I_k` under `T_xMᵢ = T_xMⱼ`, tangent spaces `T_xMᵢ` as in V9_2 (`TyMB`); `ClassesB`
  is the finite set of these classes.
- `Θ_k(y) = ∑_{dim Mᵢ = k, y ∈ Mᵢ} σᵢ` (`dimPartB`).  The printed `Θ_k(x^k_e)` is read as
  `Θ_k(x^e_j)` (index misprint), for every `j`.
- The data for a class: `p`, blocks `I^1, …, I^p` (`I : Fin p → Finset ι`), indices `i_e ∈ I^e`
  (the only role of `i_1, …, i_p` I can read from the statement), sequences `x^e_j` (`j : ℕ`) of
  top-good points, `x^e_j → x` (added: the sequences approximate `x`, which the statement
  presupposes), and `x^e_j ∈ Mᵢ ↔ i ∈ I^e` for every index `i` (all indices, as printed).
- **Misprint, formalized literally:** the partition is printed as a partition of `I_k`
  (`⋃_e I^e = I_k`, disjoint), not of `Ξ`.  Then for each class `∑_e Θ_k(x^e_j) = Θ_k(x)`, and
  the formula gives `♯(classes) · Θ_k(x)`; it fails whenever there are two classes, e.g. the
  trivial ep-groupoid on `ℝ²`, `Θ = 1_{L₁} + 1_{L₂}` for two lines through `x = 0` with different
  tangents (`Θ_1(0) = 2`, the right side is `4`).  So `B` as printed is false.  I also record
  `BIntended`, with the partition of `Ξ` (`⋃_e I^e = Ξ`), which I believe is the intended claim.
- `B` = existence of the data for every class ∧ the formula for every choice of data for all the
  classes, at every `j` (the formula is a computation valid for any such data).
-/
namespace RoundTrip.V9_62
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

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

/-- `I_k`, the top-dimensional indices. -/
noncomputable def IkB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) : Finset B.ι :=
  Finset.univ.filter (fun i => dim i = topDimB B dim)

/-- The classes of `I_k` under `T_xMᵢ = T_xMⱼ`. -/
noncomputable def ClassesB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) :
    Finset (Finset B.ι) :=
  (IkB B dim).image (fun i₀ =>
    (IkB B dim).filter (fun i => TyMB X.PObj (B.M i) x = TyMB X.PObj (B.M i₀) x))

/-- The data of Proposition 9.6.5 with the blocks partitioning `S` (`S = I_k` as printed,
`S = Ξ` as intended): disjoint blocks `I^e` with union `S`, `i_e ∈ I^e`, sequences of top-good
points `x^e_j → x` with `x^e_j ∈ Mᵢ ↔ i ∈ I^e`. -/
def IsSliceDataB (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (S : Finset B.ι) (p : ℕ)
    (I : Fin p → Finset B.ι) (ie : Fin p → B.ι) (xs : Fin p → ℕ → Obj) : Prop :=
  Pairwise (fun e e' => Disjoint (I e) (I e')) ∧ Finset.univ.biUnion I = S ∧
  (∀ e, ie e ∈ I e) ∧ (∀ e j, IsTopGoodB B dim (xs e j)) ∧
  (∀ e, Filter.Tendsto (xs e) Filter.atTop (nhds x)) ∧
  (∀ e j i, xs e j ∈ B.M i ↔ i ∈ I e)

end

/-- The claim with the blocks partitioning `S Ξ` for the class `Ξ`. -/
def BWith (S : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ),
    Finset B.ι → Finset B.ι) : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ), IsDimLabelB B dim →
      IsTopBadB B dim x →
      -- Proposition 9.6.5: the data exist for every class
      (∀ Ξ ∈ ClassesB B dim, ∃ (p : ℕ) (I : Fin p → Finset B.ι) (ie : Fin p → B.ι)
        (xs : Fin p → ℕ → Obj), IsSliceDataB B dim (S B dim Ξ) p I ie xs) ∧
      -- the formula on p. 457, for any data for all the classes
      (∀ (p : Finset B.ι → ℕ) (I : ∀ Ξ, Fin (p Ξ) → Finset B.ι) (ie : ∀ Ξ, Fin (p Ξ) → B.ι)
        (xs : ∀ Ξ, Fin (p Ξ) → ℕ → Obj),
        (∀ Ξ ∈ ClassesB B dim, IsSliceDataB B dim (S B dim Ξ) (p Ξ) (I Ξ) (ie Ξ) (xs Ξ)) →
        ∀ j : ℕ, dimPartB B dim (topDimB B dim) x =
          ∑ Ξ ∈ ClassesB B dim, ∑ e : Fin (p Ξ), dimPartB B dim (topDimB B dim) (xs Ξ e j))

/-- **Proposition 9.6.5 and the formula on p. 457, as printed** (blocks partitioning `I_k`;
false as printed, see the header). -/
def B : Prop := BWith (fun B dim _ => IkB B dim)

/-- The intended reading (blocks partitioning the class `Ξ`); not part of the claim `B`. -/
def BIntended : Prop := BWith (fun _ _ Ξ => Ξ)

end RoundTrip.V9_62
