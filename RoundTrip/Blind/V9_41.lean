import Polyfold
/-! Blind formalization of V9_41 (the 2021 book's Part II, §9.4, Property (T) and Lemma 9.4.3,
p. 430; 2017 p. 316).

Text: (T): if `y₀ ∈ Mᵢ ∩ Mᵢ'`, `T_{y₀}Mᵢ = T_{y₀}Mᵢ'` and `o_{i,y₀} = ε o_{i',y₀}`, then
`T_y(Mᵢ, oᵢ) = T_y(Mᵢ', ε oᵢ')` for all `y ∈ Mᵢ ∩ Mᵢ'` with `T_yMᵢ = T_yMᵢ'`.  Lemma 9.4.3: (T)
holds after restricting to a smaller `U'(x)`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor`.  Unlike my V9_42, V9_44–V9_48, this item needs
  neither essential points nor null sets, so the project's vocabulary for oriented local branching
  structures expresses it: `OrientedBranchingStructure` (read with `#print`: a local branching
  structure `(Mᵢ)`, `(σᵢ)` on `U(x)` with dimensions `dᵢ` and orientations
  `oᵢ : SubmanifoldOrientation (Mᵢ) dᵢ`), `T_yMᵢ` = `submanifoldTangent (Mᵢ) y`, and the oriented
  tangent space `T_y(Mᵢ, oᵢ)` = `(oᵢ).tangent y` (an `OrTangent`: dimension, carrier, positive
  frames).
- `ε = ±1`.  `TX` carries no linear structure in the project, so `-o` (the opposite orientation)
  cannot be written; I use that `T_{y₀}Mᵢ = T_{y₀}Mᵢ'` has exactly two orientations: for `ε = 1`
  the condition reads "`T_{y₀}(Mᵢ, oᵢ) = T_{y₀}(Mᵢ', oᵢ')` implies `T_y(Mᵢ, oᵢ) = T_y(Mᵢ', oᵢ')`",
  for `ε = -1` "the two differ at `y₀` implies they differ at `y`" (`PropTB`, two conjuncts).
  "(T) on `V`": `y₀`, `y` range over `V ∩ Mᵢ ∩ Mᵢ'` (restriction of the structure to `V`).
- B is the conjunction of (a) the project's `PropertyT` is my `PropTB` (this item introduces the
  notion), (b) Lemma 9.4.3: for every oriented local branching structure at `x ∈ supp(Θ)` there is
  an open `U'(x)` with `x ∈ U'(x) ⊆ U(x)` on which (T) holds.
- Hypotheses of (b) (the standing assumptions of §9.4, all harmless): `Θ` a branched
  ep⁺-subgroupoid (`IsBranchedEpSubgroupoid`), tame (`IsTameBranched`), orientable
  (`IsOrientable`) and `n`-dimensional (`IsNDimensional`); the structure has `n`-dimensional sheets
  with tame induced structure (`HasTameInducedStructure`).  The structure is not required to
  represent a particular orientation `T̂Θ` (the lemma concerns the structure only).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_41
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Property (T)** on `V` for an oriented local branching structure, with the two cases
`ε = 1`, `ε = -1`. -/
def PropTB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.OrientedBranchingStructure Θ x) (V : Set Obj) : Prop :=
  ∀ i i' : B.ι, ∀ y₀ ∈ V ∩ (B.M i ∩ B.M i'), ∀ y ∈ V ∩ (B.M i ∩ B.M i'),
    X.PObj.submanifoldTangent (B.M i) y₀ = X.PObj.submanifoldTangent (B.M i') y₀ →
    X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B.M i') y →
      -- `ε = 1`
      ((B.orient i).tangent y₀ = (B.orient i').tangent y₀ →
        (B.orient i).tangent y = (B.orient i').tangent y) ∧
      -- `ε = -1`: `o_{i,y₀} = -o_{i',y₀}` means the two orientations of one space differ
      ((B.orient i).tangent y₀ ≠ (B.orient i').tangent y₀ →
        (B.orient i).tangent y ≠ (B.orient i').tangent y)

end

/-- Property (T) is the project's `PropertyT`, and Lemma 9.4.3: (T) holds on a smaller
neighbourhood `U'(x)`. -/
def B : Prop :=
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (x : Obj) (B : X.OrientedBranchingStructure Θ x) (V : Set Obj),
    B.PropertyT V ↔ PropTB B V) ∧
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (n : ℕ),
    X.IsBranchedEpSubgroupoid Θ → X.IsTameBranched Θ → X.IsOrientable Θ →
    X.IsNDimensional Θ n →
    ∀ x ∈ EpGroupoid.supp Θ, ∀ B : X.OrientedBranchingStructure Θ x,
      (∀ i, B.dim i = n) → (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      ∃ U' : Set Obj, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ B.U ∧ PropTB B U')

end RoundTrip.V9_41
