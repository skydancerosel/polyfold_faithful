import Polyfold
/-! Blind formalization of V9_49 (the 2021 book's Part II, §9.5, Definition 9.5.1, p. 437;
2017: Definition 9.15, p. 322): sets of measure zero in `S = |supp(Θ)|`.

Text: for an oriented, tame, compact `n`-dimensional `Θ` and `S = |supp(Θ)|`: `A ⊆ S` has measure
zero if for every `x ∈ supp(Θ)` and a choice of local branching structure on a suitable `U(x)` the
preimages `Aᵢ ⊆ Mᵢ` of `A ∩ |M_U|` have measure zero in the sense of Definition 9.4.5.

Choices:
- This item is a definition.  B says that the project's `IsMeasureZeroSupp` is my
  `IsMeasureZeroB`, for every `Θ` as in the text and every `A ⊆ |supp(Θ)|`.
- Setting: `Obj Mor : Type` (universe 0) with the instances of the project's `EpGroupoid`,
  `X : EpGroupoid Obj Mor`, `|X|` = `X.OrbitSpace`, `π` = `X.π`.  "Oriented, tame, compact,
  `n`-dimensional": `IsBranchedEpSubgroupoid`, `IsOrientable`, `IsTameBranched`,
  `IsCompactBranched`, `IsNDimensional Θ n` (hypotheses of B; the definition is only made for such
  `Θ`).  `S = |supp(Θ)|` = `X.orbitSupp Θ`; `A ⊆ S`.
- "for every `x ∈ supp(Θ)` and a choice of local branching structure": for every `x` there is
  (a choice of) one; "on a suitable `U(x)`": a tame local branching structure in the project's
  sense (`TameBranchingStructure`, read with `#print`: `U(x)` the domain of the natural
  `G_x`-action, with the properness property, the sheets with tame induced structure), the
  setting in which §9.4 works.  I did not take "every choice" (the text speaks of a choice).
- "The preimages `Aᵢ ⊆ Mᵢ` of `A ∩ |M_U|` under the canonical maps `Mᵢ → |M_U|`":
  `{y ∈ Mᵢ | π(y) ∈ A ∩ π(M_U)}`.
- "Measure zero in the sense of Definition 9.4.5" (Lebesgue measure zero in every smooth chart of
  the sheet `Mᵢ`): the project has no smooth charts on sheets of an ep-groupoid, so I take it as a
  parameter: an arbitrary system `G` of null sets on a class `𝒮` of sheets (the project's
  `SheetNullSets 𝒮`, `G.IsNull N C` = "`C ∩ N` has measure zero in `N`"), and require the sheets of
  the chosen structure to lie in `𝒮` (outside `𝒮` the system says nothing).  So B checks the
  logical form of the definition only; whether `G` is the text's notion is not checked here (my
  V9_43 checks the notion on a manifold).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_49
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 9.5.1**: `A ⊆ |supp(Θ)|` has measure zero if at every `x ∈ supp(Θ)` some tame
local branching structure (sheets in the class `𝒮`) has the preimages
`Aᵢ = {y ∈ Mᵢ | π(y) ∈ A ∩ |M_U|}` of measure zero in `Mᵢ`. -/
def IsMeasureZeroB (X : EpGroupoid Obj Mor) {𝒮 : Set (Set Obj)} (G : SheetNullSets 𝒮)
    (Θ : Obj → ℚ) (A : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ EpGroupoid.supp Θ, ∃ B : X.TameBranchingStructure Θ x,
    (∀ i, B.M i ∈ 𝒮) ∧
      ∀ i, G.IsNull (B.M i) {y | y ∈ B.M i ∧ X.π y ∈ A ∩ X.π '' B.MU}

end

/-- Definition 9.5.1: the project's measure-zero subsets of `|supp(Θ)|` are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (𝒮 : Set (Set Obj)) (G : SheetNullSets 𝒮) (Θ : Obj → ℚ) (n : ℕ),
    X.IsBranchedEpSubgroupoid Θ → X.IsOrientable Θ → X.IsTameBranched Θ →
    X.IsCompactBranched Θ → X.IsNDimensional Θ n →
    ∀ A : Set X.OrbitSpace, A ⊆ X.orbitSupp Θ →
      (X.IsMeasureZeroSupp G Θ A ↔ IsMeasureZeroB X G Θ A)

end RoundTrip.V9_49
