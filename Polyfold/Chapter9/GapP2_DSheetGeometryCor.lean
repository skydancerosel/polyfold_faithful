import Polyfold.Chapter9.GapP2_DSheetMeasure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Lemma 9.4.8, p. 432, Proposition 9.4.9, p. 434, Proposition 9.4.10, p. 435 (2017: Lemma
9.15, Propositions 9.5, 9.6), for an `n`-dimensional branched ep⁺-subgroupoid of an arbitrary
ep-groupoid.

# §9.4 without a sheet-geometry hypothesis

`lemma_9_4_8`, `proposition_9_4_9` and `proposition_9_4_10` (`Chapter9/BranchingGeometry.lean`)
are stated for a `SheetGeometry` on a class containing the sheets.  For an `n`-dimensional `Θ`
the sheets of every local branching structure are `n`-dimensional submanifolds
(`LocalBranchingStructure.isOfDim_of_isNDimensional`), and these carry the sheet geometry
`MPolyfold.sheetGeometry n` (essential points and measure zero read in M-polyfold charts; Lemmas
9.4.4 and 9.4.6 are theorems).  The statements below are the three results for this geometry,
with no hypothesis beyond the text's; the independence of the tangent sums in Proposition 9.4.9
is a theorem (`hasIndependentTangentSums`).
-/

set_option maxSynthPendingDepth 3

open Set

universe u

namespace Polyfold

namespace EpGroupoid

open MPolyfold OrientedBranchingStructure

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- **Lemma 9.4.8, 2021 p. 432 (2017: Lemma 9.15)**, for a local branching structure of an
`n`-dimensional `Θ`: the points of `M_U` with at least two `y`-equivalence classes form a set of
measure zero in every sheet. -/
theorem lemma_9_4_8_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.LocalBranchingStructure Θ x) :
    (X.PObj.sheetGeometry n).IsNullIn B.M
      {y | y ∈ ⋃ i, B.M i ∧ 2 ≤ (X.PObj.sheetGeometry n).numClasses B.M y} :=
  (X.PObj.sheetGeometry n).lemma_9_4_8 B.M fun i => B.isOfDim_of_isNDimensional hΘ i

open scoped Classical in
/-- **Proposition 9.4.9, 2021 p. 434 (2017: Proposition 9.5)**, for an oriented local branching
structure with Property (T) of an `n`-dimensional `Θ` on an arbitrary ep-groupoid, with the sheet
geometry of the `n`-dimensional submanifolds (`MPolyfold.sheetGeometry n`): the statement of
`proposition_9_4_9` with no hypothesis beyond the text's. -/
theorem proposition_9_4_9_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.OrientedBranchingStructure Θ x) (hT : B.PropertyT B.U) :
    (X.PObj.sheetGeometry n).IsNullIn B.M (B.MU \ (X.PObj.sheetGeometry n).MStar B.M) ∧
    (X.PObj.sheetGeometry n).MStar B.M = ⋃ J, (X.PObj.sheetGeometry n).MStarPart B.M J ∧
    Pairwise (Function.onFun Disjoint ((X.PObj.sheetGeometry n).MStarPart B.M)) ∧
    ∀ J : Finset B.ι, ∃ AJ ⊆ J, ∀ y ∈ (X.PObj.sheetGeometry n).MStarPart B.M J,
      Θ y = ∑ i ∈ J, B.σ i ∧
      (∀ i ∈ J, X.tangentValue Θ y =
        Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (∑ j ∈ J, B.σ j)) ∧
      ∃ ga gb : X.PObj.OrTangent, X.PObj.IsOrientedAt y ga ∧ X.PObj.IsOrientedAt y gb ∧
        ga ≠ gb ∧ (∀ i ∈ J, ga.carrier = X.PObj.submanifoldTangent (B.M i) y ∧
          gb.carrier = X.PObj.submanifoldTangent (B.M i) y) ∧
        (∀ i ∈ AJ, (B.orient i).tangent y = ga) ∧ (∀ i ∈ J \ AJ, (B.orient i).tangent y = gb) ∧
        B.orientedSum y =
          Finsupp.single ga (∑ i ∈ AJ, B.σ i) + Finsupp.single gb (∑ i ∈ J \ AJ, B.σ i) ∧
        (∑ i ∈ AJ, B.σ i) + (∑ i ∈ J \ AJ, B.σ i) = ∑ i ∈ J, B.σ i :=
  proposition_9_4_9 (X.PObj.sheetGeometry n) B
    (fun i => B.toLocalBranchingStructure.isOfDim_of_isNDimensional hΘ i)
    (hasIndependentTangentSums Θ) hT

open scoped Classical in
/-- **Proposition 9.4.10, 2021 p. 435 (2017: Proposition 9.6)**, for two oriented local branching
structures of `n`-dimensional `Θ`, `Θ'` on the same `U(x)` with (a) the same weights and (b) the
same oriented sums, with the sheet geometry of the `n`-dimensional submanifolds: the statement of
`proposition_9_4_10` with no sheet-geometry hypothesis. -/
theorem proposition_9_4_10_of_isNDimensional {n : ℕ} {Θ' : Obj → ℚ}
    (hΘ : X.IsNDimensional Θ n) (hΘ' : X.IsNDimensional Θ' n)
    (B : X.OrientedBranchingStructure Θ x) (B' : X.OrientedBranchingStructure Θ' x)
    (hU : B.U = B'.U)
    (ha : ∀ y ∈ B.U, ∑ i with y ∈ B.M i, B.σ i = ∑ i with y ∈ B'.M i, B'.σ i)
    (hb : ∀ y ∈ B.U, B.orientedSum y = B'.orientedSum y) :
    B.MU = B'.MU ∧ ∃ (MUd : Set Obj) (ℓ : ℕ) (A : Fin ℓ → Set Obj), MUd ⊆ B.MU ∧
      (X.PObj.sheetGeometry n).IsNullIn B.M (B.MU \ MUd) ∧
      (X.PObj.sheetGeometry n).IsNullIn B'.M (B.MU \ MUd) ∧
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ p, A p) = MUd ∧
      ∀ p, ∃ (J : Finset B.ι) (J' : Finset B'.ι) (Jp : Finset B.ι) (Jp' : Finset B'.ι),
        Jp ⊆ J ∧ Jp' ⊆ J' ∧ ∀ y ∈ A p,
          Finset.univ.filter (fun i => y ∈ B.M i) = J ∧
          Finset.univ.filter (fun i => y ∈ B'.M i) = J' ∧
          (∀ i ∈ J, ∀ j ∈ J,
            X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B.M j) y) ∧
          (∀ i ∈ J, ∀ i' ∈ J',
            X.PObj.submanifoldTangent (B.M i) y = X.PObj.submanifoldTangent (B'.M i') y) ∧
          (∀ i' ∈ J', ∀ j' ∈ J',
            X.PObj.submanifoldTangent (B'.M i') y = X.PObj.submanifoldTangent (B'.M j') y) ∧
          ∑ i ∈ J, B.σ i = ∑ i ∈ J', B'.σ i ∧
          (∀ i ∈ J, ∀ j ∈ J, (i ∈ Jp ↔ j ∈ Jp) →
            (B.orient i).tangent y = (B.orient j).tangent y) ∧
          (∀ i ∈ J, ∀ i' ∈ J', (i ∈ Jp ↔ i' ∈ Jp') →
            (B.orient i).tangent y = (B'.orient i').tangent y) ∧
          (∀ i' ∈ J', ∀ j' ∈ J', (i' ∈ Jp' ↔ j' ∈ Jp') →
            (B'.orient i').tangent y = (B'.orient j').tangent y) ∧
          (∀ i ∈ Jp, ∀ i' ∈ Jp', Finsupp.single ((B.orient i).tangent y) (∑ j ∈ Jp, B.σ j) =
            Finsupp.single ((B'.orient i').tangent y) (∑ j ∈ Jp', B'.σ j)) ∧
          (∀ i ∈ J \ Jp, ∀ i' ∈ J' \ Jp',
            Finsupp.single ((B.orient i).tangent y) (∑ j ∈ J \ Jp, B.σ j) =
              Finsupp.single ((B'.orient i').tangent y) (∑ j ∈ J' \ Jp', B'.σ j)) :=
  proposition_9_4_10 (X.PObj.sheetGeometry n) B B'
    (fun i => B.toLocalBranchingStructure.isOfDim_of_isNDimensional hΘ i)
    (fun i => B'.toLocalBranchingStructure.isOfDim_of_isNDimensional hΘ' i) hU ha hb

end EpGroupoid

end Polyfold
