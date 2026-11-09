import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_26

/-! Round trip for V9_26 (Proposition 9.2.15, p. 420 of the 2021 book; 2017: Proposition 9.4,
p. 308: the boundary weights `∑_{y ∈ ∂Mᵢ} σᵢ`).

The item lists the definitions `submanifoldBoundary`, `boundaryPart`, `boundaryTheta`
(vocabulary) and seven theorems.  `A` is the conjunction of their types, universes at `0`:
`MPolyfold.mem_submanifoldBoundary_iff` (`y ∈ ∂M ⟺ y ∈ M, y ∈ ∂X, T_yM ⊄ T_y^R X`),
`boundaryTheta_eq` (the local formula `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` for every structure),
`proposition_9_2_15_1`, `proposition_9_2_15_2`, `isFunctorial_boundaryTheta`,
`proposition_9_2_15_3` and `filter_tangentValue_eq`.  Every one of them except
`mem_submanifoldBoundary_iff` and `proposition_9_2_15_2` takes the hypothesis
`hind : X.HasIndependentTangentSums Θ` (Theorem 9.2.1's independence of `∑ σᵢ T_xMᵢ` from the
local branching structure), which the project proves only in special cases (good points, `ℝⁿ`,
the equidimensional case with tangent slices, or from Proposition 9.1.12, which is stated but not
proved).

* `A → B` is **not proved**: `B` (1) and (3) are claimed for every branched ep⁺-subgroupoid,
  without `hind`, and `A` gives them only under `hind`.  `B` (2) needs no `hind`
  (`proposition_9_2_15_2`).  With `hind` added to `B`'s hypotheses the implication holds:
  `A_to_BInd` (with `F = ∂Θ` for (3); `F = 0` where `Θ = 0` by the non-item
  `boundaryTheta_eq_zero_of_not_mem_supp`).  `hind` is satisfiable (indicators, `Θ = 1` on
  `[0, ∞)`, every `Θ` on `ℝⁿ`) and is the content of the text's Theorem 9.2.1, so the gap is
  the unproved Theorem 9.2.1 in general, not a difference of reading.
* `B → A` is proved.  Functoriality of `∂Θ` (in `isFunctorial_boundaryTheta` and
  `proposition_9_2_15_3`), its nonnegativity and `supp ∂Θ ⊆ ∂X` come from `B` (3): `B`'s `F`
  agrees with the local sums on every structure at a point of `supp Θ` and vanishes off
  `supp Θ`, so `F = ∂Θ` (by the local formula, re-proved).  The other conjuncts are stated for
  arbitrary `Θ` (not necessarily branched) and every `x`, which `B` does not cover; they are
  re-proved outright as copies of the project's proofs with the banned lemmas replaced by local
  copies (`mem_submanifoldBoundary_iff'`, `boundaryTheta_eq'`; the copies use only
  `remark_9_2_14_iff`, `mem_boundary_subPolyfold_iff`, `isReducedTangentSet_iff`,
  `tangentValue_eq`, `boundaryPart_sum_single` and the like, none banned). -/

namespace RoundTrip.V9_26
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.mem_submanifoldBoundary_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.boundaryTheta_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_2_15_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_2_15_2.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isFunctorial_boundaryTheta.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_2_15_3.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.filter_tangentValue_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.mem_submanifoldBoundary_iff.{0},
    @Polyfold.EpGroupoid.boundaryTheta_eq.{0},
    @Polyfold.EpGroupoid.proposition_9_2_15_1.{0},
    @Polyfold.EpGroupoid.proposition_9_2_15_2.{0},
    @Polyfold.EpGroupoid.isFunctorial_boundaryTheta.{0},
    @Polyfold.EpGroupoid.proposition_9_2_15_3.{0},
    @Polyfold.EpGroupoid.filter_tangentValue_eq.{0}⟩

/-! ### `A → B` with Theorem 9.2.1's independence added -/

/-- `B` with the hypothesis `HasIndependentTangentSums Θ` (Theorem 9.2.1) added. -/
def BInd : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    X.HasIndependentTangentSums Θ →
    (∀ x ∈ EpGroupoid.supp Θ, x ∈ X.PObj.boundary →
      ∀ (B B' : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U ∩ B'.U, bsumB B y = bsumB B' y) ∧
    (∀ x ∈ EpGroupoid.supp Θ, x ∈ X.PObj.boundary →
      ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U, X.PObj.degIndex y = 0 → bsumB B y = 0) ∧
    (∃ F : Obj → ℚ, (∀ y, 0 ≤ F y) ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
      EpGroupoid.supp F ⊆ X.PObj.boundary ∧
      (∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U,
        F y = bsumB B y) ∧
      (∀ y, Θ y = 0 → F y = 0))

theorem A_to_BInd : A → BInd := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ hind
  obtain ⟨-, heq, h1, h2, -, h3, -⟩ := hA
  obtain ⟨hfun, hnn, hsupp, -⟩ := h3 hΘ hind
  refine ⟨fun x _ _ B B' y hy => h1 hind B B' hy.1 hy.2,
    fun x _ _ B y _ hy0 => (h2 B hy0).1,
    ⟨X.boundaryTheta Θ, hnn, hfun, hsupp, fun x _ B y hy => heq hind B hy, fun y hy => ?_⟩⟩
  exact EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp (fun h => by
    change (0 : ℚ) < Θ y at h; rw [hy] at h; exact lt_irrefl _ h)

/-! ### `B → A` -/

section Copies

/-- Copy of `MPolyfold.mem_submanifoldBoundary_iff`. -/
theorem mem_submanifoldBoundary_iff' {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} :
    y ∈ P.submanifoldBoundary A ↔ y ∈ A ∧ y ∈ P.boundary ∧ ¬ P.IsTangentReducedAt A y := by
  constructor
  · rintro ⟨_, hy, h⟩
    exact ⟨hy, (MPolyfold.remark_9_2_14_iff hA ⟨y, hy⟩).1
      ((MPolyfold.mem_boundary_subPolyfold_iff _ _).2 h)⟩
  · rintro ⟨hy, hb⟩
    exact ⟨hA, hy, (MPolyfold.mem_boundary_subPolyfold_iff _ _).1
      ((MPolyfold.remark_9_2_14_iff hA ⟨y, hy⟩).2 hb)⟩

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

open scoped Classical in
/-- Copy of `EpGroupoid.boundaryTheta_eq`. -/
theorem boundaryTheta_eq' {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) :
    X.boundaryTheta Θ y = ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i := by
  rw [EpGroupoid.boundaryTheta]
  split_ifs with hb
  · rw [X.tangentValue_eq hind (B.restrictAt hy), EpGroupoid.LocalBranchingStructure.tangentSum,
      EpGroupoid.boundaryPart_sum_single, ← Finset.sum_filter]
    have hT : ∀ i' : (B.restrictAt hy).ι,
        X.PObj.IsReducedTangentSet y (X.PObj.submanifoldTangent ((B.restrictAt hy).M i') y) ↔
          X.PObj.IsTangentReducedAt (B.M i'.1) y := fun i' => by
      rw [EpGroupoid.LocalBranchingStructure.restrictAt_M,
        MPolyfold.submanifoldTangent_inter_isOpen (B.isOpen_nbhdAt y) (B.mem_nbhdAt_self hy),
        MPolyfold.isReducedTangentSet_iff (B.isSmoothSubmanifold i'.1) i'.2]
    refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ hab => Subtype.ext hab)
      (fun i hi => ?_) fun _ _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (mem_submanifoldBoundary_iff' (B.isSmoothSubmanifold a.1)).2
        ⟨a.2, hb, (hT a).not.1 ha⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨hyi, -, hr⟩ := (mem_submanifoldBoundary_iff' (B.isSmoothSubmanifold i)).1 hi
      exact ⟨⟨i, hyi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hT ⟨i, hyi⟩).not.2 hr⟩, rfl⟩
  · exact (Finset.sum_eq_zero fun i hi => absurd
      (MPolyfold.submanifoldBoundary_subset_boundary _ (Finset.mem_filter.1 hi).2) hb).symm

/-- From `B` (3): `B`'s functor is `∂Θ` (it is the local sum on `supp Θ`, zero off it). -/
theorem eq_boundaryTheta_of_B {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) {F : Obj → ℚ}
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U,
      F y = bsumB B y)
    (h0 : ∀ y, Θ y = 0 → F y = 0) : F = X.boundaryTheta Θ := by
  funext y
  by_cases hy : y ∈ EpGroupoid.supp Θ
  · obtain ⟨Bs⟩ := hΘ.localBranching y hy
    rw [hloc y hy Bs y Bs.mem_U, bsumB, boundaryTheta_eq' hind Bs Bs.mem_U]
  · have hΘy : Θ y = 0 := le_antisymm (not_lt.1 hy) (hΘ.nonneg y)
    rw [h0 y hΘy, EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hy]

end Copies

theorem B_to_A : B → A := by
  intro hB
  -- the functor `∂Θ` from `B` (3)
  have hF : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      X.HasIndependentTangentSums Θ →
      X.IsFunctorial (X.boundaryTheta Θ) ∧ (∀ y, 0 ≤ X.boundaryTheta Θ y) ∧
        EpGroupoid.supp (X.boundaryTheta Θ) ⊆ X.PObj.boundary := by
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ hind
    obtain ⟨-, -, F, hnn, hfun, hsupp, hloc, h0⟩ := hB Obj Mor X Θ hΘ
    have h := eq_boundaryTheta_of_B hΘ hind hloc h0
    subst h
    exact ⟨hfun, hnn, hsupp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `mem_submanifoldBoundary_iff`
    intro Z _ _ _ P A hA y
    exact mem_submanifoldBoundary_iff' hA
  · -- `boundaryTheta_eq`
    intro Obj Mor _ _ _ _ _ _ X Θ hind x Bs y hy
    exact boundaryTheta_eq' hind Bs hy
  · -- `proposition_9_2_15_1`
    intro Obj Mor _ _ _ _ _ _ X Θ hind x Bs Bs' y hy hy'
    rw [← boundaryTheta_eq' hind Bs hy, ← boundaryTheta_eq' hind Bs' hy']
  · -- `proposition_9_2_15_2`
    intro Obj Mor _ _ _ _ _ _ X Θ x Bs y hy0
    classical
    have hnot : ∀ i ∈ Finset.univ.filter
        fun i => y ∈ X.PObj.submanifoldBoundary (Bs.M i), False := fun i hi => by
      have h := MPolyfold.submanifoldBoundary_subset_boundary _ (Finset.mem_filter.1 hi).2
      change 1 ≤ X.PObj.degIndex y at h
      omega
    exact ⟨Finset.sum_eq_zero fun i hi => (hnot i hi).elim,
      Finset.sum_eq_zero fun i hi => (hnot i hi).elim⟩
  · -- `isFunctorial_boundaryTheta`
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ hind
    exact (hF Obj Mor X Θ hΘ hind).1
  · -- `proposition_9_2_15_3`
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ hind
    obtain ⟨h1, h2, h3⟩ := hF Obj Mor X Θ hΘ hind
    exact ⟨h1, h2, h3, fun _ _ Bs _ hy => boundaryTheta_eq' hind Bs hy⟩
  · -- `filter_tangentValue_eq`
    intro Obj Mor _ _ _ _ _ _ X Θ hind x Bs y hy hb
    classical
    have hT : ∀ i' : (Bs.restrictAt hy).ι,
        X.PObj.submanifoldTangent ((Bs.restrictAt hy).M i') y =
          X.PObj.submanifoldTangent (Bs.M i'.1) y := fun i' =>
      MPolyfold.submanifoldTangent_inter_isOpen (Bs.isOpen_nbhdAt y) (Bs.mem_nbhdAt_self hy)
    have hR : ∀ i' : (Bs.restrictAt hy).ι,
        X.PObj.IsReducedTangentSet y (X.PObj.submanifoldTangent ((Bs.restrictAt hy).M i') y) ↔
          X.PObj.IsTangentReducedAt (Bs.M i'.1) y := fun i' => by
      rw [hT i', MPolyfold.isReducedTangentSet_iff (Bs.isSmoothSubmanifold i'.1) i'.2]
    rw [X.tangentValue_eq hind (Bs.restrictAt hy), EpGroupoid.LocalBranchingStructure.tangentSum,
      Finsupp.filter_sum]
    have hsingle : ∀ i' : (Bs.restrictAt hy).ι,
        (Finsupp.single (X.PObj.submanifoldTangent ((Bs.restrictAt hy).M i') y)
          ((Bs.restrictAt hy).σ i')).filter (fun L => ¬ X.PObj.IsReducedTangentSet y L) =
          if ¬ X.PObj.IsTangentReducedAt (Bs.M i'.1) y then
            Finsupp.single (X.PObj.submanifoldTangent (Bs.M i'.1) y) (Bs.σ i'.1) else 0 :=
        fun i' => by
      by_cases h : X.PObj.IsTangentReducedAt (Bs.M i'.1) y
      · rw [if_neg (not_not.2 h)]
        exact Finsupp.filter_single_of_neg (fun L => ¬ X.PObj.IsReducedTangentSet y L)
          (fun h' => h' ((hR i').2 h))
      · rw [if_pos h, Finsupp.filter_single_of_pos (fun L => ¬ X.PObj.IsReducedTangentSet y L)
          ((hR i').not.2 h), hT i']
        rfl
    rw [Finset.sum_congr rfl fun i' _ => hsingle i', ← Finset.sum_filter]
    refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ hab => Subtype.ext hab)
      (fun i hi => ?_) fun _ _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (mem_submanifoldBoundary_iff' (Bs.isSmoothSubmanifold a.1)).2 ⟨a.2, hb, ha⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨hyi, -, hr⟩ := (mem_submanifoldBoundary_iff' (Bs.isSmoothSubmanifold i)).1 hi
      exact ⟨⟨i, hyi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩, rfl⟩

#rt_check RoundTrip.V9_26.A_to_BInd [Polyfold.MPolyfold.mem_submanifoldBoundary_iff,
  Polyfold.EpGroupoid.boundaryTheta_eq, Polyfold.EpGroupoid.proposition_9_2_15_1,
  Polyfold.EpGroupoid.proposition_9_2_15_2, Polyfold.EpGroupoid.isFunctorial_boundaryTheta,
  Polyfold.EpGroupoid.proposition_9_2_15_3, Polyfold.EpGroupoid.filter_tangentValue_eq]
#rt_check RoundTrip.V9_26.B_to_A [Polyfold.MPolyfold.mem_submanifoldBoundary_iff,
  Polyfold.EpGroupoid.boundaryTheta_eq, Polyfold.EpGroupoid.proposition_9_2_15_1,
  Polyfold.EpGroupoid.proposition_9_2_15_2, Polyfold.EpGroupoid.isFunctorial_boundaryTheta,
  Polyfold.EpGroupoid.proposition_9_2_15_3, Polyfold.EpGroupoid.filter_tangentValue_eq]
#rt_overlap RoundTrip.V9_26.B_to_A [Polyfold.MPolyfold.mem_submanifoldBoundary_iff,
  Polyfold.EpGroupoid.boundaryTheta_eq, Polyfold.EpGroupoid.proposition_9_2_15_1,
  Polyfold.EpGroupoid.proposition_9_2_15_2, Polyfold.EpGroupoid.isFunctorial_boundaryTheta,
  Polyfold.EpGroupoid.proposition_9_2_15_3, Polyfold.EpGroupoid.filter_tangentValue_eq]

end RoundTrip.V9_26
