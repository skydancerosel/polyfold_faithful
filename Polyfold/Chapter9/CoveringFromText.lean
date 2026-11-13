import Polyfold.Chapter9.MultiChartTheorem
import Polyfold.Chapter9.PropertyTShrinking2021
import Polyfold.Chapter9.OrientationAnyDim

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.4 and 9.5.5** (p. 438; 2017: Theorems 9.2, 9.3), gap
G.107.  Numbers and pages are the 2021 text's.

# The covering hypothesis of Theorem 9.5.4 from the text's hypotheses, without boundary

Theorem 9.5.4 integrates over the oriented tame structures `(U(x), (Mᵢ, σᵢ, oᵢ))` describing the
orientation `T̂Θ`.  The Lean statements (`theorem_9_5_4`, `theorem_9_5_4_tame`,
`theorem_9_5_4_multi`) take as hypothesis `hloc`: every `x ∈ supp Θ` has such a structure.

For an ep-groupoid whose object M-polyfold has no boundary (`degIndex = 0`), `hloc` follows from
the text's hypotheses `Θ` `n`-dimensional and `T̂Θ` an orientation
(`hloc_of_degIndex_eq_zero`): the oriented local branching structure of Definition 9.3.2 has
`n`-dimensional sheets (`IsOrientation.isOrientationOfDim`); restricted to the domain of a
natural representation (Theorem 7.1.13) inside an open set with the properness property, it is
tame, since without boundary every submanifold has a tame induced structure.  Hence Theorems
9.5.4 for sheets in several charts holds with exactly the printed hypotheses
(`theorem_9_5_4_of_degIndex_eq_zero`).

With boundary the step "the sheets `Mᵢ` of the oriented structure have tame induced structures"
is not among the hypotheses: `IsTameBranched` provides tame sheets of *some* local branching
structure, and `IsOrientation` oriented sheets of *another* one; the text does not say that the
latter can be taken tame.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- Transporting an orientation along `m = n` does not change its oriented tangent spaces. -/
theorem SubmanifoldOrientation.tangent_cast {M : Set Z} {m n : ℕ} (h : m = n)
    (o : P.SubmanifoldOrientation M m) : (h ▸ o : P.SubmanifoldOrientation M n).tangent =
      o.tangent := by
  subst h; rfl

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

open scoped Classical

/-- **An oriented local branching structure with `n`-dimensional sheets gives an oriented tame
structure**, when the object M-polyfold has no boundary: restrict it to the domain of a natural
representation inside an open set with the properness property. -/
theorem exists_orientedTameStructure_of_degIndex_eq_zero
    (hdeg : ∀ a, X.PObj.degIndex a = 0) {x : Obj} (B : X.OrientedBranchingStructure Θ x)
    (hdim : ∀ i, B.dim i = n) (hBT : ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) :
    ∃ C : X.OrientedTameStructure n Θ x, C.Represents T := by
  obtain ⟨V, hxV, hVU, hVP⟩ := X.exists_hasPropernessProperty_subset (B.isOpen_U.mem_nhds B.mem_U)
  obtain ⟨R, hRV⟩ := theorem_7_1_13 X x hVP.1 hxV
  set B' := B.restrict R.isOpen_U R.mem_U (hRV.trans hVU) with hB'
  refine ⟨{ toLocalBranchingStructure := B'.toLocalBranchingStructure
            rep := R
            U_eq := rfl
            hasPropernessProperty := hVP.mono R.isOpen_U hRV
            hasTameInducedStructure := fun i =>
              MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (B'.isSmoothSubmanifold i)
                fun a _ => hdeg a
            isSubmanifoldOfDim := fun i => hdim i ▸ B'.isSubmanifoldOfDim i
            orient := fun i => hdim i ▸ B'.orient i }, fun y hy hys => ?_⟩
  have hyU : y ∈ R.U := hy
  rw [hBT y (hVU (hRV hyU)) hys, OrientedTameStructure.orientedSum_eq_sum_ite,
    OrientedBranchingStructure.orientedSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  split_ifs with h1 h2 h2
  · congr 1
    exact ((B.orient i).restrict_tangent R.isOpen_U hyU).symm.trans
      (congrFun (MPolyfold.SubmanifoldOrientation.tangent_cast (hdim i) (B'.orient i)) y).symm
  · exact absurd ⟨h1, hyU⟩ h2
  · exact absurd h2.1 h1
  · rfl

/-- **The covering hypothesis `hloc` of Theorem 9.5.4 from the printed hypotheses, without
boundary**: for `Θ` `n`-dimensional (Definition 9.1.2) with an orientation `T̂Θ = T`
(Definition 9.3.2), every point of `supp Θ` has an oriented tame structure of dimension `n`
describing `T`, provided all points of the object M-polyfold have degeneracy index `0`. -/
theorem hloc_of_degIndex_eq_zero (hdeg : ∀ a, X.PObj.degIndex a = 0)
    (hnd : X.IsNDimensional Θ n) (hT : X.IsOrientation Θ T) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T := fun x hx => by
  obtain ⟨B, hdim, hBT⟩ := (hT.isOrientationOfDim hnd).2 x hx
  exact exists_orientedTameStructure_of_degIndex_eq_zero hdeg B hdim hBT

namespace FormEval

variable {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), with the printed hypotheses, without
boundary**: `Θ` a compact `n`-dimensional branched ep⁺-subgroupoid, `n ≥ 1`, with an orientation
`T̂Θ = T`, in an ep-groupoid whose objects have degeneracy index `0`.  There is exactly one
linear map `ω ↦ μ_ω` with `μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for every oriented tame
structure describing `T̂Θ` whose sheets carry finite integrals of `|ω|`, and every measurable
`K ⊆ |U(x)|`.  (Tameness, Definition 9.3.6, holds automatically here.) -/
theorem theorem_9_5_4_of_degIndex_eq_zero (hn : 0 < n) (hdeg : ∀ a, X.PObj.degIndex a = 0)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ n) (hT : X.IsOrientation Θ T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.msheets) ∧ C.Represents T) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.msheetIntegration hn) ω (Subtype.val '' K) :=
  F.theorem_9_5_4_multi hn hΘ hcpt hT (hloc_of_degIndex_eq_zero hdeg hnd hT)

end FormEval

/-- The hypothesis `degIndex = 0` is satisfiable: `ℝⁿ` (e.g. the circle of
`CircleWitness.lean`, where all other hypotheses hold with nonempty support). -/
theorem degIndex_rnPolyfold_trivial (m : ℕ) :
    ∀ a, (trivial (rnPolyfold m)).PObj.degIndex a = 0 := fun a => rnPolyfold_degIndex m a

end EpGroupoid

end Polyfold
