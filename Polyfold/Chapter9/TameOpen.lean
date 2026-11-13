import Polyfold.Chapter9.IntegralCovering
import Polyfold.Chapter9.SolutionFaceForms2021
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter9.OrientationExample
import Polyfold.Chapter9.BoundaryPosition
import Polyfold.Chapter9.FormEvalEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, Definition 9.3.6 (pp. 425–426) and §9.5, Theorems 9.5.4, 9.5.5 (p. 438;
2017: Theorems 9.2, 9.3), gap G.107.  Numbers and pages are the 2021 text's.

# Open pieces of tame sheets are tame; Theorems 9.5.4 and 9.5.5 for the concrete integral

* `MPolyfold.HasTameInducedStructure.inter_isOpen`: if the structure induced on a smooth
  finite-dimensional submanifold `N` is tame (2021 Definition 2.5.18), so is the one induced on
  an open piece `N ∩ V`: the inclusion `N ∩ V → N` is an sc-diffeomorphism onto an open subset
  of `N`, and tame charts are carried along (`IsScDiffeoOn.exists_tame_chart`).
* `FormEval.hcov_of_loc`, `hcovEff_of_loc`, `theorem_9_5_4_tame`, `theorem_9_5_5_tame`,
  `tameBranchedIntegral`, `tameBranchedIntegralEff`: the statements of
  `IntegralCovering.lean` without the hypothesis on open pieces.  What remains is the text's
  standing assumption in the form of E1's files: near every point of the support there is an
  oriented tame branching structure of dimension `n` describing the orientation.
  (2026-11-13) Without boundary it is derived (`hloc_of_degIndex_eq_zero`, `CoveringFromText.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An open piece of a submanifold with a tame induced structure has a tame induced
structure** (2021 Definition 2.5.18). -/
theorem HasTameInducedStructure.inter_isOpen {N V : Set X} (hN : P.IsSmoothSubmanifold N)
    (ht : P.HasTameInducedStructure N) (hV : IsOpen V) : P.HasTameInducedStructure (N ∩ V) := by
  classical
  obtain ⟨hY, htame⟩ := ht
  have hY' : P.IsSubMPolyfold (N ∩ V) := (hN.inter_isOpen hV).isSubMPolyfold
  let _ := P.paracompactSpace_subtype N
  let _ := P.paracompactSpace_subtype (N ∩ V)
  refine ⟨hY', isTame_of_forall_exists_chart _ fun x => ?_⟩
  let j : ↥(N ∩ V) → ↥N := fun y => ⟨y.1, y.2.1⟩
  let g : ↥N → ↥(N ∩ V) := fun y => if h : y.1 ∈ V then ⟨y.1, y.2, h⟩ else x
  let W : Set ↥N := {y | y.1 ∈ V}
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hg : ∀ y ∈ W, ((g y : ↥(N ∩ V)) : X) = y.1 := fun y hy => by
    simp only [g, dif_pos (show y.1 ∈ V from hy)]
  have hj : (subPolyfold hY').IsScSmoothOn (subPolyfold hY) j univ :=
    isScSmoothOn_subPolyfold_of_val hY (f := j) (subPolyfold_inclusion_isScSmooth hY')
  have hgs : (subPolyfold hY).IsScSmoothOn (subPolyfold hY') g W :=
    isScSmoothOn_subPolyfold_of_val hY' (f := g)
      (((subPolyfold_inclusion_isScSmooth hY).mono hW (subset_univ W)).congr
        fun y hy => (hg y hy).symm)
  have hd : (subPolyfold hY').IsScDiffeoOn (subPolyfold hY) j g univ W :=
    { isScSmoothOn := hj
      isScSmoothOn_inv := hgs
      mapsTo := fun y _ => y.2.2
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun y _ => Subtype.ext (hg (j y) y.2.2)
      right_inv := fun y hy => Subtype.ext (hg y hy) }
  exact hd.exists_tame_chart htame (mem_univ x)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω} {Θ : Obj → ℚ}
  {T : Obj → X.PObj.OrTangent →₀ ℚ}

namespace FormEval

variable (X) in
/-- Open pieces of submanifolds with tame induced structure, in the form used in
`IntegralCovering.lean`. -/
theorem tameOpen (N V : Set Obj) (hN : X.PObj.IsSmoothSubmanifold N)
    (ht : X.PObj.HasTameInducedStructure N) (hV : IsOpen V) :
    X.PObj.HasTameInducedStructure (N ∩ V) :=
  MPolyfold.HasTameInducedStructure.inter_isOpen hN ht hV

/-- **The covering hypothesis of Theorem 9.5.4 for the class `F.sheets`**: an oriented tame
structure describing `T` at every point of the support restricts to one with sheets in the
class. -/
theorem hcov_of_loc
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T :=
  hcov_of_tameOpen (tameOpen X) hloc

/-- **The covering hypothesis of Theorem 9.5.5 for the class `F.sheets`.** -/
theorem hcovEff_of_loc
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC :=
  hcovEff_of_tameOpen (tameOpen X) hloc

variable (F)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), for the integrals of
`SheetIntegrationConcrete.lean`**: `Θ` a compact branched ep⁺-subgroupoid with an orientation
`T̂Θ = T` described near every point of its support by an oriented tame branching structure of
dimension `n ≥ 1`.  There is exactly one linear map `ω ↦ μ_ω` into the signed measures on
`(S, L(S))` with `μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for the oriented tame structures
describing `T̂Θ` with sheets in the class `F.sheets`, and the measurable `K ⊆ |U(x)|`. -/
theorem theorem_9_5_4_tame (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.sheets) ∧ C.Represents T) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.sheetIntegration hn) ω (Subtype.val '' K) :=
  F.theorem_9_5_4_concrete hn hΘ hcpt hT (tameOpen X) hloc

/-- **Theorem 9.5.5, 2021 p. 438 (2017: Theorem 9.3), for the integrals of
`SheetIntegrationConcrete.lean`**: the same with the weights `1/♯G_x^eff`, for structures whose
`U(x)` has the property of Definition 7.2.18. -/
theorem theorem_9_5_5_tame (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasureEff (F.sheetIntegration hn) ω (Subtype.val '' K) :=
  F.theorem_9_5_5_concrete hn hΘ hcpt hT (tameOpen X) hloc

/-- **Definition 9.5.6 (1), 2021 p. 439**: the branched integral `∫_Θ̂ ω = μ_ω(S)` of the
integrals of `SheetIntegrationConcrete.lean`. -/
def tameBranchedIntegral (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) (ω : Ω) : ℝ :=
  F.concreteBranchedIntegral hn hΘ hcpt hT (tameOpen X) hloc ω

/-- **Definition 9.5.6 (2), 2021 p. 439**: the effective branched integral
`∮_Θ̂ ω = μ_ω^eff(S)` of the integrals of `SheetIntegrationConcrete.lean`. -/
def tameBranchedIntegralEff (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) (ω : Ω) : ℝ :=
  F.concreteBranchedIntegralEff hn hΘ hcpt hT (tameOpen X) hloc ω

end FormEval

/-! ### A witness with nonempty support and `n = 1` -/

section Witness

open scoped Classical

variable {m : ℕ}

/-- **Oriented tame structures on `ℝᵐ`**: for finitely many closed oriented `k`-dimensional
submanifolds `(Mᵢ, oᵢ)` of `ℝᵐ` and weights `σᵢ > 0`, every point has an oriented tame branching
structure of `Θ = ∑ σᵢ 1_{Mᵢ}` (trivial ep-groupoid of `ℝᵐ`) describing
`T̂(y) = ∑_{y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)`: the structure of `orientedBranchingStructure_sum_rn`
restricted to the domain of a natural representation. -/
theorem exists_orientedTameStructure_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin m → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {k : ℕ}
    (hM : ∀ i, (rnPolyfold m).IsSubmanifoldOfDim (M i) k) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold m).SubmanifoldOrientation (M i) k) (x : Fin m → ℝ) :
    ∃ C : (trivial (rnPolyfold m)).OrientedTameStructure k (fun y => ∑ i with y ∈ M i, σ i) x,
      C.Represents (orientedSumRn M σ o) := by
  set B₀ := orientedBranchingStructure_sum_rn M σ hσ hM hc o x with hB₀
  obtain ⟨R, hRU⟩ := theorem_7_1_13 (trivial (rnPolyfold m)) x B₀.isOpen_U B₀.mem_U
  let B := B₀.restrict R.isOpen_U R.mem_U hRU
  refine ⟨{ toLocalBranchingStructure := B.toLocalBranchingStructure
            rep := R
            U_eq := rfl
            hasPropernessProperty := hasPropernessProperty_trivial (rnPolyfold m) R.isOpen_U
            hasTameInducedStructure := fun i =>
              MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (B.isSmoothSubmanifold i)
                fun a _ => rnPolyfold_degIndex m a
            isSubmanifoldOfDim := B.isSubmanifoldOfDim
            orient := B.orient }, fun y hy _ => ?_⟩
  have hyU : y ∈ R.U := hy
  rw [← orientedSum_sum_rn_eq M σ hσ hM hc o (hRU hyU)]
  change B₀.orientedSum y = B.orientedSum y
  rw [OrientedBranchingStructure.orientedSum, OrientedBranchingStructure.orientedSum,
    Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hyi : y ∈ B₀.M i
  · rw [if_pos hyi, if_pos (show y ∈ B.M i from ⟨hyi, hyU⟩)]
    exact congrArg (fun g => Finsupp.single g (B₀.σ i))
      ((B₀.orient i).restrict_tangent R.isOpen_U hyU).symm
  · rw [if_neg hyi, if_neg (show y ∉ B.M i from fun h => hyi h.1)]

/-- **The covering hypothesis of Theorem 9.5.4 is satisfiable with nonempty support and
`n = 1`**: for the `x`-axis of `ℝ²` (the graph of `β = 0`, oriented by `(1, 0)`), `Θ = 1` on it,
the trivial ep-groupoid of `ℝ²` and the sc-differential `1`-forms of Definition 8.2.1, every
point of the support (the origin is one) has an oriented tame structure with sheets in the class
`sheets` describing the orientation.  `Θ` is not compact. -/
theorem hcov_axis :
    let X := trivial (rnPolyfold 2)
    let Mf : Unit → Set (Fin 2 → ℝ) := fun _ => graph2 fun _ => (0 : ℝ)
    let Θ : (Fin 2 → ℝ) → ℚ := fun y => ∑ i with y ∈ Mf i, (1 : ℚ)
    let T := orientedSumRn Mf (fun _ => (1 : ℚ))
      (fun _ => graphOrientation (β := fun _ => (0 : ℝ)) contDiff_const 1 one_ne_zero)
    X.IsOrientation Θ T ∧ (0 : Fin 2 → ℝ) ∈ supp Θ ∧
      ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure 1 Θ x,
        (∀ i, C.M i ∈ (X.epFormEval 1).sheets) ∧ C.Represents T := by
  intro X Mf Θ T
  have hM : ∀ i : Unit, (rnPolyfold 2).IsSubmanifoldOfDim (Mf i) 1 := fun _ =>
    rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const
  have hc : ∀ i : Unit, IsClosed (Mf i) := fun _ => isClosed_graph2 continuous_const
  refine ⟨isOrientation_sum_trivial_rn Mf (fun _ => 1) (fun _ => one_pos) hM hc _, ?_,
    FormEval.hcov_of_loc fun x _ =>
      exists_orientedTameStructure_sum_rn Mf (fun _ => 1) (fun _ => one_pos) hM hc _ x⟩
  have h0 : (0 : Fin 2 → ℝ) ∈ Mf () := by simp [Mf, graph2]
  change (0 : ℚ) < ∑ i with (0 : Fin 2 → ℝ) ∈ Mf i, (1 : ℚ)
  exact Finset.sum_pos (fun _ _ => one_pos) ⟨(), by simp [h0]⟩

end Witness

end EpGroupoid

end Polyfold
