import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_86

/-!
Round trip for V3_86 (Theorem 3.56).  `A` is the conjunction of the types of
`Polyfold.theorem_3_56`, `Polyfold.theorem_3_57` and `Polyfold.lemma_2_26`, universes
instantiated at `0`.

Glue for `A → B`:
* `PX.boundary = ∅` is `PX.IsWithoutBoundary` (`isWithoutBoundary_iff`).
* B's hypothesis `IsLinSurjAt` at a zero (`d_X = 0`) gives A's `IsGoodPositionGermTame`
  (`StrongBundle.isGoodPositionGerm_of_isLinSurjAt`, using the tame germ data of
  `IsScFredholmSectionTame`).
* A assumes `S ≠ ∅`; for `S = ∅` B's conclusion holds with the empty atlas.
* A's conclusion "`IsManifoldWithCornersLoc` and `d_S ≡ 0`" gives B's atlas of charts onto open
  subsets of finite-dimensional spaces (`boundaryless_of_loc`): around each point, a corner chart
  realizes `d_S = 0` (it is a tame retract), so the image point has all quadrant coordinates
  `> 0`; restrict the chart to the open set where they are `> 0` and change the model to
  `(U, univ, E₀)` with the constant structure (`compDiffeo` with the identity).

**Refresh 2026-11-02 (germ reading at HEAD).**  `theorem_3_56` and `theorem_3_57` now state the
germ reading, and A gains `theorem_3_56_sc` (good position with the text's sc-complement).  B's
`IsScFredholmSectionTame` is the germ reading too; the proof (through `theorem_3_56` and the germ
form of `isGoodPositionGerm_of_isLinSurjAt`) checks unchanged.  B ⇒ A still fails.
-/

namespace RoundTrip.V3_86
open Polyfold Set

/-- The project's statement: Theorem 3.56, Theorem 3.57 (germ reading), Lemma 2.26 and Theorem
3.56 with the sc-complement form of good position, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_56.{0, 0} ∧ type_of% @Polyfold.theorem_3_57.{0, 0} ∧
    type_of% @Polyfold.lemma_2_26.{0} ∧ type_of% @Polyfold.theorem_3_56_sc.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_56.{0, 0}, @Polyfold.theorem_3_57.{0, 0}, @Polyfold.lemma_2_26.{0},
    @Polyfold.theorem_3_56_sc.{0, 0}⟩

section Glue

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {QZ : MPolyfold Z}

/-- A chart of `QZ` modelled on a relatively open subset of a partial quadrant in a
finite-dimensional space, at a point `z` with `d(z) = 0`, gives a chart of `QZ` around `z` onto an
open subset of `E₀` with the constant structure and `C = univ`. -/
theorem exists_open_chart {χ : MChart Z} (hχ : QZ.IsChart χ)
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O)
    (hfin : FiniteDimensional ℝ (χ.model.E 0)) {z : Z} (hz : z ∈ χ.source)
    (hd : QZ.degIndex z = 0) :
    ∃ χ' : MChart Z, QZ.IsChart χ' ∧ z ∈ χ'.source ∧
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
        (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
        χ'.model = LocalModel.ofRelOpen hU := by
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨G, hG, hOG⟩ := hU.relOpen
  -- `d_C(χ z) = 0`: the chart is a tame retract
  have htame : IsTameRetract χ.model.E χ.model.C χ.model.O :=
    ⟨ScRetraction.id hU, image_id _, ScRetraction.id_isTame _⟩
  have hdeg : degIndexWith T (χ z) = 0 := by
    have h1 := QZ.degIndex_eq_chartDegIndex_of_isTameRetract hχ htame hz
    rw [hd, MPolyfold.chartDegIndex, degIndex_eq T hT (χ.apply_mem_C hz)] at h1
    exact h1.symm
  have hcoord : ∀ i, (T 0 (χ z)).1 i ≠ 0 := by
    simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies] at hdeg
    exact hdeg
  -- the open set where all quadrant coordinates are positive
  set W' : Set (χ.model.E 0) := {v | ∀ i, 0 < (T 0 v).1 i} with hW'
  have hW'o : IsOpen W' := by
    have : W' = ⋂ i, (fun v => (T 0 v).1 i) ⁻¹' Ioi 0 := by ext v; simp [hW']
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage
      ((continuous_apply i).comp (continuous_fst.comp (T 0).continuous))
  have hW'C : W' ⊆ χ.model.C := fun v hv => by
    rw [hT]; exact fun i => (hv i).le
  have hzW' : χ z ∈ W' := by
    have hzC := χ.apply_mem_C hz
    rw [hT] at hzC
    exact fun i => lt_of_le_of_ne (hzC i) (hcoord i).symm
  -- restrict the chart
  set s : Set Z := χ.source ∩ χ ⁻¹' W' with hs
  have hss : s ⊆ χ.source := inter_subset_left
  have hso : IsOpen s := χ.continuousOn_toFun.isOpen_inter_preimage χ.isOpen_source hW'o
  have himg : χ '' s = χ.model.O ∩ W' := by
    rw [hs, image_inter_preimage, χ.image_source]
  have hopen : IsOpen (χ '' s) := by
    rw [himg, hOG, inter_assoc, inter_eq_right.2 hW'C]
    exact hG.inter hW'o
  set χ₁ := χ.restrict hss hso with hχ₁
  have hχ₁c : QZ.IsChart χ₁ := MPolyfold.IsChart.restrict QZ hχ hss hso
  -- the identity onto the constant structure with `C = univ`
  have hU₁ : IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' s) :=
    ⟨hU.isPartialQuadrant, χ '' s, hopen,
      (inter_eq_left.2 ((χ.image_subset_model hss).trans χ.model.O_subset_C)).symm⟩
  have hU₂ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ (χ '' s) :=
    ⟨isPartialQuadrant_univ _, χ '' s, hopen, (inter_univ _).symm⟩
  have d := hU₁.isScDiffeoQuadrant_toConst
  have h : IsScDiffeoQuadrant hU₁ hU₂ (id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0)
      (id : (ScBanach.const (χ.model.E 0)) 0 → χ.model.E 0) :=
    ⟨d.isScSmooth, d.isScSmooth_inv, d.mapsTo, d.mapsTo_inv, d.left_inv, d.right_inv⟩
  have hU₃ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ
      ((id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0) '' (χ '' s)) := by
    rw [image_id]; exact hU₂
  refine ⟨χ₁.compDiffeo h subset_rfl hU₃.isScRetract, MChart.compDiffeo_isChart hχ₁c h subset_rfl _,
    ⟨hz, hzW'⟩, χ.model.E 0, inferInstance, inferInstance, hfin, _, hU₃, rfl⟩

/-- `IsManifoldWithCornersLoc` and `d ≡ 0` give B's boundaryless manifold structure. -/
theorem boundaryless_of_loc (hc : QZ.IsManifoldWithCornersLoc) (hb : QZ.IsWithoutBoundary) :
    HasBoundarylessManifoldStructure QZ := by
  obtain ⟨A, hA, hcA⟩ := hc
  let A' : MAtlas Z :=
    { charts := {χ | QZ.IsChart χ ∧ ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
        (_ : FiniteDimensional ℝ V) (U : Set V)
        (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U), χ.model = LocalModel.ofRelOpen hU}
      compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible QZ hφ.1 hψ.1
      cover := fun z => by
        obtain ⟨χ, hχA, hz⟩ := A.cover z
        obtain ⟨χ', hχ', hz', hrest⟩ := exists_open_chart (QZ.isChart_of_mem_equiv hA hχA)
          (hcA χ hχA).1 (hcA χ hχA).2 hz (hb z)
        exact ⟨χ', ⟨hχ', hrest⟩, hz'⟩ }
  exact ⟨A', (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

/-- B's conclusion for an empty set: the empty atlas. -/
theorem empty_case {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {S : Set X} (hS : ¬ S.Nonempty) :
    ∃ (hsub : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
      HasBoundarylessManifoldStructure (PX.subPolyfold hsub) := by
  have hsub : PX.IsSubMPolyfold S := fun a ha => absurd ⟨a, ha⟩ hS
  have hpc := PX.paracompactSpace_subtype S
  exact ⟨hsub, hpc, ⟨∅, fun φ hφ => absurd hφ (notMem_empty φ), fun y => absurd ⟨y.1, y.2⟩ hS⟩,
    (MAtlas.equiv_iff _ _).2 fun φ hφ => absurd hφ (notMem_empty φ),
    fun φ hφ => absurd hφ (notMem_empty φ)⟩

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f _ hb hf hsurj
  have hX : PX.IsWithoutBoundary := PX.isWithoutBoundary_iff.2 hb
  have hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x := fun x hx =>
    StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hx (hX x) (hsurj x hx)
  by_cases hne : (solutionSet P f).Nonempty
  · have := PX.paracompactSpace_subtype (solutionSet P f)
    obtain ⟨hsub, h1, h2⟩ := hA.1 hX hf.toIsScFredholmSection hall hne
    exact ⟨hsub, inferInstance, boundaryless_of_loc h1 h2⟩
  · exact empty_case hne

#rt_check RoundTrip.V3_86.A_to_B [Polyfold.theorem_3_56, Polyfold.theorem_3_57,
  Polyfold.lemma_2_26, Polyfold.theorem_3_56_sc]

end RoundTrip.V3_86
