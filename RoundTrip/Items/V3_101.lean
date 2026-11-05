import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_101

/-!
Round trip for V3_101 (Theorems 3.19 and 3.56 with "`f'(x)` surjective").  `A` is the conjunction
of the types of `Polyfold.theorem_3_19_of_surjective`, `Polyfold.theorem_3_56_of_surjective` and
`Polyfold.theorem_3_56_tame`, universes instantiated at `0`.

Neither direction is proved.

* `A → B`: the (3.56) conjunct of `B` follows from `A` (`A_to_B_3_56` below:
  `theorem_3_56_of_surjective` when `S ≠ ∅`, the empty atlas when `S = ∅`, and the open-chart
  glue of V3_95 for `IsManifoldWithCornersLoc ∧ d ≡ 0 ⇒ HasBoundarylessManifoldStructure`).  The
  (3.19) conjunct does not: (i) `B` assumes only `IsScFredholmSection` (germ data in some chart, no
  tameness) while `theorem_3_19_of_surjective` needs `IsScFredholmSectionTame`, and
  `theorem_3_56_tame` (which takes a plain `IsScFredholmSection`) needs good position in a *tame*
  chart at every zero; the project has no lemma producing tame germ data when `d_X ≡ 0`;
  (ii) `B` asserts that `f'(x₀) : T_zO → K_z` is an sc-Fredholm *sc-operator* between the induced
  sc-subspaces, with sc-index `d`, in every chart (`ChartLinScFredholm`), while `A` gives only the
  level-`0` statement `IsSurjLinOfIndex` (surjective, Fredholm, index `d = dim ker`).
* `B → A`: `B`'s (3.56) assumes a tame strong bundle (`IsTameStrongBundle`), which `A` does not,
  and `A` concludes more (tameness of the induced structure, regular tangent data of
  Definition 3.25 (2), `IsSurjLinOfIndex` at the nearby zeros, `theorem_3_56_tame` under good
  position for a non-tame section).

**Refresh 2026-11-02 (germ reading at HEAD).**  The three theorems now state the germ reading;
`A_to_B_3_56` checks unchanged.  Obstacle (ii) below is now addressed by a project lemma up to
glue (`StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`: given `IsSurjLinOfIndex f y d`, in
every chart `Lin(z) : T_zO → K_z` is sc-Fredholm, onto on every level, of index `d`; the glue to
B's `ChartLinScFredholm` was not carried out).  Obstacle (i) remains: the project still has no way
to move untamed germ data (`IsScFredholmSection`) into a tame chart (left open in
`Chapter3/TameGermData.lean`), and every theorem of A needs tame germ data or good position in a
tame chart.
-/

namespace RoundTrip.V3_101
open Polyfold Set

/-- The project's statement: Theorems 3.19 and 3.56 with "`f'` surjective", and Theorem 3.56 with
tameness, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_19_of_surjective.{0, 0} ∧
    type_of% @Polyfold.theorem_3_56_of_surjective.{0, 0} ∧
    type_of% @Polyfold.theorem_3_56_tame.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_19_of_surjective.{0, 0}, @Polyfold.theorem_3_56_of_surjective.{0, 0},
    @Polyfold.theorem_3_56_tame.{0, 0}⟩

section Glue

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {QZ : MPolyfold Z}

/-- (From V3_95.)  A chart of `QZ` modelled on a relatively open subset of a partial quadrant in a
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

/-- (From V3_95.)  `IsManifoldWithCornersLoc` and `d ≡ 0` give B's boundaryless manifold
structure. -/
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

/-- An M-polyfold on an empty type has a boundaryless manifold structure (the empty atlas). -/
theorem boundaryless_of_isEmpty (hZ : IsEmpty Z) (QZ : MPolyfold Z) :
    HasBoundarylessManifoldStructure QZ := by
  let A' : MAtlas Z :=
    { charts := ∅
      compatible := fun φ hφ _ _ => absurd hφ (notMem_empty φ)
      cover := fun z => (hZ.false z).elim }
  exact ⟨A', (MAtlas.equiv_iff _ _).2 fun φ hφ _ _ => absurd hφ (notMem_empty φ),
    fun φ hφ => absurd hφ (notMem_empty φ)⟩

end Glue

/-- **The (3.56) conjunct of `B` follows from `A`** (from `theorem_3_56_of_surjective`; `∂X = ∅`
is `d_X ≡ 0`, `isWithoutBoundary_iff`; the tame-bundle hypothesis of `B` is not used). -/
theorem A_to_B_3_56 (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y),
      IsTameStrongBundle Bd → PX.boundary = ∅ → Bd.IsScFredholmSectionTame f →
      (∀ x ∈ solutionSet P f, Bd.IsLinSurjAt f x) →
        ∃ (hS : PX.IsSubMPolyfold (solutionSet P f)) (_ : ParacompactSpace (solutionSet P f)),
          HasBoundarylessManifoldStructure (PX.subPolyfold hS) := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f _ hbd hf hsurj
  have hX : PX.IsWithoutBoundary := PX.isWithoutBoundary_iff.2 hbd
  have := PX.paracompactSpace_subtype (solutionSet P f)
  by_cases hne : (solutionSet P f).Nonempty
  · obtain ⟨hsub, -, h1, h2, -⟩ := hA.2.1 hX hf (fun x hx => hsurj x hx) hne
    exact ⟨hsub, inferInstance, boundaryless_of_loc h1 h2⟩
  · have hsub : PX.IsSubMPolyfold (solutionSet P f) := fun a ha => absurd ⟨a, ha⟩ hne
    refine ⟨hsub, inferInstance, boundaryless_of_isEmpty ⟨fun z => hne ⟨z.1, z.2⟩⟩ _⟩

#rt_check RoundTrip.V3_101.A_to_B_3_56 [Polyfold.theorem_3_19_of_surjective,
  Polyfold.theorem_3_56_of_surjective, Polyfold.theorem_3_56_tame]

end RoundTrip.V3_101
