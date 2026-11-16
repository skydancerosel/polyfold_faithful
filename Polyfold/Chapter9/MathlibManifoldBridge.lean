import Polyfold.Chapter9.GeneralLevelZero
import Polyfold.Chapter9.BranchingGeometryManifold
import Polyfold.Chapter3.GlobalIFTTheorems
import Polyfold.Chapter6.CornerCoordinates

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part I, **Definition 4.1.1** (p. 175; 2014 preprint: Definition 4.1, p. 147) and
**Theorem 4.2.7** (p. 188; preprint: Theorem 4.18, p. 159), and Part II, **Definition 9.3.6**
(p. 425; 2017: Definition 9.10, p. 314), last sentence: "in particular every `Mᵢ` is a manifold
with boundary with corners".  Numbers and pages are the 2021 text's, older numbers in parentheses.

# The bridge from corner structures to Mathlib's manifolds with corners (gap G.102)

## The text, paraphrased

(Definition 4.1.1) An M-polyfold has a compatible smooth manifold structure with boundary with
corners if it admits an equivalent atlas whose charts are sc-diffeomorphisms onto relatively open
subsets of partial quadrants `[0,∞)ᵏ × ℝⁿ⁻ᵏ`; the transition maps are then classically smooth.
(Theorem 4.2.7, Definition 9.3.6) A tame finite-dimensional submanifold of an M-polyfold, in
particular a sheet `Mᵢ` of a tame branching structure, has this structure.

## What is formalized

The project's "manifold with boundary with corners" is `MPolyfold.HasCornerStructure`
(Definition 4.1.1, with `MChart.IsCornerChart`) and, with the dimension fixed,
`MPolyfold.IsManifoldWithCorners n` (Theorem 3.2.3 (preprint 3.27)).  This file turns these into
Mathlib's notions, `ChartedSpace` and `IsManifold`:

* `CornerCoords`: a corner chart `χ` of `X` of dimension `n` read in coordinates, i.e. with a
  continuous linear isomorphism `Ψ : E₀ ≃ ℝⁿ` and a translation `c` such that `Ψ ∘ χ + c` maps an
  open piece `s` of the chart domain onto `W ∩ [0,∞)ⁿ`, `W ⊆ ℝⁿ` open.  Every corner chart has such
  coordinates near each point of its domain (`CornerCoords.exists_mem`, from
  `exists_cle_partialQuadrant`: a partial quadrant of a finite-dimensional space is, in suitable
  linear coordinates, `{y | yᵢ ≥ 0 for i ∈ S}`; the partial quadrant `[0,∞)ᵏ × ℝⁿ⁻ᵏ` is translated
  into the full quadrant `[0,∞)ⁿ`, with the chart domain shrunk to a bounded piece).
* `CornerCoords.toQuadrantChart`: the Mathlib chart `X → EuclideanQuadrant n`;
  `CornerCoords.toEuclideanChart`: the chart `X → ℝⁿ` when the piece misses the boundary
  (`CornerCoords.IsInterior`).  The transition maps are `C^∞` (`CornerCoords.contDiffOn_trans`,
  from `MChart.IsCornerChart.contDiffOn_transition`, Definition 4.1.1's "classically smooth").
* **Definition 4.1.1 with the dimension `n`**: `MPolyfold.HasCornerStructureOfDim P n` (every
  point lies in a corner chart of dimension `n`); `IsManifoldWithCorners.hasCornerStructureOfDim`.
* **The bridge** (gap G.102): `MPolyfold.cornerChartedSpace`, a `ChartedSpace (EuclideanQuadrant n)
  X`, with `MPolyfold.isManifold_cornerChartedSpace`:
  `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ X`; without boundary
  (`∀ x, d_X(x) = 0`), `MPolyfold.interiorChartedSpace` and
  `MPolyfold.isManifold_interiorChartedSpace`: `IsManifold (𝓡 n) ∞ X`.
* **Downstream, in Mathlib's language**:
  - `theorem_3_2_3_isManifold`: the solution set of Theorem 3.2.3 (preprint Theorem 3.27, the
    implicit function theorem for the germs of Definition 3.2.1, `IsManifoldWithCorners n`) is a
    smooth manifold with corners, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`;
  - **Theorem 4.2.7 with the dimension**: `IsSubmanifoldOfDim.hasCornerStructureOfDim_of_centred`
    (the corner charts of Theorem 4.1.2 are modelled on `T_aA`, of dimension `n`),
    `IsSubmanifoldOfDim.hasCornerStructureOfDim_of_tame` (tame `X`, good position),
    `IsSubmanifoldOfDim.hasCornerStructureOfDim_of_degIndex_eq_zero` (`A ∩ ∂X = ∅`), and in
    Mathlib's language `theorem_4_2_7_isManifold`,
    `IsSubmanifoldOfDim.isManifold_of_degIndex_eq_zero` (`IsManifold (𝓡 n) ∞ A`, with
    `IsSmoothSubmanifold.subPolyfold_degIndex_eq_zero` from Lemma 2.4.6 (preprint 2.26), `d_A ≤ d_X` (`lemma_2_4_6`));
  - **Definition 9.3.6, last sentence: a tame `n`-dimensional submanifold is a manifold with
    boundary and corners.**  The step the text leaves implicit is that `T₀O` is in good position
    in a tame centred chart (`IsTameRetract.isInGoodPosition_zero`: `0` is a full corner, so the
    tame complement in `E_0` is a good complement); the dimension of `T_zO` in every chart of the
    induced structure is `n` (`IsSubmanifoldOfDim.tangentSpace_subPolyfold_chart`, with the
    chart change `finiteDimensional_tangentSpace_chart_change`,
    `finiteDimensional_span_tangentSpace_of_isDiffeoGerm`).  Then
    `IsSubmanifoldOfDim.hasCornerStructureOfDim_of_hasTameInducedStructure`,
    `IsSubmanifoldOfDim.isManifold_of_hasTameInducedStructure`, and for the sheets of a tame
    branching structure `EpGroupoid.TameBranchingStructure.hasCornerStructureOfDim`,
    `EpGroupoid.TameBranchingStructure.isManifold` (row V9.34, gap G.102);
  - **Lemma 9.4.6 for the sheets of an M-polyfold** (gaps G.105, G.106):
    `lemma_9_4_6_cornerChartedSpace`, `lemma_9_4_6_sheet`,
    `EpGroupoid.TameBranchingStructure.lemma_9_4_6`: the non-essential points of any `K ⊆ Mᵢ`
    form a Lebesgue null set (Definition 9.4.5, `Polyfold.IsMeasureZero`) in the sheet.

## What the text leaves implicit, and the choices made

* Mathlib's manifolds with corners are modelled on one model space; the charts of
  Definition 4.1.1 take values in partial quadrants `[0,∞)ᵏ × ℝⁿ⁻ᵏ` with `k` depending on the
  chart.  As is standard, the full quadrant `[0,∞)ⁿ` (`EuclideanQuadrant n`) is the model, and a
  relatively open bounded subset of `[0,∞)ᵏ × ℝⁿ⁻ᵏ` is translated into the full quadrant; the
  translation is affine, so the transition maps stay `C^∞`.
* The dimension is fixed (`HasCornerStructureOfDim P n`), as in `IsManifoldWithCorners n`; the
  text lets it vary from chart to chart (Definition 4.1.1).  A Mathlib `ChartedSpace` has one
  model, so the statement with varying dimension is per component of constant dimension.
* "Smooth" is `C^∞` (`∞ : WithTop ℕ∞`), not Mathlib's analytic `ω`.

Corner coordinates (`coordQuadrant`, `abs_apply_le_norm_pi`, `MPolyfold.CornerCoords`,
`exists_cle_partialQuadrant`, …): `Chapter6/CornerCoordinates.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module Manifold WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable {P : MPolyfold X} {n : ℕ}

/-! ### Theorem 4.2.7 with the dimension, and the Mathlib structure on submanifolds -/

section Submanifold

variable {A : Set X}

/-- **Theorem 4.2.7 (preprint 4.18) in Mathlib's language** (gap G.102): a tame `X`, an
`n`-dimensional smooth submanifold `A` in good position at every point; then `A`, with the
subspace topology and the charted space `cornerChartedSpace` of its induced corner structure, is a
smooth manifold with boundary and corners, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ A`.
This is also the last sentence of Definition 9.3.6 for a sheet `Mᵢ` in good position. -/
theorem theorem_4_2_7_isManifold (hP : P.IsTame) (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A] (hgp : ∀ a ∈ A, P.IsGoodPositionAt A a) :
    letI := (subPolyfold hA.1.isSubMPolyfold).cornerChartedSpace
      (hA.hasCornerStructureOfDim_of_tame hP hgp)
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ A :=
  isManifold_cornerChartedSpace _

/-- **Remark 4.2.2 in Mathlib's language**: an `n`-dimensional smooth submanifold avoiding `∂X`
is a smooth manifold without boundary, `IsManifold (𝓡 n) ∞ A`. -/
theorem IsSubmanifoldOfDim.isManifold_of_degIndex_eq_zero (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A] (h0 : ∀ a ∈ A, P.degIndex a = 0) :
    letI := (subPolyfold hA.1.isSubMPolyfold).interiorChartedSpace
      (hA.hasCornerStructureOfDim_of_degIndex_eq_zero h0)
      (hA.1.subPolyfold_degIndex_eq_zero h0)
    IsManifold (𝓡 n) ∞ A :=
  isManifold_interiorChartedSpace _ _

end Submanifold

/-! ### Theorem 3.2.3: the solution set of the implicit function theorem, in Mathlib's language -/

/-! ### Lemma 9.4.6 for the sheets of an M-polyfold (gaps G.105, G.106) -/

/-- **Lemma 9.4.6 (2021 p. 431; 2017: Lemma 9.14) for a sheet of an M-polyfold**: on an
M-polyfold `X` with a corner structure of dimension `n` (a sheet `Mᵢ` with its induced structure,
Definition 9.3.6), the non-essential points `K ∖ K^e` (Definition 9.4.1) of any `K ⊆ X` form a
set of Lebesgue measure zero (Definition 9.4.5, `Polyfold.IsMeasureZero`, read in the charts of
`cornerChartedSpace`).  `lemma_9_4_6` through the bridge. -/
theorem lemma_9_4_6_cornerChartedSpace (h : P.HasCornerStructureOfDim n) (K : Set X) :
    letI := P.cornerChartedSpace h
    IsMeasureZero (modelWithCornersEuclideanQuadrant n)
      (K \ essentialSet (modelWithCornersEuclideanQuadrant n) K) := by
  let _ := P.cornerChartedSpace h
  have := P.isManifold_cornerChartedSpace h
  exact lemma_9_4_6 K

/-- **Lemma 9.4.6 for a tame `n`-dimensional sheet in good position** (Definition 9.3.6,
Theorem 4.2.7): for a tame `X`, an `n`-dimensional submanifold `A` in good position and any
`K ⊆ A`, `K ∖ K^e` has measure zero in `A`. -/
theorem lemma_9_4_6_sheet {A : Set X} (hP : P.IsTame) (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A] (hgp : ∀ a ∈ A, P.IsGoodPositionAt A a) (K : Set A) :
    letI := (subPolyfold hA.1.isSubMPolyfold).cornerChartedSpace
      (hA.hasCornerStructureOfDim_of_tame hP hgp)
    IsMeasureZero (modelWithCornersEuclideanQuadrant n)
      (K \ essentialSet (modelWithCornersEuclideanQuadrant n) K) :=
  lemma_9_4_6_cornerChartedSpace _ K

/-! ### Tame finite-dimensional submanifolds are manifolds with corners (Definition 9.3.6) -/

section TameCorners

variable {A : Set X}

/-- **`T₀O` is in good position in a tame centred chart** (the step of Definition 9.3.6's "in
particular" and of Theorem 4.1.2 (ii) that the text leaves implicit): for a tame retract
`(O, C, E)` (Definition 2.5.1) with `0 ∈ O`, the tangent space `N = T₀O = Dr(0)E` is in good
position to `C` (Definition 3.1.21).  *Proof*: `0` is a full corner of `C = T⁻¹([0,∞)ᵏ × W)`,
so the tame sc-complement `B ⊆ E_0 = T⁻¹(0 × W)` of `N` is a good complement
(`T(n + b)` and `T(n)` have the same first `k` coordinates), and `N ∩ C` has interior in `N`
(the `N`-component of `T⁻¹((1, …, 1), 0)` has all first coordinates `1`). -/
theorem _root_.Polyfold.IsTameRetract.isInGoodPosition_zero {E : ScBanach} {C O : Set (E 0)}
    (h : IsTameRetract E C O) (h0 : (0 : E 0) ∈ O) :
    ∃ N : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C O 0 ∧ IsInGoodPosition E C N := by
  obtain ⟨R, hR, hRt⟩ := h
  obtain ⟨k, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  have hRT := hRt k W T hT
  have h0R : (0 : E 1) ∈ E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, hR]; exact h0
  have h0s : (0 : E 1) ∈ E.smoothLvl 1 :=
    E.mem_smoothLvl_iff.2 fun j => ⟨0, by rw [map_zero, map_zero]⟩
  obtain ⟨B, hsplit, hB⟩ := hRT.exists_complement 0 h0R h0s
  set N : Submodule ℝ (E 0) := LinearMap.range (scDeriv R.U R 0 : E 0 →ₗ[ℝ] E 0)
  have hN : (N : Set (E 0)) = tangentSpace E C O 0 := by
    rw [← hR]; exact (tangentSpace_eq_coe_submodule R h0R).symm
  have hcompl : IsCompl N B := by
    have := hsplit.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have hB' : ∀ b ∈ B, ∀ i, (T 0 b).1 i = 0 := fun b hb i =>
    (mem_minimalSubspaceWith T).1 (hB hb) i (by simp)
  refine ⟨N, hN, ?_, B, hcompl, 1, one_pos, fun x _ p hp _ => ?_⟩
  · -- the interior of `N ∩ C` in `N` is nonempty
    set e : E 0 := (T 0).symm ((fun _ => 1 : Fin k → ℝ), 0)
    have he : e ∈ N ⊔ B := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨m, hm, b, hb, hmb⟩ := Submodule.mem_sup.1 he
    have hm1 : ∀ i, (T 0 m).1 i = 1 := by
      intro i
      have : (T 0 e).1 i = 1 := by
        simp only [e, ContinuousLinearEquiv.apply_symm_apply]
      rw [← hmb, map_add, Prod.fst_add, Pi.add_apply, hB' b hb i, add_zero] at this
      exact this
    refine ⟨⟨m, hm⟩, mem_interior.2 ⟨{v : N | ∀ i, 0 < (T 0 v.1).1 i}, fun v hv => ?_, ?_,
      fun i => by rw [hm1 i]; exact one_pos⟩⟩
    · rw [mem_preimage, hT]; exact fun i => (hv i).le
    · have : {v : N | ∀ i, 0 < (T 0 v.1).1 i} = ⋂ i, {v : N | 0 < (T 0 v.1).1 i} := by
        ext; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (((continuous_apply i).comp (continuous_fst.comp (T 0).continuous)).comp
          continuous_subtype_val)
  · -- the tame complement is a good complement
    have hkey : ∀ i, (T 0 (x + p)).1 i = (T 0 x).1 i := fun i => by
      rw [map_add, Prod.fst_add, Pi.add_apply, hB' p hp i, add_zero]
    rw [hT]
    show (∀ i, 0 ≤ (T 0 x).1 i) ↔ ∀ i, 0 ≤ (T 0 (x + p)).1 i
    simp only [hkey]

/-- **A tame `n`-dimensional submanifold has an induced corner structure of dimension `n`**
(Definition 9.3.6, last sentence; Theorem 4.1.2 (ii) ⇒ (i) for the induced structure): if the
induced structure on the `n`-dimensional submanifold `A` is tame (Definition 2.5.18,
`HasTameInducedStructure`), it has a corner structure of dimension `n`.  *Proof*: at `a ∈ A` take a
tame chart `ψ` of `A` centred at `a` (`IsTame.exists_centredChart`); `N = T₀O` is
finite-dimensional of dimension `n` (`tangentSpace_subPolyfold_chart`) and in good position to
`C` (`IsTameRetract.isInGoodPosition_zero`); Theorem 4.1.2's chart (`theorem_4_1_2_chart`) is a
corner chart modelled on `N`. -/
theorem IsSubmanifoldOfDim.hasCornerStructureOfDim_of_hasTameInducedStructure
    (hA : P.IsSubmanifoldOfDim A n) [ParacompactSpace A] (htame : P.HasTameInducedStructure A) :
    (subPolyfold hA.1.isSubMPolyfold).HasCornerStructureOfDim n := by
  set Q := subPolyfold hA.1.isSubMPolyfold
  obtain ⟨hY, hQ⟩ := htame
  have hQt : Q.IsTame := hQ
  intro a
  have h1 : a ∈ Q.levelSet 1 :=
    (hA.1.mem_levelSet_subPolyfold_iff a 1).2 (hA.1.mem_levelSet_one a.2)
  set x₀ := Q.levelMk 1 a h1
  obtain ⟨hsm, hmap⟩ := hA.1.proposition_4_2_3_four x₀
  have has : a ∈ Q.smoothSet := hA.1.proposition_4_2_3_one.2 a
  obtain ⟨ψ, hψ, haψ, hψ0, hret⟩ := hQt.exists_centredChart has
  have h0O : (0 : ψ.model.E 0) ∈ ψ.model.O := hψ0 ▸ ψ.mapsTo_model a haψ
  obtain ⟨N, hN, hgood⟩ := hret.isInGoodPosition_zero h0O
  have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
  obtain ⟨hfin, hdim⟩ := hA.tangentSpace_subPolyfold_chart hψ haψ hz
  rw [← hN, Submodule.span_eq] at hfin hdim
  obtain ⟨c, hc, hac, -, hcc⟩ :=
    @theorem_4_1_2_chart _ _ _ _ _ x₀ hsm hmap ψ hψ a haψ hψ0 N hfin hN hgood
  exact ⟨@CornerChartData.chart _ _ _ _ hfin c, hc, hac, hcc, hdim⟩

/-- **Definition 4.2.6 / Definition 9.3.6 in Mathlib's language**: a tame `n`-dimensional
submanifold `A` of an M-polyfold (its induced structure tame) is a smooth manifold with boundary
and corners, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ A`. -/
theorem IsSubmanifoldOfDim.isManifold_of_hasTameInducedStructure (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A] (htame : P.HasTameInducedStructure A) :
    letI := (subPolyfold hA.1.isSubMPolyfold).cornerChartedSpace
      (hA.hasCornerStructureOfDim_of_hasTameInducedStructure htame)
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ A :=
  isManifold_cornerChartedSpace _

end TameCorners

end MPolyfold

/-! ### Definition 9.3.6: the sheets of a tame branching structure -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- **Definition 9.3.6, last sentence (gap G.102)**: every sheet `Mᵢ` of a tame local branching
structure of dimension `n` has an induced corner structure of dimension `n`
(`hasCornerStructureOfDim_of_hasTameInducedStructure`). -/
theorem TameBranchingStructure.hasCornerStructureOfDim (T : X.TameBranchingStructure Θ x) {n : ℕ}
    (hdim : T.toLocalBranchingStructure.IsOfDim n) (i : T.ι) :
    letI := X.PObj.paracompactSpace_subtype (T.M i)
    (MPolyfold.subPolyfold (hdim i).1.isSubMPolyfold).HasCornerStructureOfDim n :=
  letI := X.PObj.paracompactSpace_subtype (T.M i)
  (hdim i).hasCornerStructureOfDim_of_hasTameInducedStructure (T.hasTameInducedStructure i)

/-- **Definition 9.3.6, last sentence, in Mathlib's language (gap G.102)**: "in particular every
`Mᵢ` is a manifold with boundary with corners": each sheet of a tame local branching structure of
dimension `n`, with the subspace topology and the charted space of its induced corner structure,
satisfies `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ (Mᵢ)`. -/
theorem TameBranchingStructure.isManifold (T : X.TameBranchingStructure Θ x) {n : ℕ}
    (hdim : T.toLocalBranchingStructure.IsOfDim n) (i : T.ι) :
    letI := X.PObj.paracompactSpace_subtype (T.M i)
    letI := (MPolyfold.subPolyfold (hdim i).1.isSubMPolyfold).cornerChartedSpace
      (T.hasCornerStructureOfDim hdim i)
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ (T.M i) :=
  letI := X.PObj.paracompactSpace_subtype (T.M i)
  MPolyfold.isManifold_cornerChartedSpace _

/-- **Lemma 9.4.6 for the sheets of a tame branching structure** (gaps G.105, G.106): for any
`K ⊆ Mᵢ`, the non-essential points `K ∖ K^e` form a Lebesgue null set in the sheet `Mᵢ`. -/
theorem TameBranchingStructure.lemma_9_4_6 (T : X.TameBranchingStructure Θ x) {n : ℕ}
    (hdim : T.toLocalBranchingStructure.IsOfDim n) (i : T.ι) (K : Set (T.M i)) :
    letI := X.PObj.paracompactSpace_subtype (T.M i)
    letI := (MPolyfold.subPolyfold (hdim i).1.isSubMPolyfold).cornerChartedSpace
      (T.hasCornerStructureOfDim hdim i)
    IsMeasureZero (modelWithCornersEuclideanQuadrant n)
      (K \ essentialSet (modelWithCornersEuclideanQuadrant n) K) :=
  letI := X.PObj.paracompactSpace_subtype (T.M i)
  MPolyfold.lemma_9_4_6_cornerChartedSpace _ K

end EpGroupoid

end Polyfold
