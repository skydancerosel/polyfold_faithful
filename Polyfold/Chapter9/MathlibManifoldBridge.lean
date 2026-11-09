import Polyfold.Chapter9.GeneralLevelZero
import Polyfold.Chapter9.BranchingGeometryManifold
import Polyfold.Chapter3.GlobalIFTTheorems

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
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module Manifold WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Partial quadrants of finite-dimensional spaces in coordinates -/

section Coordinates

/-- The coordinate partial quadrant `{y ∈ ℝⁿ | yᵢ ≥ 0 for i ∈ S}`. -/
def coordQuadrant (n : ℕ) (S : Set (Fin n)) : Set (Fin n → ℝ) := {y | ∀ i ∈ S, 0 ≤ y i}

/-- **A partial quadrant of a finite-dimensional space in coordinates**: if `E₀` has dimension
`n` and `C ⊆ E₀` is a partial quadrant (Definition 1.1.11, `C = T⁻¹([0,∞)ᵏ × W)`), there is a
continuous linear isomorphism `Ψ : E₀ ≃ ℝⁿ` and a set `S` of coordinates with
`C = Ψ⁻¹{y | yᵢ ≥ 0 for i ∈ S}` (the basis of `ℝᵏ × W` made of the standard basis of `ℝᵏ` and a
basis of `W`, reindexed by `Fin n`). -/
theorem exists_cle_partialQuadrant {E : ScBanach} [FiniteDimensional ℝ (E 0)] {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) {n : ℕ} (hn : finrank ℝ (E 0) = n) :
    ∃ (Ψ : E 0 ≃L[ℝ] (Fin n → ℝ)) (S : Set (Fin n)), C = Ψ ⁻¹' coordQuadrant n S := by
  obtain ⟨k, W, T, hT⟩ := hC
  let T₀ : E 0 ≃L[ℝ] (Fin k → ℝ) × W 0 := T 0
  have : FiniteDimensional ℝ ((Fin k → ℝ) × W 0) := T₀.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ (W 0) :=
    Module.Finite.of_injective (LinearMap.inr ℝ (Fin k → ℝ) (W 0)) LinearMap.inr_injective
  let b₁ : Basis (Fin k) ℝ (Fin k → ℝ) := Pi.basisFun ℝ (Fin k)
  let b₂ : Basis (Fin (finrank ℝ (W 0))) ℝ (W 0) := Module.finBasis ℝ (W 0)
  let b : Basis (Fin k ⊕ Fin (finrank ℝ (W 0))) ℝ ((Fin k → ℝ) × W 0) := b₁.prod b₂
  let b₀ : Basis (Fin n) ℝ ((Fin k → ℝ) × W 0) :=
    (Module.finBasisOfFinrankEq ℝ (E 0) hn).map T₀.toLinearEquiv
  let σ : Fin k ⊕ Fin (finrank ℝ (W 0)) ≃ Fin n := b.indexEquiv b₀
  let Ψ : E 0 ≃L[ℝ] (Fin n → ℝ) := T₀.trans (b.reindex σ).equivFun.toContinuousLinearEquiv
  refine ⟨Ψ, range (σ ∘ Sum.inl), ?_⟩
  have hΨ : ∀ (v : E 0) (j : Fin k), Ψ v (σ (Sum.inl j)) = (T 0 v).1 j := by
    intro v j
    change (b.reindex σ).equivFun (T₀ v) (σ (Sum.inl j)) = (T 0 v).1 j
    rw [Basis.equivFun_apply, Basis.repr_reindex_apply, Equiv.symm_apply_apply,
      Basis.prod_repr_inl, Pi.basisFun_repr]
  ext v
  rw [hT]
  constructor
  · rintro hv _ ⟨j, rfl⟩
    rw [Function.comp_apply, hΨ v j]
    exact hv j
  · intro hv j
    have := hv (σ (Sum.inl j)) ⟨j, rfl⟩
    rwa [hΨ v j] at this

/-- The sup norm bounds each coordinate: `|yᵢ| ≤ ‖y‖` on `Fin n → ℝ`. -/
theorem abs_apply_le_norm_pi {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : |y i| ≤ ‖y‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i

end Coordinates

/-! ### Corner charts in coordinates -/

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **A corner chart of `X` of dimension `n` in coordinates**: a corner chart `χ` of the
M-polyfold structure (Definition 4.1.1, `MChart.IsCornerChart`), an open piece `s` of its
domain, a continuous linear isomorphism `Ψ : E₀ ≃ ℝⁿ` and a translation `c ∈ ℝⁿ` such that the
coordinate chart `x ↦ Ψ(χ(x)) + c` maps `s` onto `W ∩ [0,∞)ⁿ` for an open `W ⊆ ℝⁿ`.  The Mathlib
chart `toQuadrantChart` is this coordinate chart, with values in `EuclideanQuadrant n`. -/
structure CornerCoords (P : MPolyfold X) (n : ℕ) where
  /-- The corner chart `χ`. -/
  χ : MChart X
  isChart : P.IsChart χ
  isCornerChart : χ.IsCornerChart
  /-- The open piece `s ⊆ dom χ`. -/
  s : Set X
  isOpen_s : IsOpen s
  s_subset : s ⊆ χ.source
  /-- The linear coordinates `Ψ : E₀ ≃ ℝⁿ`. -/
  Ψ : χ.model.E 0 ≃L[ℝ] (Fin n → ℝ)
  /-- The translation `c`. -/
  c : Fin n → ℝ
  /-- The open set `W ⊆ ℝⁿ` with `(Ψ ∘ χ + c)(s) = W ∩ [0,∞)ⁿ`. -/
  W : Set (Fin n → ℝ)
  isOpen_W : IsOpen W
  image_s : (fun v => Ψ v + c) '' (χ '' s) = W ∩ {y | ∀ i, 0 ≤ y i}

namespace CornerCoords

variable {P : MPolyfold X} {n : ℕ} (κ : CornerCoords P n)

/-- The coordinate chart `Ψ ∘ χ + c : X → ℝⁿ`. -/
def coord (x : X) : Fin n → ℝ := κ.Ψ (κ.χ x) + κ.c

/-- The inverse `y ↦ χ⁻¹(Ψ⁻¹(y − c))` of the coordinate chart. -/
def coordInv (y : Fin n → ℝ) : X := κ.χ.symm (κ.Ψ.symm (y - κ.c))

theorem coord_image : κ.coord '' κ.s = κ.W ∩ {y | ∀ i, 0 ≤ y i} := by
  rw [← κ.image_s, image_image]; rfl

theorem coord_mem_W {x : X} (hx : x ∈ κ.s) : κ.coord x ∈ κ.W :=
  (κ.coord_image ▸ mem_image_of_mem κ.coord hx).1

theorem coord_nonneg {x : X} (hx : x ∈ κ.s) (i : Fin n) : 0 ≤ κ.coord x i :=
  (κ.coord_image ▸ mem_image_of_mem κ.coord hx).2 i

theorem coordInv_coord {x : X} (hx : x ∈ κ.s) : κ.coordInv (κ.coord x) = x := by
  simp only [coordInv, coord, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  exact κ.χ.symm_apply_apply (κ.s_subset hx)

/-- A point of `W ∩ [0,∞)ⁿ` is the coordinate of a point of `s`. -/
theorem exists_coord_eq {y : Fin n → ℝ} (hyW : y ∈ κ.W) (hy : ∀ i, 0 ≤ y i) :
    ∃ x ∈ κ.s, κ.coord x = y := by
  have : y ∈ κ.coord '' κ.s := by rw [κ.coord_image]; exact ⟨hyW, hy⟩
  exact this

theorem coordInv_mem {y : Fin n → ℝ} (hyW : y ∈ κ.W) (hy : ∀ i, 0 ≤ y i) :
    κ.coordInv y ∈ κ.s := by
  obtain ⟨x, hx, rfl⟩ := κ.exists_coord_eq hyW hy
  rw [κ.coordInv_coord hx]; exact hx

theorem coord_coordInv {y : Fin n → ℝ} (hyW : y ∈ κ.W) (hy : ∀ i, 0 ≤ y i) :
    κ.coord (κ.coordInv y) = y := by
  obtain ⟨x, hx, rfl⟩ := κ.exists_coord_eq hyW hy
  rw [κ.coordInv_coord hx]

/-- The chart value `Ψ⁻¹(y − c) = χ(χ⁻¹(Ψ⁻¹(y − c)))` of a coordinate point. -/
theorem apply_coordInv {y : Fin n → ℝ} (hyW : y ∈ κ.W) (hy : ∀ i, 0 ≤ y i) :
    κ.χ (κ.coordInv y) = κ.Ψ.symm (y - κ.c) := by
  obtain ⟨x, hx, rfl⟩ := κ.exists_coord_eq hyW hy
  rw [κ.coordInv_coord hx]
  simp only [coord, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]

theorem continuousOn_coord : ContinuousOn κ.coord κ.s :=
  ((κ.Ψ.continuous.comp_continuousOn (κ.χ.continuousOn_toFun.mono κ.s_subset)).add
    continuousOn_const)

theorem continuousOn_coordInv : ContinuousOn κ.coordInv (κ.W ∩ {y | ∀ i, 0 ≤ y i}) := by
  refine κ.χ.continuousOn_invFun.comp
    (κ.Ψ.symm.continuous.comp (continuous_id.sub continuous_const)).continuousOn ?_
  rintro y ⟨hyW, hy⟩
  dsimp only
  rw [← κ.apply_coordInv hyW hy]
  exact κ.χ.mapsTo_model _ (κ.s_subset (κ.coordInv_mem hyW hy))

/-! #### The transition map between two coordinate charts -/

variable (κ' : CornerCoords P n)

/-- The transition map `κ'.coord ∘ κ.coordInv` between two coordinate charts, as a total map of
`ℝⁿ`; it is `χ'.transition χ` read in coordinates. -/
def trans (y : Fin n → ℝ) : Fin n → ℝ := κ'.Ψ (κ.χ.transition κ'.χ (κ.Ψ.symm (y - κ.c))) + κ'.c

theorem trans_eq {y : Fin n → ℝ} (hyW : y ∈ κ.W) (hy : ∀ i, 0 ≤ y i) :
    κ.trans κ' y = κ'.coord (κ.coordInv y) := by
  unfold trans coord
  rw [← κ.apply_coordInv hyW hy, κ.χ.transition_apply κ'.χ (κ.s_subset (κ.coordInv_mem hyW hy))]

/-- **The transition maps are `C^∞`** (Definition 4.1.1: "classically smooth"), on the
coordinate overlap `{y ∈ W ∩ [0,∞)ⁿ | κ.coordInv y ∈ s'}` (one-sided derivatives at the
boundary), from `MChart.IsCornerChart.contDiffOn_transition` composed with the affine coordinate
changes. -/
theorem contDiffOn_trans :
    ContDiffOn ℝ ∞ (κ.trans κ')
      ((κ.W ∩ {y | ∀ i, 0 ≤ y i}) ∩ κ.coordInv ⁻¹' κ'.s) := by
  have hcomp : κ.χ.Compatible κ'.χ := IsChart.compatible P κ.isChart κ'.isChart
  have htr := κ.isCornerChart.contDiffOn_transition κ'.isCornerChart hcomp
  have hin : ContDiff ℝ ∞ fun y : Fin n → ℝ => κ.Ψ.symm (y - κ.c) :=
    κ.Ψ.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hout : ContDiff ℝ ∞ fun z : κ'.χ.model.E 0 => κ'.Ψ z + κ'.c :=
    κ'.Ψ.contDiff.add contDiff_const
  refine hout.comp_contDiffOn (htr.comp hin.contDiffOn ?_)
  rintro y ⟨⟨hyW, hy⟩, hy'⟩
  dsimp only
  rw [← κ.apply_coordInv hyW hy]
  exact κ.χ.mem_overlap κ'.χ (κ.s_subset (κ.coordInv_mem hyW hy)) (κ'.s_subset hy')

/-! #### Existence of coordinates -/

/-- **A coordinate piece misses the boundary** if its coordinate image `W ∩ [0,∞)ⁿ` is all of
`W`, i.e. open in `ℝⁿ`. -/
def IsInterior : Prop := κ.W ⊆ {y | ∀ i, 0 ≤ y i}

theorem IsInterior.coord_image (hκ : κ.IsInterior) : κ.coord '' κ.s = κ.W := by
  rw [κ.coord_image]; exact inter_eq_left.2 hκ

/-- **Every corner chart of dimension `n` has coordinates near each point of its domain**: for a
corner chart `χ` (Definition 4.1.1) with `dim E₀ = n`, `x ∈ dom χ` and an open `B₀ ∋ χ(x)` in
`E₀`, there are coordinates `κ` with chart `χ`, `x` in the piece `s`, and the piece inside the
boundary-free part if `B₀ ⊆ C`.  *Construction*: `exists_cle_partialQuadrant` gives `Ψ` and `S`
with `C = Ψ⁻¹{yᵢ ≥ 0, i ∈ S}`; the piece is `s = {x' ∈ dom χ | χ(x') ∈ B₀, ‖Ψ χ(x')‖ < R}` with
`R = ‖Ψ χ(x)‖ + 1`, and the translation `c` is `R` in the coordinates outside `S` and `0` in
those of `S`, so that `Ψ χ(s) + c ⊆ [0,∞)ⁿ`. -/
theorem exists_mem {χ : MChart X} (hχ : P.IsChart χ) (hc : χ.IsCornerChart)
    (hn : finrank ℝ (χ.model.E 0) = n) {x : X} (hx : x ∈ χ.source) {B₀ : Set (χ.model.E 0)}
    (hB₀ : IsOpen B₀) (hxB₀ : χ x ∈ B₀) :
    ∃ κ : CornerCoords P n, κ.χ = χ ∧ x ∈ κ.s ∧ (B₀ ⊆ χ.model.C → κ.IsInterior) := by
  have := hc.finiteDimensional
  have hU := hc.isRelOpenInQuadrant
  obtain ⟨O₀, hO₀, hOeq⟩ := hU.relOpen
  obtain ⟨Ψ, S, hC⟩ := exists_cle_partialQuadrant hU.isPartialQuadrant hn
  set R : ℝ := ‖Ψ (χ x)‖ + 1 with hR
  set B : Set (χ.model.E 0) := B₀ ∩ Ψ ⁻¹' Metric.ball 0 R with hB
  have hBo : IsOpen B := hB₀.inter (Metric.isOpen_ball.preimage Ψ.continuous)
  set s : Set X := χ.source ∩ χ ⁻¹' B with hs
  have hso : IsOpen s := χ.continuousOn_toFun.isOpen_inter_preimage χ.isOpen_source hBo
  set c : Fin n → ℝ := Sᶜ.indicator fun _ => R with hcdef
  have hc_mem : ∀ i ∈ S, c i = 0 := fun i hi => Set.indicator_of_notMem (by simpa using hi) _
  have hc_nmem : ∀ i ∉ S, c i = R := fun i hi => Set.indicator_of_mem (by simpa using hi) _
  set W : Set (Fin n → ℝ) := (fun y => y - c) ⁻¹' (Ψ '' (O₀ ∩ B)) with hW
  have hWo : IsOpen W :=
    (Ψ.isOpenMap _ (hO₀.inter hBo)).preimage (continuous_id.sub continuous_const)
  -- the coordinates of a point of `B ∩ C` are nonnegative
  have hnonneg : ∀ v ∈ B, v ∈ χ.model.C → ∀ i, 0 ≤ (Ψ v + c) i := by
    intro v hvB hvC i
    by_cases hi : i ∈ S
    · rw [Pi.add_apply, hc_mem i hi, add_zero]
      rw [hC] at hvC
      exact hvC i hi
    · rw [Pi.add_apply, hc_nmem i hi]
      have h1 : ‖Ψ v‖ < R := by simpa using hvB.2
      have h2 := abs_apply_le_norm_pi (Ψ v) i
      linarith [neg_abs_le (Ψ v i)]
  -- the image of `s`
  have himg : (fun v => Ψ v + c) '' (χ '' s) = W ∩ {y | ∀ i, 0 ≤ y i} := by
    ext y
    constructor
    · rintro ⟨_, ⟨x', ⟨hx's, hx'B⟩, rfl⟩, rfl⟩
      have hO : χ x' ∈ χ.model.O := χ.mapsTo_model x' hx's
      rw [hOeq] at hO
      refine ⟨⟨χ x', ⟨hO.1, hx'B⟩, ?_⟩, hnonneg _ hx'B hO.2⟩
      simp
    · rintro ⟨⟨v, ⟨hvO, hvB⟩, hv⟩, hy⟩
      have hv' : Ψ v = y - c := hv
      have hvC : v ∈ χ.model.C := by
        rw [hC]
        intro i hi
        have := hy i
        rw [← sub_add_cancel y c, Pi.add_apply, ← hv', hc_mem i hi, add_zero] at this
        exact this
      have hvO' : v ∈ χ.model.O := by rw [hOeq]; exact ⟨hvO, hvC⟩
      refine ⟨v, ⟨χ.symm v, ⟨χ.symm_mapsTo hvO', ?_⟩, χ.apply_symm_apply hvO'⟩, ?_⟩
      · show χ (χ.symm v) ∈ B
        rw [χ.apply_symm_apply hvO']; exact hvB
      · show Ψ v + c = y
        rw [hv', sub_add_cancel]
  refine ⟨⟨χ, hχ, hc, s, hso, inter_subset_left, Ψ, c, W, hWo, himg⟩, rfl, ⟨hx, hxB₀, ?_⟩, ?_⟩
  · show Ψ (χ x) ∈ Metric.ball 0 R
    rw [Metric.mem_ball, dist_zero_right, hR]; linarith
  · intro hB₀C y hyW
    obtain ⟨v, ⟨-, hvB⟩, hv⟩ := hyW
    have hv' : Ψ v = y - c := hv
    have : y = Ψ v + c := by rw [hv', sub_add_cancel]
    rw [this]
    exact hnonneg v hvB (hB₀C hvB.1)

/-! #### The Mathlib charts -/

/-- The quadrant model: `I q = q` for `q ∈ [0,∞)ⁿ ⊆ ℝⁿ`, `I⁻¹ y = max(y, 0)`. -/
theorem quadrant_apply (q : EuclideanQuadrant n) :
    (modelWithCornersEuclideanQuadrant n) q = q.1 := rfl

theorem quadrant_right_inv {y : EuclideanSpace ℝ (Fin n)} (hy : ∀ i, 0 ≤ y i) :
    (modelWithCornersEuclideanQuadrant n) ((modelWithCornersEuclideanQuadrant n).symm y) = y :=
  (modelWithCornersEuclideanQuadrant n).right_inv ⟨⟨y, hy⟩, rfl⟩

/-- **The Mathlib chart `X → [0,∞)ⁿ` of a coordinate corner chart**: `x ↦ Ψ χ(x) + c` on the
piece `s`, with values in `EuclideanQuadrant n`, an open partial homeomorphism with target
`{q | q ∈ W}`. -/
def toQuadrantChart : OpenPartialHomeomorph X (EuclideanQuadrant n) where
  toFun x := (modelWithCornersEuclideanQuadrant n).symm (toLp 2 (κ.coord x))
  invFun q := κ.coordInv (ofLp q.1)
  source := κ.s
  target := {q : EuclideanQuadrant n | ofLp q.1 ∈ κ.W}
  map_source' x hx := by
    show ofLp ((modelWithCornersEuclideanQuadrant n)
      ((modelWithCornersEuclideanQuadrant n).symm (toLp 2 (κ.coord x)))) ∈ κ.W
    rw [quadrant_right_inv (fun i => κ.coord_nonneg hx i)]
    exact κ.coord_mem_W hx
  map_target' q hq := κ.coordInv_mem hq fun i => q.2 i
  left_inv' x hx := by
    show κ.coordInv (ofLp ((modelWithCornersEuclideanQuadrant n)
      ((modelWithCornersEuclideanQuadrant n).symm (toLp 2 (κ.coord x))))) = x
    rw [quadrant_right_inv (fun i => κ.coord_nonneg hx i)]
    exact κ.coordInv_coord hx
  right_inv' q hq := by
    show (modelWithCornersEuclideanQuadrant n).symm
      (toLp 2 (κ.coord (κ.coordInv (ofLp q.1)))) = q
    rw [κ.coord_coordInv hq fun i => q.2 i]
    exact (modelWithCornersEuclideanQuadrant n).left_inv q
  open_source := κ.isOpen_s
  open_target := κ.isOpen_W.preimage ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  continuousOn_toFun := (modelWithCornersEuclideanQuadrant n).continuous_symm.comp_continuousOn
    ((PiLp.continuous_toLp 2 _).comp_continuousOn κ.continuousOn_coord)
  continuousOn_invFun := κ.continuousOn_coordInv.comp
    ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).continuousOn
    fun q hq => ⟨hq, fun i => q.2 i⟩

@[simp] theorem toQuadrantChart_source : κ.toQuadrantChart.source = κ.s := rfl

theorem toQuadrantChart_apply (x : X) :
    κ.toQuadrantChart x = (modelWithCornersEuclideanQuadrant n).symm (toLp 2 (κ.coord x)) := rfl

theorem toQuadrantChart_symm_apply (q : EuclideanQuadrant n) :
    κ.toQuadrantChart.symm q = κ.coordInv (ofLp q.1) := rfl

theorem mem_toQuadrantChart_target {q : EuclideanQuadrant n} :
    q ∈ κ.toQuadrantChart.target ↔ ofLp q.1 ∈ κ.W := Iff.rfl

/-- **The Mathlib chart `X → ℝⁿ` of a coordinate corner chart missing the boundary**:
`x ↦ Ψ χ(x) + c` on `s`, with values in `EuclideanSpace ℝ (Fin n)` and the open target `W`. -/
def toEuclideanChart (hκ : κ.IsInterior) : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) where
  toFun x := toLp 2 (κ.coord x)
  invFun y := κ.coordInv (ofLp y)
  source := κ.s
  target := {y | ofLp y ∈ κ.W}
  map_source' x hx := κ.coord_mem_W hx
  map_target' y hy := κ.coordInv_mem hy (hκ hy)
  left_inv' x hx := κ.coordInv_coord hx
  right_inv' y hy := by
    show toLp 2 (κ.coord (κ.coordInv (ofLp y))) = y
    rw [κ.coord_coordInv hy (hκ hy)]
  open_source := κ.isOpen_s
  open_target := κ.isOpen_W.preimage (PiLp.continuous_ofLp 2 _)
  continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn κ.continuousOn_coord
  continuousOn_invFun := κ.continuousOn_coordInv.comp (PiLp.continuous_ofLp 2 _).continuousOn
    fun y hy => ⟨hy, hκ hy⟩

@[simp] theorem toEuclideanChart_source (hκ : κ.IsInterior) :
    (κ.toEuclideanChart hκ).source = κ.s := rfl

theorem toEuclideanChart_apply (hκ : κ.IsInterior) (x : X) :
    κ.toEuclideanChart hκ x = toLp 2 (κ.coord x) := rfl

/-! #### The transition maps of the Mathlib charts are `C^∞` -/

/-- The transition map of two coordinate charts read in `EuclideanSpace ℝ (Fin n)`. -/
theorem contDiffOn_trans_euclidean :
    ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (toLp 2 (κ.trans κ' (ofLp y)) :
      EuclideanSpace ℝ (Fin n)))
      (ofLp ⁻¹' ((κ.W ∩ {y | ∀ i, 0 ≤ y i}) ∩ κ.coordInv ⁻¹' κ'.s)) := by
  have h1 : ContDiff ℝ ∞ fun y : EuclideanSpace ℝ (Fin n) => ofLp y :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).contDiff
  have h2 : ContDiff ℝ ∞ fun f : Fin n → ℝ => (toLp 2 f : EuclideanSpace ℝ (Fin n)) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).symm.contDiff
  exact h2.comp_contDiffOn ((κ.contDiffOn_trans κ').comp h1.contDiffOn (mapsTo_preimage _ _))

/-- **The transition maps between the quadrant charts are `C^∞`** in the sense of Mathlib's
`contDiffGroupoid ∞ (modelWithCornersEuclideanQuadrant n)`. -/
theorem contDiffOn_quadrant_trans :
    ContDiffOn ℝ ∞ ((modelWithCornersEuclideanQuadrant n) ∘
        (κ.toQuadrantChart.symm ≫ₕ κ'.toQuadrantChart) ∘
        (modelWithCornersEuclideanQuadrant n).symm)
      ((modelWithCornersEuclideanQuadrant n).symm ⁻¹'
        (κ.toQuadrantChart.symm ≫ₕ κ'.toQuadrantChart).source ∩
        range (modelWithCornersEuclideanQuadrant n)) := by
  set I := modelWithCornersEuclideanQuadrant n
  refine ((κ.contDiffOn_trans_euclidean κ').mono ?_).congr ?_
  · rintro _ ⟨hy, ⟨q, rfl⟩⟩
    rw [mem_preimage, I.left_inv, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] at hy
    exact ⟨⟨hy.1, fun i => q.2 i⟩, hy.2⟩
  · rintro _ ⟨hy, ⟨q, rfl⟩⟩
    rw [mem_preimage, I.left_inv, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] at hy
    simp only [Function.comp_apply, I.left_inv, OpenPartialHomeomorph.trans_apply]
    show I (I.symm (toLp 2 (κ'.coord (κ.coordInv (ofLp q.1))))) = toLp 2 (κ.trans κ' (ofLp q.1))
    rw [quadrant_right_inv (fun i => κ'.coord_nonneg hy.2 i), κ.trans_eq κ' hy.1 fun i => q.2 i]

/-- **The transition maps between the Euclidean charts are `C^∞`** in the sense of Mathlib's
`contDiffGroupoid ∞ (𝓡 n)`. -/
theorem contDiffOn_euclidean_trans (hκ : κ.IsInterior) (hκ' : κ'.IsInterior) :
    ContDiffOn ℝ ∞ ((𝓡 n) ∘ ((κ.toEuclideanChart hκ).symm ≫ₕ κ'.toEuclideanChart hκ') ∘
        (𝓡 n).symm)
      ((𝓡 n).symm ⁻¹' ((κ.toEuclideanChart hκ).symm ≫ₕ κ'.toEuclideanChart hκ').source ∩
        range (𝓡 n)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.comp_id, Function.id_comp]
  refine ((κ.contDiffOn_trans_euclidean κ').mono ?_).congr ?_
  · intro y hy
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
    exact ⟨⟨hy.1, hκ hy.1⟩, hy.2⟩
  · intro y hy
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
    rw [OpenPartialHomeomorph.trans_apply]
    show toLp 2 (κ'.coord (κ.coordInv (ofLp y))) = toLp 2 (κ.trans κ' (ofLp y))
    rw [κ.trans_eq κ' hy.1 (hκ hy.1)]

end CornerCoords

/-! ### Definition 4.1.1 with a fixed dimension, and the bridge -/

variable (P : MPolyfold X) (n : ℕ) in
/-- **Definition 4.1.1 (preprint 4.1) with the dimension `n`**: every point of `X` lies in a
corner chart (`MChart.IsCornerChart`) of the M-polyfold structure of dimension `n`.  It is the
local form of `IsManifoldWithCorners n` (`IsManifoldWithCorners.hasCornerStructureOfDim`), and
implies `HasCornerStructure` (`HasCornerStructureOfDim.hasCornerStructure`). -/
def HasCornerStructureOfDim : Prop :=
  ∀ x : X, ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧ χ.IsCornerChart ∧
    finrank ℝ (χ.model.E 0) = n

variable {P : MPolyfold X} {n : ℕ}

theorem HasCornerStructureOfDim.hasCornerStructure (h : P.HasCornerStructureOfDim n) :
    P.HasCornerStructure :=
  hasCornerStructure_iff.2 fun x => by
    obtain ⟨χ, hχ, hx, hc, -⟩ := h x
    exact ⟨χ, hχ, hx, hc⟩

/-- An `n`-dimensional manifold with corners (Theorem 3.2.3's `IsManifoldWithCorners n`) has a
corner structure of dimension `n` (`MChart.exists_isCornerChart_of_finiteDimensional`: the
constant sc-structure is no restriction). -/
theorem IsManifoldWithCorners.hasCornerStructureOfDim (h : P.IsManifoldWithCorners n) :
    P.HasCornerStructureOfDim n := by
  obtain ⟨A, hA, hc⟩ := h
  intro x
  obtain ⟨χ, hχA, hx⟩ := A.cover x
  obtain ⟨hU, hfin, hn⟩ := hc χ hχA
  obtain ⟨χ', hχ', hsrc, hc', hn'⟩ :=
    MChart.exists_isCornerChart_of_finiteDimensional (P.isChart_of_mem_equiv hA hχA) hU hfin
  exact ⟨χ', hχ', hsrc ▸ hx, hc', hn'.trans hn⟩

/-- Every point has coordinate corner charts. -/
theorem HasCornerStructureOfDim.exists_cornerCoords (h : P.HasCornerStructureOfDim n) (x : X) :
    ∃ κ : CornerCoords P n, x ∈ κ.s := by
  obtain ⟨χ, hχ, hx, hc, hn⟩ := h x
  obtain ⟨κ, -, hxκ, -⟩ := CornerCoords.exists_mem hχ hc hn hx isOpen_univ (mem_univ _)
  exact ⟨κ, hxκ⟩

/-- **Without boundary** (`d_X ≡ 0`, Definition 2.5.1), every point has coordinate corner charts
missing the boundary: in a corner chart `χ` (a tame retract) `d_X(x) = 0` is read as
`χ(x) ∈ int C` (`mem_interior_of_degIndex_eq_zero`), and `B₀ = int C`. -/
theorem HasCornerStructureOfDim.exists_cornerCoords_isInterior (h : P.HasCornerStructureOfDim n)
    (h0 : ∀ x, P.degIndex x = 0) (x : X) :
    ∃ κ : CornerCoords P n, x ∈ κ.s ∧ κ.IsInterior := by
  obtain ⟨χ, hχ, hx, hc, hn⟩ := h x
  have hU := hc.isRelOpenInQuadrant
  have hxC : χ x ∈ χ.model.C := by
    obtain ⟨O₀, -, hOeq⟩ := hU.relOpen
    have := χ.mapsTo_model x hx
    rw [hOeq] at this
    exact this.2
  have hint : χ x ∈ interior χ.model.C := by
    refine Polyfold.mem_interior_of_degIndex_eq_zero hU.isPartialQuadrant hxC ?_
    have := P.degIndex_eq_chartDegIndex_of_isTameRetract hχ hc.isTameRetract hx
    rw [h0 x] at this
    exact this.symm
  obtain ⟨κ, -, hxκ, hκ⟩ := CornerCoords.exists_mem hχ hc hn hx _root_.isOpen_interior hint
  exact ⟨κ, hxκ, hκ interior_subset⟩

/-- **The bridge, Definition 4.1.1 → Mathlib (gap G.102)**: an M-polyfold with a corner structure
of dimension `n` is a charted space modelled on the quadrant `[0,∞)ⁿ` (`EuclideanQuadrant n`),
with the Mathlib charts `CornerCoords.toQuadrantChart` of the coordinate corner charts. -/
@[instance_reducible]
def cornerChartedSpace (h : P.HasCornerStructureOfDim n) : ChartedSpace (EuclideanQuadrant n) X where
  atlas := range fun κ : CornerCoords P n => κ.toQuadrantChart
  chartAt x := (h.exists_cornerCoords x).choose.toQuadrantChart
  mem_chart_source x := (h.exists_cornerCoords x).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

/-- **The bridge, Definition 4.1.1 → Mathlib (gap G.102)**: with the charted space
`cornerChartedSpace`, `X` is a smooth (`C^∞`) manifold with boundary and corners in Mathlib's
sense, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ X` (the transition maps are `C^∞`,
`CornerCoords.contDiffOn_quadrant_trans`). -/
theorem isManifold_cornerChartedSpace (h : P.HasCornerStructureOfDim n) :
    letI := P.cornerChartedSpace h
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ X := by
  let _ := P.cornerChartedSpace h
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨κ, rfl⟩ ⟨κ', rfl⟩
  exact κ.contDiffOn_quadrant_trans κ'

/-- **The bridge without boundary**: an M-polyfold with a corner structure of dimension `n` and
`d_X ≡ 0` is a charted space modelled on `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`). -/
@[instance_reducible]
def interiorChartedSpace (h : P.HasCornerStructureOfDim n) (h0 : ∀ x, P.degIndex x = 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) X where
  atlas := {e | ∃ (κ : CornerCoords P n) (hκ : κ.IsInterior), e = κ.toEuclideanChart hκ}
  chartAt x := (h.exists_cornerCoords_isInterior h0 x).choose.toEuclideanChart
    (h.exists_cornerCoords_isInterior h0 x).choose_spec.2
  mem_chart_source x := (h.exists_cornerCoords_isInterior h0 x).choose_spec.1
  chart_mem_atlas _ := ⟨_, _, rfl⟩

/-- **The bridge without boundary**: with the charted space `interiorChartedSpace`, `X` is a
smooth manifold without boundary in Mathlib's sense, `IsManifold (𝓡 n) ∞ X`
(`CornerCoords.contDiffOn_euclidean_trans`). -/
theorem isManifold_interiorChartedSpace (h : P.HasCornerStructureOfDim n)
    (h0 : ∀ x, P.degIndex x = 0) :
    letI := P.interiorChartedSpace h h0
    IsManifold (𝓡 n) ∞ X := by
  let _ := P.interiorChartedSpace h h0
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨κ, hκ, rfl⟩ ⟨κ', hκ', rfl⟩
  exact κ.contDiffOn_euclidean_trans κ' hκ hκ'

/-! ### Theorem 4.2.7 with the dimension, and the Mathlib structure on submanifolds -/

section Submanifold

variable {A : Set X}

/-- **The corner charts of an `n`-dimensional submanifold have dimension `n`**
(`hasCornerStructure_of_centred_isInGoodPosition` with the dimension): if `A` is an
`n`-dimensional submanifold (Remark 9.1.1, `IsSubmanifoldOfDim`) and every `a ∈ A` lies in a
chart `ψ` of `X` centred at `a` in which `N = T₀(ψ(W ∩ A))` is in good position to `C`, the
induced structure on `A` has a corner structure of dimension `n`.  *Proof*: Theorem 4.1.2's chart
(`theorem_4_1_2_chart`) is modelled on `N`, and `dim N = dim T_aA = n` (`HasDimAt.finrank_eq`). -/
theorem IsSubmanifoldOfDim.hasCornerStructureOfDim_of_centred (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A]
    (h : ∀ a (ha : a ∈ A), ∃ ψ : MChart X, P.IsChart ψ ∧ a ∈ ψ.source ∧ ψ a = 0 ∧
      ∀ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C (ψ '' ((hA.1.data ha).toSubData.shrink ψ ∩ A)) 0 →
        IsInGoodPosition ψ.model.E ψ.model.C N) :
    (subPolyfold hA.1.isSubMPolyfold).HasCornerStructureOfDim n := by
  intro a
  have h1 : a ∈ (subPolyfold hA.1.isSubMPolyfold).levelSet 1 :=
    (hA.1.mem_levelSet_subPolyfold_iff a 1).2 (hA.1.mem_levelSet_one a.2)
  set x₀ := (subPolyfold hA.1.isSubMPolyfold).levelMk 1 a h1
  obtain ⟨hsm, hmap⟩ := hA.1.proposition_4_2_3_four x₀
  obtain ⟨ψ, hψ, haψ, hψ0, hgood⟩ := h a a.2
  set d := hA.1.data a.2
  have haW : a.1 ∈ d.toSubData.shrink ψ :=
    d.toSubData.mem_shrink ψ a.2 (hA.1.mem_data_V a.2) haψ
  have hψ' := subPolyfold_isChart hA.1.isSubMPolyfold d.toSubData hψ a
  obtain ⟨R, hR⟩ := ψ.model.isScRetract
  have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hψ (P.levelMk 1 a.1 (hA.1.mem_levelSet_one a.2)) R hR
  have h0t : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht, hz]; exact ⟨a.1, ⟨haW, a.2⟩, rfl⟩
  set N : Submodule ℝ (ψ.model.E 0) :=
    LinearMap.range (scDeriv t.U t 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0)
  have hN : (N : Set (ψ.model.E 0)) =
      tangentSpace ψ.model.E ψ.model.C (ψ '' (d.toSubData.shrink ψ ∩ A)) 0 := by
    rw [← ht]; exact (tangentSpace_eq_coe_submodule t h0t).symm
  have hfin : FiniteDimensional ℝ N := lemma_4_1_7_ii htp h0t
  obtain ⟨c, hc, hac, -, hcc⟩ :=
    @theorem_4_1_2_chart _ _ _ _ _ x₀ hsm hmap (subChart d.toSubData hψ a) hψ' a haW hψ0 N hfin hN
      (hgood N hN)
  refine ⟨@CornerChartData.chart _ _ _ _ hfin c, hc, hac, hcc, ?_⟩
  have hdim := (hA.2 a.1 a.2).finrank_eq d hψ (hA.1.mem_data_V a.2) haψ hz
  rw [← hN, Submodule.span_eq] at hdim
  exact hdim

/-- **Theorem 4.2.7 (preprint 4.18) with the dimension**: if `X` is tame and the `n`-dimensional
submanifold `A` is in good position at every point (Definition 4.2.5), the induced structure on
`A` has a corner structure of dimension `n` (the proof of `theorem_4_2_7`:
`IsTame.exists_centredChart` and `IsGoodPositionAt.isInGoodPosition_of_tame`). -/
theorem IsSubmanifoldOfDim.hasCornerStructureOfDim_of_tame (hP : P.IsTame)
    (hA : P.IsSubmanifoldOfDim A n) [ParacompactSpace A]
    (hgp : ∀ a ∈ A, P.IsGoodPositionAt A a) :
    (subPolyfold hA.1.isSubMPolyfold).HasCornerStructureOfDim n := by
  refine hA.hasCornerStructureOfDim_of_centred fun a ha => ?_
  obtain ⟨ψ, hψ, haψ, hψ0, htame⟩ := hP.exists_centredChart (hA.1.subset_smoothSet ha)
  exact ⟨ψ, hψ, haψ, hψ0, fun N hN =>
    (hgp a ha).isInGoodPosition_of_tame (hA.1.data ha) (hA.1.mem_data_V ha) hψ haψ hψ0 htame hN⟩

/-- **Remark 4.2.2 (preprint 4.14), last sentences, with the dimension**: an `n`-dimensional
submanifold avoiding `∂X` has an induced corner structure of dimension `n` (the proof of
`hasCornerStructure_of_degIndex_eq_zero`: in a chart realizing `d_X(a) = 0`, re-centred at `a`,
the partial quadrant is the whole space and every subspace is in good position to it). -/
theorem IsSubmanifoldOfDim.hasCornerStructureOfDim_of_degIndex_eq_zero
    (hA : P.IsSubmanifoldOfDim A n) [ParacompactSpace A] (h0 : ∀ a ∈ A, P.degIndex a = 0) :
    (subPolyfold hA.1.isSubMPolyfold).HasCornerStructureOfDim n := by
  refine hA.hasCornerStructureOfDim_of_centred fun a ha => ?_
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a
  obtain ⟨k, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have he : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.1.subset_smoothSet ha)
  refine ⟨φ.recentre T hT (φ a) he, φ.recentre_isChart T hT (φ a) he hφ,
    φ.mem_recentre_source T hT (φ a) he haφ rfl, φ.recentre_apply_self T hT (φ a) he rfl,
    fun N _ => ?_⟩
  rw [MChart.recentre_model_C, partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero T hT
    (φ.apply_mem_C haφ) (hd.symm.trans (h0 a ha))]
  exact isInGoodPosition_univ N

/-- A submanifold avoiding `∂X` has `d_A ≡ 0` (Proposition 4.2.3 (3); Lemma 2.4.6 (preprint 2.26),
`d_A(a) ≤ d_X(a)`, `lemma_2_4_6`). -/
theorem IsSmoothSubmanifold.subPolyfold_degIndex_eq_zero (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] (h0 : ∀ a ∈ A, P.degIndex a = 0) (a : A) :
    (subPolyfold hA.isSubMPolyfold).degIndex a = 0 :=
  Nat.eq_zero_of_le_zero ((lemma_2_4_6 hA.isSubMPolyfold a).trans_eq (h0 a a.2))

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

/-- **Theorem 3.2.3 (preprint 3.27) in Mathlib's language**: the solution set `M` of the implicit
function theorem for the germs of Definition 3.2.1 (regular data `TangentGermChart` of dimension
`n` at every point; `theorem_3_2_3_isManifoldWithCorners`) is a smooth manifold with boundary and
corners, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`. -/
theorem theorem_3_2_3_isManifold (P : MPolyfold X) {M : Set X} [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ d : P.TangentGermChart M x n, d.IsRegular) (hne : M.Nonempty) :
    letI := (subPolyfold (theorem_3_2_3_isSubMPolyfold P hM)).cornerChartedSpace
      (theorem_3_2_3_isManifoldWithCorners P hM hne).hasCornerStructureOfDim
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M :=
  isManifold_cornerChartedSpace _

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

/-- **Finite-dimensionality of the tangent space of a sub-retract is carried by a germ of
sc-diffeomorphisms** (as `finrank_span_tangentSpace_eq`: `D(F ∘ r)(z)` restricts to a linear
isomorphism `T_zQ ≅ T_{F(z)}Q'`). -/
theorem _root_.Polyfold.finiteDimensional_span_tangentSpace_of_isDiffeoGerm {E E' : ScBanach}
    {C : Set (E 0)} {C' : Set (E' 0)} {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) (hGs : IsScSmooth R'.U (G ∘ R'))
    {Q : Set (E 0)} {Q' : Set (E' 0)} (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q')
    (hQR : Q ⊆ R.retract) (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q') (hGQ : MapsTo G Q' Q)
    {z : E 1} (hz : z ∈ E.lvlSet Q 1)
    [FiniteDimensional ℝ (Submodule.span ℝ (tangentSpace E C Q z))] :
    FiniteDimensional ℝ (Submodule.span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z))) := by
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  have hy' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hzQ' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet Q' 1 := by
    rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
  have himg : levelMap (G ∘ R') 1 (levelMap (F ∘ R) 1 z) = z := h.image_image hx
  have hT := coe_span_tangentSpace hQ hz
  have hT' := coe_span_tangentSpace hQ' hzQ'
  have ha : ∀ v ∈ Submodule.span ℝ (tangentSpace E C Q z),
      scDeriv R.U (F ∘ R) z v ∈
        Submodule.span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)) := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    rw [← SetLike.mem_coe, hT']
    exact scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hv
  have ha' : ∀ w ∈ Submodule.span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈
        Submodule.span ℝ (tangentSpace E C Q z) := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    rw [← SetLike.mem_coe, hT]
    have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
    rwa [himg] at this
  have h1 : ∀ v ∈ Submodule.span ℝ (tangentSpace E C Q z),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) (scDeriv R.U (F ∘ R) z v) = v := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    have hv' := tangentSpace_subset_of_subset R hQ hQR hz hv
    rw [tangentSpace_eq_range R hx] at hv'
    obtain ⟨w, rfl⟩ := hv'
    rw [h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have h2 : ∀ w ∈ Submodule.span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R.U (F ∘ R) z (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w) = w := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    have hw' := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
    rw [tangentSpace_eq_range R' hy'] at hw'
    obtain ⟨u, rfl⟩ := hw'
    rw [h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  exact (restrictEquiv _ _ _ _ ha ha' h1 h2).toLinearEquiv.finiteDimensional

/-- **The chart change for the finite-dimensionality of the tangent spaces of `A`**
(`chart_change_of_transport` for the property "`T_zQ` is finite-dimensional", as
`finrank_tangentSpace_chart_change`). -/
theorem finiteDimensional_tangentSpace_chart_change {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') (has : a ∈ P.smoothSet) {z : φ.model.E 1}
    {z' : φ'.model.E 1} (hz : φ.model.E.toBase 1 z = φ a)
    (hz' : φ'.model.E.toBase 1 z' = φ' a)
    [hfin : FiniteDimensional ℝ
      (Submodule.span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z))] :
    FiniteDimensional ℝ
      (Submodule.span ℝ (tangentSpace φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) z')) := by
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact (mem_smoothSet_iff hφ (hGφ haG)).1 has
  obtain ⟨k, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨k', Wq', T', hT'⟩ := φ'.model.isPartialQuadrant
  exact chart_change_of_transport
    (fun E C _ Q _ _ _ w => FiniteDimensional ℝ (Submodule.span ℝ (tangentSpace E C Q w)))
    (fun _ _ _ _ _ _ _ _ _ _ hQ _ h => by rw [← hQ]; exact h)
    (fun _ _ _ _ _ _ _ _ h hF hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz _ _ _ _ _ _ _ _ _ hk => by
      have := hk
      exact finiteDimensional_span_tangentSpace_of_isDiffeoGerm h hF hG hQ hQ' hQR hQ'R hFQ hGQ hz)
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' hfin

variable {A : Set X}

/-- **The tangent space of `A` in any chart of its induced structure has dimension `n`**: for an
`n`-dimensional submanifold `A`, a chart `ψ` of the induced M-polyfold `A` (Proposition 2.3.19)
and a level-`1` point `z` over `ψ(a)`, `T_z(ψ(dom ψ))` is finite-dimensional of dimension `n`
(the chart change from the induced chart `subChart` of a chart of `X`, where the dimension is
`dim T_aA = n`, `HasDimAt.finrank_eq`, and the tangent space is that of the sc⁺ chart retraction,
`lemma_4_1_7_ii`). -/
theorem IsSubmanifoldOfDim.tangentSpace_subPolyfold_chart (hA : P.IsSubmanifoldOfDim A n)
    [ParacompactSpace A] {ψ : MChart A} (hψ : (subPolyfold hA.1.isSubMPolyfold).IsChart ψ)
    {a : A} (haψ : a ∈ ψ.source) {z : ψ.model.E 1} (hz : ψ.model.E.toBase 1 z = ψ a) :
    FiniteDimensional ℝ (Submodule.span ℝ (tangentSpace ψ.model.E ψ.model.C ψ.model.O z)) ∧
      finrank ℝ (Submodule.span ℝ (tangentSpace ψ.model.E ψ.model.C ψ.model.O z)) = n := by
  set Q := subPolyfold hA.1.isSubMPolyfold
  obtain ⟨ψ₀, hψ₀, haψ₀⟩ := P.exists_isChart_mem_source a.1
  set d := hA.1.data a.2
  set ψ' : MChart A := subChart d.toSubData hψ₀ a
  have hψ' : Q.IsChart ψ' := subPolyfold_isChart hA.1.isSubMPolyfold d.toSubData hψ₀ a
  have haψ' : a ∈ ψ'.source := d.toSubData.mem_shrink ψ₀ a.2 (hA.1.mem_data_V a.2) haψ₀
  have h1 : a ∈ Q.levelSet 1 :=
    (hA.1.mem_levelSet_subPolyfold_iff a 1).2 (hA.1.mem_levelSet_one a.2)
  have has : a ∈ Q.smoothSet := hA.1.proposition_4_2_3_one.2 a
  set z' := levelLift ψ' 1 a
  have hz' : ψ'.model.E.toBase 1 z' = ψ' a := Q.toBase_levelLift hψ' haψ' h1
  have hQ : IsScRetract ψ.model.E ψ.model.C (ψ '' (ψ.source ∩ univ)) := by
    rw [inter_univ, ψ.image_source]; exact ψ.model.isScRetract
  have hQ' : IsScRetract ψ'.model.E ψ'.model.C (ψ' '' (ψ'.source ∩ univ)) := by
    rw [inter_univ, ψ'.image_source]; exact ψ'.model.isScRetract
  -- the dimension in the induced chart `ψ'` is `n`
  have hdim' : finrank ℝ (Submodule.span ℝ
      (tangentSpace ψ'.model.E ψ'.model.C (ψ' '' (ψ'.source ∩ univ)) z')) = n := by
    rw [inter_univ, ψ'.image_source]
    exact (hA.2 a.1 a.2).finrank_eq d hψ₀ (hA.1.mem_data_V a.2) haψ₀ hz'
  have hfin' : FiniteDimensional ℝ (Submodule.span ℝ
      (tangentSpace ψ'.model.E ψ'.model.C (ψ' '' (ψ'.source ∩ univ)) z')) := by
    rw [inter_univ, ψ'.image_source]
    obtain ⟨t, ht, htp⟩ := exists_plusRetraction hψ₀ d a.2 (hA.1.mem_data_V a.2)
    set z₀ : ψ₀.model.E 1 := z' with hz₀
    have hz'₀ : ψ₀.model.E.toBase 1 z₀ = ψ₀ a.1 := hz'
    have h0t : z₀ ∈ ψ₀.model.E.lvlSet t.retract 1 := by
      rw [ScBanach.mem_lvlSet, ht, hz'₀]; exact ⟨a.1, ⟨haψ', a.2⟩, rfl⟩
    change FiniteDimensional ℝ (Submodule.span ℝ
      (tangentSpace ψ₀.model.E ψ₀.model.C (ψ₀ '' (d.toSubData.shrink ψ₀ ∩ A)) z₀))
    rw [← ht, tangentSpace_eq_coe_submodule t h0t, Submodule.span_eq]
    exact lemma_4_1_7_ii htp h0t
  have hfr := finrank_tangentSpace_chart_change hψ' hψ ψ'.isOpen_source ψ.isOpen_source
    subset_rfl subset_rfl hQ' hQ (mem_univ a) haψ' haψ has hz' hz
  have hfin := finiteDimensional_tangentSpace_chart_change hψ' hψ ψ'.isOpen_source
    ψ.isOpen_source subset_rfl subset_rfl hQ' hQ (mem_univ a) haψ' haψ has hz' hz
  rw [inter_univ, inter_univ, ψ'.image_source, ψ.image_source] at hfr
  rw [inter_univ, ψ.image_source] at hfin
  rw [inter_univ, ψ'.image_source] at hdim'
  exact ⟨hfin, hfr.symm.trans hdim'⟩

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
