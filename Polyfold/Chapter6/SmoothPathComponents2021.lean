import Polyfold.Chapter2.SmoothPaths
import Polyfold.Chapter3.IndexAlongPathsInterval2021
import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter4.Characterization
import Polyfold.Chapter5.StrongBundleShift
import Polyfold.Chapter6.PathCategory
import Polyfold.Chapter6.ScPaths
import Polyfold.Chapter6.PathsInterval
import Polyfold.Chapter7.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.2, p. 240, the
sentence before **Proposition 6.2.2** (preprint: before Proposition 6.2, p. 201).  Gap G.56,
row V6.49.

# Smooth points of a component are joined by sc⁺-smooth paths

## The text, paraphrased

An M-polyfold is locally path connected, and any two smooth points in the same connected
component (preprint: path component) are joined by an sc⁺-smooth path `φ : [0, 1] → X`.

## What is formalized

* `MPolyfold.ScJoinedIn P U x y`: `x` and `y` are joined by an sc-smooth path `γ : ℝ → X` with
  `γ(0) = x`, `γ(1) = y` and all values in `U` (the paths of decision D2); it is reflexive on
  smooth points, symmetric, transitive (the concatenation `concatPath`) and monotone in `U`.
* `MPolyfold.exists_nhds_scJoinedIn` (**the local step**): for `U` open and `u ∈ U` there is an
  open `N` with `u ∈ N ⊆ U` whose smooth points are pairwise joined by sc-smooth paths in `U`
  (the retracted segment `chartSegPath` of a chart around `u`; unlike `exists_nhds_scPath` no
  strong bundle chart is needed).
* `MPolyfold.scJoinedIn_of_isConnected` (**the global step**): in a connected open `U` any two
  smooth points are joined by an sc-smooth path in `U` (a chain argument, as
  `isPathConnected_smoothVal_preimage`, with the concatenation of paths).
* `MPolyfold.IsScSmoothMap.exists_scPlus_lift`: an sc-smooth path `φ : [0, 1] → X` is
  **sc⁺-smooth**: it lifts to an sc-smooth path `[0, 1] → X¹` (`[0, 1]` is modelled on
  sc⁺-retracts, Remark 4.1.3, so `1₀¹ : [0, 1] → [0, 1]¹` is sc-smooth, Proposition 4.1.8;
  then `φ` raised by one index, `IsScSmoothMap.levelOne`).
* **`paths_before_proposition_6_2_2`**: the sentence of the text: `X` is locally path connected
  (`MPolyfold.locallyPathConnectedSpace`), and two smooth points in the same connected component
  are joined by an sc-smooth path `φ : [0, 1] → X` with values in that component which lifts to
  an sc-smooth path `[0, 1] → X¹`.
* `mem_connectedComponent_iff_exists_scPath`, `mem_pathComponent_iff_exists_scPath`: for smooth
  `x`, `y`, being in the same connected component, being in the same path component and being
  joined by an sc-smooth path `[0, 1] → X` are equivalent.  This justifies the reading of "in the
  same path component" in Definitions 6.6.2 and 6.6.14 as "joined by an sc-smooth path".
* `proposition_6_2_2_connectedComponent_2021def`: with Proposition 6.2.2 on `[0, 1]`
  (`proposition_6_2_2_interval_2021def'`), two smooth points of one connected component have the
  same index.

## Reading

* "sc⁺-smooth path `φ : [0, 1] → X`" is read as: `φ` is sc-smooth and is the image of an
  sc-smooth path `φ⁺ : [0, 1] → X¹` under the inclusion `X¹ → X`.  Since `[0, 1]` is
  finite-dimensional, every sc-smooth path on `[0, 1]` has this property.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- `x` and `y` are **joined in `U` by an sc-smooth path**: an sc-smooth `γ : ℝ → X` with
`γ(0) = x`, `γ(1) = y` and all values in `U`. -/
def ScJoinedIn (U : Set X) (x y : X) : Prop :=
  ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap P γ ∧ γ (pt1 0) = x ∧ γ (pt1 1) = y ∧
    ∀ t, γ t ∈ U

variable {P} {U V : Set X} {x y z : X}

theorem ScJoinedIn.refl (hx : x ∈ P.smoothSet) (hxU : x ∈ U) : P.ScJoinedIn U x x :=
  ⟨fun _ => x, isScSmoothMap_const_of_mem_smoothSet hx, rfl, rfl, fun _ => hxU⟩

theorem ScJoinedIn.symm (h : P.ScJoinedIn U x y) : P.ScJoinedIn U y x := by
  obtain ⟨γ, hγ, h0, h1, hU⟩ := h
  refine ⟨fun s => γ (pt1 (1 - s 0)), isScSmoothMap_reparam hγ (contDiff_const.sub contDiff_id),
    ?_, ?_, fun _ => hU _⟩
  · simpa only [pt1_apply, sub_zero] using h1
  · simpa only [pt1_apply, sub_self] using h0

theorem ScJoinedIn.trans (h₁ : P.ScJoinedIn U x y) (h₂ : P.ScJoinedIn U y z) :
    P.ScJoinedIn U x z := by
  obtain ⟨γ₁, hγ₁, h10, h11, hU₁⟩ := h₁
  obtain ⟨γ₂, hγ₂, h20, h21, hU₂⟩ := h₂
  refine ⟨concatPath γ₁ γ₂, isScSmoothMap_concatPath hγ₁ hγ₂ (h11.trans h20.symm),
    concatPath_zero.trans h10, concatPath_one.trans h21, fun s => ?_⟩
  rcases le_or_gt (s 0) (1 / 2) with hs | hs
  · rw [concatPath_of_le hs]; exact hU₁ _
  · rw [concatPath_of_gt hs]; exact hU₂ _

theorem ScJoinedIn.mono (h : P.ScJoinedIn U x y) (hUV : U ⊆ V) : P.ScJoinedIn V x y :=
  let ⟨γ, hγ, h0, h1, hU⟩ := h
  ⟨γ, hγ, h0, h1, fun t => hUV (hU t)⟩

theorem ScJoinedIn.mem_smoothSet_left (h : P.ScJoinedIn U x y) : x ∈ P.smoothSet := by
  obtain ⟨γ, hγ, h0, -, -⟩ := h
  exact h0 ▸ mem_smoothSet_of_isScSmoothMap hγ _

theorem ScJoinedIn.mem_smoothSet_right (h : P.ScJoinedIn U x y) : y ∈ P.smoothSet :=
  h.symm.mem_smoothSet_left

theorem ScJoinedIn.mem_left (h : P.ScJoinedIn U x y) : x ∈ U := by
  obtain ⟨γ, -, h0, -, hU⟩ := h
  exact h0 ▸ hU _

theorem ScJoinedIn.mem_right (h : P.ScJoinedIn U x y) : y ∈ U := h.symm.mem_left

/-- An sc-smooth path is a continuous path: `ScJoinedIn` implies `JoinedIn`. -/
theorem ScJoinedIn.joinedIn (h : P.ScJoinedIn U x y) : JoinedIn U x y := by
  obtain ⟨γ, hγ, h0, h1, hU⟩ := h
  have := joinedIn_of_continuous_pt1 (continuousOn_univ.1 hγ.continuousOn) hU
  rwa [h0, h1] at this

/-- **The path on `[0, 1]`** (2021 reading): an sc-smooth path on `ℝ` restricts to an sc-smooth
path `φ : [0, 1] → X` with the same end points and values in `U`. -/
theorem ScJoinedIn.exists_unitInterval (h : P.ScJoinedIn U x y) :
    ∃ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap P φ ∧ φ 0 = x ∧ φ 1 = y ∧
      ∀ t, φ t ∈ U := by
  obtain ⟨γ, hγ, h0, h1, hU⟩ := h
  exact ⟨restrictUnitPath γ, isScSmoothMap_restrictUnitPath hγ, h0, h1, fun _ => hU _⟩

/-- Conversely, an sc-smooth path `φ : [0, 1] → X` with values in `U` gives `ScJoinedIn`
(through `unitPath φ`). -/
theorem scJoinedIn_of_unitInterval {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap P φ) (hU : ∀ t, φ t ∈ U) :
    P.ScJoinedIn U (φ 0) (φ 1) :=
  ⟨unitPath φ, isScSmoothMap_unitPath hφ, unitPath_zero φ, unitPath_one φ, fun _ => hU _⟩

variable (P)

/-- **The local step**: for `U ⊆ X` open and `u ∈ U` there is an open `N` with `u ∈ N ⊆ U` such
that any two smooth points of `N` are joined in `U` by an sc-smooth path, the retracted segment
between their images in a chart around `u` (as `exists_nhds_joinedIn_smooth`, which only records
the continuous path). -/
theorem exists_nhds_scJoinedIn (hU : IsOpen U) {u : X} (hu : u ∈ U) :
    ∃ N : Set X, IsOpen N ∧ u ∈ N ∧ N ⊆ U ∧
      ∀ x ∈ N, ∀ y ∈ N, x ∈ P.smoothSet → y ∈ P.smoothSet → P.ScJoinedIn U x y := by
  obtain ⟨φ, hφ, huφ⟩ := P.exists_isChart_mem_source u
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set u₀ := φ u with hu₀def
  have hOR : ∀ {v}, v ∈ φ.model.O → v ∈ R.retract := fun hv => hR ▸ hv
  have hu₀O : u₀ ∈ φ.model.O := φ.mapsTo_model u huφ
  have hu₀U : u₀ ∈ R.U := R.retract_subset (hOR hu₀O)
  have hRu₀ : R u₀ = u₀ := R.apply_eq_self_of_mem_retract (hOR hu₀O)
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := U ∩ φ.source) inter_subset_right
    (hU.inter φ.isOpen_source)
  have hu₀W₀ : u₀ ∈ W₀ := by
    have : φ u ∈ φ '' (U ∩ φ.source) := ⟨u, ⟨hu, huφ⟩, rfl⟩
    rw [hW₀eq] at this
    exact this.2
  have hcont : ContinuousWithinAt R R.U u₀ := R.isSc1.isSc0.continuousOn_base u₀ hu₀U
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.mem_nhdsWithin_iff.1 (hcont (hW₀.mem_nhds (by rwa [hRu₀])))
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := R.relOpen.exists_ball_inter_subset hu₀U
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hUC : R.U ⊆ φ.model.C := by
    obtain ⟨O', -, h⟩ := R.relOpen.relOpen
    rw [h]
    exact inter_subset_right
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  set N := φ.source ∩ φ ⁻¹' Metric.ball u₀ δ ∩ U with hNdef
  have hNo : IsOpen N :=
    (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball).inter hU
  refine ⟨N, hNo, ⟨⟨huφ, Metric.mem_ball_self hδ⟩, hu⟩, inter_subset_right, ?_⟩
  intro x hx y hy hxs hys
  have hκ : ∀ p : Fin 1 → ℝ, Real.smoothTransition (p 0) ∈ Icc (0 : ℝ) 1 := fun p =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  set a := φ x with hadef
  set b := φ y with hbdef
  have haO : a ∈ φ.model.O := φ.mapsTo_model _ hx.1.1
  have hbO : b ∈ φ.model.O := φ.mapsTo_model _ hy.1.1
  have hseg : ∀ p : Fin 1 → ℝ,
      a + Real.smoothTransition (p 0) • (b - a) ∈ Metric.ball u₀ δ ∩ R.U := fun p => by
    have hball : a + Real.smoothTransition (p 0) • (b - a) ∈ Metric.ball u₀ δ :=
      (convex_ball u₀ δ).add_smul_sub_mem hx.1.2 hy.1.2 (hκ p)
    refine ⟨hball, hδ₂U ⟨Metric.ball_subset_ball (min_le_right _ _) hball, ?_⟩⟩
    exact hCconv.add_smul_sub_mem (hUC (R.retract_subset (hOR haO)))
      (hUC (R.retract_subset (hOR hbO))) (hκ p)
  have hRseg : ∀ p : Fin 1 → ℝ, chartSegPath φ R a b p ∈ U := fun p => by
    have h1 : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ φ.model.O :=
      hR ▸ R.apply_mem_retract (hseg p).2
    have h2 : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ W₀ :=
      hδ₁W ⟨Metric.ball_subset_ball (min_le_left _ _) (hseg p).1, (hseg p).2⟩
    have : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ φ '' (U ∩ φ.source) := by
      rw [hW₀eq]
      exact ⟨h1, h2⟩
    obtain ⟨w, hw, hweq⟩ := this
    change φ.symm (R (a + Real.smoothTransition (p 0) • (b - a))) ∈ U
    rw [← hweq, φ.symm_apply_apply hw.2]
    exact hw.1
  have hsm : ∀ {w}, w ∈ φ.source → w ∈ P.smoothSet → φ w ∈ φ.model.E.smooth := fun hw hws =>
    φ.model.E.mem_smooth_iff.2 fun m => (P.mem_levelSet_iff hφ hw).1 (mem_iInter.1 hws m)
  refine ⟨chartSegPath φ R a b,
    isScSmoothMap_chartSegPath hφ hR (hsm hx.1.1 hxs) (hsm hy.1.1 hys) fun p => (hseg p).2,
    ?_, ?_, hRseg⟩
  · change φ.symm (R (a + Real.smoothTransition ((pt1 0 : Fin 1 → ℝ) 0) • (b - a))) = x
    rw [pt1_apply, Real.smoothTransition.zero, zero_smul, add_zero,
      R.apply_eq_self_of_mem_retract (hOR haO), hadef, φ.symm_apply_apply hx.1.1]
  · change φ.symm (R (a + Real.smoothTransition ((pt1 1 : Fin 1 → ℝ) 0) • (b - a))) = y
    rw [pt1_apply, Real.smoothTransition.one, one_smul, add_sub_cancel,
      R.apply_eq_self_of_mem_retract (hOR hbO), hbdef, φ.symm_apply_apply hy.1.1]

/-- **The global step**: in a connected open `U ⊆ X` any two smooth points are joined by an
sc-smooth path with values in `U`.  The points of `U` near which every smooth point is joined to
`x` form an open set, closed in `U` by the local step and the density of `X_∞`. -/
theorem scJoinedIn_of_isConnected (hU : IsOpen U) (hc : IsConnected U) (hx : x ∈ U)
    (hy : y ∈ U) (hxs : x ∈ P.smoothSet) (hys : y ∈ P.smoothSet) : P.ScJoinedIn U x y := by
  set A : Set X := {u | ∃ N : Set X, IsOpen N ∧ u ∈ N ∧
    ∀ w ∈ N, w ∈ P.smoothSet → P.ScJoinedIn U w x} with hAdef
  have hAo : IsOpen A := isOpen_iff_forall_mem_open.2 fun u ⟨N, hNo, huN, hN⟩ =>
    ⟨N, fun v hv => ⟨N, hNo, hv, hN⟩, hNo, huN⟩
  have hUA : U ⊆ A := by
    refine hc.isPreconnected.subset_of_closure_inter_subset hAo ⟨x, hx, ?_⟩ ?_
    · obtain ⟨N, hNo, hxN, -, hN⟩ := P.exists_nhds_scJoinedIn hU hx
      exact ⟨N, hNo, hxN, fun w hw hws => hN w hw x hxN hws hxs⟩
    · rintro u ⟨hucl, huU⟩
      obtain ⟨N, hNo, huN, -, hN⟩ := P.exists_nhds_scJoinedIn hU huU
      obtain ⟨u', hu'N, N', hN'o, hu'N', hN'⟩ := mem_closure_iff.1 hucl N hNo huN
      obtain ⟨w, hws, hw⟩ := P.dense_smoothSet.exists_mem_open (hNo.inter hN'o) ⟨u', hu'N, hu'N'⟩
      exact ⟨N, hNo, huN, fun v hv hvs => (hN v hv w hw.1 hvs hws).trans (hN' w hw.2 hws)⟩
  obtain ⟨N, -, hyN, hN⟩ := hUA hy
  exact (hN y hyN hys).symm

/-! ### Sc-smooth paths on `[0, 1]` are sc⁺-smooth -/

/-- `1₀¹ : [0, 1] → [0, 1]¹` is sc-smooth: the two charts of `[0, 1]` are modelled on
sc⁺-retracts (Remark 4.1.3 for the constant sc-structure of `ℝ`, Proposition 4.1.8). -/
theorem _root_.Polyfold.unitIntervalPolyfold_isScSmoothMap_toLevelOne
    (t₀ : unitIntervalPolyfold.Level 1) :
    unitIntervalPolyfold.IsScSmoothMap unitIntervalPolyfold.shift
      (unitIntervalPolyfold.toLevelOne t₀) := by
  refine (MPolyfold.isScSmoothMap_toLevelOne_of_cover t₀ fun t => ?_).2
  rcases UnitInterval.mem_leftChart_or_rightChart t with h | h
  · exact ⟨UnitInterval.leftChart, UnitInterval.isChart_leftChart, h,
      (remark_4_1_3_const (Fin 1 → ℝ)).2.2 _ _ UnitInterval.leftChart.model.isScRetract⟩
  · exact ⟨UnitInterval.rightChart, UnitInterval.isChart_rightChart, h,
      (remark_4_1_3_const (Fin 1 → ℝ)).2.2 _ _ UnitInterval.rightChart.model.isScRetract⟩

variable {P}

/-- **An sc-smooth path on `[0, 1]` is sc⁺-smooth**: it is the image of an sc-smooth path
`φ⁺ : [0, 1] → X¹` under the inclusion `X¹ → X` (raise the index of `φ`, then precompose with the
sc-smooth `1₀¹ : [0, 1] → [0, 1]¹`). -/
theorem IsScSmoothMap.exists_scPlus_lift {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap P φ) :
    ∃ φ' : unitInterval → P.Level 1, unitIntervalPolyfold.IsScSmoothMap P.shift φ' ∧
      ∀ t, P.levelVal 1 (φ' t) = φ t := by
  set φ₁ : unitIntervalPolyfold.Level 1 → P.Level 1 := fun s =>
    P.levelMk 1 (φ (unitIntervalPolyfold.levelVal 1 s)) (hφ.mapsTo_levelSet 1 (levelVal_mem s))
  have hφ₁ : unitIntervalPolyfold.shift.IsScSmoothMap P.shift φ₁ :=
    IsScSmoothMap.levelOne hφ fun _ => rfl
  have hall : ∀ t, t ∈ unitIntervalPolyfold.smoothSet := fun t => by
    obtain ⟨p, rfl⟩ := sinSqInterval_surjective t
    exact mem_smoothSet_of_isScSmoothMap isScSmoothMap_sinSqInterval p
  set t₀ := unitIntervalPolyfold.levelMk 1 0 (mem_iInter.1 (hall 0) 1)
  refine ⟨φ₁ ∘ unitIntervalPolyfold.toLevelOne t₀,
    hφ₁.comp (unitIntervalPolyfold_isScSmoothMap_toLevelOne t₀), fun t => ?_⟩
  change φ (unitIntervalPolyfold.levelVal 1 (unitIntervalPolyfold.toLevelOne t₀ t)) = φ t
  rw [levelVal_toLevelOne t₀ (mem_iInter.1 (hall t) 1)]

/-! ### The sentence before Proposition 6.2.2 -/

/-- **Two smooth points in the same connected component are joined by an sc⁺-smooth path**
(2021, p. 240, before Proposition 6.2.2): an sc-smooth `φ : [0, 1] → X` from `x` to `y` with
values in the component, which lifts to an sc-smooth path `[0, 1] → X¹`. -/
theorem exists_scPlusPath_of_mem_connectedComponent (hx : x ∈ P.smoothSet)
    (hy : y ∈ P.smoothSet) (hxy : y ∈ connectedComponent x) :
    ∃ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap P φ ∧ φ 0 = x ∧ φ 1 = y ∧
      (∀ t, φ t ∈ connectedComponent x) ∧
      ∃ φ' : unitInterval → P.Level 1, unitIntervalPolyfold.IsScSmoothMap P.shift φ' ∧
        ∀ t, P.levelVal 1 (φ' t) = φ t := by
  obtain ⟨φ, hφ, h0, h1, hU⟩ := (P.scJoinedIn_of_isConnected (P.isOpen_connectedComponent x)
    isConnected_connectedComponent mem_connectedComponent hxy hx hy).exists_unitInterval
  exact ⟨φ, hφ, h0, h1, hU, hφ.exists_scPlus_lift⟩

variable (P) in
/-- **2021, p. 240, the sentence before Proposition 6.2.2** (preprint p. 201): an M-polyfold is
locally path connected, and any two smooth points in the same connected component are joined by
an sc⁺-smooth path `φ : [0, 1] → X` (sc-smooth, with values in the component, and the image of an
sc-smooth path `[0, 1] → X¹`). -/
theorem paths_before_proposition_6_2_2 :
    LocallyPathConnectedSpace X ∧
      ∀ x y : X, x ∈ P.smoothSet → y ∈ P.smoothSet → y ∈ connectedComponent x →
        ∃ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap P φ ∧ φ 0 = x ∧ φ 1 = y ∧
          (∀ t, φ t ∈ connectedComponent x) ∧
          ∃ φ' : unitInterval → P.Level 1, unitIntervalPolyfold.IsScSmoothMap P.shift φ' ∧
            ∀ t, P.levelVal 1 (φ' t) = φ t :=
  ⟨P.locallyPathConnectedSpace, fun _ _ hx hy hxy =>
    exists_scPlusPath_of_mem_connectedComponent hx hy hxy⟩

/-- An sc-smooth path `φ : [0, 1] → X` runs in the path component of `φ(0)`. -/
theorem mem_pathComponent_of_isScSmoothMap {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap P φ) : φ 1 ∈ pathComponent (φ 0) :=
  ((scJoinedIn_of_unitInterval hφ (U := univ) fun _ => trivial).joinedIn).joined

/-- **For smooth points, "same connected component" means "joined by an sc-smooth path
`[0, 1] → X`"**. -/
theorem mem_connectedComponent_iff_exists_scPath (hx : x ∈ P.smoothSet)
    (hy : y ∈ P.smoothSet) :
    y ∈ connectedComponent x ↔
      ∃ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap P φ ∧ φ 0 = x ∧ φ 1 = y := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨φ, hφ, h0, h1, -⟩ := exists_scPlusPath_of_mem_connectedComponent hx hy h
    exact ⟨φ, hφ, h0, h1⟩
  · rintro ⟨φ, hφ, rfl, rfl⟩
    exact pathComponent_subset_component _ (mem_pathComponent_of_isScSmoothMap hφ)

/-- **For smooth points, "same path component" (preprint) means "joined by an sc-smooth path
`[0, 1] → X`"**: the reading of "in the same path component" in Definitions 6.6.2 and 6.6.14
(preprint 6.27, 6.38) as "joined by an sc-smooth path" is the text's notion. -/
theorem mem_pathComponent_iff_exists_scPath (hx : x ∈ P.smoothSet) (hy : y ∈ P.smoothSet) :
    y ∈ pathComponent x ↔
      ∃ φ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap P φ ∧ φ 0 = x ∧ φ 1 = y := by
  have := P.locallyPathConnectedSpace
  rw [pathComponent_eq_connectedComponent]
  exact mem_connectedComponent_iff_exists_scPath hx hy

end MPolyfold

/-! ### With Proposition 6.2.2: the index is constant on components -/

section Index

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Proposition 6.2.2 on connected components** (2021, p. 240, with the sentence before it):
for an sc-Fredholm section in the 2021 sense with germ data in tame charts, two smooth points in
the same connected component have the same index (`proposition_6_2_2_interval_2021def'` along the
sc-smooth path of `exists_scPlusPath_of_mem_connectedComponent`). -/
theorem proposition_6_2_2_connectedComponent_2021def (hf : B.IsScFredholmSectionTame2021 f)
    {x y : X} (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (hxy : y ∈ connectedComponent x)
    {i j : ℤ} (hi : B.IsIndexAtLocal f x i) (hj : B.IsIndexAtLocal f y j) : i = j := by
  obtain ⟨φ, hφ, rfl, rfl, -⟩ := MPolyfold.exists_scPlusPath_of_mem_connectedComponent hx hy hxy
  exact proposition_6_2_2_interval_2021def' hf hφ hi hj

end Index

end Polyfold
