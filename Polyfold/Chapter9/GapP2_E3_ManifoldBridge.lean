import Polyfold.Chapter9.GapP2_E3_SheetIntegration
import Polyfold.Chapter9.GapP2_E3_FormEvalEp
import Polyfold.Chapter9.GapP2_E2Stokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 (Definition 9.3.3, p. 422) and §9.5, pp. 438–451 (gaps G.107, G.110).
Numbers and pages are the 2021 text's.

# From the orientations of Definition 9.3.3 to tangent orientations of a tame sheet

A tame `n`-dimensional submanifold `N` of an M-polyfold is a smooth manifold with boundary with
corners (`cornerChartedSpace`); its tangent vectors in corner coordinates are carried into `TX`
by the tangent map of the inclusion.

## What is formalized

* `incFrame`: the tangent vector `Tι(v) ∈ T_yX` of `v ∈ ℝⁿ = T_yN` read in corner coordinates
  `κ`; `incFrame_mem`: it lies in `T_yN` (Remark 4.2.2); `chartVec_incFrame`: its chart vector
  is `modelDeriv v`.
* `orIn o κ hy`: the orientation of `ℝⁿ` whose positive bases `b` are those with
  `(Tι(b₁), …, Tι(bₙ))` a positive frame of `T_y(N, o)` (`orientation_eq_orIn_iff`).
* **`bridgeOrientation o`**: the tangent orientation (`TangentOrientation`, Chapter 6) of the
  manifold `N` given by an orientation `o` of Definition 9.3.3; read in the Mathlib chart of any
  corner coordinates `κ` it is `orIn o κ` (`orientationIn_bridgeOrientation`), and it is
  continuous (`isContinuous_bridgeOrientation`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {N : Set X} [ParacompactSpace N] {n : ℕ} {hY : P.IsSubMPolyfold N}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

/-- **`Tι(v)`**: the tangent vector of `X` at `y ∈ N` given by `v ∈ ℝⁿ = T_yN` in the corner
coordinates `κ` of `N`. -/
def incFrame (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin n)) : P.TangentSpace :=
  tangentMap (subPolyfold_inclusion_isScSmooth hY)
    (κ.fiberMap (x := hcs.levelOne y) (κ.s_subset hy) v).1

variable {hcs}

theorem levelVal_tangentProj_incFrame (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) (v : EuclideanSpace ℝ (Fin n)) :
    P.levelVal 1 (P.tangentProj (incFrame hcs κ hy v)) = y.1 := by
  unfold incFrame
  rw [levelVal_tangentProj_tangentMap,
    tangentProj_eq_of_mem_fiber (κ.fiberMap (x := hcs.levelOne y) (κ.s_subset hy) v).2]
  rfl

/-- The chart vector of `Tι(v)` is `modelDeriv v`. -/
theorem chartVec_incFrame (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin n)) {φ : MChart X} (hφ : P.IsChart φ) (d : P.SubData N) (a₀ : N)
    (hyσ : y ∈ (subChart d hφ a₀).source) :
    chartVec hφ (incFrame hcs κ hy v) = modelDeriv κ hφ d a₀ (levelLift κ.χ 1 y) v :=
  tangentChartMap_tangentMap_fiberMap κ (x := hcs.levelOne y) (κ.s_subset hy) hφ d a₀ hyσ v

include hcs in
/-- `modelDeriv v` lies in the chart image of `T_yN`. -/
theorem modelDeriv_mem_chartTangent (hN : P.IsSmoothSubmanifold N)
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin n)) {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y.1 ∈ φ.source) :
    modelDeriv κ hφ (hN.data y.2).toSubData y (levelLift κ.χ 1 y) v ∈
      P.chartTangent hφ N y.1 := by
  set d' := hN.data y.2
  have hyV : y.1 ∈ d'.V := hN.mem_data_V y.2
  set d := d'.toSubData
  set σ := subChart d hφ y with hσdef
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ y
  have hyσ : y ∈ σ.source := d.mem_shrink φ y.2 hyV hyφ
  have hyχ : y ∈ κ.χ.source := κ.s_subset hy
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart hyχ (levelVal_mem (hcs.levelOne y))
  have h1 := transDeriv_mem_tangentSpace κ.isCornerChart κ.isChart hσ hyχ hyσ hz
    (κ.Ψ.symm (ofLpCLM n v))
  have hw := toBase_levelMap_transition κ.isCornerChart κ.isChart hσ hyχ hyσ hz
  have hy1 : y.1 ∈ P.levelSet 1 := d'.mem_levelSet_one y.2 hyV
  have hw' : levelMap (κ.χ.transition σ ∘ overlapRet κ.isCornerChart σ) 1
      (levelLift κ.χ 1 y) = levelLift φ 1 y.1 :=
    φ.model.E.toBase_injective 1 (hw.trans (P.toBase_levelLift hφ hyφ hy1).symm)
  obtain ⟨R, hR⟩ := d.isScRetract_image φ hφ
  have hQR : σ.overlap κ.χ ⊆ R.retract := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hR]
    exact ⟨a.1, ⟨ha.1, a.2⟩, rfl⟩
  have hlv : levelMap (κ.χ.transition σ ∘ overlapRet κ.isCornerChart σ) 1
      (levelLift κ.χ 1 y) ∈ σ.model.E.lvlSet (σ.overlap κ.χ) 1 := by
    change σ.model.E.toBase 1 _ ∈ σ.overlap κ.χ
    rw [hw]
    exact σ.mem_overlap κ.χ hyσ hyχ
  have h2 := tangentSpace_subset_of_subset R (σ.isScRetract_overlap κ.χ) hQR hlv h1
  rw [hR, hw'] at h2
  rw [chartTangent_eq hφ d' y.2 hyV hyφ]
  exact h2

/-- **`Tι(v) ∈ T_yN`.** -/
theorem incFrame_mem (hN : P.IsSmoothSubmanifold N) (κ : CornerCoords (subPolyfold hY) n)
    {y : N} (hy : y ∈ κ.s) (v : EuclideanSpace ℝ (Fin n)) :
    incFrame hcs κ hy v ∈ P.submanifoldTangent N y.1 := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y.1
  have hyσ : y ∈ (subChart (hN.data y.2).toSubData hφ y).source :=
    (hN.data y.2).toSubData.mem_shrink φ y.2 (hN.mem_data_V y.2) hyφ
  have h := modelDeriv_mem_chartTangent (hcs := hcs) hN κ hy v hφ hyφ
  rw [← chartVec_incFrame (hcs := hcs) κ hy v hφ _ y hyσ] at h
  obtain ⟨α, hα, hαv⟩ := h
  have : incFrame hcs κ hy v = α :=
    chartVec_injOn hφ hyφ (levelVal_tangentProj_incFrame κ hy v) hα.1 hαv.symm
  rw [this]; exact hα

/-- The frames of two bases of `ℝⁿ` are in the same class of `o` iff the bases have the same
orientation. -/
theorem incFrame_mem_frames_iff (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) (b b' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ((fun i => incFrame hcs κ hy (b' i)) ∈ o.frames y ↔
      (fun i => incFrame hcs κ hy (b i)) ∈ o.frames y) ↔ 0 < b.det b' := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y.1
  set d := (hN.1.data y.2).toSubData
  have hyσ : y ∈ (subChart d hφ y).source :=
    d.mem_shrink φ y.2 (hN.1.mem_data_V y.2) hyφ
  have hyχ : y ∈ κ.χ.source := κ.s_subset hy
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart hyχ (levelVal_mem (hcs.levelOne y))
  set m := modelDeriv κ hφ d y (levelLift κ.χ 1 y) with hm
  have hinj : Function.Injective m := modelDeriv_injective κ hφ d y hy hyσ hz
  have hcv : ∀ v, chartVec hφ (incFrame hcs κ hy v) = m v := fun v =>
    chartVec_incFrame κ hy v hφ d y hyσ
  have hli : ∀ c : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      LinearIndependent ℝ fun i => chartVec hφ (incFrame hcs κ hy (c i)) := fun c => by
    have h := c.linearIndependent.map' (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0)
      (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i => chartVec hφ (incFrame hcs κ hy (c i))) =
        (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) ∘ c := funext fun i => hcv (c i)
    rw [e]; exact h
  rw [Basis.det_apply]
  refine IsOrientedAt.frames_iff_frames_iff_det_pos hN y.2 (o.isOrientedAt y y.2) hφ hyφ
    (fun i => incFrame_mem hN.1 κ hy _) (fun i => incFrame_mem hN.1 κ hy _) (hli b) (hli b')
    (b.toMatrix b') fun j => ?_
  rw [hcv]
  conv_lhs => rw [← b.sum_repr (b' j)]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hcv, Basis.toMatrix_apply]

/-- For `n ≥ 1` some basis of `ℝⁿ` has a positive frame. -/
theorem exists_basis_incFrame_mem_frames (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (fun i => incFrame hcs κ hy (b i)) ∈ o.frames y := by
  classical
  set b₀ : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  by_cases h0 : (fun i => incFrame hcs κ hy (b₀ i)) ∈ o.frames y
  · exact ⟨b₀, h0⟩
  · set w : Fin n → ℝˣ := Function.update (fun _ => 1) ⟨0, hn⟩ (-1) with hw
    refine ⟨b₀.unitsSMul w, ?_⟩
    have hdet : b₀.det (b₀.unitsSMul w) = -1 := by
      rw [Basis.det_unitsSMul_self]
      have hwi : ∀ i, ((w i : ℝˣ) : ℝ) =
          Function.update (fun _ => (1 : ℝ)) (⟨0, hn⟩ : Fin n) (-1) i := fun i => by
        rw [hw]
        by_cases h : i = ⟨0, hn⟩
        · subst h; simp
        · simp [Function.update_of_ne h]
      simp only [hwi]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    have key := incFrame_mem_frames_iff (hcs := hcs) hN o κ hy b₀ (b₀.unitsSMul w)
    rw [hdet] at key
    by_contra h1
    exact absurd (key.1 ⟨fun h => (h1 h).elim, fun h => (h0 h).elim⟩) (by norm_num)

variable (hcs) in
open Classical in
/-- **The orientation of `ℝⁿ` read from `o` in the corner coordinates `κ` at `y`**: its positive
bases are those whose frames `(Tι(bᵢ))ᵢ` are positive for `o`. -/
def orIn (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  if h : ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (fun i => incFrame hcs κ hy (b i)) ∈ o.frames y then h.choose.orientation
  else stdOrientation n

/-- **The positive bases of `orIn`.** -/
theorem orientation_eq_orIn_iff (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    b.orientation = orIn hcs o κ hy ↔ (fun i => incFrame hcs κ hy (b i)) ∈ o.frames y := by
  have hex := exists_basis_incFrame_mem_frames (hcs := hcs) hn hN o κ hy
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold orIn
  rw [dif_pos hex, Basis.orientation_eq_iff_det_pos]
  have key := incFrame_mem_frames_iff (hcs := hcs) hN o κ hy b hex.choose
  exact ⟨fun h => (key.2 h).1 hex.choose_spec, fun h => key.1 ⟨fun _ => h, fun _ => hex.choose_spec⟩⟩

omit [ParacompactSpace N] in
/-- A frame of `T_yN` in terms of a positive frame. -/
theorem exists_matrix_of_mem_frames (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) {y : X} (hy : y ∈ N) {φ : MChart X} (hφ : P.IsChart φ)
    (hyφ : y ∈ φ.source) {α : Fin n → P.TangentSpace} (hα : α ∈ o.frames y)
    {β : Fin n → P.TangentSpace} (hβ : ∀ j, β j ∈ P.submanifoldTangent N y) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ,
      ∀ j, chartVec hφ (β j) = ∑ i, M i j • chartVec hφ (α i) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; exact ⟨0, fun j => j.elim0⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨N₀, hN₀, hfin, hrank⟩ := exists_submodule_chartVec_image hφ hN.1 (hN.2 y hy) hyφ
  have hg := o.isOrientedAt y hy
  have hmem : ∀ γ ∈ P.submanifoldTangent N y, chartVec hφ γ ∈ N₀ := fun γ hγ => by
    rw [← SetLike.mem_coe, hN₀]; exact ⟨γ, hγ, rfl⟩
  have hαc : ∀ i, α i ∈ P.submanifoldTangent N y := fun i => hg.mem_carrier hα i
  set w : Fin n → N₀ := fun i => ⟨chartVec hφ (α i), hmem _ (hαc i)⟩ with hw
  have hli : LinearIndependent ℝ w := by
    refine LinearIndependent.of_comp N₀.subtype ?_
    exact hg.linearIndependent_chartVec hφ hyφ hα
  set bb := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hrank])
  refine ⟨fun i j => bb.repr ⟨chartVec hφ (β j), hmem _ (hβ j)⟩ i, fun j => ?_⟩
  have h := congrArg (N₀.subtype) (bb.sum_repr ⟨chartVec hφ (β j), hmem _ (hβ j)⟩)
  rw [map_sum] at h
  rw [← show N₀.subtype ⟨chartVec hφ (β j), hmem _ (hβ j)⟩ = chartVec hφ (β j) from rfl, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- **The orientation read in corner coordinates is locally constant.** -/
theorem eventually_orIn_eq (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {x : N}
    (hx : x ∈ κ.s) : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ κ.s, orIn hcs o κ hy = orIn hcs o κ hx := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨φ, hφ, V, hV, hxV, hVφ, e, he, hc⟩ := o.continuous hn x.1 x.2
  set d := (hN.1.data x.2).toSubData
  set σ := subChart d hφ x with hσdef
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ x
  have hxσ : x ∈ σ.source := d.mem_shrink φ x.2 (hN.1.mem_data_V x.2) (hVφ hxV)
  obtain ⟨b₀, hb₀⟩ := exists_basis_incFrame_mem_frames (hcs := hcs) hn hN o κ hx
  have hfin := κ.isCornerChart.finiteDimensional
  -- the functional adapted to the frame `e x`
  obtain ⟨N₀, hN₀, hfinN, hrank⟩ :=
    exists_submodule_chartVec_image hφ hN.1 (hN.2 x.1 x.2) (hVφ hxV)
  have hgx := o.isOrientedAt x.1 x.2
  have hex : e x.1 ∈ o.frames x.1 := he x.1 ⟨x.2, hxV⟩
  have hmem : ∀ γ ∈ P.submanifoldTangent N x.1, chartVec hφ γ ∈ N₀ := fun γ hγ => by
    rw [← SetLike.mem_coe, hN₀]; exact ⟨γ, hγ, rfl⟩
  set w : Fin n → N₀ := fun i => ⟨chartVec hφ (e x.1 i), hmem _ (hgx.mem_carrier hex i)⟩
  have hli : LinearIndependent ℝ w :=
    LinearIndependent.of_comp N₀.subtype (hgx.linearIndependent_chartVec hφ (hVφ hxV) hex)
  set bb := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hrank])
  obtain ⟨pr, hpr⟩ := Submodule.ClosedComplemented.of_finiteDimensional N₀
  set Λ : φ.model.E 0 →L[ℝ] (Fin n → ℝ) :=
    (LinearMap.toContinuousLinearMap (bb.equivFun : N₀ →ₗ[ℝ] (Fin n → ℝ))).comp pr with hΛ
  have hΛe : ∀ i j, Λ (chartVec hφ (e x.1 i)) j = if i = j then 1 else 0 := fun i j => by
    have h1 : pr (chartVec hφ (e x.1 i)) = bb i := by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      exact hpr (w i)
    change bb.equivFun (pr (chartVec hφ (e x.1 i))) j = _
    rw [h1, Basis.equivFun_self]
  -- the two matrix fields
  set G : Set N := (κ.s ∩ σ.source) ∩ Subtype.val ⁻¹' V with hG
  have hGo : IsOpen G := (κ.isOpen_s.inter σ.isOpen_source).inter (hV.preimage continuous_subtype_val)
  have hxG : x ∈ G := ⟨⟨hx, hxσ⟩, hxV⟩
  let m : N → EuclideanSpace ℝ (Fin n) →L[ℝ] φ.model.E 0 := fun y =>
    modelDeriv κ hφ d x (levelLift κ.χ 1 y)
  let Cm : N → Matrix (Fin n) (Fin n) ℝ := fun y i j => Λ (m y (b₀ j)) i
  let Bm : N → Matrix (Fin n) (Fin n) ℝ := fun y i j => Λ (chartVec hφ (e y.1 j)) i
  have hcv : ∀ y (hy : y ∈ G) v, chartVec hφ (incFrame hcs κ hy.1.1 v) = m y v := fun y hy v =>
    chartVec_incFrame κ hy.1.1 v hφ d x hy.1.2
  -- continuity
  have hBc : ContinuousOn Bm G := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have h1 : ContinuousOn (fun y : N => chartVec hφ (e y.1 j)) G :=
      ((continuous_apply j).comp_continuousOn hc).comp continuous_subtype_val.continuousOn
        fun y hy => ⟨y.2, hy.2⟩
    exact ((continuous_apply i).comp Λ.continuous).comp_continuousOn h1
  have hCc : ContinuousOn Cm G := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    set R := overlapRet κ.isCornerChart σ
    have hf : IsScSmooth R.U (κ.χ.transition σ ∘ R) :=
      (MPolyfold.IsChart.compatible (subPolyfold hY) κ.isChart hσ).1.comp_isScSmooth R
        (overlapRet_retract κ.isCornerChart σ)
    have hD := hf.isSc1.isSc1With_scDeriv.continuousOn_deriv
    have hz : ∀ y ∈ G, κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y := fun y hy =>
      (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy.1.1)
        (levelVal_mem (hcs.levelOne y))
    have hl : ContinuousOn (fun y : N => levelLift κ.χ 1 y) G := by
      have h1 : ContinuousOn (fun y : N => (κ.χ.model.E.scIsoConst 1).symm (κ.χ y)) G :=
        (κ.χ.model.E.scIsoConst 1).symm.continuous.comp_continuousOn
          (κ.χ.continuousOn_toFun.mono fun y hy => κ.s_subset hy.1.1)
      refine h1.congr fun y hy => ?_
      apply κ.χ.model.E.toBase_injective 1
      rw [hz y hy]
      exact ((κ.χ.model.E.scIsoConst 1).apply_symm_apply (κ.χ y)).symm
    have hcomp := hD.comp (hl.prodMk (continuousOn_const (c := κ.Ψ.symm (ofLpCLM n (b₀ j)))))
      (fun y hy => R.lvlSet_retract_subset 1
        (mem_lvlSet_overlapRet κ.isCornerChart (κ.s_subset hy.1.1) hy.1.2 (hz y hy)))
    exact ((continuous_apply i).comp Λ.continuous).comp_continuousOn hcomp
  have hBx : (Bm x).det = 1 := by
    have : Bm x = 1 := by
      ext i j
      change Λ (chartVec hφ (e x.1 j)) i = _
      rw [hΛe, Matrix.one_apply]
      simp [eq_comm]
    rw [this, Matrix.det_one]
  -- the matrix of the frame of `b₀` in the frame `e`
  have hrel : ∀ y (hy : y ∈ G), ∃ M : Matrix (Fin n) (Fin n) ℝ, Cm y = Bm y * M ∧
      ((fun j => incFrame hcs κ hy.1.1 (b₀ j)) ∈ o.frames y ↔ 0 < M.det) := by
    intro y hy
    have hey : e y.1 ∈ o.frames y.1 := he y.1 ⟨y.2, hy.2⟩
    have hβ : ∀ j, incFrame hcs κ hy.1.1 (b₀ j) ∈ P.submanifoldTangent N y.1 := fun j =>
      incFrame_mem hN.1 κ hy.1.1 _
    obtain ⟨M, hM⟩ := exists_matrix_of_mem_frames hN o y.2 hφ (hVφ hy.2) hey hβ
    refine ⟨M, ?_, IsOrientedAt.mem_frames_iff_det_pos (o.isOrientedAt y.1 y.2) hφ (hVφ hy.2)
      hey hβ M hM⟩
    ext i j
    change Λ (m y (b₀ j)) i = _
    rw [← hcv y hy, hM j, map_sum, Finset.sum_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hCx : 0 < (Cm x).det := by
    obtain ⟨M, hM, hiff⟩ := hrel x hxG
    rw [hM, Matrix.det_mul, hBx, one_mul]
    exact hiff.1 hb₀
  have hdetB : ContinuousAt (fun y => (Bm y).det) x :=
    ((continuous_id.matrix_det).comp_continuousOn hBc).continuousAt (hGo.mem_nhds hxG)
  have hdetC : ContinuousAt (fun y => (Cm y).det) x :=
    ((continuous_id.matrix_det).comp_continuousOn hCc).continuousAt (hGo.mem_nhds hxG)
  have hB0 : ∀ᶠ y in 𝓝 x, 0 < (Bm y).det :=
    hdetB.eventually (lt_mem_nhds (by change 0 < (Bm x).det; rw [hBx]; exact one_pos))
  have hC0 : ∀ᶠ y in 𝓝 x, 0 < (Cm y).det := hdetC.eventually (lt_mem_nhds hCx)
  filter_upwards [hB0, hC0, hGo.mem_nhds hxG] with y hBy hCy hyG
  refine ⟨hyG.1.1, ?_⟩
  obtain ⟨M, hM, hiff⟩ := hrel y hyG
  rw [hM, Matrix.det_mul] at hCy
  have hMpos : 0 < M.det := by
    by_contra h
    exact absurd hCy (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hBy.le (not_lt.1 h)))
  rw [← (orientation_eq_orIn_iff hn hN o κ hyG.1.1 b₀).2 (hiff.2 hMpos),
    ← (orientation_eq_orIn_iff hn hN o κ hx b₀).2 hb₀]

/-! ### The tangent orientation of the manifold `N` -/

section Bridge

variable [inst : ChartedSpace (EuclideanQuadrant n) N]

variable (hcs) in
/-- **The tangent orientation of the tame sheet `N` given by an orientation `o` of Definition
9.3.3**: at `y`, in the chosen corner coordinates at `y`, the positive bases of `ℝⁿ = T_yN` are
those carried by `Tι` to positive frames of `T_y(N, o)`. -/
def bridgeOrientation (o : P.SubmanifoldOrientation N n) : TangentOrientation (𝓠 n) N n :=
  fun y => modelOrToTangent y (orIn hcs o (hcs.coords y) (hcs.mem_coords y))

variable (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **`bridgeOrientation o` read in the Mathlib chart of any corner coordinates `κ`** is
`orIn o κ`. -/
theorem orientationIn_bridgeOrientation (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) (κ : CornerCoords (subPolyfold hY) n) {y : N}
    (hy : y ∈ κ.s) :
    orientationIn κ.toQuadrantChart y (bridgeOrientation hcs o y) = orIn hcs o κ hy := by
  have hman := isManifold_of_eq hcs hch
  have hm := mem_maximalAtlas_of_eq hcs hch
  have hyy : y ∈ (hcs.coords y).s := hcs.mem_coords y
  unfold orientationIn
  rw [chartAt_eq_of_eq hcs hch y]
  change signMap (chartChangeDeriv (𝓠 n) (hcs.coords y).toQuadrantChart κ.toQuadrantChart y)
    (orIn hcs o (hcs.coords y) hyy) = _
  set D := chartChangeDeriv (𝓠 n) (hcs.coords y).toQuadrantChart κ.toQuadrantChart y with hD
  have hdet : D.det ≠ 0 :=
    det_chartChangeDeriv_ne_zero (n := ∞) (by simp) (hm (hcs.coords y)) (hm κ) hyy hy
  obtain ⟨b, hb⟩ := exists_basis_incFrame_mem_frames (hcs := hcs) hn hN o (hcs.coords y) hyy
  have hb' := (orientation_eq_orIn_iff hn hN o (hcs.coords y) hyy b).2 hb
  set f : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearMap.equivOfDetNeZero (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hdet
  have h1 := map_eq_signMap f (A := D) (fun v => rfl)
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin]) b.orientation
  rw [← hb', ← h1, ← Basis.orientation_map, orientation_eq_orIn_iff hn hN o κ hy]
  have hfr : ∀ v, incFrame hcs κ hy (D v) = incFrame hcs (hcs.coords y) hyy v := fun v => by
    unfold incFrame
    rw [fiberMap_chartChange hch (hcs.coords y) κ hyy hy v]
  have : (fun i => incFrame hcs κ hy ((b.map f) i)) =
      fun i => incFrame hcs (hcs.coords y) hyy (b i) := funext fun i => by
    rw [Basis.map_apply]; exact hfr (b i)
  rw [this]; exact hb

/-- **The tangent orientation given by an orientation of Definition 9.3.3 is continuous.** -/
theorem isContinuous_bridgeOrientation (hn : 0 < n) (hN : P.IsSubmanifoldOfDim N n)
    (o : P.SubmanifoldOrientation N n) : (bridgeOrientation hcs o).IsContinuous (𝓠 n) ∞ := by
  have hman := isManifold_of_eq hcs hch
  refine TangentOrientation.isContinuous_of_forall (by simp) fun x =>
    ⟨(hcs.coords x).toQuadrantChart, mem_maximalAtlas_of_eq hcs hch _, hcs.mem_coords x, ?_⟩
  filter_upwards [eventually_orIn_eq hn hN o (hcs.coords x) (hcs.mem_coords x)] with y hy
  obtain ⟨hy, h⟩ := hy
  rw [orientationIn_bridgeOrientation hch hn hN o (hcs.coords x) hy,
    orientationIn_bridgeOrientation hch hn hN o (hcs.coords x) (hcs.mem_coords x), h]

end Bridge

/-! ### Comparison with a graph chart of `N` -/

/-- The frames of a basis of `ℝⁿ` have linearly independent chart vectors. -/
theorem linearIndependent_chartVec_incFrame (hN : P.IsSmoothSubmanifold N)
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {φ : MChart X} (hφ : P.IsChart φ)
    (hyφ : y.1 ∈ φ.source) :
    LinearIndependent ℝ fun i => chartVec hφ (incFrame hcs κ hy (b i)) := by
  set d := (hN.data y.2).toSubData
  have hyσ : y ∈ (subChart d hφ y).source := d.mem_shrink φ y.2 (hN.mem_data_V y.2) hyφ
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy) (levelVal_mem (hcs.levelOne y))
  set m := modelDeriv κ hφ d y (levelLift κ.χ 1 y)
  have hinj : Function.Injective m := modelDeriv_injective κ hφ d y hy hyσ hz
  have h := b.linearIndependent.map' (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0)
    (LinearMap.ker_eq_bot.2 hinj)
  have e : (fun i => chartVec hφ (incFrame hcs κ hy (b i))) =
      (m : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) ∘ b :=
    funext fun i => chartVec_incFrame κ hy (b i) hφ d y hyσ
  rw [e]; exact h

/-- **The frame `Tι(v)` in the frame of a graph chart `c` of `N`**: the coefficients are the
coordinates `c.p` of its chart vector. -/
theorem chartVec_incFrame_eq_sum_tvec (hN : P.IsSmoothSubmanifold N) (c : P.GraphChart n N)
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin n)) :
    chartVec c.isChart (incFrame hcs κ hy v) =
      ∑ i, c.p (chartVec c.isChart (incFrame hcs κ hy v)) i •
        chartVec c.isChart (c.tvec y.1 i) := by
  have hmem : chartVec c.isChart (incFrame hcs κ hy v) ∈ P.chartTangent c.isChart N y.1 :=
    ⟨_, incFrame_mem hN κ hy v, rfl⟩
  conv_lhs => rw [← c.L_p_of_mem y.2 hmem, c.L_apply y.2]

include hcs in
/-- **The coordinate change from corner coordinates `κ` to a graph chart `c`** is differentiable
within the quadrant, with derivative `c.p ∘ modelDeriv`. -/
theorem hasFDerivWithinAt_coord_corner (c : P.GraphChart n N)
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s) (d : P.SubData N) (a₀ : N)
    (hyσ : y ∈ (subChart d c.isChart a₀).source) :
    HasFDerivWithinAt (fun u => c.coord ((κ.toQuadrantChart.extend (𝓠 n)).symm u).1)
      (c.p.comp (modelDeriv κ c.isChart d a₀ (levelLift κ.χ 1 y))) (range (𝓠 n))
      (κ.toQuadrantChart.extend (𝓠 n) y) := by
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy) (levelVal_mem (hcs.levelOne y))
  exact c.p.hasFDerivAt.comp_hasFDerivWithinAt _
    (hasFDerivWithinAt_incl κ c.isChart d a₀ hy hyσ hz)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {N : Set Obj} [ParacompactSpace N] {hY : X.PObj.IsSubMPolyfold N}
  {hcs : (MPolyfold.subPolyfold hY).HasCornerStructureOfDim n}

/-- **The value of an sc-form of the ep-groupoid on the frame `Tι(v)`** is the pull-back of the
form to `N` on `v` in corner coordinates: for `κ` the chosen coordinates at `y` this is
`scFormRestrict n hcs 0 ω y v` (`scFormRestrict_zero_apply`). -/
theorem epFormEval_ev_incFrame (hn : 0 < n) (ω : X.epForms n)
    (κ : MPolyfold.CornerCoords (MPolyfold.subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (X.epFormEval n).ev ω (fun i => MPolyfold.incFrame hcs κ hy (v i)) =
      MPolyfold.formPullback (MPolyfold.subPolyfold_inclusion_isScSmooth hY) ω.1
        (hcs.levelOne y) fun i => κ.fiberMap (x := hcs.levelOne y) (κ.s_subset hy) (v i) := by
  rw [MPolyfold.formPullback_apply, ← X.epFormEval_ev_eq hn ω]
  congr 1
  funext i
  exact (MPolyfold.coe_tangentFiberMap_apply _ _).symm

open Classical in
/-- **The density of a graph chart and the value on a corner frame**: for a basis `b` of `ℝⁿ`,
`± ω(Tι(b₁), …, Tι(bₙ)) = |det M| · density`, the sign `+` iff the frame is positive for `o`,
`M` the matrix of the coordinates of the frame in the graph chart `c` (the matrix of the
derivative of the coordinate change, `hasFDerivWithinAt_coord_corner`). -/
theorem FormEval.sgn_mul_ev_incFrame {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (F : X.FormEval n Ω) (hN : X.PObj.IsSubmanifoldOfDim N n) (c : X.PObj.GraphChart n N)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (κ : MPolyfold.CornerCoords (MPolyfold.subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (if (fun i => MPolyfold.incFrame hcs κ hy (b i)) ∈ o.frames y then (1 : ℝ) else -1) *
        F.ev ω (fun i => MPolyfold.incFrame hcs κ hy (b i)) =
      |(Matrix.of fun i j =>
          c.p (MPolyfold.chartVec c.isChart (MPolyfold.incFrame hcs κ hy (b j))) i).det| *
        F.density c ω o.tangent y := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    c.p (MPolyfold.chartVec c.isChart (MPolyfold.incFrame hcs κ hy (b j))) i with hM
  set β : Fin n → X.PObj.TangentSpace := fun i => MPolyfold.incFrame hcs κ hy (b i) with hβdef
  have hsrc : y.1 ∈ c.φ.source := c.subset_source y.2
  have hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y.1 := fun i =>
    MPolyfold.incFrame_mem hN.1 κ hy _
  have hD : ∀ j, MPolyfold.chartVec c.isChart (β j) =
      ∑ i, M i j • MPolyfold.chartVec c.isChart (c.tvec y.1 i) := fun j =>
    MPolyfold.chartVec_incFrame_eq_sum_tvec hN.1 c κ hy (b j)
  have hev : F.ev ω β = M.det * F.ev ω (c.tvec y.1) :=
    F.ev_det ω hN.1 y.2 c.isChart hsrc (c.tvec y.1) β (c.tvec_mem y.2) hβ M hD
  have key := MPolyfold.IsOrientedAt.frames_iff_frames_iff_det_pos hN y.2
    (o.isOrientedAt y y.2) c.isChart hsrc (c.tvec_mem y.2) hβ
    (c.linearIndependent_chartVec_tvec y.2)
    (MPolyfold.linearIndependent_chartVec_incFrame hN.1 κ hy b c.isChart hsrc) M hD
  simp only [FormEval.density, c.frameSgn_tangent]
  rw [hev]
  by_cases hpos : 0 < M.det
  · have hiff := key.2 hpos
    rw [abs_of_pos hpos]
    by_cases h : β ∈ o.frames y
    · rw [if_pos h, if_pos (hiff.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; ring
  · have hniff : ¬ (β ∈ o.frames y ↔ c.tvec y.1 ∈ o.frames y) := fun h => hpos (key.1 h)
    rw [abs_of_nonpos (not_lt.1 hpos)]
    by_cases h : β ∈ o.frames y
    · have h' : c.tvec y.1 ∉ o.frames y := fun h' => hniff ⟨fun _ => h', fun _ => h⟩
      rw [if_pos h, if_neg h']; ring
    · have h' : c.tvec y.1 ∈ o.frames y := by
        by_contra h'
        exact hniff ⟨fun a => (h a).elim, fun a => (h' a).elim⟩
      rw [if_neg h, if_pos h']; ring

/-- The standard basis of `ℝⁿ`. -/
abbrev stdBasis (n : ℕ) : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

open Classical in
/-- The density of `ω` on `(N, o)` in the corner coordinates `κ`:
`± ω(Tι(e₁), …, Tι(eₙ))`, the sign `+` iff the coordinate frame is positive for `o`. -/
def FormEval.cornerDensity {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)
    (hcs : (MPolyfold.subPolyfold hY).HasCornerStructureOfDim n)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (κ : MPolyfold.CornerCoords (MPolyfold.subPolyfold hY) n) (y : N) : ℝ :=
  if hy : y ∈ κ.s then
    (if (fun i => MPolyfold.incFrame hcs κ hy (stdBasis n i)) ∈ o.frames y then (1 : ℝ) else -1) *
      F.ev ω (fun i => MPolyfold.incFrame hcs κ hy (stdBasis n i))
  else 0

/-- **The integral in a graph chart and in corner coordinates agree on one corner chart**: for
`A ⊆ κ.s` with measurable coordinate image, `∫_A ω|(N, o)` computed in the graph chart `c` is
the Lebesgue integral over `κ(A) ⊆ [0,∞)ⁿ` of `± ω(Tι(e₁), …, Tι(eₙ))`. -/
theorem FormEval.chartInteg_eq_setIntegral_corner {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (F : X.FormEval n Ω) (hN : X.PObj.IsSubmanifoldOfDim N n) (c : X.PObj.GraphChart n N)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (κ : MPolyfold.CornerCoords (MPolyfold.subPolyfold hY) n) {A : Set N} (hA : A ⊆ κ.s)
    (hAm : MeasurableSet (κ.toQuadrantChart.extend (𝓠 n) '' A)) :
    F.chartInteg c ω o.tangent (Subtype.val '' A) =
      ∫ u in κ.toQuadrantChart.extend (𝓠 n) '' A,
        F.cornerDensity hcs o ω κ ((κ.toQuadrantChart.extend (𝓠 n)).symm u) := by
  set ext := κ.toQuadrantChart.extend (𝓠 n) with hext
  have hleft : ∀ y ∈ κ.s, ext.symm (ext y) = y := fun y hy =>
    κ.toQuadrantChart.extend_left_inv (I := 𝓠 n) hy
  let DN : N → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun y =>
    c.p.comp (modelDeriv κ c.isChart (hN.1.data y.2).toSubData y (MPolyfold.levelLift κ.χ 1 y))
  have hσ : ∀ y : N, y ∈ (MPolyfold.subChart (hN.1.data y.2).toSubData c.isChart y).source :=
    fun y => (hN.1.data y.2).toSubData.mem_shrink c.φ y.2 (hN.1.mem_data_V y.2)
      (c.subset_source y.2)
  set τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => c.coord (ext.symm u).1 with hτ
  have hsub : ext '' A ⊆ range (𝓠 n) := by
    rintro _ ⟨y, -, rfl⟩
    rw [hext, OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hderiv : ∀ u ∈ ext '' A, HasFDerivWithinAt τ (DN (ext.symm u)) (ext '' A) u := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hleft y (hA hy)]
    exact (MPolyfold.hasFDerivWithinAt_coord_corner (hcs := hcs) c κ (hA hy) _ y (hσ y)).mono hsub
  have hinj : InjOn τ (ext '' A) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩ h
    simp only [hτ, hleft y (hA hy), hleft w (hA hw)] at h
    rw [Subtype.ext (c.injOn_coord y.2 w.2 h)]
  have himg : τ '' (ext '' A) = c.coord '' (Subtype.val '' A ∩ N) := by
    rw [image_image, inter_eq_left.2 (by rintro _ ⟨y, -, rfl⟩; exact y.2), image_image]
    exact image_congr fun y hy => by simp only [hτ, hleft y (hA hy)]
  unfold FormEval.chartInteg
  rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hAm hderiv hinj]
  refine setIntegral_congr_fun hAm ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyκ := hA hy
  simp only [hτ, hleft y hyκ, smul_eq_mul]
  rw [c.q_coord' y.2, FormEval.cornerDensity, dif_pos hyκ,
    F.sgn_mul_ev_incFrame (hcs := hcs) hN c o ω κ hyκ (stdBasis n)]
  congr 2
  rw [← MPolyfold.GraphChart.det_matrix_bvec (DN y)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, DN, ContinuousLinearMap.comp_apply]
  rw [← MPolyfold.chartVec_incFrame (hcs := hcs) κ hyκ _ c.isChart _ y (hσ y)]
  have hb : stdBasis n j = MPolyfold.GraphChart.bvec j := by
    simp [stdBasis, MPolyfold.GraphChart.bvec]
  rw [hb]

end EpGroupoid

end Polyfold
