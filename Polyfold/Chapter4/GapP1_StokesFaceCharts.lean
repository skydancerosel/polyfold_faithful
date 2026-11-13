import Polyfold.Chapter4.GapP1_StokesFaces
import Polyfold.Chapter9.SolutionFaces2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28): the faces `F` of the compact tame
submanifold `N` as manifolds in their own right (gap G.40, first step).

# A corner structure of dimension `n` on each face

Let `P` be an M-polyfold with a corner structure of dimension `n + 1` (2021 Definition 4.1.1,
`HasCornerStructureOfDim`), face-structured (Definition 2.5.10; the reading of the text's
"whose boundary is a union of smooth faces").  Then every face `F` is a sub-M-polyfold
(Theorem 2.5.17, `theorem_2_5_17_isSubMPolyfold_face`), and here it gets a **corner structure of
dimension `n`** (`hasCornerStructureOfDim_face`), so `F` is a Mathlib manifold modelled on
`[0,∞)ⁿ` (`cornerChartedSpace`).

* `CornerCoords.linChart`: the corner coordinates `x ↦ Ψ χ(x) + c` of `P` as a chart of `P`
  (a corner chart modelled on `W ∩ [0,∞)ⁿ⁺¹` in `ℝⁿ⁺¹` with the constant structure),
  `CornerCoords.linChart_isChart` (`MChart.compRetract_isChart`).
* `CornerCoords.exists_faceData`: at a point `x` of a face `F` in the coordinate piece of `κ`,
  `F` is near `x` the coordinate face `{yᵢ = 0}` (`exists_face_eq_coordHyper`).
* `FaceData.chart`: the face chart `y ↦ (yₖ)_{k ≠ i}` of `F` (`faceChart` on `linChart`, with the
  linear maps `insertNth i 0`, `removeNth i` between constant structures).  It is a corner chart
  as defined (`FaceData.chart_isCornerChart`): its model is *propositionally* the model of the
  relatively open piece `W' ∩ [0,∞)ⁿ`, and the two local models agree by proof irrelevance once the
  retract is identified (`FaceData.image_eq`), so no copy of the chart is needed.
* `FaceData.coords`: the corresponding corner coordinates of `F`, with
  `coord_F = removeNth i ∘ coord` (`FaceData.coords_coord`).
-/

open Set Function Topology Module

noncomputable section

namespace Polyfold

/-! ### Inserting and removing a coordinate, as linear maps -/

section InsertRemove

variable {n : ℕ}

/-- `z ↦ insertNth i 0 z`, `ℝⁿ → ℝⁿ⁺¹`. -/
def insertZeroL (i : Fin (n + 1)) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => i.insertNth (α := fun _ => ℝ) 0 z
      map_add' := fun y z => by
        ext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩ <;> simp
      map_smul' := fun c z => by
        ext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩ <;> simp }

/-- `y ↦ (y_k)_{k ≠ i}`, `ℝⁿ⁺¹ → ℝⁿ`. -/
def removeL (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => i.removeNth y
      map_add' := fun y z => by ext k; simp [Fin.removeNth]
      map_smul' := fun c y => by ext k; simp [Fin.removeNth] }

@[simp] theorem insertZeroL_apply (i : Fin (n + 1)) (z : Fin n → ℝ) :
    insertZeroL i z = i.insertNth (α := fun _ => ℝ) 0 z := rfl

@[simp] theorem removeL_apply (i : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    removeL i y = i.removeNth y := rfl

theorem removeL_insertZeroL (i : Fin (n + 1)) (z : Fin n → ℝ) :
    removeL i (insertZeroL i z) = z := by
  simp

theorem insertZeroL_removeL {i : Fin (n + 1)} {y : Fin (n + 1) → ℝ} (hy : y i = 0) :
    insertZeroL i (removeL i y) = y := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · simp [hy]
  · simp [Fin.removeNth]

end InsertRemove

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- A corner structure of dimension `n` makes the M-polyfold tame (its corner charts are). -/
theorem HasCornerStructureOfDim.isTame {n : ℕ} (h : P.HasCornerStructureOfDim n) : P.IsTame :=
  h.hasCornerStructure.isTame

/-! ### Corner coordinates as a chart -/

namespace CornerCoords

variable {m : ℕ} (κ : CornerCoords P m)

/-- The local model `W ∩ [0,∞)ᵐ` of the coordinates, in `ℝᵐ` with the constant structure. -/
abbrev linModel : LocalModel := LocalModel.ofRelOpen (isRelOpenInQuadrant_stdQuadrant κ.isOpen_W)

theorem image_coordAff : (fun v => κ.Ψ v + κ.c) '' (κ.χ '' κ.s) = κ.W ∩ {y | ∀ i, 0 ≤ y i} :=
  κ.image_s

theorem isScSmoothRetractMap_coordAff :
    IsScSmoothRetractMap (κ.χ.restrict κ.s_subset κ.isOpen_s).model.E
      (κ.χ.restrict κ.s_subset κ.isOpen_s).model.C (κ.χ.restrict κ.s_subset κ.isOpen_s).model.O
      κ.linModel.E κ.linModel.C κ.linModel.O (fun v => κ.Ψ v + κ.c) :=
  (isScSmoothRetractMap_iff_exists (κ.χ.restrict κ.s_subset κ.isOpen_s).model.isScRetract).2
    ⟨fun v hv => by
        change v ∈ κ.χ '' κ.s at hv
        have h := mem_image_of_mem (fun v => κ.Ψ v + κ.c) hv
        rw [κ.image_coordAff] at h
        exact h,
      ScRetraction.id κ.isRelOpenInQuadrant_image_s, image_id _, κ.isScSmooth_coordAff⟩

theorem mapsTo_coordAffInv :
    MapsTo (fun y => κ.Ψ.symm (y - κ.c)) (κ.W ∩ {y | ∀ i, 0 ≤ y i}) (κ.χ '' κ.s) := by
  intro y hy
  rw [← κ.image_coordAff] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  simpa using hv

theorem isScSmoothRetractMap_coordAffInv :
    IsScSmoothRetractMap κ.linModel.E κ.linModel.C κ.linModel.O
      (κ.χ.restrict κ.s_subset κ.isOpen_s).model.E (κ.χ.restrict κ.s_subset κ.isOpen_s).model.C
      (κ.χ.restrict κ.s_subset κ.isOpen_s).model.O (fun y : Fin m → ℝ => κ.Ψ.symm (y - κ.c)) :=
  (isScSmoothRetractMap_iff_exists κ.linModel.isScRetract).2
    ⟨κ.mapsTo_coordAffInv, ScRetraction.id (isRelOpenInQuadrant_stdQuadrant κ.isOpen_W),
      image_id _, κ.isScSmooth_coordAffInv⟩

/-- **The corner coordinates as a chart** `x ↦ Ψ χ(x) + c` on the piece `s`, modelled on
`W ∩ [0,∞)ᵐ ⊆ ℝᵐ` (the constant structure, identity retraction). -/
def linChart : MChart X :=
  (κ.χ.restrict κ.s_subset κ.isOpen_s).compRetract κ.linModel κ.isScSmoothRetractMap_coordAff
    κ.isScSmoothRetractMap_coordAffInv
    (fun v _ => (congrArg κ.Ψ.symm (add_sub_cancel_right (κ.Ψ v) κ.c)).trans
      (κ.Ψ.symm_apply_apply v))
    (fun (y : Fin m → ℝ) _ => (congrArg (· + κ.c) (κ.Ψ.apply_symm_apply (y - κ.c))).trans
      (sub_add_cancel (y : Fin m → ℝ) κ.c))

@[simp] theorem linChart_apply (x : X) : κ.linChart x = κ.coord x := rfl

@[simp] theorem linChart_source : κ.linChart.source = κ.s := rfl

theorem linChart_model : κ.linChart.model = κ.linModel := rfl

theorem linChart_isChart : P.IsChart κ.linChart :=
  MChart.compRetract_isChart _ _ _ _ (IsChart.restrict P κ.isChart κ.s_subset κ.isOpen_s)

theorem linChart_isCornerChart : κ.linChart.IsCornerChart :=
  ⟨Fin m → ℝ, inferInstance, inferInstance, inferInstance, _, _,
    isRelOpenInQuadrant_stdQuadrant κ.isOpen_W, rfl⟩

theorem coord_injOn : InjOn κ.coord κ.s := fun x hx y hy h => by
  rw [← κ.coordInv_coord hx, h, κ.coordInv_coord hy]

theorem isOpen_inter_preimage_coord {B : Set (Fin m → ℝ)} (hB : IsOpen B) :
    IsOpen (κ.s ∩ κ.coord ⁻¹' B) :=
  κ.continuousOn_coord.isOpen_inter_preimage κ.isOpen_s hB

/-! ### A face is a coordinate face near each of its points -/

/-- **A face in corner coordinates**: if `P` is face-structured, `F` a face and `x ∈ F` in the
piece of `κ`, there are a coordinate `i` with `κ.coord x i = 0` and an open `B ∋ κ.coord x` such
that, for `y` in the piece with `κ.coord y ∈ B`, `y ∈ F ↔ κ.coord y i = 0`
(`exists_face_eq_coordHyper` for the chart `linChart`). -/
theorem exists_face_coord (hfs : P.IsFaceStructured) {F : Set X} (hF : P.IsFace F) {x : X}
    (hx : x ∈ F) (hxs : x ∈ κ.s) :
    ∃ i : Fin m, κ.coord x i = 0 ∧ ∃ B : Set (Fin m → ℝ), IsOpen B ∧ κ.coord x ∈ B ∧
      ∀ y ∈ κ.s, κ.coord y ∈ B → (y ∈ F ↔ κ.coord y i = 0) := by
  have hU := isRelOpenInQuadrant_stdQuadrant κ.isOpen_W
  obtain ⟨i, hi, B, hB, hxB, hEq⟩ := exists_face_eq_coordHyper hfs hF hx κ.linChart_isChart
    hxs (ScRetraction.id hU) (image_id _) (T := stdQuadrantPres m) (stdQuadrant_eq m)
    (ScRetraction.id_isTame hU m _ (stdQuadrantPres m) (stdQuadrant_eq m))
  refine ⟨i, hi, B, hB, hxB, fun y hy hyB => ⟨fun hyF => ?_, fun hyi => ?_⟩⟩
  · exact ((Set.ext_iff.1 hEq (κ.linChart y)).1 ⟨⟨y, ⟨hyF, hy⟩, rfl⟩, hyB⟩).1.1
  · obtain ⟨⟨y', ⟨hy'F, hy's⟩, hyy'⟩, -⟩ :=
      (Set.ext_iff.1 hEq (κ.linChart y)).2 ⟨⟨hyi, κ.linChart.mapsTo_model y hy⟩, hyB⟩
    rwa [κ.coord_injOn hy's hy hyy'] at hy'F

end CornerCoords

/-! ### Face data and the face charts -/

variable {n : ℕ}

/-- **A face `F` in the coordinates `κ`**: a coordinate `i` and an open `B ⊆ ℝⁿ⁺¹` such that the
points `y` of the piece with `κ.coord y ∈ B` lie in `F` iff `κ.coord y i = 0`. -/
structure FaceData (κ : CornerCoords P (n + 1)) (F : Set X) where
  /-- The coordinate of the face. -/
  i : Fin (n + 1)
  /-- The open set of coordinates in which `F` is the coordinate face. -/
  B : Set (Fin (n + 1) → ℝ)
  isOpen_B : IsOpen B
  mem_iff : ∀ y ∈ κ.s, κ.coord y ∈ B → (y ∈ F ↔ κ.coord y i = 0)

namespace CornerCoords

variable (κ : CornerCoords P (n + 1))

/-- At every point of a face in the piece of `κ` there is face data, with `B` inside a prescribed
open set `B₀ ∋ κ.coord x` (`exists_face_coord`). -/
theorem exists_faceData (hfs : P.IsFaceStructured) {F : Set X} (hF : P.IsFace F) {x : X}
    (hx : x ∈ F) (hxs : x ∈ κ.s) {B₀ : Set (Fin (n + 1) → ℝ)} (hB₀ : IsOpen B₀)
    (hxB₀ : κ.coord x ∈ B₀) :
    ∃ D : FaceData κ F, κ.coord x D.i = 0 ∧ κ.coord x ∈ D.B ∧ D.B ⊆ B₀ := by
  obtain ⟨i, hi, B, hB, hxB, h⟩ := κ.exists_face_coord hfs hF hx hxs
  exact ⟨⟨i, B ∩ B₀, hB.inter hB₀, fun y hy hyB => h y hy hyB.1⟩, hi, ⟨hxB, hxB₀⟩,
    inter_subset_right⟩

end CornerCoords

namespace FaceData

variable {κ : CornerCoords P (n + 1)} {F : Set X} (D : FaceData κ F)

/-- The domain `V₁ = {y ∈ s | κ.coord y ∈ B}` of the face chart. -/
def V₁ : Set X := κ.s ∩ κ.coord ⁻¹' D.B

theorem isOpen_V₁ : IsOpen D.V₁ := κ.isOpen_inter_preimage_coord D.isOpen_B

theorem V₁_subset : D.V₁ ⊆ κ.linChart.source := inter_subset_left

theorem coord_eq_zero {y : X} (hyF : y ∈ F) (hy : y ∈ D.V₁) : κ.coord y D.i = 0 :=
  (D.mem_iff y hy.1 hy.2).1 hyF

theorem mem_of_coord_eq_zero {y : X} (hy : y ∈ D.V₁) (hi : κ.coord y D.i = 0) : y ∈ F :=
  (D.mem_iff y hy.1 hy.2).2 hi

/-- The open set `W' = {z ∈ ℝⁿ | insertNth i 0 z ∈ W ∩ B}` of the face chart. -/
def W' : Set (Fin n → ℝ) := insertZeroL D.i ⁻¹' (κ.W ∩ D.B)

theorem isOpen_W' : IsOpen D.W' :=
  (κ.isOpen_W.inter D.isOpen_B).preimage (insertZeroL D.i).continuous

/-- **The image of the face**: `removeNth i (κ.coord (F ∩ V₁)) = W' ∩ [0,∞)ⁿ`. -/
theorem image_eq :
    removeL D.i '' (κ.coord '' (F ∩ D.V₁)) = D.W' ∩ {z | ∀ k, 0 ≤ z k} := by
  ext z
  constructor
  · rintro ⟨_, ⟨y, ⟨hyF, hy⟩, rfl⟩, rfl⟩
    have hi := D.coord_eq_zero hyF hy
    refine ⟨?_, fun k => ?_⟩
    · change insertZeroL D.i (removeL D.i (κ.coord y)) ∈ κ.W ∩ D.B
      rw [insertZeroL_removeL hi]
      exact ⟨κ.coord_mem_W hy.1, hy.2⟩
    · exact κ.coord_nonneg hy.1 _
  · rintro ⟨⟨hzW, hzB⟩, hz⟩
    have hnn : ∀ k, 0 ≤ insertZeroL D.i z k := fun k => by
      rcases Fin.eq_self_or_eq_succAbove D.i k with rfl | ⟨l, rfl⟩
      · simp
      · simpa using hz l
    obtain ⟨y, hys, hyz⟩ := κ.exists_coord_eq hzW hnn
    have hyV : y ∈ D.V₁ := ⟨hys, by rw [mem_preimage, hyz]; exact hzB⟩
    have hyi : κ.coord y D.i = 0 := by rw [hyz]; simp
    refine ⟨κ.coord y, ⟨y, ⟨D.mem_of_coord_eq_zero hyV hyi, hyV⟩, rfl⟩, ?_⟩
    rw [hyz, removeL_insertZeroL]

theorem isRelOpenInQuadrant :
    IsRelOpenInQuadrant (ScBanach.const (Fin n → ℝ)) {z : Fin n → ℝ | ∀ k, 0 ≤ z k}
      (ScOperator.ofConst (removeL D.i) 0 '' (κ.linChart '' (F ∩ D.V₁))) := by
  change IsRelOpenInQuadrant (ScBanach.const (Fin n → ℝ)) {z : Fin n → ℝ | ∀ k, 0 ≤ z k}
    (removeL D.i '' (κ.coord '' (F ∩ D.V₁)))
  rw [D.image_eq]
  exact isRelOpenInQuadrant_stdQuadrant D.isOpen_W'

variable (x₀ : F)

/-- **The face chart** `y ↦ removeNth i (κ.coord y)` of `F` on `F ∩ V₁` (`faceChart` on the chart
`linChart`, with `ι = insertNth i 0`, `π = removeNth i`), modelled on `W' ∩ [0,∞)ⁿ`. -/
def chart : MChart F :=
  faceChart x₀ κ.linChart D.V₁ {z : Fin n → ℝ | ∀ k, 0 ≤ z k}
    (ScOperator.ofConst (insertZeroL D.i)) (ScOperator.ofConst (removeL D.i)) D.isOpen_V₁
    D.V₁_subset
    (by
      rintro _ ⟨y, ⟨hyF, hy⟩, rfl⟩
      exact insertZeroL_removeL (D.coord_eq_zero hyF hy))
    (fun z => removeL_insertZeroL D.i z) D.isRelOpenInQuadrant.isScRetract

theorem chart_apply (y : F) : D.chart x₀ y = removeL D.i (κ.coord y) := rfl

theorem chart_source : (D.chart x₀).source = {y : F | (y : X) ∈ D.V₁} := rfl

theorem chart_model_O : (D.chart x₀).model.O = D.W' ∩ {z | ∀ k, 0 ≤ z k} := D.image_eq

/-- **The face chart is a corner chart** (Definition 4.1.1): its model is the relatively open
piece `W' ∩ [0,∞)ⁿ` of `ℝⁿ` with the constant structure; the two local models agree by proof
irrelevance. -/
theorem chart_isCornerChart : (D.chart x₀).IsCornerChart :=
  ⟨Fin n → ℝ, inferInstance, inferInstance, inferInstance, _, _, D.isRelOpenInQuadrant, rfl⟩

theorem chart_finrank : finrank ℝ ((D.chart x₀).model.E 0) = n := by
  change finrank ℝ (Fin n → ℝ) = n
  simp

/-- **The face chart is a chart of the induced structure on `F`** (its transition maps to the
sub-charts of `F` built on `linChart` are `ι` and `π`, `faceChart_compatible_subChart`). -/
theorem chart_isChart [ParacompactSpace F] (hA : P.IsSubMPolyfold F) :
    (subPolyfold hA).IsChart (D.chart x₀) :=
  isChart_subPolyfold_of_compatible hA κ.linChart_isChart (fun _ hy => D.V₁_subset hy)
    fun d b₀ => faceChart_compatible_subChart κ.linChart_isChart D.isOpen_V₁ D.V₁_subset _
      (fun z => removeL_insertZeroL D.i z) _ d b₀

/-- **The corner coordinates of the face chart**: `Ψ = id`, `c = 0`, the piece `F ∩ V₁` and
`W'`. -/
def coords [ParacompactSpace F] (hA : P.IsSubMPolyfold F) : CornerCoords (subPolyfold hA) n where
  χ := D.chart x₀
  isChart := D.chart_isChart x₀ hA
  isCornerChart := D.chart_isCornerChart x₀
  s := {y : F | (y : X) ∈ D.V₁}
  isOpen_s := D.isOpen_V₁.preimage continuous_subtype_val
  s_subset := subset_rfl
  Ψ := ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)
  c := 0
  W := D.W'
  isOpen_W := D.isOpen_W'
  image_s := by
    have h : (D.chart x₀) '' {y : F | (y : X) ∈ D.V₁} = D.W' ∩ {z | ∀ k, 0 ≤ z k} := by
      rw [← D.chart_model_O x₀]; exact (D.chart x₀).image_source
    simp only [add_zero]
    exact (image_congr (fun z _ => rfl)).trans ((image_id _).trans h)

variable [ParacompactSpace F] (hA : P.IsSubMPolyfold F)

theorem coords_s : (D.coords x₀ hA).s = {y : F | (y : X) ∈ D.V₁} := rfl

theorem coords_coord (y : F) : (D.coords x₀ hA).coord y = removeL D.i (κ.coord y) := by
  change removeL D.i (κ.coord y) + 0 = _
  rw [add_zero]

/-- The point of `F` over `z ∈ W' ∩ [0,∞)ⁿ`: its coordinates are `insertNth i 0 z`. -/
theorem coord_coordInv {z : Fin n → ℝ} (hzW : z ∈ D.W') (hz : ∀ k, 0 ≤ z k) :
    κ.coord ((D.coords x₀ hA).coordInv z : X) = insertZeroL D.i z := by
  have h1 := (D.coords x₀ hA).coord_coordInv hzW hz
  have h2 := (D.coords x₀ hA).coordInv_mem hzW hz
  rw [coords_coord] at h1
  calc κ.coord ((D.coords x₀ hA).coordInv z : X)
      = insertZeroL D.i (removeL D.i (κ.coord ((D.coords x₀ hA).coordInv z : X))) :=
        (insertZeroL_removeL (D.coord_eq_zero ((D.coords x₀ hA).coordInv z).2 h2)).symm
    _ = insertZeroL D.i z := by rw [h1]

theorem coordInv_mem_V₁ {z : Fin n → ℝ} (hzW : z ∈ D.W') (hz : ∀ k, 0 ≤ z k) :
    ((D.coords x₀ hA).coordInv z : X) ∈ D.V₁ :=
  (D.coords x₀ hA).coordInv_mem hzW hz

end FaceData

/-! ### The corner structure of a face -/

/-- **Every face of a face-structured M-polyfold with a corner structure of dimension `n + 1` has
a corner structure of dimension `n`** (2021 Theorem 4.4.7: the faces `F` of `N` as manifolds in
their own right): at `x ∈ F`, the face chart of the coordinate face `{yᵢ = 0}` through `x` of
corner coordinates of `P` at `x`. -/
theorem hasCornerStructureOfDim_face (hcs : P.HasCornerStructureOfDim (n + 1))
    (hfs : P.IsFaceStructured) {F : Set X} (hF : P.IsFace F) :
    haveI : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed P hF)
    (subPolyfold (theorem_2_5_17_isSubMPolyfold_face P hcs.isTame hfs hF)).HasCornerStructureOfDim
      n := by
  have : ParacompactSpace F := paracompactSpace_of_isClosed (IsFace.isClosed P hF)
  intro x
  obtain ⟨κ, hxκ⟩ := hcs.exists_cornerCoords x
  obtain ⟨D, -, hxB, -⟩ := κ.exists_faceData hfs hF x.2 hxκ isOpen_univ (mem_univ _)
  exact ⟨D.chart x, D.chart_isChart x _, show (x : X) ∈ D.V₁ from ⟨hxκ, hxB⟩,
    D.chart_isCornerChart x, D.chart_finrank x⟩

end MPolyfold

end Polyfold
