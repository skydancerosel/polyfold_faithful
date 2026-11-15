import Polyfold.Chapter15.BoundaryFrameCriterion
import Polyfold.Chapter15.CylinderEndStructures
import Polyfold.Chapter15.CanonicalOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the sign in "`∂Θ̃ = Θ₁ ⊔ −Θ₀`"; Definition 9.3.8
(p. 427), Remark 6.6.19 and Theorem 6.7.1 for the conventions.

# The sign of the boundary orientation on the ends of the cylinder

## The text, paraphrased

With the canonical orientations, `∂Θ̃ = Θ₁ ⊔ −Θ₀`: over the end `{i} × X` the boundary
orientation of a sheet `M̃ = {f̃ = s̃}` of the cobordism is `(−1)^{i+1}` times the orientation of
the sheet `M = {f = s̃(i, ·)}` of `Θᵢ`.  The kernel `ker (f̃ − s̃)'(i, y)` is
`ℝ·(∂_t + u) ⊕ ker (f − s)'(y)`, oriented with the `ℝ`-factor first (Remark 6.6.19), and the
boundary orientation puts the outward normal first (Definition 9.3.8): `+∂_t` at `t = 1`,
`−∂_t` at `t = 0`.

## What is formalized

* `MPolyfold.cubePresentedChart`, `MPolyfold.cubeTimeComponent`, `cylTimeComponent`: the
  product charts of `[0, 1] × X` with their partial quadrants, and the `t`-component `dt(w)`
  of a tangent vector, through the tangent map of the projection to `[0, 1]`.
* `MPolyfold.not_isInwardVec_of_cubeTimeComponent_pos`,
  `MPolyfold.isInwardVec_of_cubeTimeComponent_pos`: `dt(w) > 0` is outward at `t = 1` and
  inward at `t = 0`.
* **`boundaryOrient_tangent_eq_faceOrient_of_end_one`**,
  **`boundaryOrient_tangent_ne_faceOrient_of_end_zero`**: the pointwise frame criterion.  If
  `(w, Tι_q α)` is a positive frame of a sheet `M̃` of the cylinder at `(q, y)`, with
  `dt(w) > 0` and `α` a positive frame of `(N, o)`, `∂₁M̃ = ι_q(N)`, then the boundary
  orientation of `∂₁M̃` is `ι_q_*o` at `t = 1` and the opposite one at `t = 0`.
* `mem_tangent_cubeFace_iff_cylTimeComponent`: `T_{(q, y)}M̃ ∩ {dt = 0} = Tι_q(T_yN)`.
* `HasTimeFirstFrames`: the convention "`t` first" for a pair of oriented tame structures;
  **`areMatchedAt_of_timeFirstFrames_one`**, **`areMatchedAt_of_timeFirstFrames_zero`**: with
  it, structures whose sheets match over the end are matched (`AreMatchedAt`) with sign `+1`
  at `t = 1` and `−1` at `t = 0`.
* `CylinderKernelFrameConvention`: the convention for the canonical orientations of `(f, o)`
  and `(f̃, õ)` in structures described by kernels;
  `KernelBranching.hasTimeFirstFrames_of_convention`,
  **`KernelBranching.areMatchedAt_one`**, **`KernelBranching.areMatchedAt_zero`**: the sign
  clause for the structures `KernelBranching.toOrientedTame`.

## Reading

The convention of the library for Definition 9.3.8 is "outward vector first"
(`MPolyfold.boundaryOp`); with the `ℝ`-factor of the kernel first and pointing in the direction
of increasing `t`, the signs are `+1` at `t = 1` and `−1` at `t = 0`, as in the text.
`CylinderKernelFrameConvention` is a hypothesis: it states the relation between `õ` and `o` of
Remark 6.6.19 on the kernels, and is not derived here from the orientations of the
determinants.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]

/-- **The presented product chart of `[0, 1] × X` at `(q, y)`**: the corner chart `b` of
`[0, 1]` (coordinate `s = t` for `b = true`, `s = 1 − t` for `b = false`) times a presented
chart of `X` at `y`; the first quadrant coordinate is `s`. -/
def cubePresentedChart (b : Fin 1 → Bool) {q : Fin 1 → unitInterval}
    (hq : q ∈ (UnitCube.chart b).source) {y : X} (c : P.PresentedChart y) :
    ((cubePolyfold 1).prod P).PresentedChart (q, y) where
  φ := (UnitCube.chart b).prod c.φ
  isChart := (UnitCube.isChart_chart b).prod c.isChart
  mem_source := ⟨hq, c.mem_source⟩
  n := 1 + c.n
  W := (ScBanach.const (Fin 0 → ℝ)).prod c.W
  T := prodPresentation (UnitCube.quadIso 1) c.T
  hT := prod_eq_prodPresentation (UnitCube.quadIso 1) c.T (by ext v; rfl) c.hT

/-- The index of the quadrant coordinate `s` of `[0, 1]` in the presented product chart. -/
def cubeTimeIndex (b : Fin 1 → Bool) {q : Fin 1 → unitInterval}
    (hq : q ∈ (UnitCube.chart b).source) {y : X} (c : P.PresentedChart y) :
    Fin (cubePresentedChart b hq c).n := Fin.castAdd c.n 0

theorem cubePresentedChart_coord (b : Fin 1 → Bool) {q : Fin 1 → unitInterval}
    (hq : q ∈ (UnitCube.chart b).source) {y : X} (c : P.PresentedChart y)
    (v : (cubePresentedChart b hq c).φ.model.E 0) :
    ((cubePresentedChart b hq c).T 0 v).1 (cubeTimeIndex b hq c) =
      (show (Fin 1 → ℝ) × c.φ.model.E 0 from v).1 0 :=
  prodPresentation_castAdd (UnitCube.quadIso 1) c.T v 0

/-- The chart vector in a product chart: its first component is the chart vector of the
image under the tangent map of the projection. -/
theorem chartVec_prod_fst {T : Type v} [TopologicalSpace T] [T2Space T] [ParacompactSpace T]
    {P₀ : MPolyfold T} [ParacompactSpace (T × X)] {χ : MChart T} (hχ : P₀.IsChart χ)
    {φ : MChart X} (hφ : P.IsChart φ) {w : (P₀.prod P).TangentSpace}
    (hw : (P₀.prod P).levelVal 1 ((P₀.prod P).tangentProj w) ∈ (χ.prod φ).source) :
    (chartVec (hχ.prod hφ) w).1 = chartVec hχ (tangentMap (isScSmoothMap_fst P₀ P) w) :=
  (chartVec_tangentMap_of_scOperator (isScSmoothMap_fst P₀ P)
    (hχ.prod hφ) hχ (χ.model.E.prodFstOp φ.model.E) (fun _ hx => ⟨hx.1, rfl⟩) hw).symm

/-- The sign of the corner chart of `[0, 1]` at `q`: `+1` for the coordinate `t`, `−1` for
`1 − t`. -/
def cubeTimeSign (q : Fin 1 → unitInterval) : ℝ := if UnitCube.corner q 0 then 1 else -1

theorem cubeTimeSign_of_eq_zero {q : Fin 1 → unitInterval} (hq : (q 0 : ℝ) = 0) :
    cubeTimeSign q = 1 := by
  simp [cubeTimeSign, UnitCube.corner, hq]

theorem cubeTimeSign_of_eq_one {q : Fin 1 → unitInterval} (hq : (q 0 : ℝ) = 1) :
    cubeTimeSign q = -1 := by
  simp [cubeTimeSign, UnitCube.corner, hq]

/-- At the ends `t = 0`, `t = 1` the corner chart at `q` vanishes. -/
theorem chart_corner_apply_of_end {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) :
    (UnitCube.chart (UnitCube.corner q) q : Fin 1 → ℝ) 0 = 0 := by
  rw [UnitCube.chart_apply]
  rcases hq with hq | hq <;> simp [UnitCube.corner, UnitCube.fl, hq]

/-- **The `t`-component `dt(w)` of a tangent vector `w` of `[0, 1] × X` over `(q, ·)`**: the
component of `T pr₁(w)`, `pr₁ : [0, 1] × X → [0, 1]`, in the corner chart of `[0, 1]` at `q`,
with the sign that makes it the derivative of `t` (the chart is `t` for `q < 1` and `1 − t` at
`q = 1`). -/
def cubeTimeComponent (q : Fin 1 → unitInterval) (w : ((cubePolyfold 1).prod P).TangentSpace) :
    ℝ :=
  cubeTimeSign q * (chartVec (UnitCube.isChart_chart (UnitCube.corner q))
      (tangentMap (isScSmoothMap_fst (cubePolyfold 1) P) w) : Fin 1 → ℝ) 0

/-- `dt(w)` is, up to the sign of the chart, the first quadrant coordinate of `w` in the
presented product chart. -/
theorem cubeTimeComponent_eq (q : Fin 1 → unitInterval) {y : X} (c : P.PresentedChart y)
    {w : ((cubePolyfold 1).prod P).TangentSpace}
    (hw : ((cubePolyfold 1).prod P).levelVal 1 (((cubePolyfold 1).prod P).tangentProj w) =
      (q, y)) :
    cubeTimeComponent q w = cubeTimeSign q *
      ((cubePresentedChart (UnitCube.corner q) (UnitCube.mem_chart_corner q) c).T 0
        ((cubePresentedChart (UnitCube.corner q) (UnitCube.mem_chart_corner q) c).vec w)).1
        (cubeTimeIndex (UnitCube.corner q) (UnitCube.mem_chart_corner q) c) := by
  rw [cubePresentedChart_coord]
  have h := chartVec_prod_fst (UnitCube.isChart_chart (UnitCube.corner q)) c.isChart (w := w)
    (by rw [hw]; exact ⟨UnitCube.mem_chart_corner q, c.mem_source⟩)
  unfold cubeTimeComponent
  rw [← h]
  rfl

/-- At the ends the first quadrant coordinate of `(q, y)` in the presented product chart
vanishes. -/
theorem cubePresentedChart_coord_base {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) {y : X} (c : P.PresentedChart y) :
    ((cubePresentedChart (UnitCube.corner q) (UnitCube.mem_chart_corner q) c).T 0
      ((cubePresentedChart (UnitCube.corner q) (UnitCube.mem_chart_corner q) c).φ (q, y))).1
        (cubeTimeIndex (UnitCube.corner q) (UnitCube.mem_chart_corner q) c) = 0 := by
  rw [cubePresentedChart_coord]
  exact chart_corner_apply_of_end hq

/-- **At `t = 1` a vector with `dt(w) > 0` points out of `[0, 1] × X`.** -/
theorem not_isInwardVec_of_cubeTimeComponent_pos {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 1) {y : X} {w : ((cubePolyfold 1).prod P).TangentSpace}
    (hw : ((cubePolyfold 1).prod P).levelVal 1 (((cubePolyfold 1).prod P).tangentProj w) =
      (q, y)) (hpos : 0 < cubeTimeComponent q w) :
    ¬ ((cubePolyfold 1).prod P).IsInwardVec (q, y) w := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  rw [cubeTimeComponent_eq q c hw, cubeTimeSign_of_eq_one hq] at hpos
  exact not_isInwardVec_of_coord_neg _ (cubeTimeIndex _ _ c)
    (cubePresentedChart_coord_base (Or.inr hq) c) (by linarith)

/-- **At `t = 0` a vector of `T_{(0, y)}M̃` with `dt(w) > 0` points into `[0, 1] × X`** and is
not tangent to the boundary, in the situation of Definition 9.3.8. -/
theorem isInwardVec_of_cubeTimeComponent_pos {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0) {y : X} {g : OrTangent ((cubePolyfold 1).prod P)}
    (hO : ((cubePolyfold 1).prod P).IsOrientedAt (q, y) g)
    (hadm : ((cubePolyfold 1).prod P).IsBoundaryAdmissible (q, y) g)
    {w : ((cubePolyfold 1).prod P).TangentSpace} (hw : w ∈ g.carrier)
    (hpos : 0 < cubeTimeComponent q w) :
    ((cubePolyfold 1).prod P).IsInwardVec (q, y) w ∧
      ¬ ((cubePolyfold 1).prod P).IsReducedVec (q, y) w := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  rw [cubeTimeComponent_eq q c (hO.1 w hw), cubeTimeSign_of_eq_zero hq, one_mul] at hpos
  exact isInwardVec_of_coord_pos hO hadm _ (cubeTimeIndex _ _ c)
    (cubePresentedChart_coord_base (Or.inl hq) c) hw hpos

/-- **At an end, `T_z∂M̃ = T_zM̃ ∩ {dt = 0}`** in the situation of Definition 9.3.8, if
`T_zM̃` contains a vector with `dt ≠ 0`. -/
theorem mem_boundaryCarrier_iff_cubeTimeComponent {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) {y : X} {g : OrTangent ((cubePolyfold 1).prod P)}
    (hO : ((cubePolyfold 1).prod P).IsOrientedAt (q, y) g)
    (hadm : ((cubePolyfold 1).prod P).IsBoundaryAdmissible (q, y) g)
    {w : ((cubePolyfold 1).prod P).TangentSpace} (hw : w ∈ g.carrier)
    (hw0 : cubeTimeComponent q w ≠ 0) (v : ((cubePolyfold 1).prod P).TangentSpace) :
    v ∈ ((cubePolyfold 1).prod P).boundaryCarrier g.carrier ↔
      v ∈ g.carrier ∧ cubeTimeComponent q v = 0 := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  have hs : cubeTimeSign q ≠ 0 := by
    rcases hq with hq | hq
    · rw [cubeTimeSign_of_eq_zero hq]; exact one_ne_zero
    · rw [cubeTimeSign_of_eq_one hq]; norm_num
  rw [boundaryCarrier_eq hO.1]
  refine and_congr_right fun hv => ?_
  rw [cubeTimeComponent_eq q c (hO.1 w hw)] at hw0
  rw [cubeTimeComponent_eq q c (hO.1 v hv), mul_eq_zero, or_iff_right hs]
  exact isReducedVec_iff_coord_eq_zero hO hadm _ (cubeTimeIndex _ _ c)
    (cubePresentedChart_coord_base hq c) hw (fun h => hw0 (by rw [h, mul_zero])) hv

end MPolyfold

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-- **The `t`-component `dt(w)` of a tangent vector of the cylinder `[0, 1] × X`** over
`(q, ·)`: the derivative of `t` along `w`, read through the tangent map of the projection
`[0, 1] × X → [0, 1]` (`MPolyfold.cubeTimeComponent`). -/
def cylTimeComponent (A : SEP.{u}) (q : Fin 1 → unitInterval)
    (w : (A.cubeSEP 1).X.PObj.TangentSpace) : ℝ :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  MPolyfold.cubeTimeComponent (P := A.X.PObj) q w

section Pointwise

variable {m : ℕ} {Θ' : (A.cubeSEP 1).Obj → ℚ} {z : (A.cubeSEP 1).Obj}
  (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' z) (j : C'.ι)
  {q : Fin 1 → unitInterval} {N : Set A.Obj} (hN : A.X.PObj.IsSmoothSubmanifold N)
  (o : A.X.PObj.SubmanifoldOrientation N (m + 1))
  (hM : C'.boundarySheet j = (cubeFaceIncl A q).obj '' N)

include hM in
/-- **The sign at `t = 1` is `+1`** (Definition 9.3.8, outward normal first; `+∂_t` points out
of `[0, 1] × X` at `t = 1`).  Let `M̃` be a sheet of an oriented tame structure of the cylinder
whose boundary stratum is the slice `ι_q(N)`, `q = 1`, of an oriented submanifold `(N, o)` of
`X`.  If for one positive frame `α` of `(N, o)` at `y` and one `w ∈ T_{(q, y)}M̃` with
`dt(w) > 0` the frame `(w, Tι_q α₁, …, Tι_q α_{m+1})` is positive for `M̃`, then the boundary
orientation of `∂₁M̃` at `(q, y)` is the orientation `ι_q_*o`. -/
theorem boundaryOrient_tangent_eq_faceOrient_of_end_one (hq : (q 0 : ℝ) = 1) {y : A.Obj}
    (hy : y ∈ N) {α : Fin (m + 1) → A.X.PObj.TangentSpace} (hα : α ∈ o.frames y)
    {w : (A.cubeSEP 1).X.PObj.TangentSpace}
    (hw : w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y))
    (hpos : 0 < cylTimeComponent A q w)
    (hcons : (Fin.cons w (fun i => (cubeFaceIncl A q).tangent.obj (α i)) :
      Fin (m + 1 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) ∈ (C'.orient j).frames (q, y)) :
    (C'.boundaryOrient j).tangent ((cubeFaceIncl A q).obj y) =
      (faceOrient q o hN).tangent ((cubeFaceIncl A q).obj y) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  exact MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward (C'.orient j)
    (C'.isSubmanifoldOfDim j) (C'.hasTameInducedStructure j) hM (faceOrient q o hN)
    ⟨y, hy, rfl⟩ ((faceOrient_frames q o hN y).symm ▸ ⟨α, hα, rfl⟩) hw
    (MPolyfold.not_isInwardVec_of_cubeTimeComponent_pos hq hw.1 hpos) hcons

include hM in
/-- **The sign at `t = 0` is `−1`** (Definition 9.3.8, outward normal first; `+∂_t` points
into `[0, 1] × X` at `t = 0`).  In the situation of
`boundaryOrient_tangent_eq_faceOrient_of_end_one` with `q = 0`: if `(w, Tι_q α)` is positive
for `M̃` with `dt(w) > 0` and `α` positive for `(N, o)`, then the boundary orientation of
`∂₁M̃` at `(q, y)` is opposite to `ι_q_*o`. -/
theorem boundaryOrient_tangent_ne_faceOrient_of_end_zero (hq : (q 0 : ℝ) = 0) {y : A.Obj}
    (hy : y ∈ N) {α : Fin (m + 1) → A.X.PObj.TangentSpace} (hα : α ∈ o.frames y)
    {w : (A.cubeSEP 1).X.PObj.TangentSpace}
    (hw : w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y))
    (hpos : 0 < cylTimeComponent A q w)
    (hcons : (Fin.cons w (fun i => (cubeFaceIncl A q).tangent.obj (α i)) :
      Fin (m + 1 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) ∈ (C'.orient j).frames (q, y)) :
    (C'.boundaryOrient j).tangent ((cubeFaceIncl A q).obj y) ≠
      (faceOrient q o hN).tangent ((cubeFaceIncl A q).obj y) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have hzB : ((q, y) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.boundaryStratum (C'.M j) := by
    change (q, y) ∈ C'.boundarySheet j
    rw [hM]
    exact ⟨y, hy, rfl⟩
  obtain ⟨hin, hred⟩ := MPolyfold.isInwardVec_of_cubeTimeComponent_pos hq
    ((C'.orient j).isOrientedAt (q, y) hzB.1)
    ((C'.orient j).isBoundaryAdmissible_tangent (C'.isSubmanifoldOfDim j).1 hzB) hw hpos
  exact MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward (C'.orient j)
    (C'.isSubmanifoldOfDim j) (C'.hasTameInducedStructure j) hM (faceOrient q o hN)
    ⟨y, hy, rfl⟩ ((faceOrient_frames q o hN y).symm ▸ ⟨α, hα, rfl⟩) hw hin hred hcons

include hM hN in
/-- **`T_{(q, y)}M̃ ∩ {dt = 0} = Tι_q(T_yN)` at an end** (the splitting
`ker (f̃ − s̃)' = ℝ·(∂_t + u) ⊕ ker (f − s)'` on the level of the sheets): if the boundary
stratum of `M̃` is the slice `ι_q(N)`, `q ∈ {0, 1}`, and some `w ∈ T_{(q, y)}M̃` has
`dt(w) ≠ 0`, then the vectors of `T_{(q, y)}M̃` with `dt = 0` are the images under `Tι_q` of
the vectors of `T_yN`. -/
theorem mem_tangent_cubeFace_iff_cylTimeComponent (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1)
    {y : A.Obj} (hy : y ∈ N) {w : (A.cubeSEP 1).X.PObj.TangentSpace}
    (hw : w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y))
    (hw0 : cylTimeComponent A q w ≠ 0) (v : (A.cubeSEP 1).X.PObj.TangentSpace) :
    v ∈ (cubeFaceIncl A q).tangent.obj '' A.X.PObj.submanifoldTangent N y ↔
      v ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y) ∧
        cylTimeComponent A q v = 0 := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have hzB : ((q, y) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.boundaryStratum (C'.M j) := by
    change (q, y) ∈ C'.boundarySheet j
    rw [hM]
    exact ⟨y, hy, rfl⟩
  have h1 := submanifoldTangent_cubeFace q hN hy
  have h2 := MPolyfold.submanifoldTangent_boundaryStratum (C'.isSubmanifoldOfDim j)
    (C'.hasTameInducedStructure j) hzB
  have h3 : (A.cubeSEP 1).X.PObj.boundaryStratum (C'.M j) = (cubeFaceIncl A q).obj '' N := hM
  rw [h3] at h2
  have h4 : (cubeFaceIncl A q).tangent.obj '' A.X.PObj.submanifoldTangent N y =
      (A.cubeSEP 1).X.PObj.boundaryCarrier
        ((A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y)) := h1.symm.trans h2
  rw [h4]
  exact MPolyfold.mem_boundaryCarrier_iff_cubeTimeComponent hq
    ((C'.orient j).isOrientedAt (q, y) hzB.1)
    ((C'.orient j).isBoundaryAdmissible_tangent (C'.isSubmanifoldOfDim j).1 hzB) hw hw0 v

end Pointwise

/-! ### The frame convention and the sign clause of matched structures -/

/-- **The frame convention "`t` first" for a pair of structures** (Remark 6.6.19, Theorem 6.7.1:
`ker (f̃ − s̃ⱼ)' = ℝ·(∂_t + u) ⊕ ker (f − sⱼ)'` is oriented with the `ℝ`-factor first): for the
sheets `M̃_{g j}` of `C̃` and `M_{e j}` of `C` and every `y ∈ M_{e j}` there are a positive frame
`α` of `M_{e j}` at `y` and a vector `w ∈ T_{(q, y)}M̃_{g j}` with `dt(w) > 0` such that
`(w, Tι_q α₁, …, Tι_q α_{m+1})` is a positive frame of `M̃_{g j}` at `(q, y)`.  (One such frame
fixes the orientation of `T_{(q, y)}M̃_{g j}`: `MPolyfold.IsOrientedAt.frames_eq_of_mem`.) -/
def HasTimeFirstFrames {m : ℕ} {Θ : A.Obj → ℚ} {x : A.Obj} (q : Fin 1 → unitInterval)
    (C : A.X.OrientedTameStructure (m + 1) Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {z : (A.cubeSEP 1).Obj} (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' z)
    {J : Type*} (g : J → C'.ι) (e : J → C.ι) : Prop :=
  ∀ j, ∀ y ∈ C.M (e j), ∃ α ∈ (C.orient (e j)).frames y,
    ∃ w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M (g j)) (q, y),
      0 < cylTimeComponent A q w ∧
        (Fin.cons w (fun i => (cubeFaceIncl A q).tangent.obj (α i)) :
          Fin (m + 1 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) ∈ (C'.orient (g j)).frames (q, y)

section Matched

variable {m : ℕ} {Θ : A.Obj → ℚ} {x : A.Obj} {q : Fin 1 → unitInterval}
  (C : A.X.OrientedTameStructure (m + 1) Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
  {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
  (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' (q, x))
  (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T')
  (hS : ∀ i, C.M i ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets)

/-- **The sign clause at `t = 1`: `ε = +1`.**  Structures whose sheets match over the end
`t = 1` (boundary sheets of `C̃` = slices of the sheets of `C`, same weights) and which satisfy
the frame convention "`t` first" are matched with sign `+1`. -/
theorem areMatchedAt_of_timeFirstFrames_one (hq : (q 0 : ℝ) = 1)
    (e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι) (he : Injective e)
    (hrange : ∀ i, i ∉ range e → C.M i = ∅) (hσ : ∀ j, C'.σ j.1 = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j))
    (hU : ∀ y ∈ C.U, (q, y) ∈ C'.U)
    (hconv : HasTimeFirstFrames q C C' (fun j => j.1) e) :
    AreMatchedAt q C C' hΘ' hCT' hS 1 := by
  refine ⟨e, he, hrange, hσ, hM, hU, Or.inl ⟨rfl, fun j y hy => ?_⟩⟩
  obtain ⟨α, hα, w, hw, hpos, hcons⟩ := hconv j y hy
  exact boundaryOrient_tangent_eq_faceOrient_of_end_one C' j.1 (hS (e j)).1.1 (C.orient (e j))
    (hM j) hq hy hα hw hpos hcons

/-- **The sign clause at `t = 0`: `ε = −1`.**  Structures whose sheets match over the end
`t = 0` and which satisfy the frame convention "`t` first" are matched with sign `−1`. -/
theorem areMatchedAt_of_timeFirstFrames_zero (hq : (q 0 : ℝ) = 0)
    (e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι) (he : Injective e)
    (hrange : ∀ i, i ∉ range e → C.M i = ∅) (hσ : ∀ j, C'.σ j.1 = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j))
    (hU : ∀ y ∈ C.U, (q, y) ∈ C'.U)
    (hconv : HasTimeFirstFrames q C C' (fun j => j.1) e) :
    AreMatchedAt q C C' hΘ' hCT' hS (-1) := by
  refine ⟨e, he, hrange, hσ, hM, hU, Or.inr ⟨rfl, fun j y hy => ?_⟩⟩
  obtain ⟨α, hα, w, hw, hpos, hcons⟩ := hconv j y hy
  exact boundaryOrient_tangent_ne_faceOrient_of_end_zero C' j.1 (hS (e j)).1.1
    (C.orient (e j)) (hM j) hq hy hα hw hpos hcons

end Matched

/-! ### Structures described by kernels -/

section Kernels

/-- The frames of a submanifold orientation transported along an equality of dimensions. -/
theorem mem_frames_cast_iff {M : Set A.Obj} {d n : ℕ} (h : d = n)
    (so : A.X.PObj.SubmanifoldOrientation M d) (y : A.Obj)
    (v : Fin n → A.X.PObj.TangentSpace) :
    v ∈ (h ▸ so).frames y ↔ (fun k => v (Fin.cast h k)) ∈ so.frames y := by
  subst h
  rfl

theorem cons_cast_eq {T : Type*} {d₁ d₂ n : ℕ} (h1 : d₁ = n) (h2 : d₂ = n + 1)
    (hd : d₂ = d₁ + 1) (w : T) (β : Fin d₁ → T) (k : Fin d₂) :
    (Fin.cons w (fun l : Fin n => β (Fin.cast h1.symm l)) : Fin (n + 1) → T) (Fin.cast h2 k) =
      (Fin.cons w β : Fin (d₁ + 1) → T) (Fin.cast hd k) := by
  subst h1
  subst h2
  rfl

variable {f : A.Obj → A.W} {f' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W}
  (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy)
  (hf' : (A.cubeSEP 1).B.IsScFredholmSection f')
  (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o' : ∀ z (hz : z ∈ (A.cubeSEP 1).X.PObj.smoothSet), Orx f' hf' z hz)

/-- **The frame convention of the canonical orientations on the end `q` of the cylinder**
(Remark 6.6.19, Theorem 6.7.1 and p. 703: the orientation `õ` of `f̃` is "`[0, 1]` first, then
`o`").  For structures described by kernels `K` of `(f, Λ)` at `x` and `K̃` of `(f̃, Λ̃)` at
`(q, x)`, a sheet `Mᵢ = {f = sᵢ}` of `K` and a sheet `M̃ⱼ = {f̃ = s̃ⱼ}` of `K̃` with
`s̃ⱼ(q, ·) = sᵢ` and `dim M̃ⱼ = dim Mᵢ + 1`, and `y ∈ Mᵢ` with `(q, y) ∈ M̃ⱼ`: there are a frame
`α` of `ker (f − sᵢ)'(y) = T_yMᵢ` positive for `o_y` and a vector
`w ∈ ker (f̃ − s̃ⱼ)'(q, y) = T_{(q, y)}M̃ⱼ` with `dt(w) > 0` such that `(w, Tι_q α)` is positive
for `õ_{(q, y)}`. -/
def CylinderKernelFrameConvention (q : Fin 1 → unitInterval) : Prop :=
  ∀ (Λ : A.W → ℚ≥0) (Λ' : (A.cubeSEP 1).W → ℚ≥0) (x : A.Obj) (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) f' Λ' (q, x)) (i : K.ι) (j : K'.ι)
    (hd : K'.dim j = K.dim i + 1),
    (∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y)) →
      ∀ y ∈ K.M i, (q, y) ∈ K'.M j → ∃ α ∈ K.frames hf hsec o i y,
        ∃ w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y),
          0 < cylTimeComponent A q w ∧
            (fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
              Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)) ∈
              K'.frames hf' hsec' o' j (q, y)

variable {hf hsec o hf' hsec' o'}

/-- **Under the frame convention of the canonical orientations, the oriented tame structures of
kernel branchings satisfy "`t` first"**: for index maps `g`, `e` such that the sections of the
sheets `M̃_{g j}`, `M_{e j}` agree over the end and `{q} × M_{e j} ⊆ M̃_{g j}`. -/
theorem KernelBranching.hasTimeFirstFrames_of_convention {q : Fin 1 → unitInterval}
    (hconv : CylinderKernelFrameConvention hf hsec o hf' hsec' o' q) {Λ : A.W → ℚ≥0}
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) f' Λ' (q, x)) (hc : K.FramesContinuous hf hsec o)
    (hc' : K'.FramesContinuous hf' hsec' o') {m : ℕ} (hn : ∀ i, K.dim i = m + 1)
    (hn' : ∀ j, K'.dim j = m + 1 + 1) {J : Type*} (g : J → K'.ι) (e : J → K.ι)
    (hs : ∀ j, ∀ y ∈ K.O, (q, y) ∈ K'.O →
      cubeVal (K'.s (g j) (q, y)) = ((q, y), K.s (e j) y))
    (hsub : ∀ j, ∀ y ∈ K.M (e j), (q, y) ∈ K'.M (g j)) :
    HasTimeFirstFrames q (K.toOrientedTame hc hn) (K'.toOrientedTame hc' hn') g e := by
  intro j y hy
  have hd : K'.dim (g j) = K.dim (e j) + 1 := by rw [hn, hn']
  obtain ⟨α, hα, w, hw, hpos, hcons⟩ :=
    hconv Λ Λ' x K K' (e j) (g j) hd (hs j) y hy (hsub j y hy)
  refine ⟨fun l => α (Fin.cast (hn (e j)).symm l), ?_, w, hw, hpos, ?_⟩
  · refine (mem_frames_cast_iff (hn (e j)) (K.orient hc (e j)) y _).2 ?_
    exact hα
  · refine (mem_frames_cast_iff (hn' (g j)) (K'.orient hc' (g j)) (q, y) _).2 ?_
    have hfun : (fun k => (Fin.cons w (fun l : Fin (m + 1) =>
        (cubeFaceIncl A q).tangent.obj (α (Fin.cast (hn (e j)).symm l))) :
          Fin (m + 1 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast (hn' (g j)) k)) =
        fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
          Fin (K.dim (e j) + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k) :=
      funext fun k => cons_cast_eq (hn (e j)) (hn' (g j)) hd w
        (fun l => (cubeFaceIncl A q).tangent.obj (α l)) k
    rw [hfun]
    exact hcons

section KernelMatched

variable {q : Fin 1 → unitInterval} {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj}
  (K : KernelBranching A f Λ x) (K' : KernelBranching (A.cubeSEP 1) f' Λ' (q, x))
  (hc : K.FramesContinuous hf hsec o) (hc' : K'.FramesContinuous hf' hsec' o') {m : ℕ}
  (hn : ∀ i, K.dim i = m + 1) (hn' : ∀ j, K'.dim j = m + 1 + 1)
  {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
  (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid (fun z => (Λ' (f' z) : ℚ)))
  (hCT' : (K'.toOrientedTame hc' hn').Represents T')
  (hS : ∀ i, (K.toOrientedTame hc hn).M i ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets)

/-- **Corollary 15.4.4, the sign at `t = 1`, for the canonical orientations**: under the frame
convention of the canonical orientations, the oriented tame structures of kernel branchings
`K` of `(f, Λ)` at `x` and `K̃` of `(f̃, Λ̃)` at `(1, x)` whose sheets match over the end are
matched with sign `+1`. -/
theorem KernelBranching.areMatchedAt_one (hq : (q 0 : ℝ) = 1)
    (hconv : CylinderKernelFrameConvention hf hsec o hf' hsec' o' q)
    (e : ((K'.toOrientedTame hc' hn').boundaryFamily hΘ' hCT').nonemptyPart.ι → K.ι)
    (he : Injective e) (hrange : ∀ i, i ∉ range e → K.M i = ∅)
    (hσ : ∀ j, K'.σ j.1 = K.σ (e j))
    (hM : ∀ j, (K'.toOrientedTame hc' hn').boundarySheet j.1 =
      (cubeFaceIncl A q).obj '' K.M (e j))
    (hU : ∀ y ∈ K.U, (q, y) ∈ K'.U)
    (hs : ∀ j, ∀ y ∈ K.O, (q, y) ∈ K'.O →
      cubeVal (K'.s j.1 (q, y)) = ((q, y), K.s (e j) y)) :
    AreMatchedAt q (K.toOrientedTame hc hn) (K'.toOrientedTame hc' hn') hΘ' hCT' hS 1 :=
  areMatchedAt_of_timeFirstFrames_one (K.toOrientedTame hc hn) (K'.toOrientedTame hc' hn') hΘ'
    hCT' hS hq e he hrange hσ hM hU
    (K.hasTimeFirstFrames_of_convention hconv K' hc hc' hn hn' (fun j => j.1) e hs
      fun j y hy => (K'.toOrientedTame hc' hn').boundarySheet_subset j.1 (by
        rw [hM j]
        exact ⟨y, hy, rfl⟩))

/-- **Corollary 15.4.4, the sign at `t = 0`, for the canonical orientations**: the same at
`(0, x)`, with sign `−1`. -/
theorem KernelBranching.areMatchedAt_zero (hq : (q 0 : ℝ) = 0)
    (hconv : CylinderKernelFrameConvention hf hsec o hf' hsec' o' q)
    (e : ((K'.toOrientedTame hc' hn').boundaryFamily hΘ' hCT').nonemptyPart.ι → K.ι)
    (he : Injective e) (hrange : ∀ i, i ∉ range e → K.M i = ∅)
    (hσ : ∀ j, K'.σ j.1 = K.σ (e j))
    (hM : ∀ j, (K'.toOrientedTame hc' hn').boundarySheet j.1 =
      (cubeFaceIncl A q).obj '' K.M (e j))
    (hU : ∀ y ∈ K.U, (q, y) ∈ K'.U)
    (hs : ∀ j, ∀ y ∈ K.O, (q, y) ∈ K'.O →
      cubeVal (K'.s j.1 (q, y)) = ((q, y), K.s (e j) y)) :
    AreMatchedAt q (K.toOrientedTame hc hn) (K'.toOrientedTame hc' hn') hΘ' hCT' hS (-1) :=
  areMatchedAt_of_timeFirstFrames_zero (K.toOrientedTame hc hn) (K'.toOrientedTame hc' hn')
    hΘ' hCT' hS hq e he hrange hσ hM hU
    (K.hasTimeFirstFrames_of_convention hconv K' hc hc' hn hn' (fun j => j.1) e hs
      fun j y hy => (K'.toOrientedTame hc' hn').boundarySheet_subset j.1 (by
        rw [hM j]
        exact ⟨y, hy, rfl⟩))

end KernelMatched

end Kernels

end SBLocalization

end Polyfold
