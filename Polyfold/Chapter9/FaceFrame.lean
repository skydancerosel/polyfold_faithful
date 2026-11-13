import Polyfold.Chapter9.FaceOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.3, Definition 9.3.8 (p. 427), and §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps
G.109, G.110).  Numbers and pages are the 2021 text's.

# Face frames of a tame sheet and the density of a form on the boundary stratum

For corner coordinates `κ` of a tame `(m+1)`-dimensional sheet `M` and a face `{yₗ = 0}`, the
**face frame** at `y` is `Tι(ιₗ e₁), …, Tι(ιₗ e_m)` (`ιₗ = faceEmbedding l`, `Tι = incFrame`).

## What is formalized

* `FormEval.sgn_mul_ev_of_frame`: for a frame `β` of `T_yN` of an `m`-dimensional submanifold
  `N` with linearly independent chart vectors and a graph chart `c` of `N`,
  `± ω(β) = |det M| · density`, `M` the matrix of the coordinates of `β` in `c`, the sign `+` iff
  `β` is positive.  `FormEval.density_eq_zero_of_frame`: if `ω(β) = 0` the density vanishes.
* `MPolyfold.faceFrame`, `linearIndependent_chartVec_faceFrame`, `faceFrame_mem_tangent`
  (the face frame is a frame of `T_y∂₁M`).
* **`MPolyfold.faceFrame_mem_stratumOrientation_iff`**: if `o` reads in `κ` at `y` as
  `signedOr b` of the standard orientation, the face frame is positive for `o_{∂M}` iff
  `b == faceBool l`; `orSign_mul_faceSign`: the number `orSign b · faceSign l` is the sign of
  the face frame.
* `FormEval.faceDensity`: `± ω(face frame)`, the sign that of the face frame for the frames `O`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-! ### Frames of a submanifold in a graph chart -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

/-- A vector of `T_yN` in the frame of a graph chart `c` of `N`. -/
theorem chartVec_eq_sum_tvec {N : Set Obj} (c : X.PObj.GraphChart n N) {y : Obj} (hy : y ∈ N)
    {α : X.PObj.TangentSpace} (hα : α ∈ X.PObj.submanifoldTangent N y) :
    chartVec c.isChart α =
      ∑ i, c.p (chartVec c.isChart α) i • chartVec c.isChart (c.tvec y i) := by
  have hmem : chartVec c.isChart α ∈ X.PObj.chartTangent c.isChart N y := ⟨_, hα, rfl⟩
  conv_lhs => rw [← c.L_p_of_mem hy hmem, c.L_apply hy]

open Classical in
/-- **The density of a graph chart and the value on a frame**: for a frame `β` of `T_yN` with
linearly independent chart vectors, `± ω(β) = |det M| · density`, the sign `+` iff `β` is
positive for `o`, `M` the matrix of the coordinates of `β` in the graph chart `c`. -/
theorem sgn_mul_ev_of_frame {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (c : X.PObj.GraphChart n N) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω) {y : Obj}
    (hy : y ∈ N) (β : Fin n → X.PObj.TangentSpace)
    (hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y)
    (hli : LinearIndependent ℝ fun i => chartVec c.isChart (β i)) :
    (if β ∈ o.frames y then (1 : ℝ) else -1) * F.ev ω β =
      |(Matrix.of fun i j => c.p (chartVec c.isChart (β j)) i).det| *
        F.density c ω o.tangent y := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => c.p (chartVec c.isChart (β j)) i
    with hM
  have hsrc : y ∈ c.φ.source := c.subset_source hy
  have hD : ∀ j, chartVec c.isChart (β j) = ∑ i, M i j • chartVec c.isChart (c.tvec y i) :=
    fun j => chartVec_eq_sum_tvec c hy (hβ j)
  have hev : F.ev ω β = M.det * F.ev ω (c.tvec y) :=
    F.ev_det ω hN.1 hy c.isChart hsrc (c.tvec y) β (c.tvec_mem hy) hβ M hD
  have key := IsOrientedAt.frames_iff_frames_iff_det_pos hN hy (o.isOrientedAt y hy) c.isChart
    hsrc (c.tvec_mem hy) hβ (c.linearIndependent_chartVec_tvec hy) hli M hD
  simp only [FormEval.density, c.frameSgn_tangent]
  rw [hev]
  by_cases hpos : 0 < M.det
  · have hiff := key.2 hpos
    rw [abs_of_pos hpos]
    by_cases h : β ∈ o.frames y
    · rw [if_pos h, if_pos (hiff.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; ring
  · have hniff : ¬ (β ∈ o.frames y ↔ c.tvec y ∈ o.frames y) := fun h => hpos (key.1 h)
    rw [abs_of_nonpos (not_lt.1 hpos)]
    by_cases h : β ∈ o.frames y
    · have h' : c.tvec y ∉ o.frames y := fun h' => hniff ⟨fun _ => h', fun _ => h⟩
      rw [if_pos h, if_neg h']; ring
    · have h' : c.tvec y ∈ o.frames y := by
        by_contra h'
        exact hniff ⟨fun a => (h a).elim, fun a => (h' a).elim⟩
      rw [if_neg h, if_pos h']; ring

/-- The matrix of the coordinates of a frame with linearly independent chart vectors is
invertible. -/
theorem det_ne_zero_of_frame {N : Set Obj} (c : X.PObj.GraphChart n N) {y : Obj} (hy : y ∈ N)
    (β : Fin n → X.PObj.TangentSpace) (hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y)
    (hli : LinearIndependent ℝ fun i => chartVec c.isChart (β i)) :
    (Matrix.of fun i j => c.p (chartVec c.isChart (β j)) i).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [Fintype.linearIndependent_iff] at hli
  refine hv (funext fun j => hli v ?_ j)
  have hD : ∀ j, chartVec c.isChart (β j) =
      ∑ i, c.p (chartVec c.isChart (β j)) i • chartVec c.isChart (c.tvec y i) := fun j =>
    chartVec_eq_sum_tvec c hy (hβ j)
  calc ∑ j, v j • chartVec c.isChart (β j)
      = ∑ j, ∑ i, (v j * c.p (chartVec c.isChart (β j)) i) •
          chartVec c.isChart (c.tvec y i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [hD j]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    _ = ∑ i, (∑ j, v j * c.p (chartVec c.isChart (β j)) i) •
          chartVec c.isChart (c.tvec y i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have := congrFun hMv i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
        rw [show (∑ j, v j * c.p (chartVec c.isChart (β j)) i) = 0
          from by rw [← this]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _, zero_smul]

/-- **If `ω` vanishes on a frame of `T_yN`, the density of a graph chart vanishes at `y`.** -/
theorem density_eq_zero_of_frame {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (c : X.PObj.GraphChart n N) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω) {y : Obj}
    (hy : y ∈ N) (β : Fin n → X.PObj.TangentSpace)
    (hβ : ∀ i, β i ∈ X.PObj.submanifoldTangent N y)
    (hli : LinearIndependent ℝ fun i => chartVec c.isChart (β i)) (h0 : F.ev ω β = 0) :
    F.density c ω o.tangent y = 0 := by
  have h := F.sgn_mul_ev_of_frame hN c o ω hy β hβ hli
  rw [h0, mul_zero] at h
  exact (mul_eq_zero.1 h.symm).resolve_left
    (abs_ne_zero.2 (det_ne_zero_of_frame c hy β hβ hli))

end FormEval

end EpGroupoid

/-! ### Face frames -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {m : ℕ} {hY : P.IsSubMPolyfold M}

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)) in
/-- **The face frame** `Tι(ιₗ e₁), …, Tι(ιₗ e_m)` at `y` for the face `{yₗ = 0}` of the corner
coordinates `κ`. -/
def faceFrame (κ : CornerCoords (subPolyfold hY) (m + 1)) {y : M} (hy : y ∈ κ.s)
    (l : Fin (m + 1)) : Fin m → P.TangentSpace :=
  fun k => incFrame hcs κ hy (faceEmbedding l (stdFrame m k))

theorem faceEmbedding_injective (l : Fin (m + 1)) : Function.Injective (faceEmbedding l) :=
  fun u v h => by
    ext k
    have := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x (l.succAbove k)) h
    simpa using this

variable {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}

/-- The chart vectors of a face frame are linearly independent. -/
theorem linearIndependent_chartVec_faceFrame (hN : P.IsSmoothSubmanifold M)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) {y : M} (hy : y ∈ κ.s) (l : Fin (m + 1))
    {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y.1 ∈ φ.source) :
    LinearIndependent ℝ fun k => chartVec hφ (faceFrame hcs κ hy l k) := by
  set d := (hN.data y.2).toSubData
  have hyσ : y ∈ (subChart d hφ y).source := d.mem_shrink φ y.2 (hN.mem_data_V y.2) hyφ
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy) (levelVal_mem (hcs.levelOne y))
  set g := modelDeriv κ hφ d y (levelLift κ.χ 1 y)
  have hinj : Function.Injective g := modelDeriv_injective κ hφ d y hy hyσ hz
  set G : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] φ.model.E 0 :=
    (g : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] φ.model.E 0).comp
      (faceEmbedding l : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
  have hG : Function.Injective G := hinj.comp (faceEmbedding_injective l)
  have hstd : LinearIndependent ℝ (stdFrame m) := by
    rw [← coe_basisFun_toBasis]; exact Basis.linearIndependent _
  have h := hstd.map' G (LinearMap.ker_eq_bot.2 hG)
  have e : (fun k => chartVec hφ (faceFrame hcs κ hy l k)) = G ∘ stdFrame m :=
    funext fun k => chartVec_incFrame κ hy _ hφ d y hyσ
  rw [e]; exact h

/-- **The face frame is a frame of `T_y∂₁M`.** -/
theorem faceFrame_mem_tangent (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) (m + 1))
    {l : Fin (m + 1)} {y : M} (hy : y ∈ κ.facePiece l) (hyl : κ.coord y l = 0) (k : Fin m) :
    faceFrame hcs κ hy.1 l k ∈ P.submanifoldTangent (P.boundaryStratum M) y.1 := by
  rw [← stratumOne_eq_boundaryStratum hM.1 ht]
  exact incFrame_mem_submanifoldTangent_stratumOne hcs hM ht κ hy hyl
    (by simp [mem_coordHyperplane])

/-- `faceSign l = orSign (faceBool l)`. -/
theorem faceSign_eq_orSign (l : Fin (m + 1)) : faceSign l = orSign (faceBool l) := by
  have hfb : faceBool l = decide (faceSign l = 1) := rfl
  rcases neg_one_pow_eq_or ℝ ((l : ℕ) + 1) with hs | hs
  · have hs' : faceSign l = 1 := hs
    rw [hfb, hs', decide_eq_true rfl, orSign_true]
  · have hs' : faceSign l = -1 := hs
    rw [hfb, hs', decide_eq_false (by norm_num : (-1 : ℝ) ≠ 1), orSign_false]

/-- `orSign b · faceSign l = ±1`, `+` iff `b == faceBool l`. -/
theorem orSign_mul_faceSign (b : Bool) (l : Fin (m + 1)) :
    orSign b * faceSign l = if (b == faceBool l) = true then 1 else -1 := by
  rw [faceSign_eq_orSign]
  cases b <;> cases faceBool l <;> simp [orSign_true, orSign_false]

include hcs in
open Classical in
/-- **The sign of the face frame for `o_{∂M}`**: if `o` reads in the corner coordinates `κ` at
`y` (a point of the face piece of `{yₗ = 0}` with `yₗ = 0`) as `signedOr b` of the standard
orientation, the face frame is positive for `o_{∂M}` iff `b == faceBool l` (outward normal
first, Definition 9.3.8). -/
theorem faceFrame_mem_stratumOrientation_iff (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) (o : P.SubmanifoldOrientation M (m + 1))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) {l : Fin (m + 1)} {y : M}
    (hy : y ∈ κ.facePiece l) (hyl : κ.coord y l = 0) (b : Bool)
    (hb : orIn hcs o κ hy.1 = signedOr b (stdOrientation (m + 1))) :
    faceFrame hcs κ hy.1 l ∈ (o.stratumOrientation hM ht).frames y.1 ↔
      (b == faceBool l) = true := by
  rw [SubmanifoldOrientation.stratumOrientation_frames]
  unfold faceFrame
  rw [incFrame_mem_boundaryFramesAt_iff hcs hM ht o κ hy hyl
    (fun j => faceEmbedding l (stdFrame m j)) (fun j => by simp [mem_coordHyperplane])]
  have hfun : (Fin.cons (incFrame hcs κ hy.1 (-EuclideanSpace.single l (1 : ℝ)))
        (fun j => incFrame hcs κ hy.1 (faceEmbedding l (stdFrame m j))) :
          Fin (m + 1) → P.TangentSpace) =
      fun k => incFrame hcs κ hy.1 (consFaceBasis l (EuclideanSpace.basisFun (Fin m) ℝ).toBasis k)
      := by
    funext k
    rw [coe_consFaceBasis, coe_basisFun_toBasis]
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [stdFrame_apply]
    · simp
  rw [hfun, ← orientation_eq_orIn_iff (Nat.succ_pos m) hM o κ hy.1, hb,
    orientation_consFaceBasis_eq_iff]
  have hstd : (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.orientation = stdOrientation m := rfl
  have hdec : decide (signedOr b (stdOrientation (m + 1)) = stdOrientation (m + 1)) = b :=
    (eq_signedOr_std_iff _ b).1 rfl
  rw [hstd, hdec, eq_signedOr_std_iff, decide_eq_true rfl]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end MPolyfold

/-! ### The density on a face -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M}

open Classical in
/-- **The density of `ω` on the face `{yₗ = 0}` of the corner coordinates `κ`**:
`± ω(Tι(ιₗ e₁), …, Tι(ιₗ e_m))`, the sign `+` iff the face frame lies in `O y`. -/
def FormEval.faceDensity (F : X.FormEval m Ω)
    (hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1))
    (O : Obj → Set (Fin m → X.PObj.TangentSpace)) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1)) (y : M) : ℝ :=
  if hy : y ∈ κ.s then
    (if faceFrame hcs κ hy l ∈ O y.1 then (1 : ℝ) else -1) * F.ev ω (faceFrame hcs κ hy l)
  else 0

end EpGroupoid

end Polyfold
