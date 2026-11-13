import Polyfold.Chapter9.FrameSign
import Polyfold.Chapter9.GraphDiffeo
import Polyfold.Chapter9.SheetMeasure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# The integral of a form over a measurable subset of an oriented sheet, in a graph chart

For an evaluation of forms `F : X.FormEval n Ω`, a graph chart `c` of a submanifold `N` and a
field `g` of oriented tangent spaces: the density `F.density c ω g y = ± ω(c.tvec y)` (the sign
`+` iff the frame of the chart is positive for `g y`), and the integral
`F.chartInteg c ω g A = ∫_{c(A ∩ N)} density` in the coordinates of `c` (Lebesgue measure of
`ℝⁿ`).

* `integrableOn_density`: the density is integrable if `u ↦ ω(c.tvec (c.q u))` is (the sign is
  locally constant on `N`).
* `chartInteg_congr`, `chartInteg_neg`: two graph charts of two sheets give the same integral
  over a common measurable subset on which the oriented tangent spaces agree, and opposite
  integrals where the tangent spaces agree and the orientations differ.  In particular the
  integral does not depend on the graph chart.
* `chartInteg_mapDiffeo`: invariance under an sc-diffeomorphism whose tangent maps are those of
  morphisms.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold.GraphChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {n : ℕ} {N : Set X}

open Classical in
/-- The sign of the frame of the graph chart for the oriented tangent space `g y`. -/
def frameSgn (c : P.GraphChart n N) (g : X → OrTangent P) (y : X) : ℝ :=
  if (g y).IsPos (c.tvec y) then 1 else -1

open Classical in
theorem frameSgn_tangent (c : P.GraphChart n N) {M : Set X} (o : P.SubmanifoldOrientation M n)
    (y : X) : c.frameSgn o.tangent y = if c.tvec y ∈ o.frames y then 1 else -1 := by
  unfold frameSgn
  simp only [SubmanifoldOrientation.isPos_tangent]

end MPolyfold.GraphChart

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

variable {N N' : Set Obj}

/-- The density of `ω` in the graph chart `c`, for the oriented tangent spaces `g`. -/
def density (c : X.PObj.GraphChart n N) (ω : Ω) (g : Obj → X.PObj.OrTangent) (y : Obj) : ℝ :=
  c.frameSgn g y * F.ev ω (c.tvec y)

/-- **The integral of `ω` over `A ∩ N` in the graph chart `c`.** -/
def chartInteg (c : X.PObj.GraphChart n N) (ω : Ω) (g : Obj → X.PObj.OrTangent) (A : Set Obj) :
    ℝ :=
  ∫ u in c.coord '' (A ∩ N), F.density c ω g (c.q u)

theorem density_add (c : X.PObj.GraphChart n N) (ω τ : Ω) (g : Obj → X.PObj.OrTangent)
    (y : Obj) : F.density c (ω + τ) g y = F.density c ω g y + F.density c τ g y := by
  simp only [density, F.ev_add]; ring

theorem density_smul (c : X.PObj.GraphChart n N) (a : ℝ) (ω : Ω) (g : Obj → X.PObj.OrTangent)
    (y : Obj) : F.density c (a • ω) g y = a * F.density c ω g y := by
  simp only [density, F.ev_smul]; ring

/-- **Integrability of the density**: the sign of the frame is locally constant on `N`. -/
theorem integrableOn_density (hn : 0 < n) (hN : X.PObj.IsSmoothSubmanifold N)
    (c : X.PObj.GraphChart n N) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (hint : IntegrableOn (fun u => F.ev ω (c.tvec (c.q u))) c.dom volume) :
    IntegrableOn (fun u => F.density c ω o.tangent (c.q u)) c.dom volume := by
  classical
  obtain ⟨W, hW, hWe⟩ := c.exists_isOpen_isPos hN hn o
  set T := c.coord '' (W ∩ N) with hT
  have hTm : MeasurableSet T := c.measurableSet_coord_image_borel (MeasurableSpace.measurableSet_generateFrom hW)
  have h1 : Integrable (T.piecewise (fun u => F.ev ω (c.tvec (c.q u)))
      (fun u => -F.ev ω (c.tvec (c.q u)))) (volume.restrict c.dom) :=
    Integrable.piecewise hTm hint.integrableOn hint.neg.integrableOn
  refine IntegrableOn.congr_fun h1 (fun u hu => ?_) c.measurableSet_dom'
  have hq : c.q u ∈ N := c.q_mem hu
  have hiff : u ∈ T ↔ c.tvec (c.q u) ∈ o.frames (c.q u) := by
    have h2 : c.q u ∈ {y | y ∈ N ∧ c.tvec y ∈ o.frames y} ↔ c.q u ∈ N ∩ W := by rw [hWe]
    constructor
    · rintro ⟨y, ⟨hyW, hyN⟩, rfl⟩
      rw [c.q_coord' hyN]
      have : y ∈ {y | y ∈ N ∧ c.tvec y ∈ o.frames y} := by rw [hWe]; exact ⟨hyN, hyW⟩
      exact this.2
    · intro h
      exact ⟨c.q u, ⟨(h2.1 ⟨hq, h⟩).2, hq⟩, c.coord_q hu⟩
  simp only [density, c.frameSgn_tangent, Set.piecewise]
  by_cases h : u ∈ T
  · rw [if_pos h, if_pos (hiff.1 h), one_mul]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), neg_one_mul]

open Classical in
/-- **The densities in two graph charts at a point where the tangent spaces agree**, for one
orientation `O` of the common tangent space. -/
theorem sgn_mul_ev_eq (hN' : X.PObj.IsSubmanifoldOfDim N' n) (c : X.PObj.GraphChart n N)
    (c' : X.PObj.GraphChart n N') (ω : Ω) {y : Obj} (hy : y ∈ N) (hy' : y ∈ N')
    (hT : X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y)
    {O : Set (Fin n → X.PObj.TangentSpace)}
    (hO : X.PObj.IsOrientedAt y ⟨n, X.PObj.submanifoldTangent N' y, O⟩)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : ∀ j, MPolyfold.chartVec c'.isChart (c.tvec y j) =
      ∑ i, D (MPolyfold.GraphChart.bvec j) i • MPolyfold.chartVec c'.isChart (c'.tvec y i)) :
    (if c.tvec y ∈ O then (1 : ℝ) else -1) * F.ev ω (c.tvec y) =
      |D.det| * ((if c'.tvec y ∈ O then (1 : ℝ) else -1) * F.ev ω (c'.tvec y)) := by
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => D (MPolyfold.GraphChart.bvec j) i
    with hM
  have hdet : M.det = D.det := MPolyfold.GraphChart.det_matrix_bvec D
  have hmem : ∀ i, c.tvec y i ∈ X.PObj.submanifoldTangent N' y := fun i => hT ▸ c.tvec_mem hy i
  have hsrc : y ∈ c'.φ.source := c'.subset_source hy'
  have hev : F.ev ω (c.tvec y) = M.det * F.ev ω (c'.tvec y) :=
    F.ev_det ω hN'.1 hy' c'.isChart hsrc (c'.tvec y) (c.tvec y) (c'.tvec_mem hy') hmem M hD
  have key := MPolyfold.IsOrientedAt.frames_iff_frames_iff_det_pos hN' hy' hO c'.isChart hsrc
    (c'.tvec_mem hy') hmem (c'.linearIndependent_chartVec_tvec hy')
    (c.linearIndependent_chartVec_tvec_of_chart hy c'.isChart hsrc) M hD
  rw [hev, ← hdet]
  by_cases hpos : 0 < M.det
  · have hiff := key.2 hpos
    rw [abs_of_pos hpos]
    by_cases h : c.tvec y ∈ O
    · rw [if_pos h, if_pos (hiff.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]; ring
  · have hniff : ¬ (c.tvec y ∈ O ↔ c'.tvec y ∈ O) := fun h => hpos (key.1 h)
    rw [abs_of_nonpos (not_lt.1 hpos)]
    by_cases h : c.tvec y ∈ O
    · have h' : c'.tvec y ∉ O := fun h' => hniff ⟨fun _ => h', fun _ => h⟩
      rw [if_pos h, if_neg h']; ring
    · have h' : c'.tvec y ∈ O := by
        by_contra h'
        exact hniff ⟨fun a => (h a).elim, fun a => (h' a).elim⟩
      rw [if_neg h, if_pos h']; ring

open Classical in
/-- The sign of a frame of `N` changes with the orientation. -/
theorem sgn_eq_neg_of_frames_ne (c : X.PObj.GraphChart n N) {y : Obj} (hy : y ∈ N)
    {O O' : Set (Fin n → X.PObj.TangentSpace)}
    (hO : X.PObj.IsOrientedAt y ⟨n, X.PObj.submanifoldTangent N y, O⟩)
    (hO' : X.PObj.IsOrientedAt y ⟨n, X.PObj.submanifoldTangent N y, O'⟩) (hne : O ≠ O') :
    (if c.tvec y ∈ O then (1 : ℝ) else -1) = -(if c.tvec y ∈ O' then (1 : ℝ) else -1) := by
  have h := MPolyfold.IsOrientedAt.mem_frames_iff_notMem hO hO' hne c.isChart
    (c.subset_source hy) (c.tvec_mem hy) (c.linearIndependent_chartVec_tvec hy)
  by_cases h1 : c.tvec y ∈ O
  · rw [if_pos h1, if_neg (h.1 h1)]; norm_num
  · rw [if_neg h1, if_pos (by by_contra h2; exact h1 (h.2 h2))]

/-- **Two graph charts, equal oriented tangent spaces**: the integrals over a common measurable
subset agree. -/
theorem chartInteg_congr (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hN' : X.PObj.IsSubmanifoldOfDim N' n) (c : X.PObj.GraphChart n N)
    (c' : X.PObj.GraphChart n N') (o : X.PObj.SubmanifoldOrientation N n)
    (o' : X.PObj.SubmanifoldOrientation N' n) (ω : Ω) {A : Set Obj} (hA : A ⊆ N ∩ N')
    (hAm : NullMeasurableSet (c.coord '' A) volume)
    (h : ∀ y ∈ A, o.tangent y = o'.tangent y) :
    F.chartInteg c ω o.tangent A = F.chartInteg c' ω o'.tangent A := by
  have hAN : A ∩ N = A := inter_eq_left.2 fun y hy => (hA hy).1
  have hAN' : A ∩ N' = A := inter_eq_left.2 fun y hy => (hA hy).2
  unfold chartInteg
  rw [hAN, hAN']
  have hT : ∀ y ∈ A, X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y :=
    fun y hy => congrArg MPolyfold.OrTangent.carrier (h y hy)
  refine (MPolyfold.GraphChart.setIntegral_coord_image_eq c c' hN.1 hA hAm hT
    fun y hy D hD => ?_).symm
  have hfr : o.frames y = o'.frames y := by
    have := h y hy
    simp only [MPolyfold.SubmanifoldOrientation.tangent, MPolyfold.OrTangent.mk.injEq,
      heq_eq_eq, true_and] at this
    exact this.2
  simp only [density, c.frameSgn_tangent, c'.frameSgn_tangent]
  rw [hfr]
  exact F.sgn_mul_ev_eq hN' c c' ω (hA hy).1 (hA hy).2 (hT y hy) (o'.isOrientedAt y (hA hy).2)
    D hD

/-- **Two graph charts, opposite orientations of equal tangent spaces**: the integrals over a
common measurable subset are opposite. -/
theorem chartInteg_neg (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hN' : X.PObj.IsSubmanifoldOfDim N' n) (c : X.PObj.GraphChart n N)
    (c' : X.PObj.GraphChart n N') (o : X.PObj.SubmanifoldOrientation N n)
    (o' : X.PObj.SubmanifoldOrientation N' n) (ω : Ω) {A : Set Obj} (hA : A ⊆ N ∩ N')
    (hAm : NullMeasurableSet (c.coord '' A) volume)
    (h : ∀ y ∈ A, X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y ∧
      o.tangent y ≠ o'.tangent y) :
    F.chartInteg c ω o.tangent A = -F.chartInteg c' ω o'.tangent A := by
  have hAN : A ∩ N = A := inter_eq_left.2 fun y hy => (hA hy).1
  have hAN' : A ∩ N' = A := inter_eq_left.2 fun y hy => (hA hy).2
  unfold chartInteg
  rw [hAN, hAN', ← integral_neg]
  refine (MPolyfold.GraphChart.setIntegral_coord_image_eq c c' hN.1 hA hAm (fun y hy => (h y hy).1)
    (ρ := F.density c ω o.tangent) (ρ' := fun y => -F.density c' ω o'.tangent y)
    fun y hy D hD => ?_).symm
  have hT := (h y hy).1
  have hfr : o.frames y ≠ o'.frames y := fun hc => (h y hy).2 (by
    simp only [MPolyfold.SubmanifoldOrientation.tangent, hT, hc])
  have hO : X.PObj.IsOrientedAt y ⟨n, X.PObj.submanifoldTangent N' y, o.frames y⟩ :=
    hT ▸ o.isOrientedAt y (hA hy).1
  have hO' := o'.isOrientedAt y (hA hy).2
  have h1 := F.sgn_mul_ev_eq hN' c c' ω (hA hy).1 (hA hy).2 hT hO D hD
  have h2 := sgn_eq_neg_of_frames_ne c' (hA hy).2 hO hO' hfr
  simp only [density, c.frameSgn_tangent, c'.frameSgn_tangent]
  rw [h1, h2]; ring

/-- The value of a form on the image of a frame of `T_yN` under the tangent map of an
sc-diffeomorphism whose tangent maps are those of morphisms. -/
theorem ev_tangentMapOn (hN : X.PObj.IsSmoothSubmanifold N) {f f' : Obj → Obj}
    {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hmor : X.IsMorTangentOn hf N)
    (ω : Ω) {y : Obj} (hy : y ∈ N) (α : Fin n → X.PObj.TangentSpace)
    (hα : ∀ i, α i ∈ X.PObj.submanifoldTangent N y) :
    F.ev ω (fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (α i)) = F.ev ω α := by
  obtain ⟨ψ, hs, -, hψ⟩ := hmor y hy
  rw [← F.ev_mor ω hN hy ψ hs α hα]
  congr 1
  funext i
  exact (hψ (α i) (MPolyfold.levelVal_tangentProj_of_mem (hα i))).symm

/-- **Invariance under sc-diffeomorphisms whose tangent maps are those of morphisms**: the
integral over `f(A)` in the moved chart, for the moved orientation, is the integral over `A`. -/
theorem chartInteg_mapDiffeo (hN : X.PObj.IsSmoothSubmanifold N) (c : X.PObj.GraphChart n N)
    (o : X.PObj.SubmanifoldOrientation N n) {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N)
    (ω : Ω) {A : Set Obj} (hA : A ⊆ N) (hAm : NullMeasurableSet (c.coord '' A) volume) :
    F.chartInteg (c.mapDiffeo hN hf hNU) ω (o.mapDiffeo hN hf hNU).tangent (f '' A) =
      F.chartInteg c ω o.tangent A := by
  have hAN : A ∩ N = A := inter_eq_left.2 hA
  have hAN' : f '' A ∩ f '' N = f '' A := inter_eq_left.2 (image_mono hA)
  have himg : (c.mapDiffeo hN hf hNU).coord '' (f '' A) = c.coord '' A := by
    rw [image_image]
    exact image_congr fun y hy => c.mapDiffeo_coord hN hf hNU (hA hy)
  unfold chartInteg
  rw [hAN, hAN', himg]
  refine setIntegral_congr_ae₀ hAm (Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hyN := hA hy
  change F.density _ ω _ (f (c.q (c.coord y))) = F.density c ω o.tangent (c.q (c.coord y))
  rw [c.q_coord' hyN]
  have htv : (c.mapDiffeo hN hf hNU).tvec (f y) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (c.tvec y i) :=
    funext fun i => c.mapDiffeo_tvec hN hf hNU hyN i
  simp only [density, MPolyfold.GraphChart.frameSgn_tangent, htv]
  rw [F.ev_tangentMapOn hN hf hmor ω hyN (c.tvec y) (c.tvec_mem hyN)]
  have hiff := o.mapDiffeo_frames_iff hN hf hNU hyN (c.tvec y)
    (fun i => MPolyfold.levelVal_tangentProj_of_mem (c.tvec_mem hyN i))
  rw [← htv] at hiff
  by_cases h : c.tvec y ∈ o.frames y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

end FormEval

end EpGroupoid

end Polyfold
