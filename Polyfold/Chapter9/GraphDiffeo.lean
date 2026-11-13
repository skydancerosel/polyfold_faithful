import Polyfold.Chapter9.GraphCoord
import Polyfold.Chapter11.BranchedEquivalenceTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, pp. 438–445 (gap G.107).

# Graph charts, null sets and Borel sets under sc-diffeomorphisms

An sc-diffeomorphism `f : U → U'` of an M-polyfold carries a graph chart `c` of `N ⊆ U` to a
graph chart of `f(N)`, read in the transported chart `φ ∘ f⁻¹`: the coordinate images agree, and
the frame of `T_{f(y)} f(N)` is `Tf` of the frame of `T_yN`.  Sets of `n`-dimensional measure
zero and Borel subsets of `U` are carried to such sets.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The chart vector of `Tf(α)` in the chart `φ ∘ f⁻¹` is the chart vector of `α` in `φ`. -/
theorem chartVec_transport_tangentMapOn {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    {y : X} (hy : y ∈ U) (hyφ : y ∈ φ.source) (hα : P.levelVal 1 (P.tangentProj α) = y) :
    chartVec (transportChart_isChart hf.symm hφ) (tangentMapOn hf.isScSmoothOn α) =
      chartVec hφ α := by
  have hαU : α ∈ P.tangentPreimage U := by change _ ∈ U; rw [hα]; exact hy
  have hbase : P.levelVal 1 (P.tangentProj (tangentMapOn hf.isScSmoothOn α)) = f y := by
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hαU, hα]
  have h1 := chartVec_tangentMapOn_of_isScDiffeoOn hf.symm hφ
    (α := tangentMapOn hf.isScSmoothOn α) (by
      rw [hbase]
      exact ⟨hf.mapsTo hy, by rw [mem_preimage, hf.left_inv y hy]; exact hyφ⟩)
  rw [← h1]
  exact congrArg _ (hf.tangent.left_inv α hαU)

namespace GraphChart

variable {n : ℕ} {N : Set X}

/-- **A graph chart moved by an sc-diffeomorphism.** -/
def mapDiffeo (c : P.GraphChart n N) (hN : P.IsSmoothSubmanifold N) {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') (hNU : N ⊆ U) : P.GraphChart n (f '' N) where
  φ := transportChart hf.symm c.φ
  isChart := transportChart_isChart hf.symm c.isChart
  subset_source := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hf.mapsTo (hNU hy), by
      rw [mem_preimage, hf.left_inv y (hNU hy)]; exact c.subset_source hy⟩
  p := c.p
  q := fun u => f (c.q u)
  q_coord := by
    rintro _ ⟨y, hy, rfl⟩
    change f (c.q (c.p (c.φ (g (f y))))) = f y
    rw [hf.left_inv y (hNU hy), c.q_coord y hy]
  L := fun z => c.L (g z)
  measurableSet_dom := by
    have h : (fun z => c.p (transportChart hf.symm c.φ z)) '' (f '' N) =
        (fun y => c.p (c.φ y)) '' N := by
      rw [image_image]
      refine image_congr fun y hy => ?_
      change c.p (c.φ (g (f y))) = _
      rw [hf.left_inv y (hNU hy)]
    exact h ▸ c.measurableSet_dom
  p_L := by
    rintro _ ⟨y, hy, rfl⟩ v
    change c.p (c.L (g (f y)) v) = v
    rw [hf.left_inv y (hNU hy)]
    exact c.p_L y hy v
  range_L := by
    rintro _ ⟨y, hy, rfl⟩
    change range (c.L (g (f y))) = _
    rw [hf.left_inv y (hNU hy), c.range_L y hy]
    change _ = (fun α => chartVec (transportChart_isChart hf.symm c.isChart) α) ''
      P.submanifoldTangent (f '' N) (f y)
    rw [submanifoldTangent_image_of_isScDiffeoOn hf hN hNU hy, image_image]
    exact image_congr fun α hα => (chartVec_transport_tangentMapOn hf c.isChart (hNU hy)
      (c.subset_source hy) hα.1).symm
  hasFDerivWithinAt := by
    rintro _ ⟨y, hy, rfl⟩
    have hset : (fun z => c.p (transportChart hf.symm c.φ z)) '' (f '' N) =
        (fun y => c.p (c.φ y)) '' N := by
      rw [image_image]
      refine image_congr fun y hy => ?_
      change c.p (c.φ (g (f y))) = _
      rw [hf.left_inv y (hNU hy)]
    have hgy : g (f y) = y := hf.left_inv y (hNU hy)
    have key := c.hasFDerivWithinAt y hy
    change HasFDerivWithinAt (fun u => c.φ (g (f (c.q u)))) (c.L (g (f y)))
      ((fun z => c.p (transportChart hf.symm c.φ z)) '' (f '' N)) (c.p (c.φ (g (f y))))
    rw [hset, hgy]
    refine key.congr (fun u hu => ?_) ?_
    · obtain ⟨w, hw, rfl⟩ := hu
      change c.φ (g (f (c.q (c.p (c.φ w))))) = c.φ (c.q (c.p (c.φ w)))
      rw [c.q_coord w hw, hf.left_inv w (hNU hw)]
    · change c.φ (g (f (c.q (c.p (c.φ y))))) = c.φ (c.q (c.p (c.φ y)))
      rw [c.q_coord y hy, hf.left_inv y (hNU hy)]
  continuousOn_L := by
    have hsub : f '' N ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hNU hy)
    refine c.continuousOn_L.comp (hf.isScSmoothOn_inv.continuousOn.mono hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hf.left_inv y (hNU hy)]; exact hy

variable (c : P.GraphChart n N) (hN : P.IsSmoothSubmanifold N) {f g : X → X} {U U' : Set X}
  (hf : P.IsScDiffeoOn P f g U U') (hNU : N ⊆ U)

theorem mapDiffeo_coord {y : X} (hy : y ∈ N) :
    (c.mapDiffeo hN hf hNU).coord (f y) = c.coord y := by
  change c.p (c.φ (g (f y))) = c.p (c.φ y)
  rw [hf.left_inv y (hNU hy)]

theorem mapDiffeo_dom : (c.mapDiffeo hN hf hNU).dom = c.dom := by
  change (c.mapDiffeo hN hf hNU).coord '' (f '' N) = c.coord '' N
  rw [image_image]
  exact image_congr fun y hy => c.mapDiffeo_coord hN hf hNU hy

set_option linter.unusedVariables false in
theorem mapDiffeo_q {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ c.dom) :
    (c.mapDiffeo hN hf hNU).q u = f (c.q u) := rfl

theorem mapDiffeo_tvec {y : X} (hy : y ∈ N) (i : Fin n) :
    (c.mapDiffeo hN hf hNU).tvec (f y) i = tangentMapOn hf.isScSmoothOn (c.tvec y i) := by
  have hfy : f y ∈ f '' N := mem_image_of_mem f hy
  have hα : P.levelVal 1 (P.tangentProj (c.tvec y i)) = y :=
    levelVal_tangentProj_of_mem (c.tvec_mem hy i)
  have hαU : c.tvec y i ∈ P.tangentPreimage U := by change _ ∈ U; rw [hα]; exact hNU hy
  refine chartVec_injOn (c.mapDiffeo hN hf hNU).isChart
    ((c.mapDiffeo hN hf hNU).subset_source hfy)
    (levelVal_tangentProj_of_mem ((c.mapDiffeo hN hf hNU).tvec_mem hfy i)) ?_ ?_
  · change P.levelVal 1 (P.tangentProj (tangentMapOn hf.isScSmoothOn (c.tvec y i))) = f y
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hαU, hα]
  · rw [(c.mapDiffeo hN hf hNU).chartVec_tvec hfy]
    change c.L (g (f y)) (bvec i) =
      chartVec (transportChart_isChart hf.symm c.isChart) (tangentMapOn hf.isScSmoothOn _)
    rw [chartVec_transport_tangentMapOn hf c.isChart (hNU hy) (c.subset_source hy) hα,
      hf.left_inv y (hNU hy), c.chartVec_tvec hy]

end GraphChart

/-- The image of a set of `n`-dimensional measure zero under an sc-diffeomorphism. -/
theorem IsHNull.image_of_isScDiffeoOn {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {n : ℕ} {C : Set X} (hC : C ⊆ U) (h : P.IsHNull n C) :
    P.IsHNull n (f '' C) := by
  intro ψ hψ D' hD' hD'ψ hsep
  have hgD : g '' D' ⊆ C := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hD' hd
    rw [hf.left_inv x (hC hx)]; exact hx
  have hfg : ∀ d ∈ D', f (g d) = d := fun d hd => by
    obtain ⟨x, hx, rfl⟩ := hD' hd
    rw [hf.left_inv x (hC hx)]
  have himg : transportChart hf ψ '' (g '' D') = ψ '' D' := by
    rw [image_image]
    refine image_congr fun d hd => ?_
    change ψ (f (g d)) = ψ d
    rw [hfg d hd]
  have hsrc : g '' D' ⊆ (transportChart hf ψ).source := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨hC (hgD ⟨d, hd, rfl⟩), by rw [mem_preimage, hfg d hd]; exact hD'ψ hd⟩
  have key := h (transportChart hf ψ) (transportChart_isChart hf hψ) (g '' D') hgD hsrc
    (by rw [himg]; exact hsep)
  rw [himg] at key
  exact key

/-- The image of the trace on `U` of a Borel set under an sc-diffeomorphism `f : U → U'` is a
Borel set. -/
theorem measurableSet_borel_image_of_isScDiffeoOn {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {B : Set X} (hB : MeasurableSet[borel X] B) :
    MeasurableSet[borel X] (f '' (B ∩ U)) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have hU' : IsOpen U' := hf.isScSmoothOn_inv.isOpen
  have hr : Continuous (U'.domRestrict g) :=
    continuousOn_iff_continuous_domRestrict.1 hf.isScSmoothOn_inv.continuousOn
  have hm : MeasurableSet (U'.domRestrict g ⁻¹' B) := hr.measurable hB
  have h := hU'.measurableSet.subtype_image hm
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, ⟨hxB, hxU⟩, rfl⟩
    refine ⟨⟨f x, hf.mapsTo hxU⟩, ?_, rfl⟩
    change g (f x) ∈ B
    rw [hf.left_inv x hxU]; exact hxB
  · rintro ⟨⟨w, hw⟩, hwB, rfl⟩
    exact ⟨g w, ⟨hwB, hf.mapsTo_inv hw⟩, hf.right_inv w hw⟩

/-- A frame over `y ∈ N` is positive for `o` iff its image under `Tf` is positive for the
orientation moved by `f`. -/
theorem SubmanifoldOrientation.mapDiffeo_frames_iff {N : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation N n) (hN : P.IsSmoothSubmanifold N) {f g : X → X}
    {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U') (hNU : N ⊆ U) {y : X} (hy : y ∈ N)
    (α : Fin n → P.TangentSpace) (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y) :
    (fun i => tangentMapOn hf.isScSmoothOn (α i)) ∈ (o.mapDiffeo hN hf hNU).frames (f y) ↔
      α ∈ o.frames y := by
  rw [SubmanifoldOrientation.mapDiffeo_frames, hf.left_inv y (hNU hy)]
  constructor
  · rintro ⟨v, hv, hve⟩
    have : v = α := by
      funext i
      have hvU : v i ∈ P.tangentPreimage U := by
        change _ ∈ U; rw [o.levelVal_frames hy hv i]; exact hNU hy
      have hαU : α i ∈ P.tangentPreimage U := by change _ ∈ U; rw [hα i]; exact hNU hy
      rw [← hf.tangent.left_inv (v i) hvU, ← hf.tangent.left_inv (α i) hαU]
      exact congrArg _ (congrFun hve i)
    exact this ▸ hv
  · exact fun h => ⟨α, h, rfl⟩

end MPolyfold

end Polyfold
