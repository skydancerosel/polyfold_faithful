import Polyfold.Chapter9.GraphDiffeo
import Polyfold.Chapter9.TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, pp. 542–546 (gap G.131).  Numbers and pages are the 2021 text's.

# Graph charts, null sets, Borel sets and tameness under sc-diffeomorphisms between two M-polyfolds

The cross-M-polyfold versions of the lemmas of `Chapter9/GraphDiffeo.lean` and of
`HasTameInducedStructure.inter_isOpen` (`Chapter9/TameOpen.lean`), used for
Theorem 11.4.1: an sc-diffeomorphism `f : U → U'` between open subsets of two M-polyfolds `X` and
`Y` carries

* a graph chart `c` of `N ⊆ U` to a graph chart of `f(N)`, read in the transported chart
  `φ ∘ f⁻¹` (`GraphChart.mapDiffeoCross`), with the same coordinate images and the frame
  `Tf ∘ c.tvec`;
* sets of `n`-dimensional measure zero in `U` to such sets, and traces on `U` of Borel sets to
  Borel sets;
* frames positive for an orientation `o` of `N` exactly to the frames positive for `f_*o`;
* a tame induced structure on `N` to one on `f(N)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- The chart vector of `Tf(α)` in the chart `φ ∘ f⁻¹` of `Y` is the chart vector of `α` in the
chart `φ` of `X` (`chartVec_transport_tangentMapOn` for two M-polyfolds). -/
theorem chartVec_transport_tangentMapOn_cross {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {φ : MChart X} (hφ : P.IsChart φ) {α : P.TangentSpace}
    {y : X} (hy : y ∈ U) (hyφ : y ∈ φ.source) (hα : P.levelVal 1 (P.tangentProj α) = y) :
    chartVec (transportChart_isChart hf.symm hφ) (tangentMapOn hf.isScSmoothOn α) =
      chartVec hφ α := by
  have hαU : α ∈ P.tangentPreimage U := by change _ ∈ U; rw [hα]; exact hy
  have hbase : Q.levelVal 1 (Q.tangentProj (tangentMapOn hf.isScSmoothOn α)) = f y := by
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hαU, hα]
  have h1 := chartVec_tangentMapOn_of_isScDiffeoOn hf.symm hφ
    (α := tangentMapOn hf.isScSmoothOn α) (by
      rw [hbase]
      exact ⟨hf.mapsTo hy, by rw [mem_preimage, hf.left_inv y hy]; exact hyφ⟩)
  rw [← h1]
  exact congrArg _ (hf.tangent.left_inv α hαU)

namespace GraphChart

variable {n : ℕ} {N : Set X}

/-- **A graph chart moved by an sc-diffeomorphism between two M-polyfolds.** -/
def mapDiffeoCross (c : P.GraphChart n N) (hN : P.IsSmoothSubmanifold N) {f : X → Y}
    {g : Y → X} {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hNU : N ⊆ U) :
    Q.GraphChart n (f '' N) where
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
      Q.submanifoldTangent (f '' N) (f y)
    rw [submanifoldTangent_image_of_isScDiffeoOn hf hN hNU hy, image_image]
    exact image_congr fun α hα => (chartVec_transport_tangentMapOn_cross hf c.isChart (hNU hy)
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
    · rw [c.q_coord y hy, hf.left_inv y (hNU hy)]
  continuousOn_L := by
    have hsub : f '' N ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hNU hy)
    refine c.continuousOn_L.comp (hf.isScSmoothOn_inv.continuousOn.mono hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hf.left_inv y (hNU hy)]; exact hy

variable (c : P.GraphChart n N) (hN : P.IsSmoothSubmanifold N) {f : X → Y} {g : Y → X}
  {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hNU : N ⊆ U)

/-- The coordinate of `f(y)` in the moved graph chart is the coordinate of `y`. -/
theorem mapDiffeoCross_coord {y : X} (hy : y ∈ N) :
    (c.mapDiffeoCross hN hf hNU).coord (f y) = c.coord y := by
  change c.p (c.φ (g (f y))) = c.p (c.φ y)
  rw [hf.left_inv y (hNU hy)]

/-- The moved graph chart has the same coordinate domain. -/
theorem mapDiffeoCross_dom : (c.mapDiffeoCross hN hf hNU).dom = c.dom := by
  change (c.mapDiffeoCross hN hf hNU).coord '' (f '' N) = c.coord '' N
  rw [image_image]
  exact image_congr fun y hy => c.mapDiffeoCross_coord hN hf hNU hy

set_option linter.unusedVariables false in
/-- The parametrization of the moved graph chart is `f ∘ c.q`. -/
theorem mapDiffeoCross_q {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ c.dom) :
    (c.mapDiffeoCross hN hf hNU).q u = f (c.q u) := rfl

/-- The frame of the moved graph chart at `f(y)` is `Tf` of the frame at `y`. -/
theorem mapDiffeoCross_tvec {y : X} (hy : y ∈ N) (i : Fin n) :
    (c.mapDiffeoCross hN hf hNU).tvec (f y) i = tangentMapOn hf.isScSmoothOn (c.tvec y i) := by
  have hfy : f y ∈ f '' N := mem_image_of_mem f hy
  have hα : P.levelVal 1 (P.tangentProj (c.tvec y i)) = y :=
    levelVal_tangentProj_of_mem (c.tvec_mem hy i)
  have hαU : c.tvec y i ∈ P.tangentPreimage U := by change _ ∈ U; rw [hα]; exact hNU hy
  refine chartVec_injOn (c.mapDiffeoCross hN hf hNU).isChart
    ((c.mapDiffeoCross hN hf hNU).subset_source hfy)
    (levelVal_tangentProj_of_mem ((c.mapDiffeoCross hN hf hNU).tvec_mem hfy i)) ?_ ?_
  · change Q.levelVal 1 (Q.tangentProj (tangentMapOn hf.isScSmoothOn (c.tvec y i))) = f y
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hαU, hα]
  · rw [(c.mapDiffeoCross hN hf hNU).chartVec_tvec hfy]
    change c.L (g (f y)) (bvec i) =
      chartVec (transportChart_isChart hf.symm c.isChart) (tangentMapOn hf.isScSmoothOn _)
    rw [chartVec_transport_tangentMapOn_cross hf c.isChart (hNU hy) (c.subset_source hy) hα,
      hf.left_inv y (hNU hy), c.chartVec_tvec hy]

end GraphChart

/-- The image of a set of `n`-dimensional measure zero under an sc-diffeomorphism between two
M-polyfolds has `n`-dimensional measure zero. -/
theorem IsHNull.image_of_isScDiffeoOn_cross {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {n : ℕ} {C : Set X} (hC : C ⊆ U) (h : P.IsHNull n C) :
    Q.IsHNull n (f '' C) := by
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

/-- The image of the trace on `U` of a Borel set under an sc-diffeomorphism `f : U → U'` between
two M-polyfolds is a Borel set. -/
theorem measurableSet_borel_image_of_isScDiffeoOn_cross {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {B : Set X} (hB : MeasurableSet[borel X] B) :
    MeasurableSet[borel Y] (f '' (B ∩ U)) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
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
orientation moved by an sc-diffeomorphism `f` between two M-polyfolds. -/
theorem SubmanifoldOrientation.mapDiffeo_frames_iff_cross {N : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation N n) (hN : P.IsSmoothSubmanifold N) {f : X → Y} {g : Y → X}
    {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hNU : N ⊆ U) {y : X} (hy : y ∈ N)
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

/-- An orientation of `N' ⊆ U'` moved back by `g` and then forward by `f` has, at every point of
`N'`, the frames of the original orientation. -/
theorem SubmanifoldOrientation.mapDiffeo_symm_mapDiffeo_frames {N' : Set Y} {n : ℕ}
    (o : Q.SubmanifoldOrientation N' n) (hN' : Q.IsSmoothSubmanifold N') {f : X → Y}
    {g : Y → X} {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hN'U' : N' ⊆ U')
    (hgN : P.IsSmoothSubmanifold (g '' N')) (hsub : g '' N' ⊆ U) {z : Y} (hz : z ∈ N') :
    ((o.mapDiffeo hN' hf.symm hN'U').mapDiffeo hgN hf hsub).frames z = o.frames z := by
  rw [SubmanifoldOrientation.mapDiffeo_frames, SubmanifoldOrientation.mapDiffeo_frames,
    hf.right_inv z (hN'U' hz), image_image]
  refine (image_congr (g := id) fun v hv => ?_).trans (image_id _)
  funext i
  exact hf.tangent.right_inv (v i)
    (by change _ ∈ U'; rw [o.levelVal_frames hz hv i]; exact hN'U' hz)

/-- **The image of a submanifold with a tame induced structure under an sc-diffeomorphism between
two M-polyfolds has a tame induced structure** (2021 Definition 2.5.18): `f` and `g` restrict to
an sc-diffeomorphism `f(N) → N` of the sub-M-polyfolds, and tame charts are carried along
(`IsScDiffeoOn.exists_tame_chart`). -/
theorem HasTameInducedStructure.image_of_isScDiffeoOn {N : Set X}
    (hN : P.IsSmoothSubmanifold N) (ht : P.HasTameInducedStructure N) {f : X → Y} {g : Y → X}
    {U : Set X} {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') (hNU : N ⊆ U) :
    Q.HasTameInducedStructure (f '' N) := by
  classical
  obtain ⟨hY, htame⟩ := ht
  have hY' : Q.IsSubMPolyfold (f '' N) := (hN.image_of_isScDiffeoOn hf hNU).isSubMPolyfold
  let _ := P.paracompactSpace_subtype N
  let _ := Q.paracompactSpace_subtype (f '' N)
  refine ⟨hY', isTame_of_forall_exists_chart _ fun x => ?_⟩
  have hgN : ∀ z ∈ f '' N, g z ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hf.left_inv y (hNU hy)]; exact hy
  let k : ↥(f '' N) → ↥N := fun z => ⟨g z.1, hgN z.1 z.2⟩
  let j : ↥N → ↥(f '' N) := fun y => ⟨f y.1, mem_image_of_mem f y.2⟩
  have hk : (subPolyfold hY').IsScSmoothOn (subPolyfold hY) k univ :=
    isScSmoothOn_subPolyfold_of_val hY (f := k)
      (hf.isScSmoothOn_inv.comp (subPolyfold_inclusion_isScSmooth hY')
        fun z _ => image_subset_iff.2 (fun y hy => hf.mapsTo (hNU hy)) z.2)
  have hj : (subPolyfold hY).IsScSmoothOn (subPolyfold hY') j univ :=
    isScSmoothOn_subPolyfold_of_val hY' (f := j)
      (hf.isScSmoothOn.comp (subPolyfold_inclusion_isScSmooth hY) fun y _ => hNU y.2)
  have hd : (subPolyfold hY').IsScDiffeoOn (subPolyfold hY) k j univ univ :=
    { isScSmoothOn := hk
      isScSmoothOn_inv := hj
      mapsTo := fun _ _ => mem_univ _
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun z _ => Subtype.ext (by
        obtain ⟨_, y, hy, rfl⟩ := z
        exact congrArg f (hf.left_inv y (hNU hy)))
      right_inv := fun y _ => Subtype.ext (hf.left_inv y.1 (hNU y.2)) }
  exact hd.exists_tame_chart htame (mem_univ x)

end MPolyfold

end Polyfold
