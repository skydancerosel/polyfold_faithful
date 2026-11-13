import Polyfold.Chapter9.ChartIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# The integration of forms over oriented sheets: the concrete `SheetIntegration`

For an evaluation of forms `F : X.FormEval n Ω` (`n ≥ 1`; the sc-differential forms of
Definition 8.2.1 give one, `FormEvalEp.lean`):

* `F.sheets`: the class `S` of the `n`-dimensional submanifolds `N` of the object M-polyfold
  which lie in one graph chart and on which every form of `Ω` is absolutely integrable (every
  point of an `n`-dimensional submanifold has a neighbourhood `V` with `N ∩ V` in a graph chart,
  `MPolyfold.exists_graphChart`).
* `F.sheetNull`: the sets of `n`-dimensional measure zero of Definition 9.4.5
  (`MPolyfold.IsHNull`), on this class.
* `F.integ ω N T_•(N, o) A = ∫_A ω|(N, o)`: the Lebesgue integral, in the coordinates of a graph
  chart of `N`, of `± ω(∂₁, …, ∂ₙ)`, `∂ᵢ` the coordinate frame of `T_yN`, with the sign `+` where
  this frame is positive for `o` (Definition 9.3.3).
* **`F.sheetIntegration hn : X.SheetIntegration F.sheetNull Ω`**: all fields of the structure of
  `SheetIntegrationAbstract.lean` hold, so that (9.20), Lemmas 9.5.7, 9.5.9–9.5.11 and
  Theorems 9.5.4, 9.5.5 of `GapP2_E1_*.lean` apply to it.

## The choices made

The sheets of the class lie in one chart; a sheet of a branching structure is cut into such
pieces by restricting the structure to a smaller neighbourhood.  The integral over a sheet
covered by several charts is not defined here.  (2026-11-13) It is defined in
`MultiChart.lean`, `MultiChartIntegration.lean` (`FormEval.msheetIntegration`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

/-- **The class of sheets**: `n`-dimensional submanifolds in one graph chart on which the forms
of `Ω` are absolutely integrable. -/
def sheets : Set (Set Obj) :=
  {N | X.PObj.IsSubmanifoldOfDim N n ∧ ∃ c : X.PObj.GraphChart n N,
    ∀ ω, IntegrableOn (fun u => F.ev ω (c.tvec (c.q u))) c.dom volume}

variable {F} {N N' : Set Obj}

/-- The chosen graph chart of a sheet of the class. -/
def chart (hN : N ∈ F.sheets) : X.PObj.GraphChart n N := hN.2.choose

theorem integrableOn_chart (hN : N ∈ F.sheets) (ω : Ω) :
    IntegrableOn (fun u => F.ev ω ((chart hN).tvec ((chart hN).q u))) (chart hN).dom volume :=
  hN.2.choose_spec ω

variable (F) in
/-- **The sets of `n`-dimensional measure zero** (Definition 9.4.5) on the class `F.sheets`. -/
def sheetNull : SheetNullSets F.sheets :=
  X.PObj.hNullSets n F.sheets fun N hN hne => by
    obtain ⟨y, hy⟩ := hne
    exact MPolyfold.not_isHNull_of_hasDimAt hN.1.1 (hN.1.2 y hy)

theorem sheetNull_isNull_iff {N A : Set Obj} :
    F.sheetNull.IsNull N A ↔ X.PObj.IsHNull n (A ∩ N) := Iff.rfl

/-- The coordinate image of a measurable subset of a sheet is Lebesgue measurable. -/
theorem nullMeasurableSet_coord_image (c : X.PObj.GraphChart n N) {A : Set Obj}
    (hA : F.sheetNull.IsMeasIn N A) : NullMeasurableSet (c.coord '' (A ∩ N)) volume := by
  obtain ⟨B, hB, hnull⟩ := hA
  refine c.nullMeasurableSet_coord_image hB (MPolyfold.IsHNull.mono hnull fun y hy => ⟨hy, ?_⟩)
  rcases hy with hy | hy <;> exact hy.1.2

open Classical in
variable (F) in
/-- **`∫_A ω|(N, o)`** for `g = T_•(N, o)`: the integral in the chosen graph chart of `N`. -/
def integ (ω : Ω) (N : Set Obj) (g : Obj → X.PObj.OrTangent) (A : Set Obj) : ℝ :=
  if h : N ∈ F.sheets ∧ ∃ o : X.PObj.SubmanifoldOrientation N n, g = o.tangent then
    F.chartInteg (chart h.1) ω g A
  else 0

theorem integ_eq (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (A : Set Obj) : F.integ ω N o.tangent A = F.chartInteg (chart hN) ω o.tangent A := by
  unfold integ
  rw [dif_pos ⟨hN, o, rfl⟩]

theorem chartInteg_of_inter_eq_empty (c : X.PObj.GraphChart n N) (ω : Ω)
    (g : Obj → X.PObj.OrTangent) {A : Set Obj} (hA : A ∩ N = ∅) : F.chartInteg c ω g A = 0 := by
  unfold chartInteg
  rw [hA, image_empty, Measure.restrict_empty, integral_zero_measure]

theorem integ_of_inter_eq_empty (ω : Ω) (g : Obj → X.PObj.OrTangent) {A : Set Obj}
    (hA : A ∩ N = ∅) : F.integ ω N g A = 0 := by
  unfold integ
  split_ifs with h
  · exact chartInteg_of_inter_eq_empty _ ω g hA
  · rfl

/-- The chart integral is additive in the form. -/
theorem chartInteg_add (hn : 0 < n) (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n)
    (ω τ : Ω) (A : Set Obj) :
    F.chartInteg (chart hN) (ω + τ) o.tangent A =
      F.chartInteg (chart hN) ω o.tangent A + F.chartInteg (chart hN) τ o.tangent A := by
  have hsub : (chart hN).coord '' (A ∩ N) ⊆ (chart hN).dom := image_mono inter_subset_right
  have h1 := (F.integrableOn_density hn hN.1.1 (chart hN) o ω
    (integrableOn_chart hN ω)).mono_set hsub
  have h2 := (F.integrableOn_density hn hN.1.1 (chart hN) o τ
    (integrableOn_chart hN τ)).mono_set hsub
  unfold chartInteg
  rw [← integral_add h1 h2]
  exact integral_congr_ae (Eventually.of_forall fun u => F.density_add _ ω τ _ _)

theorem chartInteg_smul (c : X.PObj.GraphChart n N) (a : ℝ) (ω : Ω)
    (g : Obj → X.PObj.OrTangent) (A : Set Obj) :
    F.chartInteg c (a • ω) g A = a * F.chartInteg c ω g A := by
  unfold chartInteg
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => F.density_smul _ a ω _ _)

/-- A sheet with a graph chart is homeomorphic to a subset of `ℝⁿ`. -/
def coordHomeomorph (c : X.PObj.GraphChart n N) : N ≃ₜ c.dom where
  toFun y := ⟨c.coord y, c.coord_mem_dom y.2⟩
  invFun u := ⟨c.q u, c.q_mem u.2⟩
  left_inv y := Subtype.ext (c.q_coord' y.2)
  right_inv u := Subtype.ext (c.coord_q u.2)
  continuous_toFun :=
    (continuousOn_iff_continuous_domRestrict.1 c.continuousOn_coord).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_domRestrict.1 c.continuousOn_q).subtype_mk _

theorem hereditarilyLindelofSpace (c : X.PObj.GraphChart n N) : HereditarilyLindelofSpace N := by
  have : SecondCountableTopology N := (coordHomeomorph c).secondCountableTopology
  infer_instance

/-- An orientation of a nonempty sheet of the class has dimension `n`. -/
theorem dim_eq (hN : N ∈ F.sheets) {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m) {y : Obj}
    (hy : y ∈ N) : m = n := (chart hN).dim_eq_of_orientation o hy

theorem inter_mem_sheets (hN : N ∈ F.sheets) {V : Set Obj} (hV : IsOpen V) :
    N ∩ V ∈ F.sheets :=
  ⟨hN.1.inter_isOpen hV, (chart hN).restrict hV, fun ω =>
    (integrableOn_chart hN ω).mono_set ((chart hN).restrict_dom_subset hV)⟩

theorem image_mem_sheets (hN : N ∈ F.sheets) {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) :
    f '' N ∈ F.sheets := by
  refine ⟨hN.1.image_of_isScDiffeoOn hf hNU, (chart hN).mapDiffeo hN.1.1 hf hNU, fun ω => ?_⟩
  rw [(chart hN).mapDiffeo_dom hN.1.1 hf hNU]
  refine (integrableOn_chart hN ω).congr_fun (fun u hu => ?_) (chart hN).measurableSet_dom'
  have hq := (chart hN).q_mem hu
  change _ = F.ev ω (((chart hN).mapDiffeo hN.1.1 hf hNU).tvec (f ((chart hN).q u)))
  have htv : ((chart hN).mapDiffeo hN.1.1 hf hNU).tvec (f ((chart hN).q u)) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn ((chart hN).tvec ((chart hN).q u) i) :=
    funext fun i => (chart hN).mapDiffeo_tvec hN.1.1 hf hNU hq i
  rw [htv, F.ev_tangentMapOn hN.1.1 hf hmor ω hq _ ((chart hN).tvec_mem hq)]

theorem isNull_tangent_ne (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hN' : X.PObj.IsSubmanifoldOfDim N' n) :
    X.PObj.IsHNull n ({y | y ∈ N ∩ N' ∧
      X.PObj.submanifoldTangent N y ≠ X.PObj.submanifoldTangent N' y} ∩ N) := by
  have h := (X.PObj.sheetGeometry n).isNull_diff_ess N hN N' hN'
  refine MPolyfold.IsHNull.mono h ?_
  rintro y ⟨⟨hy, hne⟩, hyN⟩
  exact ⟨⟨hy, fun hess =>
    hne ((X.PObj.sheetGeometry n).submanifoldTangent_eq N hN N' hN' y hess)⟩, hyN⟩

theorem _root_.Polyfold.iff_iff_iff_of_iff_iff (a b c d : Prop) (h : (a ↔ c) ↔ d) :
    (b ↔ a) ↔ (b ↔ (c ↔ d)) := by
  tauto

/-- The set where the oriented tangent spaces of two oriented sheets agree is measurable. -/
theorem isMeasIn_tangent_eq (hn : 0 < n) (hN : N ∈ F.sheets) (hN' : N' ∈ F.sheets)
    (o : X.PObj.SubmanifoldOrientation N n) (o' : X.PObj.SubmanifoldOrientation N' n) :
    F.sheetNull.IsMeasIn N {y | y ∈ N ∩ N' ∧ o.tangent y = o'.tangent y} := by
  classical
  set c := chart hN
  set c' := chart hN'
  obtain ⟨W₁, hW₁, hW₁e⟩ := c.exists_isOpen_isPos hN.1.1 hn o
  obtain ⟨W₂, hW₂, hW₂e⟩ := c'.exists_isOpen_isPos hN'.1.1 hn o'
  obtain ⟨W₃, hW₃, hW₃e⟩ := c.exists_isOpen_transMatrix_det_pos c' hN.1.1
  have hm : ∀ W : Set Obj, IsOpen W → MeasurableSet[borel Obj] W := fun W hW =>
    MeasurableSpace.measurableSet_generateFrom hW
  set B : Set Obj := N' ∩ {y | y ∈ W₁ ↔ (y ∈ W₂ ↔ y ∈ W₃)} with hB
  have hBm : MeasurableSet[borel Obj] B := by
    refine @MeasurableSet.inter Obj (borel Obj) _ _ hN'.1.1.measurableSet_borel ?_
    have e : {y | y ∈ W₁ ↔ (y ∈ W₂ ↔ y ∈ W₃)} =
        (W₁ ∩ ((W₂ ∩ W₃) ∪ (W₂ᶜ ∩ W₃ᶜ))) ∪ (W₁ᶜ ∩ ((W₂ ∩ W₃ᶜ) ∪ (W₂ᶜ ∩ W₃))) := by
      ext y
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [e]
    let _ : MeasurableSpace Obj := borel Obj
    exact ((hm W₁ hW₁).inter (((hm W₂ hW₂).inter (hm W₃ hW₃)).union
      ((hm W₂ hW₂).compl.inter (hm W₃ hW₃).compl))).union ((hm W₁ hW₁).compl.inter
      (((hm W₂ hW₂).inter (hm W₃ hW₃).compl).union ((hm W₂ hW₂).compl.inter (hm W₃ hW₃))))
  -- the description of the set at the points where the tangent spaces agree
  have key : ∀ y, y ∈ N → y ∈ N' →
      X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y →
      (o.tangent y = o'.tangent y ↔ (y ∈ W₁ ↔ (y ∈ W₂ ↔ y ∈ W₃))) := by
    intro y hy hy' hT
    have h1 : y ∈ W₁ ↔ c.tvec y ∈ o.frames y := by
      have : y ∈ {y | y ∈ N ∧ c.tvec y ∈ o.frames y} ↔ y ∈ N ∩ W₁ := by rw [hW₁e]
      exact ⟨fun h => (this.2 ⟨hy, h⟩).2, fun h => (this.1 ⟨hy, h⟩).2⟩
    have h2 : y ∈ W₂ ↔ c'.tvec y ∈ o'.frames y := by
      have : y ∈ {y | y ∈ N' ∧ c'.tvec y ∈ o'.frames y} ↔ y ∈ N' ∩ W₂ := by rw [hW₂e]
      exact ⟨fun h => (this.2 ⟨hy', h⟩).2, fun h => (this.1 ⟨hy', h⟩).2⟩
    have h3 : y ∈ W₃ ↔ 0 < (c.transMatrix c' y).det := by
      have : y ∈ {y | y ∈ N ∩ N' ∧ 0 < (c.transMatrix c' y).det} ↔ y ∈ (N ∩ N') ∩ W₃ := by
        rw [hW₃e]
      exact ⟨fun h => (this.2 ⟨⟨hy, hy'⟩, h⟩).2, fun h => (this.1 ⟨⟨hy, hy'⟩, h⟩).2⟩
    have hsrc : y ∈ c'.φ.source := c'.subset_source hy'
    have hmem : ∀ i, c.tvec y i ∈ X.PObj.submanifoldTangent N' y := fun i =>
      hT ▸ c.tvec_mem hy i
    have hdet := MPolyfold.IsOrientedAt.frames_iff_frames_iff_det_pos hN'.1 hy'
      (o'.isOrientedAt y hy') c'.isChart hsrc (c'.tvec_mem hy') hmem
      (c'.linearIndependent_chartVec_tvec hy')
      (c.linearIndependent_chartVec_tvec_of_chart hy c'.isChart hsrc) (c.transMatrix c' y)
      (c.chartVec_tvec_eq_sum_transMatrix c' hy hy' hT)
    have hO : X.PObj.IsOrientedAt y ⟨n, X.PObj.submanifoldTangent N y, o'.frames y⟩ :=
      hT ▸ o'.isOrientedAt y hy'
    have hfr : o.tangent y = o'.tangent y ↔ o.frames y = o'.frames y := by
      simp only [MPolyfold.SubmanifoldOrientation.tangent, MPolyfold.OrTangent.mk.injEq,
        heq_eq_eq, true_and, hT]
    have hfr2 : o.frames y = o'.frames y ↔ (c.tvec y ∈ o.frames y ↔ c.tvec y ∈ o'.frames y) := by
      constructor
      · intro h; rw [h]
      · intro h
        by_contra hne
        have := MPolyfold.IsOrientedAt.mem_frames_iff_notMem (o.isOrientedAt y hy) hO hne
          c.isChart (c.subset_source hy) (c.tvec_mem hy) (c.linearIndependent_chartVec_tvec hy)
        tauto
    have e1 : (c.tvec y ∈ o.frames y ↔ c.tvec y ∈ o'.frames y) ↔
        (c.tvec y ∈ o.frames y ↔ (c'.tvec y ∈ o'.frames y ↔ 0 < (c.transMatrix c' y).det)) :=
      iff_iff_iff_of_iff_iff (c.tvec y ∈ o'.frames y) (c.tvec y ∈ o.frames y) (c'.tvec y ∈ o'.frames y)
        (0 < (c.transMatrix c' y).det) hdet
    have e2 : (c.tvec y ∈ o.frames y ↔ (c'.tvec y ∈ o'.frames y ↔
        0 < (c.transMatrix c' y).det)) ↔ (y ∈ W₁ ↔ (y ∈ W₂ ↔ y ∈ W₃)) :=
      iff_congr h1.symm (iff_congr h2.symm h3.symm)
    exact hfr.trans (hfr2.trans (e1.trans e2))
  refine ⟨B, hBm, MPolyfold.IsHNull.mono (isNull_tangent_ne hN.1 hN'.1) ?_⟩
  rintro y ⟨hy, hyN⟩
  refine ⟨⟨?_, ?_⟩, hyN⟩
  · rcases hy with hy | hy
    · exact hy.1.1.1
    · exact ⟨hy.1.2, hy.1.1.1⟩
  · intro hT
    rcases hy with ⟨⟨⟨hyNN, heq⟩, -⟩, hnB⟩ | ⟨⟨⟨hyN', hW⟩, -⟩, hnQ⟩
    · exact hnB ⟨⟨hyNN.2, (key y hyNN.1 hyNN.2 hT).1 heq⟩, hyN⟩
    · exact hnQ ⟨⟨⟨hyN, hyN'⟩, (key y hyN hyN' hT).2 hW⟩, hyN⟩

theorem isMeasIn_image {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hNU : N ⊆ U) {A : Set Obj} (hA : A ⊆ N)
    (hAm : F.sheetNull.IsMeasIn N A) : F.sheetNull.IsMeasIn (f '' N) (f '' A) := by
  obtain ⟨B, hB, hnull⟩ := hAm
  refine ⟨f '' (B ∩ U), MPolyfold.measurableSet_borel_image_of_isScDiffeoOn hf hB, ?_⟩
  have h1 : X.PObj.IsHNull n (f '' ((A ∩ N) ∆ (B ∩ N))) :=
    MPolyfold.IsHNull.image_of_isScDiffeoOn hf
      (fun y hy => by rcases hy with hy | hy <;> exact hNU hy.1.2)
      (MPolyfold.IsHNull.mono hnull fun y hy => ⟨hy, by rcases hy with hy | hy <;> exact hy.1.2⟩)
  refine MPolyfold.IsHNull.mono h1 ?_
  have hinj : InjOn f U := fun a ha b hb h => by
    rw [← hf.left_inv a ha, ← hf.left_inv b hb, h]
  rintro z ⟨hz, -⟩
  rcases hz with ⟨⟨⟨a, haA, rfl⟩, -⟩, hn⟩ | ⟨⟨⟨b, ⟨hbB, hbU⟩, rfl⟩, ⟨w, hwN, hw⟩⟩, hn⟩
  · refine ⟨a, Or.inl ⟨⟨haA, hA haA⟩, fun hc => hn ⟨⟨a, ⟨hc.1, hNU hc.2⟩, rfl⟩, a, hc.2, rfl⟩⟩, rfl⟩
  · have hwb : w = b := hinj (hNU hwN) hbU hw
    subst hwb
    refine ⟨w, Or.inr ⟨⟨hbB, hwN⟩, fun hc => hn ⟨⟨w, hc.1, rfl⟩, w, hwN, rfl⟩⟩, rfl⟩

variable (F) in
/-- **The integration of the forms of `Ω` over the oriented sheets of the class `F.sheets`**
(2021 §9.5, pp. 438–445): a `SheetIntegration` in the sense of `SheetIntegrationAbstract.lean`,
with the integrals `F.integ`. -/
def sheetIntegration (hn : 0 < n) : X.SheetIntegration F.sheetNull Ω where
  integ := F.integ
  integ_add ω τ N g A := by
    unfold integ
    split_ifs with h
    · obtain ⟨hN, o, rfl⟩ := h
      exact chartInteg_add hn hN o ω τ A
    · rw [add_zero]
  integ_smul a ω N g A := by
    unfold integ
    split_ifs with h
    · exact chartInteg_smul _ a ω g A
    · rw [mul_zero]
  lindelof N hN := hereditarilyLindelofSpace (chart hN)
  inter_mem N hN V hV := inter_mem_sheets hN hV
  isMeasIn_inter N hN N' hN' :=
    (SheetNullSets.isMeasIn_of_borel hN'.1.1.measurableSet_borel).congr_inter (by
      rw [inter_comm N' N, inter_assoc, inter_comm N' N, ← inter_assoc, inter_self])
  isNull_tangent_ne N hN N' hN' := isNull_tangent_ne hN.1 hN'.1
  isMeasIn_tangent_eq N hN N' hN' m m' o o' := by
    rcases eq_empty_or_nonempty {y | y ∈ N ∩ N' ∧ o.tangent y = o'.tangent y} with he | ⟨y, hy⟩
    · rw [he]; exact MeasurableSpace.measurableSet_empty _
    · obtain rfl := dim_eq hN o hy.1.1
      obtain rfl := dim_eq hN' o' hy.1.2
      exact isMeasIn_tangent_eq hn hN hN' o o'
  integ_hasSum ω N hN m o A hAN hAm hd := by
    rcases eq_empty_or_nonempty N with he | ⟨y, hy⟩
    · have h0 : ∀ B : Set Obj, F.integ ω N o.tangent B = 0 := fun B =>
        integ_of_inter_eq_empty ω _ (by rw [he, inter_empty])
      simp only [h0]
      exact hasSum_zero
    · obtain rfl := dim_eq hN o hy
      simp only [integ_eq hN o]
      set c := chart hN
      have himg : c.coord '' ((⋃ k, A k) ∩ N) = ⋃ k, c.coord '' (A k ∩ N) := by
        rw [iUnion_inter, image_iUnion]
      unfold chartInteg
      rw [himg]
      refine hasSum_integral_iUnion_ae (fun k => nullMeasurableSet_coord_image c (hAm k))
        (fun i j hij => Disjoint.aedisjoint ?_) ?_
      · refine disjoint_left.2 ?_
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        have : b = a := c.injOn_coord hb.2 ha.2 hab
        subst this
        exact disjoint_left.1 (hd hij) ha.1 hb.1
      · exact (F.integrableOn_density hn hN.1.1 c o ω (integrableOn_chart hN ω)).mono_set
          (iUnion_subset fun k => image_mono inter_subset_right)
  integ_null ω N hN m o A hAN hnull := by
    rcases eq_empty_or_nonempty N with he | ⟨y, hy⟩
    · exact integ_of_inter_eq_empty ω _ (by rw [he, inter_empty])
    · obtain rfl := dim_eq hN o hy
      rw [integ_eq hN o]
      unfold chartInteg
      exact setIntegral_measure_zero _
        ((chart hN).volume_coord_image_eq_zero inter_subset_right hnull)
  integ_congr ω N hN N' hN' m m' o o' A hA hAm h := by
    rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
    · rw [integ_of_inter_eq_empty ω _ (by rw [he, empty_inter]),
        integ_of_inter_eq_empty ω _ (by rw [he, empty_inter])]
    · obtain rfl := dim_eq hN o (hA hy).1
      obtain rfl := dim_eq hN' o' (hA hy).2
      rw [integ_eq hN o, integ_eq hN' o']
      have hAN : A ∩ N = A := inter_eq_left.2 fun y hy => (hA hy).1
      exact F.chartInteg_congr hN.1 hN'.1 _ _ o o' ω hA
        (hAN ▸ nullMeasurableSet_coord_image (chart hN) hAm) h
  integ_neg ω N hN N' hN' m m' o o' A hA hAm h := by
    rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
    · rw [integ_of_inter_eq_empty ω _ (by rw [he, empty_inter]),
        integ_of_inter_eq_empty ω _ (by rw [he, empty_inter]), neg_zero]
    · obtain rfl := dim_eq hN o (hA hy).1
      obtain rfl := dim_eq hN' o' (hA hy).2
      rw [integ_eq hN o, integ_eq hN' o']
      have hAN : A ∩ N = A := inter_eq_left.2 fun y hy => (hA hy).1
      exact F.chartInteg_neg hN.1 hN'.1 _ _ o o' ω hA
        (hAN ▸ nullMeasurableSet_coord_image (chart hN) hAm) h
  image_mem N hN f f' U U' hf hNU hmor := image_mem_sheets hN hf hNU hmor
  isMeasIn_image N hN _ _ _ _ hf hNU _ A hA hAm := isMeasIn_image hf hNU hA hAm
  integ_image ω N hN m o hM f f' U U' hf hNU hmor A hA hAm := by
    rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
    · rw [integ_of_inter_eq_empty ω _ (by rw [he, image_empty, empty_inter]),
        integ_of_inter_eq_empty ω _ (by rw [he, empty_inter])]
    · obtain rfl := dim_eq hN o (hA hy)
      have hfN : f '' N ∈ F.sheets := image_mem_sheets hN hf hNU hmor
      rw [integ_eq hfN (o.mapDiffeo hM hf hNU), integ_eq hN o]
      have hAN : A ∩ N = A := inter_eq_left.2 hA
      have hfA : f '' A ⊆ f '' N ∩ f '' N := fun z hz => ⟨image_mono hA hz, image_mono hA hz⟩
      have hfAN : f '' A ∩ f '' N = f '' A := inter_eq_left.2 (image_mono hA)
      have hm1 := nullMeasurableSet_coord_image (chart hfN) (isMeasIn_image hf hNU hA hAm)
      rw [hfAN] at hm1
      rw [F.chartInteg_congr hfN.1 hfN.1 (chart hfN) ((chart hN).mapDiffeo hN.1.1 hf hNU)
        (o.mapDiffeo hM hf hNU) (o.mapDiffeo hM hf hNU) ω hfA hm1 fun _ _ => rfl]
      exact F.chartInteg_mapDiffeo hN.1.1 (chart hN) o hf hNU hmor ω hA
        (hAN ▸ nullMeasurableSet_coord_image (chart hN) hAm)

@[simp] theorem sheetIntegration_integ (hn : 0 < n) : (F.sheetIntegration hn).integ = F.integ :=
  rfl

/-- **Locality**: if `ω` vanishes on the frames of `T_yN` for (almost) all `y ∈ A`, then
`∫_A ω|(N, o) = 0`. -/
theorem integ_eq_zero_of_ev_eq_zero (ω : Ω) (N : Set Obj) (g : Obj → X.PObj.OrTangent)
    {A : Set Obj} (h : ∀ y ∈ A ∩ N, ∀ α : Fin n → X.PObj.TangentSpace,
      (∀ i, α i ∈ X.PObj.submanifoldTangent N y) → F.ev ω α = 0) : F.integ ω N g A = 0 := by
  unfold integ
  split_ifs with hN
  · unfold chartInteg
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [(chart hN.1).q_coord' hy.2]
    simp only [density, h y hy _ ((chart hN.1).tvec_mem hy.2), mul_zero]
  · rfl

end FormEval

end EpGroupoid

end Polyfold
