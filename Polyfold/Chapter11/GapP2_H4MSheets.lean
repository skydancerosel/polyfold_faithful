import Polyfold.Chapter9.GapP2_E4_MultiChartInteg
import Polyfold.Chapter11.GapP2_H4Move

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, proof of Theorem 11.4.1 (pp. 543–544; 2017: Theorem 11.8, p. 396),
gap G.131, with the integration of 2021 §9.5, pp. 438–445.  Numbers and pages are the 2021
text's.

# Sheets covered by several graph charts, moved between two ep-groupoids

`GapP2_H4Move.lean` moves the one-chart sheets of the class `FS.sheets` along an
sc-diffeomorphism `f : W → W'` between open subsets of the object spaces of two ep-groupoids
`X` and `Y` (`image_mem_sheets_cross`, `integ_image_cross`).  Here the same is done for the class
`FS.msheets` of sheets covered by countably many graph charts with `∫ |ω| < ∞`
(`GapP2_E4_MultiChart.lean`) and its integral `FS.msInteg` (`GapP2_E4_MultiChartInteg.lean`):

* `isMeasIn_image_cross`, `isMeasIn_image_cross_of_inter_eq`: measurable subsets of `N` are
  carried to measurable subsets of `f(N)`;
* `EvCompatOn.inter_isOpen`: the relation `ω_T(Tf ∘ β) = ω_S(β)` passes to open pieces;
* `chartAbs_mapDiffeoCross`: `∫_{f(A)} |ω_T|` in the moved graph chart is `∫_A |ω_S|`;
* `ChartCover.imageCross`, `ChartCover.imageCross_isFinite`, **`image_mem_msheets_cross`**: the
  image of a sheet of `FS.msheets` is a sheet of `FT.msheets` if every form of `ΩT` is moved to a
  form of `ΩS` on the sheet;
* `msInteg_image_cross_of_mem_sheets` and **`msInteg_image_cross`**:
  `∫_B ω_T|(f(N), f_* o) = ∫_A ω_S|(N, o)` whenever `B ∩ f(N) = f(A ∩ N)` (the step
  (11.12) → (11.13) for sheets which do not lie in one chart); `msInteg_image_cross_of_tangent`
  for any orientation of `f(N)` with the tangent spaces of `f_* o`.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}

namespace FormEval

variable {ΩS ΩT : Type*} [AddCommGroup ΩS] [Module ℝ ΩS] [AddCommGroup ΩT] [Module ℝ ΩT]
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}
  {FS : X.FormEval n ΩS} {FT : Y.FormEval n ΩT}
  (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') {N : Set Obj}

/-! ### Sets moved by `f` -/

include hf in
theorem injOn_cross : InjOn f W := fun a ha b hb h => by
  rw [← hf.left_inv a ha, ← hf.left_inv b hb, h]

include hf in
theorem image_inter_preimage_cross (hNW : N ⊆ W) (V : Set Obj) :
    f '' N ∩ (W' ∩ g ⁻¹' V) = f '' (N ∩ V) := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, -, hV⟩
    rw [mem_preimage, hf.left_inv y (hNW hy)] at hV
    exact ⟨y, ⟨hy, hV⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hV⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, hf.mapsTo (hNW hy), ?_⟩
    rw [mem_preimage, hf.left_inv y (hNW hy)]
    exact hV

omit [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace Obj']
  [T2Space Obj'] [ParacompactSpace Obj'] in
theorem image_inter_eq_image_cross (hNW : N ⊆ W) (V' : Set Obj') :
    f '' N ∩ V' = f '' (N ∩ (W ∩ f ⁻¹' V')) := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hV⟩
    exact ⟨y, ⟨hy, hNW hy, hV⟩, rfl⟩
  · rintro ⟨y, ⟨hy, -, hV⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hV⟩

include hf in
theorem isOpen_inter_preimage_cross {V' : Set Obj'} (hV' : IsOpen V') :
    IsOpen (W ∩ f ⁻¹' V') :=
  hf.isScSmoothOn.continuousOn.isOpen_inter_preimage hf.isScSmoothOn.isOpen hV'

include hf in
/-- The trace on `W` of the preimage of a Borel set of `Y` is a Borel set of `X`. -/
theorem measurableSet_inter_preimage_cross {S : Set Obj'} (hS : MeasurableSet[borel Obj'] S) :
    MeasurableSet[borel Obj] (W ∩ f ⁻¹' S) := by
  let : MeasurableSpace Obj := borel Obj
  have : BorelSpace Obj := ⟨rfl⟩
  let : MeasurableSpace Obj' := borel Obj'
  have : BorelSpace Obj' := ⟨rfl⟩
  have hW : IsOpen W := hf.isScSmoothOn.isOpen
  have hr : Continuous (W.domRestrict f) :=
    continuousOn_iff_continuous_domRestrict.1 hf.isScSmoothOn.continuousOn
  have hm : MeasurableSet (W.domRestrict f ⁻¹' S) := hr.measurable hS
  have h := hW.measurableSet.subtype_image hm
  convert h using 1
  ext y
  constructor
  · rintro ⟨hyW, hyS⟩
    exact ⟨⟨y, hyW⟩, hyS, rfl⟩
  · rintro ⟨⟨w, hw⟩, hwS, rfl⟩
    exact ⟨hw, hwS⟩

/-! ### Measurable subsets moved by `f` -/

include hf in
/-- **A measurable subset of a sheet is carried to a measurable subset of the image sheet**:
`f(A ∩ N)` is measurable in `f(N)` if `A` is measurable in `N ⊆ W`. -/
theorem isMeasIn_image_cross (hNW : N ⊆ W) {A : Set Obj} (hA : FS.sheetNull.IsMeasIn N A) :
    FT.sheetNull.IsMeasIn (f '' N) (f '' (A ∩ N)) := by
  obtain ⟨B, hB, hnull⟩ := hA
  refine ⟨f '' (B ∩ W), MPolyfold.measurableSet_borel_image_of_isScDiffeoOn_cross hf hB, ?_⟩
  have h1 : Y.PObj.IsHNull n (f '' ((A ∩ N) ∆ (B ∩ N))) :=
    MPolyfold.IsHNull.image_of_isScDiffeoOn_cross hf
      (fun y hy => by rcases hy with hy | hy <;> exact hNW hy.1.2)
      (MPolyfold.IsHNull.mono hnull fun y hy => ⟨hy, by rcases hy with hy | hy <;> exact hy.1.2⟩)
  refine MPolyfold.IsHNull.mono h1 ?_
  have hinj := injOn_cross hf
  rintro z ⟨hz, -⟩
  rcases hz with ⟨⟨⟨a, haA, rfl⟩, -⟩, hn⟩ | ⟨⟨⟨b, ⟨hbB, hbW⟩, rfl⟩, ⟨w, hwN, hw⟩⟩, hn⟩
  · exact ⟨a, Or.inl ⟨haA, fun hc => hn ⟨⟨a, ⟨hc.1, hNW hc.2⟩, rfl⟩, a, hc.2, rfl⟩⟩, rfl⟩
  · have hwb : w = b := hinj (hNW hwN) hbW hw
    subst hwb
    exact ⟨w, Or.inr ⟨⟨hbB, hwN⟩, fun hc => hn ⟨⟨w, hc, rfl⟩, w, hwN, rfl⟩⟩, rfl⟩

include hf in
/-- `B` is measurable in `f(N)` if it meets `f(N)` in `f(A ∩ N)` with `A` measurable in `N`. -/
theorem isMeasIn_image_cross_of_inter_eq (hNW : N ⊆ W) {A : Set Obj}
    (hA : FS.sheetNull.IsMeasIn N A) {B : Set Obj'} (hB : B ∩ f '' N = f '' (A ∩ N)) :
    FT.sheetNull.IsMeasIn (f '' N) B :=
  (isMeasIn_image_cross (FT := FT) hf hNW hA).congr_inter (by
    rw [hB]; exact inter_eq_left.2 (image_mono inter_subset_right))

/-! ### Forms moved on open pieces, `|ω|` and orientations of pieces -/

/-- The relation `ω_T(Tf ∘ β) = ω_S(β)` on `N` holds on every open piece `N ∩ V`. -/
theorem EvCompatOn.inter_isOpen {ωS : ΩS} {ωT : ΩT} (h : EvCompatOn FS FT hf N ωS ωT)
    {V : Set Obj} (hV : IsOpen V) : EvCompatOn FS FT hf (N ∩ V) ωS ωT :=
  fun y hy β hβ => h y hy.1 β fun i => by
    have h' := hβ i
    rwa [MPolyfold.submanifoldTangent_inter_isOpen hV hy.2] at h'

/-- `∫_{f(A)} |ω_T|` in the moved graph chart is `∫_A |ω_S|`. -/
theorem chartAbs_mapDiffeoCross (hN : X.PObj.IsSmoothSubmanifold N) (c : X.PObj.GraphChart n N)
    (hNW : N ⊆ W) {ωS : ΩS} {ωT : ΩT} (hω : EvCompatOn FS FT hf N ωS ωT) {A : Set Obj}
    (hA : A ⊆ N) (hAm : NullMeasurableSet (c.coord '' A) volume) :
    FT.chartAbs (c.mapDiffeoCross hN hf hNW) ωT (f '' A) = FS.chartAbs c ωS A := by
  have hAN : A ∩ N = A := inter_eq_left.2 hA
  have hAN' : f '' A ∩ f '' N = f '' A := inter_eq_left.2 (image_mono hA)
  have himg : (c.mapDiffeoCross hN hf hNW).coord '' (f '' A) = c.coord '' A := by
    rw [image_image]
    exact image_congr fun y hy => c.mapDiffeoCross_coord hN hf hNW (hA hy)
  unfold chartAbs
  rw [hAN, hAN', himg]
  refine setIntegral_congr_ae₀ hAm (Filter.Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hyN := hA hy
  change |FT.ev ωT ((c.mapDiffeoCross hN hf hNW).tvec (f (c.q (c.coord y))))| =
    |FS.ev ωS (c.tvec (c.q (c.coord y)))|
  rw [c.q_coord' hyN]
  have htv : (c.mapDiffeoCross hN hf hNW).tvec (f y) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (c.tvec y i) :=
    funext fun i => c.mapDiffeoCross_tvec hN hf hNW hyN i
  rw [htv, hω y hyN (c.tvec y) (c.tvec_mem hyN)]

/-- The moved orientation of an open piece has, on the image of the piece, the oriented tangent
spaces of the moved orientation. -/
theorem mapDiffeo_restrict_tangent_cross (hN : X.PObj.IsSmoothSubmanifold N)
    (o : X.PObj.SubmanifoldOrientation N n) (hNW : N ⊆ W) {V : Set Obj} (hV : IsOpen V)
    (hNV : X.PObj.IsSmoothSubmanifold (N ∩ V)) (hNVW : N ∩ V ⊆ W) {y : Obj} (hy : y ∈ N ∩ V) :
    ((o.restrict hV).mapDiffeo hNV hf hNVW).tangent (f y) =
      (o.mapDiffeo hN hf hNW).tangent (f y) := by
  rw [MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent _ _ hf _ hy,
    MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent _ _ hf _ hy.1,
    MPolyfold.SubmanifoldOrientation.restrict_tangent _ hV hy.2]

/-! ### The image chart cover -/

namespace ChartCover

variable (D : FS.ChartCover N) (hNW : N ⊆ W)
  (hcomp : ∀ ωT : ΩT, ∃ ωS : ΩS, EvCompatOn FS FT hf N ωS ωT)

/-- **The image cover** of `f(N)`: the open sets `W' ∩ g⁻¹(V k)`, meeting `f(N)` in the sheets
`f(N ∩ V k)` of the class `FT.sheets`. -/
def imageCross : FT.ChartCover (f '' N) where
  V k := W' ∩ g ⁻¹' D.V k
  isOpen k := hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
    (D.isOpen k)
  cover := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover hy)
    refine mem_iUnion.2 ⟨k, hf.mapsTo (hNW hy), ?_⟩
    rw [mem_preimage, hf.left_inv y (hNW hy)]
    exact hk
  mem k := (image_inter_preimage_cross hf hNW (D.V k)).symm ▸
    image_mem_sheets_cross hf (D.mem k) (inter_subset_left.trans hNW) fun ωT =>
      (hcomp ωT).imp fun _ h => h.inter_isOpen hf (D.isOpen k)

theorem imageCross_P (k : ℕ) : (imageCross hf D hNW hcomp).P k = f '' D.P k := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨-, hk⟩, hj⟩
    have hl := hf.left_inv y (hNW hy)
    rw [mem_preimage, hl] at hk
    refine ⟨y, ⟨hy, hk, fun j hjk hjV => hj j hjk ⟨hf.mapsTo (hNW hy), ?_⟩⟩, rfl⟩
    rw [mem_preimage, hl]; exact hjV
  · rintro ⟨y, ⟨hy, hk, hj⟩, rfl⟩
    have hl := hf.left_inv y (hNW hy)
    refine ⟨⟨y, hy, rfl⟩, ⟨hf.mapsTo (hNW hy), by rw [mem_preimage, hl]; exact hk⟩,
      fun j hjk hjV => hj j hjk ?_⟩
    have := hjV.2
    rwa [mem_preimage, hl] at this

theorem imageCross_isFinite (hD : D.IsFinite) : (imageCross hf D hNW hcomp).IsFinite :=
  fun ωT => by
  obtain ⟨ωS, hω⟩ := hcomp ωT
  refine (hD ωS).congr fun k => ?_
  have hk := D.mem k
  have hsub : N ∩ D.V k ⊆ W := inter_subset_left.trans hNW
  have e := image_inter_preimage_cross hf hNW (D.V k)
  have hωk := hω.inter_isOpen hf (D.isOpen k)
  have hcompk : ∀ ωT : ΩT, ∃ ωS : ΩS, EvCompatOn FS FT hf (N ∩ D.V k) ωS ωT := fun ωT =>
    (hcomp ωT).imp fun _ h => h.inter_isOpen hf (D.isOpen k)
  set c := (chart hk).mapDiffeoCross hk.1.1 hf hsub
  have hPk : D.P k ⊆ N ∩ D.V k := D.P_subset k
  have hPm : FS.sheetNull.IsMeasIn (N ∩ D.V k) (D.P k) :=
    SheetNullSets.isMeasIn_of_borel (D.measurableSet_W k) |>.congr_inter (by
      ext y; simp only [P, mem_inter_iff]; constructor
      · rintro ⟨hW, hy, hV⟩; exact ⟨⟨hy, hW⟩, hy, hV⟩
      · rintro ⟨⟨hy, hW⟩, -, hV⟩; exact ⟨hW, hy, hV⟩)
  have hfPm : FT.sheetNull.IsMeasIn (f '' N ∩ (W' ∩ g ⁻¹' D.V k)) (f '' D.P k) := by
    rw [e]
    have h := isMeasIn_image_cross (FT := FT) hf hsub hPm
    rwa [inter_eq_left.2 hPk] at h
  have hfP : f '' D.P k ⊆ (f '' N ∩ (W' ∩ g ⁻¹' D.V k)) ∩ f '' (N ∩ D.V k) := fun z hz =>
    ⟨by rw [e]; exact image_mono hPk hz, image_mono hPk hz⟩
  have h1 := chartAbs_eq_of_mem ((imageCross hf D hNW hcomp).mem k)
    (image_mem_sheets_cross hf hk hsub hcompk) (chart ((imageCross hf D hNW hcomp).mem k))
    c ωT hfP hfPm fun y _ => by
      change Y.PObj.submanifoldTangent (f '' N ∩ (W' ∩ g ⁻¹' D.V k)) y = _
      rw [e]
  have hnm : NullMeasurableSet ((chart hk).coord '' D.P k) volume := by
    have h := nullMeasurableSet_coord_image (chart hk) hPm
    rwa [inter_eq_left.2 hPk] at h
  rw [imageCross_P, h1]
  exact (chartAbs_mapDiffeoCross hf hk.1.1 (chart hk) hsub hωk hPk hnm).symm

end ChartCover

/-- **The image of a sheet of the class `FS.msheets` is a sheet of the class `FT.msheets`**, if
every form of `ΩT` is moved to a form of `ΩS` on the sheet (2021 §9.5, pp. 438–445, and the
proof of Theorem 11.4.1, pp. 543–544). -/
theorem image_mem_msheets_cross (hN : N ∈ FS.msheets) (hNW : N ⊆ W)
    (hcomp : ∀ ωT : ΩT, ∃ ωS : ΩS, EvCompatOn FS FT hf N ωS ωT) : f '' N ∈ FT.msheets := by
  obtain ⟨D, hD⟩ := hN.2
  exact ⟨hN.1.image_isScDiffeoOn hf hNW, ChartCover.imageCross hf D hNW hcomp,
    ChartCover.imageCross_isFinite hf D hNW hcomp hD⟩

/-! ### The integrals -/

/-- `∫_{B ∩ M} ω|(M, o) = ∫_B ω|(M, o)` for a sheet of the class `FT.msheets`. -/
theorem msInteg_inter_sheet (hn : 0 < n) {M : Set Obj'} (hM : M ∈ FT.msheets)
    (o : Y.PObj.SubmanifoldOrientation M n) (ω : ΩT) {B : Set Obj'}
    (hB : FT.sheetNull.IsMeasIn M B) :
    FT.msInteg ω M o.tangent (B ∩ M) = FT.msInteg ω M o.tangent B := by
  obtain ⟨D, hD⟩ := hM.2
  rw [msInteg_eq hn hM D hD o ω hB, msInteg_eq hn hM D hD o ω
    (SheetNullSets.isMeasIn_inter_iff.2 hB), ChartCover.gInteg_inter]

/-- **(11.12) = (11.13) for a one-chart sheet with a several-chart image**:
`∫_{f(C)} ω_T|(f(M), f_* o) = ∫_C ω_S|(M, o)` for `M ∈ FS.sheets`, `f(M) ∈ FT.msheets` and
`C ⊆ M` measurable. -/
theorem msInteg_image_cross_of_mem_sheets (hn : 0 < n) {M : Set Obj} (hM : M ∈ FS.sheets)
    (hfM : f '' M ∈ FT.msheets) (hMW : M ⊆ W) (o : X.PObj.SubmanifoldOrientation M n)
    {ωS : ΩS} {ωT : ΩT} (hω : EvCompatOn FS FT hf M ωS ωT) {C : Set Obj} (hCM : C ⊆ M)
    (hC : FS.sheetNull.IsMeasIn M C) :
    FT.msInteg ωT (f '' M) (o.mapDiffeo hM.1.1 hf hMW).tangent (f '' C) =
      FS.integ ωS M o.tangent C := by
  obtain ⟨D', hD'⟩ := hfM.2
  set τ := o.mapDiffeo hM.1.1 hf hMW with hτ
  have hfCm : FT.sheetNull.IsMeasIn (f '' M) (f '' C) := by
    have h := isMeasIn_image_cross (FT := FT) hf hMW hC
    rwa [inter_eq_left.2 hCM] at h
  rw [msInteg_eq hn hfM D' hD' τ ωT hfCm]
  set Q : ℕ → Set Obj := fun l => W ∩ f ⁻¹' D'.W l with hQdef
  have hQ : ∀ l, MeasurableSet[borel Obj] (Q l) := fun l =>
    measurableSet_inter_preimage_cross hf (D'.measurableSet_W l)
  have hQd : Pairwise (Function.onFun Disjoint Q) := fun i j hij => by
    refine disjoint_left.2 fun y hi hj => ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact hj.2.2 i h hi.2.1
    · exact hi.2.2 j h hj.2.1
  have hcov : C ⊆ ⋃ l, Q l := fun y hy => by
    obtain ⟨l, hl⟩ := D'.exists_mem_P (mem_image_of_mem f (hCM hy))
    exact mem_iUnion.2 ⟨l, hMW (hCM hy), hl.2⟩
  have hsum := ChartCover.hasSum_integ_split hn hM o ωS hCM hC Q hQ hQd hcov
  rw [← hsum.tsum_eq]
  unfold ChartCover.gInteg
  refine tsum_congr fun l => ?_
  have hO : IsOpen (W ∩ f ⁻¹' D'.V l) := isOpen_inter_preimage_cross hf (D'.isOpen l)
  have hMl : M ∩ (W ∩ f ⁻¹' D'.V l) ∈ FS.sheets := inter_mem_sheets hM hO
  have hMlW : M ∩ (W ∩ f ⁻¹' D'.V l) ⊆ W := fun y hy => hy.2.1
  have e1 : f '' M ∩ D'.V l = f '' (M ∩ (W ∩ f ⁻¹' D'.V l)) :=
    image_inter_eq_image_cross hMW (D'.V l)
  have hfMl : f '' (M ∩ (W ∩ f ⁻¹' D'.V l)) ∈ FT.sheets := e1 ▸ D'.mem l
  have e2 : f '' C ∩ D'.P l = f '' (C ∩ Q l) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, -, hW⟩
      exact ⟨y, ⟨hy, hMW (hCM hy), hW⟩, rfl⟩
    · rintro ⟨y, ⟨hy, -, hW⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, ⟨y, hCM hy, rfl⟩, hW⟩
  have hClMl : C ∩ Q l ⊆ M ∩ (W ∩ f ⁻¹' D'.V l) := fun y hy =>
    ⟨hCM hy.1, hy.2.1, hy.2.2.1⟩
  have hClm : FS.sheetNull.IsMeasIn (M ∩ (W ∩ f ⁻¹' D'.V l)) (C ∩ Q l) :=
    isMeasIn_of_superset inter_subset_left
      (@MeasurableSet.inter Obj (FS.sheetNull.sheetSigma M) _ _ hC
        (SheetNullSets.isMeasIn_of_borel (hQ l)))
  have hfClm : FT.sheetNull.IsMeasIn (f '' M ∩ D'.V l) (f '' (C ∩ Q l)) := by
    rw [e1]
    have h := isMeasIn_image_cross (FT := FT) hf hMlW hClm
    rwa [inter_eq_left.2 hClMl] at h
  have hB : f '' (C ∩ Q l) ∩ f '' (M ∩ (W ∩ f ⁻¹' D'.V l)) =
      f '' ((C ∩ Q l) ∩ (M ∩ (W ∩ f ⁻¹' D'.V l))) := by
    rw [inter_eq_left.2 hClMl]; exact inter_eq_left.2 (image_mono hClMl)
  have key := integ_image_cross hf hMl hfMl hMlW (o.restrict hO) (hω.inter_isOpen hf hO) hClm hB
  unfold ChartCover.term
  rw [e2]
  have ha : FT.integ ωT (f '' M ∩ D'.V l) (τ.restrict (D'.isOpen l)).tangent (f '' (C ∩ Q l)) =
      FT.integ ωT (f '' (M ∩ (W ∩ f ⁻¹' D'.V l)))
        ((o.restrict hO).mapDiffeo hMl.1.1 hf hMlW).tangent (f '' (C ∩ Q l)) :=
    (FT.sheetIntegration hn).integ_congr ωT _ (D'.mem l) _ hfMl _ _ _
      (fun z hz => ⟨by rw [e1]; exact image_mono hClMl hz, image_mono hClMl hz⟩) hfClm
      (by
        rintro _ ⟨y, hy, rfl⟩
        rw [MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hy.2.2.1]
        exact (mapDiffeo_restrict_tangent_cross hf hM.1.1 o hMW hO _ _ (hClMl hy)).symm)
  have hc : FS.integ ωS (M ∩ (W ∩ f ⁻¹' D'.V l)) (o.restrict hO).tangent (C ∩ Q l) =
      FS.integ ωS M o.tangent (C ∩ Q l) :=
    (FS.sheetIntegration hn).integ_congr ωS _ hMl _ hM _ _ _
      (fun y hy => ⟨hClMl hy, hCM hy.1⟩) hClm
      (fun y hy => MPolyfold.SubmanifoldOrientation.restrict_tangent _ hO (hClMl hy).2)
  exact ha.trans (key.trans hc)

/-- **(11.12) = (11.13) for sheets covered by several graph charts** (2021 §9.5, pp. 438–445,
and the proof of Theorem 11.4.1, pp. 543–544): for `N ∈ FS.msheets`, `f(N) ∈ FT.msheets`,
`ω_T` moved to `ω_S` on `N`, `A` measurable in `N` and `B ∩ f(N) = f(A ∩ N)`,
`∫_B ω_T|(f(N), f_* o) = ∫_A ω_S|(N, o)`. -/
theorem msInteg_image_cross (hn : 0 < n) (hN : N ∈ FS.msheets) (hfN : f '' N ∈ FT.msheets)
    (hNW : N ⊆ W) (o : X.PObj.SubmanifoldOrientation N n) {ωS : ΩS} {ωT : ΩT}
    (hω : EvCompatOn FS FT hf N ωS ωT) {A : Set Obj} (hA : FS.sheetNull.IsMeasIn N A)
    {B : Set Obj'} (hB : B ∩ f '' N = f '' (A ∩ N)) :
    FT.msInteg ωT (f '' N) (o.mapDiffeo hN.1.1 hf hNW).tangent B =
      FS.msInteg ωS N o.tangent A := by
  obtain ⟨D, hD⟩ := hN.2
  set τ := o.mapDiffeo hN.1.1 hf hNW with hτ
  have hNb := hN.1.1.measurableSet_borel
  have hBm : FT.sheetNull.IsMeasIn (f '' N) B := isMeasIn_image_cross_of_inter_eq hf hNW hA hB
  rw [← msInteg_inter_sheet hn hfN τ ωT hBm, hB, msInteg_eq hn hN D hD o ωS hA]
  have hAN : A ∩ N = ⋃ k, A ∩ D.P k := by rw [← inter_iUnion, D.iUnion_P]
  rw [hAN, image_iUnion]
  have hinj := injOn_cross hf
  have hCk : ∀ k, A ∩ D.P k ⊆ N ∩ D.V k := fun k y hy => D.P_subset k hy.2
  have hCm : ∀ k, FS.sheetNull.IsMeasIn (N ∩ D.V k) (A ∩ D.P k) := fun k => by
    have h := D.isMeasIn_piece hNb hA k (Q := univ) MeasurableSet.univ
    rwa [inter_univ] at h
  have hfCm : ∀ k, FT.sheetNull.IsMeasIn (f '' N) (f '' (A ∩ D.P k)) := fun k => by
    have h := isMeasIn_image_cross (FT := FT) hf hNW (A := A ∩ D.P k)
      (@MeasurableSet.inter Obj (FS.sheetNull.sheetSigma N) _ _ hA
        (SheetNullSets.isMeasIn_of_borel (D.measurableSet_P hNb k)))
    rwa [inter_eq_left.2 fun y hy => (hCk k hy).1] at h
  have hd : Pairwise (Function.onFun Disjoint fun k => f '' (A ∩ D.P k)) := fun i j hij => by
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := hinj (hNW (hCk j hb).1) (hNW (hCk i ha).1) hab
    rw [hba] at hb
    exact disjoint_left.1 (D.disjoint_P hij) ha.2 hb.2
  have hsum := msInteg_hasSum hn ωT hfN τ (fun k => f '' (A ∩ D.P k))
    (fun k => image_mono fun y hy => (hCk k hy).1) hfCm hd
  rw [← hsum.tsum_eq]
  unfold ChartCover.gInteg
  refine tsum_congr fun k => ?_
  have hMk := D.mem k
  have hMkW : N ∩ D.V k ⊆ W := inter_subset_left.trans hNW
  have hO : IsOpen (W' ∩ g ⁻¹' D.V k) :=
    hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
      (D.isOpen k)
  have hfMk : f '' (N ∩ D.V k) ∈ FT.msheets :=
    image_inter_preimage_cross hf hNW (D.V k) ▸ msheets_inter_isOpen hfN hO
  have ha : FT.msInteg ωT (f '' N) τ.tangent (f '' (A ∩ D.P k)) =
      FT.msInteg ωT (f '' (N ∩ D.V k))
        ((o.restrict (D.isOpen k)).mapDiffeo hMk.1.1 hf hMkW).tangent (f '' (A ∩ D.P k)) :=
    (FT.msheetIntegration hn).integ_congr ωT _ hfN _ hfMk _ _ _
      (fun z hz => ⟨image_mono (fun y hy => (hCk k hy).1) hz, image_mono (hCk k) hz⟩) (hfCm k)
      (by
        rintro _ ⟨y, hy, rfl⟩
        exact (mapDiffeo_restrict_tangent_cross hf hN.1.1 o hNW (D.isOpen k) _ _
          (hCk k hy)).symm)
  exact ha.trans (msInteg_image_cross_of_mem_sheets hf hn hMk hfMk hMkW
    (o.restrict (D.isOpen k)) (hω.inter_isOpen hf (D.isOpen k)) (hCk k) (hCm k))

/-- `msInteg_image_cross` for any orientation `o'` of `f(N)` with the oriented tangent spaces of
`f_* o` on `f(N)`. -/
theorem msInteg_image_cross_of_tangent (hn : 0 < n) (hN : N ∈ FS.msheets)
    (hfN : f '' N ∈ FT.msheets) (hNW : N ⊆ W) (o : X.PObj.SubmanifoldOrientation N n)
    (o' : Y.PObj.SubmanifoldOrientation (f '' N) n)
    (ht : ∀ z ∈ f '' N, o'.tangent z = (o.mapDiffeo hN.1.1 hf hNW).tangent z) {ωS : ΩS}
    {ωT : ΩT} (hω : EvCompatOn FS FT hf N ωS ωT) {A : Set Obj}
    (hA : FS.sheetNull.IsMeasIn N A) {B : Set Obj'} (hB : B ∩ f '' N = f '' (A ∩ N)) :
    FT.msInteg ωT (f '' N) o'.tangent B = FS.msInteg ωS N o.tangent A := by
  have hBm : FT.sheetNull.IsMeasIn (f '' N) B := isMeasIn_image_cross_of_inter_eq hf hNW hA hB
  have h := (FT.msheetIntegration hn).integ_congr ωT _ hfN _ hfN o'
    (o.mapDiffeo hN.1.1 hf hNW) (B ∩ f '' N) (fun z hz => ⟨hz.2, hz.2⟩)
    (SheetNullSets.isMeasIn_inter_iff.2 hBm) fun z hz => ht z hz.2
  have h' : FT.msInteg ωT (f '' N) o'.tangent (B ∩ f '' N) =
      FT.msInteg ωT (f '' N) (o.mapDiffeo hN.1.1 hf hNW).tangent (B ∩ f '' N) := h
  rw [← msInteg_inter_sheet hn hfN o' ωT hBm, h', msInteg_inter_sheet hn hfN _ ωT hBm]
  exact msInteg_image_cross hf hn hN hfN hNW o hω hA hB

end FormEval

end EpGroupoid

end Polyfold
