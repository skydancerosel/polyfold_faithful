import Polyfold.Chapter15.EmbeddedSubmanifolds
import Polyfold.Chapter15.CylinderEndLocalization
import Polyfold.Chapter11.FormEvalPullbackEquivalence
import Polyfold.Chapter9.MultiChartIntegration

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" of its proof; §9.5
(pp. 438–445) for the integrals.

# Integration over the faces `{q} × M` of the cylinder

## The text, paraphrased

Over the end `{i} × X` of `[0, 1] × X` the sheets of the cobordism `Θ̃` have the boundary faces
`{i} × M`, `M` a sheet of `Θᵢ`, and the integral of `pr^*ω` over `{i} × M` is the integral of `ω`
over `M` (up to the sign of the orientations), `pr : [0, 1] × X → X` the projection.

## What is formalized

For `ι_q : X → [0, 1]ᵏ × X`, `x ↦ (q, x)` (`cubeFaceIncl`), any `q`:

* `EP.epFormsInftyEval_pullback_of_isSubTuple`: `(F^*ω)(α) = ω(TF ∘ α)` for an sc-smooth functor
  `F` and a tuple `α` of a tangent space of a submanifold whose image is one.
* `isSubmanifoldOfDim_cubeFace`, `faceOrient`: `ι_q(N)` is an `n`-dimensional submanifold of the
  cylinder with the pushed-forward orientation (`faceOrient_frames`, `faceOrient_tangent`).
* `ev_cubeProj_pullback_face`: `(pr^*ω)(Tι_q ∘ α) = ω(α)` on the tangent spaces of submanifolds.
* `cubeFace_mem_sheets`, `cubeFace_mem_msheets`: `ι_q(N)` lies in the classes of sheets of the
  cylinder if `N` does in that of `X`; `isMeasIn_cubeFace`: measurable traces are carried along.
* **`integ_cubeFace`**: `∫_{ι_q(B)} pr^*ω|(ι_q(N), ι_q_*o) = ∫_B ω|(N, o)`.
* **`integ_cubeFace_of_tangent_eq`**, **`integ_cubeFace_of_tangent_ne`**: the same for an
  orientation of `ι_q(N)` that agrees with (is opposite to) `ι_q_*o` along `ι_q(B)`: sign `±1`.
* **`sheetSum_boundaryFamily_cubeFace`**: for an oriented tame structure `C̃` of the cylinder
  whose nonempty boundary sheets are the faces `ι_q(Mⱼ)` of the sheets of a structure `C` of `X`,
  with the same weights and orientations related by the sign `ε`, the boundary sheet sum of
  `pr^*ω` for `C̃` is `ε` times the sheet sum of `ω` for `C`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology MeasureTheory
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EP

variable {A B : EP.{u}} {n : ℕ}

/-- **`(F^*ω)(α) = ω(TF ∘ α)`** for an sc-smooth functor `F`, a class `ω ∈ Ωⁿ_{ep,∞}(Y)` and a
tuple `α` of a tangent space of a smooth finite-dimensional submanifold of `X` whose image under
`TF` is a tuple of a tangent space of a submanifold of `Y`. -/
theorem epFormsInftyEval_pullback_of_isSubTuple (F : EpFunctor A.X B.X) (ω : B.epFormsInfty n)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : MPolyfold.IsSubTuple A.X.PObj α)
    (hα' : MPolyfold.IsSubTuple B.X.PObj (fun j => F.tangent.obj (α j))) :
    (A.epFormsInftyEval n).ev (epFormsInftyPullback F n ω) α =
      (B.epFormsInftyEval n).ev ω (fun j => F.tangent.obj (α j)) := by
  obtain ⟨i, ω, rfl⟩ := B.exists_epFormsInftyOf_eq n ω
  rw [epFormsInftyPullback_of, A.epFormsInftyEval_of, B.epFormsInftyEval_of,
    A.epFormsLevelEval_ev n i _ (Or.inl hα), B.epFormsLevelEval_ev n i _ (Or.inl hα')]
  exact levelEv_epFormsPullback F i ω hα

end EP

namespace SBLocalization

open MPolyfold EpGroupoid SEP EpGroupoid.FormEval

variable {A : SEP.{u}} {k : ℕ} (q : Fin k → unitInterval)

/-- **The inclusion `ι_q : X → [0, 1]ᵏ × X`, `x ↦ (q, x)`**, as an sc-smooth functor into the
base of the cylinder `A.cubeSEP k`. -/
def cubeFaceIncl (A : SEP.{u}) {k : ℕ} (q : Fin k → unitInterval) :
    EpFunctor A.X (A.cubeSEP k).X :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PMor
  A.X.cubeIncl k q

@[simp] theorem cubeFaceIncl_obj (x : A.Obj) : (cubeFaceIncl A q).obj x = (q, x) := rfl

/-- `ι_q` as a map into the product M-polyfold `[0, 1]ᵏ × X`. -/
theorem isScSmoothMap_cubeFace (A : SEP.{u}) {k : ℕ} (q : Fin k → unitInterval) :
    haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
    A.X.PObj.IsScSmoothMap ((cubePolyfold k).prod A.X.PObj) fun x => (q, x) :=
  (cubeFaceIncl A q).isScSmoothMap_obj

/-- `T pr ∘ T ι_q = id`. -/
theorem tangent_cubeProj_cubeFaceIncl (α : A.X.PObj.TangentSpace) :
    (A.X.cubeProj k).tangent.obj ((cubeFaceIncl A q).tangent.obj α) = α :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  tangentMap_tangentMap_of_leftInverse (isScSmoothMap_cubeFace A q)
    (isScSmoothMap_snd (cubePolyfold k) A.X.PObj) (fun _ => rfl) α

variable {N : Set A.Obj} {n : ℕ}

/-- `ι_q(N)` is a smooth finite-dimensional submanifold of the cylinder. -/
theorem isSmoothSubmanifold_cubeFace (hN : A.X.PObj.IsSmoothSubmanifold N) :
    (A.cubeSEP k).X.PObj.IsSmoothSubmanifold ((cubeFaceIncl A q).obj '' N) :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  hN.image_prodMk (isScSmoothMap_cubeFace A q)

/-- **`ι_q(N)` is an `n`-dimensional submanifold of the cylinder** if `N` is one of `X`. -/
theorem isSubmanifoldOfDim_cubeFace (hN : A.X.PObj.IsSubmanifoldOfDim N n) :
    (A.cubeSEP k).X.PObj.IsSubmanifoldOfDim ((cubeFaceIncl A q).obj '' N) n :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  hN.image_prodMk (isScSmoothMap_cubeFace A q)

/-- **`T_{(q, y)} ι_q(N) = Tι_q(T_yN)`.** -/
theorem submanifoldTangent_cubeFace (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj}
    (hy : y ∈ N) :
    (A.cubeSEP k).X.PObj.submanifoldTangent ((cubeFaceIncl A q).obj '' N)
        ((cubeFaceIncl A q).obj y) =
      (cubeFaceIncl A q).tangent.obj '' A.X.PObj.submanifoldTangent N y :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  submanifoldTangent_image_prodMk (isScSmoothMap_cubeFace A q) hN hy

/-- **The orientation `ι_q_*o` of the face `ι_q(N)`**: the positive frames at `(q, y)` are the
images under `Tι_q` of the positive frames of `(N, o)` at `y`. -/
def faceOrient (o : A.X.PObj.SubmanifoldOrientation N n) (hN : A.X.PObj.IsSmoothSubmanifold N) :
    (A.cubeSEP k).X.PObj.SubmanifoldOrientation ((cubeFaceIncl A q).obj '' N) n :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  o.prodMk (isScSmoothMap_cubeFace A q) hN

theorem faceOrient_frames (o : A.X.PObj.SubmanifoldOrientation N n)
    (hN : A.X.PObj.IsSmoothSubmanifold N) (y : A.Obj) :
    (faceOrient q o hN).frames ((cubeFaceIncl A q).obj y) =
      (fun v => (cubeFaceIncl A q).tangent.obj ∘ v) '' o.frames y := rfl

/-- `T_{(q, y)}(ι_q(N), ι_q_*o) = Tι_q(T_y(N, o))`. -/
theorem faceOrient_tangent (o : A.X.PObj.SubmanifoldOrientation N n)
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N) :
    (faceOrient q o hN).tangent ((cubeFaceIncl A q).obj y) =
      (o.tangent y).map (cubeFaceIncl A q).tangent.obj := by
  change MPolyfold.OrTangent.mk n _ _ = MPolyfold.OrTangent.mk n _ _
  rw [submanifoldTangent_cubeFace q hN hy]
  rfl

/-- A frame is positive for `o` iff its image under `Tι_q` is positive for `ι_q_*o`. -/
theorem faceOrient_frames_iff (o : A.X.PObj.SubmanifoldOrientation N n)
    (hN : A.X.PObj.IsSmoothSubmanifold N) (y : A.Obj) (α : Fin n → A.X.PObj.TangentSpace) :
    (fun i => (cubeFaceIncl A q).tangent.obj (α i)) ∈
      (faceOrient q o hN).frames ((cubeFaceIncl A q).obj y) ↔ α ∈ o.frames y :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  o.prodMk_frames_iff (isScSmoothMap_cubeFace A q) hN y α

/-- The images under `Tι_q` of a tuple of `T_yN` form a tuple of `T_{(q, y)} ι_q(N)`. -/
theorem isSubTuple_cubeFace (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    MPolyfold.IsSubTuple (A.cubeSEP k).X.PObj fun i => (cubeFaceIncl A q).tangent.obj (α i) :=
  ⟨(cubeFaceIncl A q).obj '' N, (cubeFaceIncl A q).obj y, isSmoothSubmanifold_cubeFace q hN,
    ⟨y, hy, rfl⟩, fun i => by
      rw [submanifoldTangent_cubeFace q hN hy]; exact ⟨α i, hα i, rfl⟩⟩

/-- **`(pr^*ω)(Tι_q α₁, …, Tι_q αₙ) = ω(α₁, …, αₙ)`** on the tangent spaces of the smooth
finite-dimensional submanifolds of `X` (`pr ∘ ι_q = id`). -/
theorem ev_cubeProj_pullback_face (ω : A.baseEP.epFormsInfty n)
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N)
    (α : Fin n → A.X.PObj.TangentSpace) (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    ((A.cubeSEP k).baseEP.epFormsInftyEval n).ev
        (EP.epFormsInftyPullback (A := (A.cubeSEP k).baseEP) (B := A.baseEP) (A.X.cubeProj k) n ω)
        (fun i => (cubeFaceIncl A q).tangent.obj (α i)) =
      (A.baseEP.epFormsInftyEval n).ev ω α := by
  have hfun : (fun i => (A.X.cubeProj k).tangent.obj ((cubeFaceIncl A q).tangent.obj (α i))) =
      α := funext fun i => tangent_cubeProj_cubeFaceIncl q (α i)
  have h0 : MPolyfold.IsSubTuple A.X.PObj α := ⟨N, y, hN, hy, hα⟩
  exact (EP.epFormsInftyEval_pullback_of_isSubTuple (A := (A.cubeSEP k).baseEP)
    (B := A.baseEP) (A.X.cubeProj k) ω (isSubTuple_cubeFace q hN hy hα)
    ((congrArg (MPolyfold.IsSubTuple A.X.PObj) hfun).mpr h0)).trans
    (congrArg ((A.baseEP.epFormsInftyEval n).ev ω) hfun)

/-- The value of a form of the cylinder on `Tι_q ∘ α` is the value of its pull-back by `ι_q`. -/
theorem ev_cubeFaceIncl_pullback (ω : (A.cubeSEP k).baseEP.epFormsInfty n)
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N)
    (α : Fin n → A.X.PObj.TangentSpace) (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    (A.baseEP.epFormsInftyEval n).ev
        (EP.epFormsInftyPullback (A := A.baseEP) (B := (A.cubeSEP k).baseEP) (cubeFaceIncl A q) n
          ω) α =
      ((A.cubeSEP k).baseEP.epFormsInftyEval n).ev ω
        (fun i => (cubeFaceIncl A q).tangent.obj (α i)) :=
  EP.epFormsInftyEval_pullback_of_isSubTuple (A := A.baseEP) (B := (A.cubeSEP k).baseEP)
    (cubeFaceIncl A q) ω ⟨N, y, hN, hy, hα⟩ (isSubTuple_cubeFace q hN hy hα)

/-! ### The classes of sheets, measurable traces -/

/-- The graph chart of `ι_q(N)` from the chosen graph chart of a sheet `N` of the class. -/
theorem exists_graphChart_cubeFace (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) :
    ∃ c : (A.cubeSEP k).X.PObj.GraphChart n ((cubeFaceIncl A q).obj '' N),
      (∀ B : Set A.Obj, c.coord '' ((cubeFaceIncl A q).obj '' B) = (chart hN).coord '' B) ∧
      (∀ u, c.q u = (cubeFaceIncl A q).obj ((chart hN).q u)) ∧
      ∀ y ∈ N, c.tvec ((cubeFaceIncl A q).obj y) =
        fun i => (cubeFaceIncl A q).tangent.obj ((chart hN).tvec y i) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold k) A.X.PObj
  obtain ⟨χ, hχ, hqχ⟩ := (cubePolyfold k).exists_isChart_mem_source q
  exact ⟨(chart hN).prodMk (isScSmoothMap_cubeFace A q) hN.1.1 hχ hqχ,
    fun B => GraphChart.prodMk_coord_image (isScSmoothMap_cubeFace A q) (chart hN) hN.1.1 hχ hqχ B,
    fun _ => rfl, fun y hy => funext fun i =>
      GraphChart.prodMk_tvec (isScSmoothMap_cubeFace A q) (chart hN) hN.1.1 hχ hqχ hy i⟩

/-- **`ι_q(N)` is a sheet of the class of the cylinder** (one graph chart, all forms absolutely
integrable) if `N` is one of the class of `X`. -/
theorem cubeFace_mem_sheets (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) :
    (cubeFaceIncl A q).obj '' N ∈ ((A.cubeSEP k).baseEP.epFormsInftyEval n).sheets := by
  obtain ⟨c, hc, hcq, htv⟩ := exists_graphChart_cubeFace q hN
  refine ⟨isSubmanifoldOfDim_cubeFace q hN.1, c, fun ω => ?_⟩
  have hdom : c.dom = (chart hN).dom := hc N
  rw [hdom]
  refine (integrableOn_chart hN (EP.epFormsInftyPullback (A := A.baseEP)
    (B := (A.cubeSEP k).baseEP) (cubeFaceIncl A q) n ω)).congr_fun (fun u hu => ?_)
    (chart hN).measurableSet_dom'
  have hqu := (chart hN).q_mem hu
  change _ = ((A.cubeSEP k).baseEP.epFormsInftyEval n).ev ω (c.tvec (c.q u))
  rw [hcq u, htv _ hqu]
  exact ev_cubeFaceIncl_pullback q ω hN.1.1 hqu _ ((chart hN).tvec_mem hqu)

theorem cubeFace_mem_msheets (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) :
    (cubeFaceIncl A q).obj '' N ∈ ((A.cubeSEP k).baseEP.epFormsInftyEval n).msheets :=
  sheets_subset_msheets (cubeFace_mem_sheets q hN)

/-- **Measurable traces are carried along `ι_q`**: if `B` is measurable in the sheet `N`, then
`ι_q(B)` is measurable in `ι_q(N)` (the null sets of Definition 9.4.5 are those of the graph
coordinates, which `N` and `ι_q(N)` share). -/
theorem isMeasIn_cubeFace (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) {B : Set A.Obj}
    (hBm : (A.baseEP.epFormsInftyEval n).sheetNull.IsMeasIn N B) :
    ((A.cubeSEP k).baseEP.epFormsInftyEval n).sheetNull.IsMeasIn
      ((cubeFaceIncl A q).obj '' N) ((cubeFaceIncl A q).obj '' B) := by
  obtain ⟨c, hc, -, -⟩ := exists_graphChart_cubeFace q hN
  obtain ⟨B₀, hB₀, hnull⟩ := hBm
  have hZN : (B ∩ N) ∆ (B₀ ∩ N) ⊆ N := fun y hy => by
    rcases hy with hy | hy <;> exact hy.1.2
  have hZ : A.X.PObj.IsHNull n ((B ∩ N) ∆ (B₀ ∩ N)) :=
    MPolyfold.IsHNull.mono hnull fun y hy => ⟨hy, hZN hy⟩
  have h1 : (A.cubeSEP k).X.PObj.IsHNull n ((cubeFaceIncl A q).obj '' ((B ∩ N) ∆ (B₀ ∩ N))) :=
    c.isHNull_of_volume_coord_image (isSmoothSubmanifold_cubeFace q hN.1.1) (image_mono hZN)
      (by rw [hc]; exact (chart hN).volume_coord_image_eq_zero hZN hZ)
  refine ⟨Prod.snd ⁻¹' B₀, continuous_snd.borel_measurable hB₀, MPolyfold.IsHNull.mono h1 ?_⟩
  rintro z ⟨hz, -⟩
  rcases hz with ⟨⟨⟨b, hb, rfl⟩, ⟨y, hy, hyb⟩⟩, hn⟩ | ⟨⟨hb0, ⟨y, hy, rfl⟩⟩, hn⟩
  · have hyb' : y = b := congrArg Prod.snd hyb
    subst hyb'
    exact ⟨y, Or.inl ⟨⟨hb, hy⟩, fun hc' => hn ⟨hc'.1, y, hc'.2, rfl⟩⟩, rfl⟩
  · exact ⟨y, Or.inr ⟨⟨hb0, hy⟩, fun hc' => hn ⟨⟨y, hc'.1, rfl⟩, y, hy, rfl⟩⟩, rfl⟩

/-! ### The integrals -/

/-- **The change of variables along the face inclusion**: for a sheet `N` of the class of `X`
with orientation `o` and `B ⊆ N` measurable in `N`,
`∫_{ι_q(B)} pr^*ω|(ι_q(N), ι_q_*o) = ∫_B ω|(N, o)`. -/
theorem integ_cubeFace (hn : 0 < n) (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets)
    (o : A.X.PObj.SubmanifoldOrientation N n) (ω : A.baseEP.epFormsInfty n) {B : Set A.Obj}
    (hB : B ⊆ N) (hBm : (A.baseEP.epFormsInftyEval n).sheetNull.IsMeasIn N B) :
    (((A.cubeSEP k).baseEP.epFormsInftyEval n).msheetIntegration hn).integ
        (EP.epFormsInftyPullback (A := (A.cubeSEP k).baseEP) (B := A.baseEP) (A.X.cubeProj k) n ω)
        ((cubeFaceIncl A q).obj '' N) (faceOrient q o hN.1.1).tangent
        ((cubeFaceIncl A q).obj '' B) =
      ((A.baseEP.epFormsInftyEval n).sheetIntegration hn).integ ω N o.tangent B := by
  have hN' := cubeFace_mem_sheets q hN
  have hBm' := isMeasIn_cubeFace q hN hBm
  obtain ⟨c, hc, hcq, htv⟩ := exists_graphChart_cubeFace q hN
  have hBN' : (cubeFaceIncl A q).obj '' B ∩ (cubeFaceIncl A q).obj '' N =
      (cubeFaceIncl A q).obj '' B := inter_eq_left.2 (image_mono hB)
  have hBN : B ∩ N = B := inter_eq_left.2 hB
  have hm1 := nullMeasurableSet_coord_image (chart hN') hBm'
  rw [hBN'] at hm1
  have hAm := nullMeasurableSet_coord_image (chart hN) hBm
  rw [hBN] at hAm
  change ((A.cubeSEP k).baseEP.epFormsInftyEval n).msInteg _ _ _ _ =
    (A.baseEP.epFormsInftyEval n).integ _ _ _ _
  rw [msInteg_eq_integ hn hN' _ _ hBm', integ_eq hN', integ_eq hN o,
    ((A.cubeSEP k).baseEP.epFormsInftyEval n).chartInteg_congr hN'.1 hN'.1 (chart hN') c
      (faceOrient q o hN.1.1) (faceOrient q o hN.1.1) _
      (fun z hz => ⟨image_mono hB hz, image_mono hB hz⟩) hm1 fun _ _ => rfl]
  unfold chartInteg
  rw [hBN, hBN', hc]
  refine setIntegral_congr_ae₀ hAm (Filter.Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hyN := hB hy
  have hqy : (chart hN).q ((chart hN).coord y) = y := (chart hN).q_coord' hyN
  simp only [density, GraphChart.frameSgn_tangent, hcq, hqy, htv y hyN]
  rw [ev_cubeProj_pullback_face q ω hN.1.1 hyN _ ((chart hN).tvec_mem hyN)]
  have hiff := faceOrient_frames_iff q o hN.1.1 y ((chart hN).tvec y)
  rw [← htv y hyN] at hiff
  by_cases h : (chart hN).tvec y ∈ o.frames y
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-- **The integral over the face for an orientation that agrees with `ι_q_*o` along
`ι_q(B)`**: `∫_{ι_q(B)} pr^*ω|(N', o') = ∫_B ω|(N, o)` for `N' = ι_q(N)`. -/
theorem integ_cubeFace_of_tangent_eq (hn : 0 < n)
    (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) (o : A.X.PObj.SubmanifoldOrientation N n)
    (ω : A.baseEP.epFormsInfty n) {B : Set A.Obj} (hB : B ⊆ N)
    (hBm : (A.baseEP.epFormsInftyEval n).sheetNull.IsMeasIn N B) {N' : Set (A.cubeSEP k).Obj}
    (hN' : N' = (cubeFaceIncl A q).obj '' N) {m' : ℕ}
    (o' : (A.cubeSEP k).X.PObj.SubmanifoldOrientation N' m')
    (h : ∀ y ∈ B, o'.tangent ((cubeFaceIncl A q).obj y) =
      (faceOrient q o hN.1.1).tangent ((cubeFaceIncl A q).obj y)) :
    (((A.cubeSEP k).baseEP.epFormsInftyEval n).msheetIntegration hn).integ
        (EP.epFormsInftyPullback (A := (A.cubeSEP k).baseEP) (B := A.baseEP) (A.X.cubeProj k) n ω)
        N' o'.tangent ((cubeFaceIncl A q).obj '' B) =
      ((A.baseEP.epFormsInftyEval n).sheetIntegration hn).integ ω N o.tangent B := by
  subst hN'
  rw [← integ_cubeFace q hn hN o ω hB hBm]
  exact (((A.cubeSEP k).baseEP.epFormsInftyEval n).msheetIntegration hn).integ_congr _ _
    (cubeFace_mem_msheets q hN) _ (cubeFace_mem_msheets q hN) o' (faceOrient q o hN.1.1) _
    (fun z hz => ⟨image_mono hB hz, image_mono hB hz⟩) (isMeasIn_cubeFace q hN hBm) (by
      rintro _ ⟨y, hy, rfl⟩; exact h y hy)

/-- **The integral over the face for an orientation opposite to `ι_q_*o` along `ι_q(B)`**:
`∫_{ι_q(B)} pr^*ω|(N', o') = −∫_B ω|(N, o)` for `N' = ι_q(N)`. -/
theorem integ_cubeFace_of_tangent_ne (hn : 0 < n)
    (hN : N ∈ (A.baseEP.epFormsInftyEval n).sheets) (o : A.X.PObj.SubmanifoldOrientation N n)
    (ω : A.baseEP.epFormsInfty n) {B : Set A.Obj} (hB : B ⊆ N)
    (hBm : (A.baseEP.epFormsInftyEval n).sheetNull.IsMeasIn N B) {N' : Set (A.cubeSEP k).Obj}
    (hN' : N' = (cubeFaceIncl A q).obj '' N) {m' : ℕ}
    (o' : (A.cubeSEP k).X.PObj.SubmanifoldOrientation N' m')
    (h : ∀ y ∈ B, o'.tangent ((cubeFaceIncl A q).obj y) ≠
      (faceOrient q o hN.1.1).tangent ((cubeFaceIncl A q).obj y)) :
    (((A.cubeSEP k).baseEP.epFormsInftyEval n).msheetIntegration hn).integ
        (EP.epFormsInftyPullback (A := (A.cubeSEP k).baseEP) (B := A.baseEP) (A.X.cubeProj k) n ω)
        N' o'.tangent ((cubeFaceIncl A q).obj '' B) =
      -((A.baseEP.epFormsInftyEval n).sheetIntegration hn).integ ω N o.tangent B := by
  subst hN'
  rw [← integ_cubeFace q hn hN o ω hB hBm]
  exact (((A.cubeSEP k).baseEP.epFormsInftyEval n).msheetIntegration hn).integ_neg _ _
    (cubeFace_mem_msheets q hN) _ (cubeFace_mem_msheets q hN) o' (faceOrient q o hN.1.1) _
    (fun z hz => ⟨image_mono hB hz, image_mono hB hz⟩) (isMeasIn_cubeFace q hN hBm) (by
      rintro _ ⟨y, hy, rfl⟩; exact ⟨rfl, h y hy⟩)

/-! ### The boundary sheet sum of a structure of the cylinder over a face -/

/-- **The boundary sheet sum over a face of the cylinder.**  Let `C` be an oriented tame
structure of dimension `m + 1` of `X` with sheets in the class of the integration, and `C̃` one
of dimension `m + 2` of the cylinder whose nonempty boundary sheets are, through an injection
`e` of the index sets that misses only empty sheets of `C`, the faces `ι_q(M_{e j})`, with the
weights of `C`, and whose boundary orientations are `ε` times the pushed-forward orientations
(`ε = ±1`) along `ι_q(A₀)`.  If `A' ∩ ι_q(Mᵢ) = ι_q(A₀ ∩ Mᵢ)` and the traces of `A₀` are
measurable, then the boundary sheet sum of `pr^*ω` for `C̃` over `A'` is `ε` times the sheet sum
of `ω` for `C` over `A₀`. -/
theorem sheetSum_boundaryFamily_cubeFace {m : ℕ} {Θ : A.Obj → ℚ} {x : A.Obj}
    (C : A.X.OrientedTameStructure (m + 1) Θ x) {Θ' : (A.cubeSEP k).Obj → ℚ}
    {T' : (A.cubeSEP k).Obj → (A.cubeSEP k).X.PObj.OrTangent →₀ ℚ} {z : (A.cubeSEP k).Obj}
    (C' : (A.cubeSEP k).X.OrientedTameStructure (m + 1 + 1) Θ' z)
    (hΘ' : (A.cubeSEP k).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T')
    (hS : ∀ i, C.M i ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets)
    (e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι) (he : Injective e)
    (hrange : ∀ i, i ∉ range e → C.M i = ∅) (hσ : ∀ j, C'.σ j.1 = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j))
    {A₀ : Set A.Obj} {A' : Set (A.cubeSEP k).Obj}
    (hA : ∀ i, A' ∩ (cubeFaceIncl A q).obj '' C.M i = (cubeFaceIncl A q).obj '' (A₀ ∩ C.M i))
    (hAm : ∀ i, (A.baseEP.epFormsInftyEval (m + 1)).sheetNull.IsMeasIn (C.M i) (A₀ ∩ C.M i))
    {ε : ℝ}
    (hε : (ε = 1 ∧ ∀ j, ∀ y ∈ A₀ ∩ C.M (e j),
        (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y)) ∨
      (ε = -1 ∧ ∀ j, ∀ y ∈ A₀ ∩ C.M (e j),
        (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y)))
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum
        (((A.cubeSEP k).baseEP.epFormsInftyEval (m + 1)).msheetIntegration (Nat.succ_pos m))
        (EP.epFormsInftyPullback (A := (A.cubeSEP k).baseEP) (B := A.baseEP) (A.X.cubeProj k)
          (m + 1) ω) A' =
      ε * C.sheetSum ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
        A₀ := by
  unfold EpGroupoid.OrientedSheetFamily.sheetSum EpGroupoid.OrientedTameStructure.sheetSum
  rw [Finset.mul_sum]
  refine Fintype.sum_of_injective e he _ _ (fun i hi => ?_) (fun j => ?_)
  · change ε * (_ * (A.baseEP.epFormsInftyEval (m + 1)).integ _ _ _ _) = 0
    rw [integ_of_inter_eq_empty ω _ (by rw [hrange i hi, inter_empty]), mul_zero,
      mul_zero]
  · have hset : A' ∩ C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' (A₀ ∩ C.M (e j)) := by
      rw [hM j, hA]
    change (C'.σ j.1 : ℝ) * (((A.cubeSEP k).baseEP.epFormsInftyEval (m + 1)).msheetIntegration
      (Nat.succ_pos m)).integ _ (C'.boundarySheet j.1) (C'.boundaryOrient j.1).tangent
      (A' ∩ C'.boundarySheet j.1) = _
    rw [hset, hσ j]
    rcases hε with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rw [integ_cubeFace_of_tangent_eq q (Nat.succ_pos m) (hS (e j)) (C.orient (e j)) ω
        inter_subset_right (hAm (e j)) (hM j) (C'.boundaryOrient j.1) (h j), one_mul]
    · rw [integ_cubeFace_of_tangent_ne q (Nat.succ_pos m) (hS (e j)) (C.orient (e j)) ω
        inter_subset_right (hAm (e j)) (hM j) (C'.boundaryOrient j.1) (h j)]
      ring

end SBLocalization

end Polyfold
