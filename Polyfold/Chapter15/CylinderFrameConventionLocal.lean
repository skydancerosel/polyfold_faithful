import Polyfold.Chapter15.CylinderCanonicalOrientation
import Polyfold.Chapter15.CubeSectionsThrough
import Polyfold.Chapter15.CylinderFrameConventionLocalOps
import Polyfold.Chapter15.CylinderFrameConventionLocalPt
import Polyfold.Chapter15.CylinderFrameConventionLocalSlice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703: the proof
of **Corollary 15.4.4** (2017: Corollary 15.2), with **Remark 6.6.19** (p. 276).

# The frames of the kernels on the ends of the cylinder, from the local sc⁺-sections

## The text, paraphrased

(p. 703) On the cylinder `[0, 1] × X` the section `f̃(t, x) = (t, f(x))` is oriented by the
standard orientation of `[0, 1]` followed by the orientation `o` of `f` (Remark 6.6.19).  Near
`(i, x)`, `i ∈ {0, 1}`, a sheet of the cobordism is `M̃ = {f̃ = s̃}`, its boundary is `{i} × M`
with `M = {f = s̃(i, ·)}`, and `ker (f̃ − s̃)'(i, y) = ℝ·(∂_t + u) ⊕ ker (f − s̃(i, ·))'(y)` is
oriented with the `ℝ`-factor first.

## What is formalized (namespace `Polyfold.SBLocalization`)

The statements of `Polyfold/Chapter15/CylinderProductOrientation.lean` and of
`cylinderKernelFrameConvention_of_isIndexAt`, proved with the local sc⁺-sections `sᵢ`, `s̃ⱼ` of
the sheets themselves (no sc-smooth bump functions on `X`):

* **`exists_timeFirst_frame_cubeOrientation_loc`**: for local branching structures described by
  kernels `K` of `(f, Λ)` at `x` and `K̃` of `(f̃, Λ̃)` at `(q, x)`, sheets `Mᵢ = {f = sᵢ}`,
  `M̃ⱼ = {f̃ = s̃ⱼ}` with `s̃ⱼ(q, ·) = sᵢ` and `dim M̃ⱼ = dim Mᵢ + 1 ≥ 2`, and `y ∈ Mᵢ` with
  `(q, y) ∈ M̃ⱼ`: there are a frame `α` of `T_yMᵢ` positive for `o_y` and `w ∈ T_{(q, y)}M̃ⱼ`
  with `dt(w) > 0` such that `(w, Tι_q α)` is positive for `(e ∧ o)_{(q, y)}`.
* **`cylinderKernelFrameConvention_cubeOrientation_loc`**: `CylinderKernelFrameConvention` for
  `õ = e ∧ o`, when the sheets of `f` have positive dimension.
* **`cylinderKernelFrameConvention_of_isIndexAt_loc`**: the same when `f` has index `m + 1` at
  every smooth point.
* `cylinderKernelFrameConvention_of_isIndexAt_loc'`: the same with the sc⁺-sections through the
  points of the cylinder obtained from those of `X` (`hasScPlusSectionsThrough_cubeSEP`).

## Proof

The linearizations `(f − sᵢ)'(y)` and `(f̃ − s̃ⱼ)'(q, y)` are computed in a chart `φ` and in the
product chart `χ × φ`, restricted to the domains of `sᵢ` and `s̃ⱼ`
(`KernelBranching.exists_op_frames_pt`); on the vectors `(0, v)` the second is the first
(`subDeriv_ivChart_restrictInter_slice`), and the two orientations of the kernels are related
by `exists_timeFirst_wedge_of_ops_lift`.

## Reading

For a sheet of dimension `0` with the negative orientation there is no positive frame, so the
statement is made for sheets of positive dimension, as in
`exists_timeFirst_frame_cubeOrientation`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid and the product chart point are unfolded in several places
/-- **The frame convention of the canonical orientations for `õ = e ∧ o`, at a pair of sheets**
(2021 p. 703, Remark 6.6.19 and the proof of Theorem 6.7.1), from the local sc⁺-sections of the
sheets.  Let `K` be a local branching structure of `(f, Λ)` at `x` described by kernels, `K̃` one
of `(f̃, Λ̃)` at `(q, x)`, and let the sheets `Mᵢ = {f = sᵢ}` of `K` and `M̃ⱼ = {f̃ = s̃ⱼ}` of `K̃`
satisfy `s̃ⱼ(q, ·) = sᵢ`, `dim M̃ⱼ = dim Mᵢ + 1` and `dim Mᵢ ≥ 1`.  For `y ∈ Mᵢ` with
`(q, y) ∈ M̃ⱼ` there are a frame `α` of `T_yMᵢ = ker (f − sᵢ)'(y)` positive for `o_y` and a vector
`w ∈ T_{(q, y)}M̃ⱼ = ker (f̃ − s̃ⱼ)'(q, y)` with `dt(w) = 1` such that `(w, Tι_q α)` is positive
for `(e ∧ o)_{(q, y)}`. -/
theorem exists_timeFirst_frame_cubeOrientation_loc
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) (q : Fin 1 → unitInterval)
    {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x)) (i : K.ι)
    (j : K'.ι) (hd : K'.dim j = K.dim i + 1) (hpos : 0 < K.dim i)
    (hs : ∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y))
    {y : A.Obj} (hy : y ∈ K.M i) (hy' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j) :
    ∃ α ∈ K.frames hf.2 hsec o i y,
      ∃ w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y),
        0 < cylTimeComponent A q w ∧
          (fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
            Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)) ∈
            K'.frames (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
              (cubeOrientation hf hft hsec o) j (q, y) := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hf₀ : A.B.IsScFredholmSection f := hf.2
  have hfc : (ivBundle A.B).IsScFredholmSection (cubeLift (n := 1) f hf₀.isScSmooth.1) :=
    (hft.paramCube (n := 1)).toIsScFredholmSection
  have hys := K.smooth i y hy
  have hzs := K'.smooth j (q, y) hy'
  -- the charts
  obtain ⟨c, hc, hyc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧ y ∈ c.φ.source :=
    ⟨orChart A.B y, isChart_orChart y, mem_orChart y⟩
  have hb := mem_chart_corner q
  obtain ⟨q₀⟩ : Nonempty (pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)) :=
    ⟨cubeLiftEp (n := 1) f hf.1.1.1 (q, y)⟩
  have hc' : (A.cubeSEP 1).B.IsChart (ivChart (corner q) c q₀) := isChart_ivChart (corner q) hc q₀
  have hzc' : ((q, y) : (Fin 1 → unitInterval) × A.Obj) ∈ (ivChart (corner q) c q₀).φ.source :=
    mem_ivChart_source q₀ hyc hb
  have hzz := ivChart_lift_eq (corner q) _ (exists_lift_of_smooth c hyc hys).choose_spec q q₀ _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec
  -- the operators `(f − sᵢ)'(y)` and `(f̃ − s̃ⱼ)'(q, y)`
  have hLex := K.exists_op_frames_pt hf₀ hsec o hy (chartPtOf c hc hyc hys)
  obtain ⟨L, hLm, hLs, hnL, hLcoe, hLker, hLfr⟩ := hLex
  have hTex := K'.exists_op_frames_pt (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
    hsec' (cubeOrientation hf hft hsec o) hy'
    (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
      (isChart_ivChart (corner q) hc q₀) hzc' hzs)
  obtain ⟨T₁, hTm, hTs, hnT, hTcoe, hTker, hTfr⟩ := hTex
  have hne := ChartPoint.linSet_nonempty (chartPtOf c hc hyc hys) hf₀ hys hsec
  -- the orientation `e ∧ o` in the product chart
  have hor : toChartOr hfc hzs (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀) hzc'
      (cubeOrientation hf hft hsec o (q, y) hzs) =
      ivOrOf (corner q) hc hyc hys hb q₀ hf₀ hfc hne (toChartOr hf₀ hys c hc hyc (o y hys)) := by
    have h := toChartOr_ivFirstFun hf₀ hfc hsec o (q, y) hzs (corner q) hb hc hyc q₀
      (isChart_ivChart (corner q) hc q₀) hzc' hne
    exact h.trans (DFunLike.congr_fun (ChartPoint.orTransfer_self _ hfc hzs) _)
  -- `(f̃ − s̃ⱼ)'(q, y) (0, v) = (f − sᵢ)'(y) v`
  have hE : ∀ (w : ↥(chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
        (isChart_ivChart (corner q) hc q₀) hzc' hzs).T) (v : ↥(chartPtOf c hc hyc hys).T),
      (w.1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (v.1 : c.φ.model.E 0)) →
        ((T₁ w).1 : c.F 0) = ((L v).1 : c.F 0) := fun w v hwv => by
    have h1 := hTcoe w
    have h2 := hLcoe v
    have h3 := subDeriv_ivChart_restrictInter_slice hf₀.isScSmooth
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2.isScSmooth K.isOpen_O
      (K.isScPlus i) K'.isOpen_O (K'.isScPlus j) q hs (chartPtOf c hc hyc hys) (K.mem_O hy)
      (K'.mem_O hy') (corner q) hb q₀ v.1
    have h4 := congrArg₂ (fun (z' : (ivChart (corner q) c q₀).φ.model.E 1)
        (u : (Fin 1 → ℝ) × c.φ.model.E 0) =>
      subDeriv (A := A.cubeSEP 1) ((ivChart (corner q) c q₀).restrictInter K'.isOpen_O)
        (cubeLiftEp (n := 1) f hf.1.1.1) (K'.s j) z' u) hzz hwv
    exact h1.trans (h4.trans (h3.trans h2.symm))
  -- a positive frame of `ker (f − sᵢ)'(y)`
  have : FiniteDimensional ℝ ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
      ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
        ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)) :=
    Module.finite_of_finrank_pos (hnL.symm ▸ hpos)
  have : Nonempty (Fin (K.dim i)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨bA, hbA⟩ : ∃ bA : Basis (Fin (K.dim i)) ℝ
      ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)),
      bA.orientation = pullOr hnL (LinearEquiv.refl ℝ _)
        ((chartPtOf c hc hyc hys).orKer (toChartOr hf₀ hys c hc hyc (o y hys)) hLm hLs rfl) :=
    ⟨(Module.finBasisOfFinrankEq ℝ _ hnL).adjustToOrientation _,
      Basis.orientation_adjustToOrientation _ _⟩
  have hrA := (orientation_eq_pullOr_iff hnL (LinearEquiv.refl ℝ _) _ bA).1 hbA
  have hna : wedge (fun l => bA l) hnL.symm ≠ 0 :=
    wedge_equiv_ne_zero hnL (LinearEquiv.refl ℝ _) bA
  have ha : (chartPtOf c hc hyc hys).orKer (toChartOr hf₀ hys c hc hyc (o y hys)) hLm hLs rfl =
      rayOfNeZero ℝ _ hna := hrA
  -- the frame of `ker (f̃ − s̃ⱼ)'(q, y)`
  have hex := exists_timeFirst_wedge_of_ops_lift (corner q) hc hyc _
    (exists_lift_of_smooth c hyc hys).choose_spec hb q₀ hzc' _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec hzz hf₀ hfc hys hne
    (toChartOr hf₀ hys c hc hyc (o y hys)) hLm hLs hTm hTs hE rfl rfl hnL (hnT.trans hd)
    (fun l => bA l) hna ha
  obtain ⟨ν, a', hna', hν1, ha', hray'⟩ := hex
  -- tangent vectors of `Mᵢ` with chart vectors `a`
  have hαex : ∀ l, ∃ α ∈ A.X.PObj.submanifoldTangent (K.M i) y,
      chartVec (chartPtOf c hc hyc hys).c.isChart α = (bA l).1 := fun l =>
    (hLker (bA l).1).1 (bA l).2
  choose α hαT hαv using hαex
  have hαm : ∀ l, chartVec (chartPtOf c hc hyc hys).c.isChart (α l) ∈
      (LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0) := fun l =>
    mem_submodule_of_eq_of_mem (hαv l) (bA l).2
  have hαw : wedge (fun l => (⟨chartVec (chartPtOf c hc hyc hys).c.isChart (α l), hαm l⟩ :
      ↥((LinearMap.ker (L : ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ]
        ↥(chartPtOf c hc hyc hys).K)).map ((chartPtOf c hc hyc hys).T.subtypeL :
          ↥(chartPtOf c hc hyc hys).T →ₗ[ℝ] (chartPtOf c hc hyc hys).c.φ.model.E 0)))) hnL.symm =
      wedge (fun l => bA l) hnL.symm := by
    congr 1
    exact funext fun l => Subtype.ext (hαv l)
  have hαF : α ∈ K.frames hf₀ hsec o i y :=
    (hLfr α).2 ⟨hαT, hαm, by rw [hαw]; exact hna,
      ha.trans (rayOfNeZero_congr hαw.symm _ _)⟩
  -- tangent vectors of `M̃ⱼ`
  have hwex := (hTker ν.1).1 ν.2
  obtain ⟨w, hwT, hwv⟩ := hwex
  have hβb : ∀ l, (A.cubeSEP 1).X.PObj.levelVal 1 ((A.cubeSEP 1).X.PObj.tangentProj
      ((cubeFaceIncl A q).tangent.obj (α l))) = (q, y) := fun l => by
    have h := levelVal_tangentProj_tangentMap (isScSmoothMap_cubeFace A q) (α l)
    rw [(hαT l).1] at h
    exact h
  have hβv : ∀ l, chartVec (ivChart (corner q) c q₀).isChart
      ((cubeFaceIncl A q).tangent.obj (α l)) = (a' l).1 := fun l => by
    have hαb : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (α l)) ∈ c.φ.source := by
      rw [(hαT l).1]
      exact hyc
    have h := chartVec_tangentMap_prodMk (P := A.X.PObj) (P₀ := cubePolyfold 1)
      (isScSmoothMap_cubeFace A q) (isChart_chart (corner q)) hb c.isChart (α := α l) hαb
    exact h.trans ((congrArg (Prod.mk (0 : Fin 1 → ℝ)) (hαv l)).trans (ha' l).symm)
  have hβT : ∀ l, (cubeFaceIncl A q).tangent.obj (α l) ∈
      (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) := fun l => by
    have hγex := (hTker (a' l).1).1 (a' l).2
    obtain ⟨γ, hγ, hγv⟩ := hγex
    have he : γ = (cubeFaceIncl A q).tangent.obj (α l) :=
      chartVec_injOn (ivChart (corner q) c q₀).isChart hzc' hγ.1 (hβb l)
        (hγv.trans (hβv l).symm)
    rw [← he]
    exact hγ
  -- the `t`-component of `w`
  have hτ : cylTimeComponent A q w = 1 := by
    have hbase : ((cubePolyfold 1).prod A.X.PObj).levelVal 1
        (((cubePolyfold 1).prod A.X.PObj).tangentProj w) = (q, y) := hwT.1
    have h := chartVec_prod_fst (P := A.X.PObj) (isChart_chart (corner q)) c.isChart (w := w)
      (by rw [hbase]; exact ⟨hb, hyc⟩)
    have h2 : (chartVec ((isChart_chart (corner q)).prod c.isChart) w).1 =
        fun _ => ivSign (corner q) := (congrArg Prod.fst hwv).trans hν1
    change cubeTimeSign q * (chartVec (isChart_chart (corner q))
      (MPolyfold.tangentMap (isScSmoothMap_fst (cubePolyfold 1) A.X.PObj) w) : Fin 1 → ℝ) 0 = 1
    rw [← h, h2, cubeTimeSign_eq_ivSign]
    exact ivSign_mul_self (corner q)
  refine ⟨α, hαF, w, hwT, by rw [hτ]; exact one_pos, ?_⟩
  -- the frame `(w, Tι_q α)`
  have hval : ∀ m : Fin (K.dim i + 1), chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m) =
      ((Fin.cons ν a' : Fin (K.dim i + 1) → _) m).1 := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwv
    · exact hβv l
  have hTan : ∀ m : Fin (K.dim i + 1), (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
      Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m ∈
      (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwT
    · exact hβT l
  have hr₁ := (congrArg (fun o' => (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
    (isChart_ivChart (corner q) hc q₀) hzc' hzs).orKer o' hTm hTs rfl) hor).trans hray'
  have hw' := fun hm => wedge_mk_comp_finCast hd (Fin.cons ν a' : Fin (K.dim i + 1) → _)
    (fun k : Fin (K'.dim j) => chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)))
    (fun k => hval (Fin.cast hd k)) hm (hnT.trans hd).symm hnT.symm
  have hm := fun k : Fin (K'.dim j) => mem_submodule_of_eq_of_mem (hval (Fin.cast hd k))
    ((Fin.cons ν a' : Fin (K.dim i + 1) → _) (Fin.cast hd k)).2
  exact (hTfr _).2 ⟨fun k => hTan _, hm, fun h0 => hna' ((hw' hm).symm.trans h0),
    hr₁.trans (rayOfNeZero_congr (hw' hm).symm _ _)⟩

/-- **`CylinderKernelFrameConvention` holds for `õ = e ∧ o`** (2021 p. 703, Remark 6.6.19), on
every end `q`, if the sheets of the local branching structures of `f` described by kernels have
positive dimension (which holds if `f` has a positive index at every point,
`KernelBranching.dim_eq_of_isIndexAt`).  No sc-smooth bump functions on `X` are used. -/
theorem cylinderKernelFrameConvention_cubeOrientation_loc
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hdim : ∀ (Λ : A.W → ℚ≥0) (x : A.Obj) (K : KernelBranching A f Λ x) (i : K.ι), 0 < K.dim i)
    (q : Fin 1 → unitInterval) :
    CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) q :=
  fun Λ _ x K K' i j hd hs _ hy hy' =>
    exists_timeFirst_frame_cubeOrientation_loc hf hft hsec hsec' o q K K' i j hd
      (hdim Λ x K i) hs hy hy'

/-- **The frame convention of the canonical orientations holds for `õ = e ∧ o`** on every end,
when `f` has index `m + 1 ≥ 1` at every smooth point: the sheets of the local branching
structures described by kernels then have dimension `m + 1`
(`KernelBranching.dim_eq_of_isIndexAt`).  No sc-smooth bump functions on `X` are used. -/
theorem cylinderKernelFrameConvention_of_isIndexAt_loc
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) {m : ℕ}
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (q : Fin 1 → unitInterval) :
    CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) q :=
  cylinderKernelFrameConvention_cubeOrientation_loc hf hft hsec hsec' o
    (fun _ x K i => by
      have hxs : x ∈ A.X.PObj.smoothSet := K.smooth i x (K.mem_M i)
      rw [K.dim_eq_of_isIndexAt hf.2 hsec (hidx x hxs) i]
      exact Nat.succ_pos m) q

/-- `cylinderKernelFrameConvention_of_isIndexAt_loc` with the sc⁺-sections through the points of
the cylinder obtained from those of `X` (`hasScPlusSectionsThrough_cubeSEP`). -/
theorem cylinderKernelFrameConvention_of_isIndexAt_loc'
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) {m : ℕ}
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (q : Fin 1 → unitInterval) :
    CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      (hasScPlusSectionsThrough_cubeSEP hsec) (cubeOrientation hf hft hsec o) q :=
  cylinderKernelFrameConvention_of_isIndexAt_loc hf hft hsec
    (hasScPlusSectionsThrough_cubeSEP hsec) o hidx q

end SBLocalization

end Polyfold
