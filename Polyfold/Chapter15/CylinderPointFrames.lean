import Polyfold.Chapter15.CylinderProductOrientation
import Polyfold.Chapter6.IntervalSliceSignedFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for the orientation `õ = e ∧ o` of `f̃` on
`[0, 1] × X`, with Remark 6.6.19 (p. 276) and the proof of Theorem 6.7.1 (p. 278).

# Signed frames of the kernels on the cylinder

## The text, paraphrased

On `[0, 1] × X` the section `f̃` is oriented by "`[0, 1]` first, then `o`".  Near `(q, y)` a sheet
of the cobordism is `M̃ = {f̃ = s̃}`, with `T_{(q, y)}M̃ = ker (f̃ − s̃)'(q, y) = ℝ·ν ⊕ T_yM`,
`M = {f = s̃(q, ·)}`, `dt(ν) = 1`.  If the Fredholm index is `0`, `M` is a point with a sign and
`M̃` a curve, oriented by `ν` at a positive point and by `−ν` at a negative one.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_signed_frame_cubeOrientation`**: for local branching structures described by
  kernels `K` of `(f, Λ)` at `x` and `K̃` of `(f̃, Λ̃)` at `(q, x)` and sheets `Mᵢ`, `M̃ⱼ` with
  `s̃ⱼ(q, ·) = sᵢ`, `dim M̃ⱼ = dim Mᵢ + 1` (any dimension, `0` included): at `y ∈ Mᵢ` with
  `(q, y) ∈ M̃ⱼ` there are a basis `α` of `T_yMᵢ` and `w ∈ T_{(q, y)}M̃ⱼ` such that `(w, Tι_q α)`
  is positive for `(e ∧ o)_{(q, y)}`, with `dt(w) = 1` if `α` is positive for `o_y` and
  `dt(w) = −1` if not.
* **`exists_signed_generator_cubeOrientation`**: the case `dim Mᵢ = 0`: the tangent line of
  the curve `M̃ⱼ` at `(q, y)` has a positive generator `w` with `dt(w) = 1` if the point `y` is
  positive (`o_{i,y}` has a frame), and with `dt(w) = −1` if not.
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
/-- **Signed frames of the kernels for `õ = e ∧ o`, at a pair of sheets** (2021 p. 703, Remark
6.6.19 and the proof of Theorem 6.7.1).  Let `X` have sc-smooth bump functions, `K` be a local
branching structure of `(f, Λ)` at `x` described by kernels, `K̃` one of `(f̃, Λ̃)` at `(q, x)`,
and let the sheets `Mᵢ = {f = sᵢ}` of `K` and `M̃ⱼ = {f̃ = s̃ⱼ}` of `K̃` satisfy
`s̃ⱼ(q, ·) = sᵢ` and `dim M̃ⱼ = dim Mᵢ + 1`.  For `y ∈ Mᵢ` with `(q, y) ∈ M̃ⱼ` there are a
basis `α` of `T_yMᵢ = ker (f − sᵢ)'(y)`, a sign `s = ±1` and a vector
`w ∈ T_{(q, y)}M̃ⱼ = ker (f̃ − s̃ⱼ)'(q, y)` with `dt(w) = s` such that `(w, Tι_q α)` is positive
for `(e ∧ o)_{(q, y)}`, where `s = 1` if `α` is positive for `o_y` and `s = −1` if not. -/
theorem exists_signed_frame_cubeOrientation (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) (q : Fin 1 → unitInterval)
    {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x)) (i : K.ι)
    (j : K'.ι) (hd : K'.dim j = K.dim i + 1)
    (hs : ∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y))
    {y : A.Obj} (hy : y ∈ K.M i) (hy' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j) :
    ∃ α : Fin (K.dim i) → A.X.PObj.TangentSpace,
      (∀ l, α l ∈ A.X.PObj.submanifoldTangent (K.M i) y) ∧
      ∃ (s : ℝ) (w : (A.cubeSEP 1).X.PObj.TangentSpace),
        ((s = 1 ∧ α ∈ K.frames hf.2 hsec o i y) ∨ (s = -1 ∧ α ∉ K.frames hf.2 hsec o i y)) ∧
        w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) ∧
        cylTimeComponent A q w = s ∧
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
  have hbump' : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  -- the global sc⁺-sections `Ŝ` and `ŝ = Ŝ(q, ·)`
  obtain ⟨Ŝ, hŜ, N₁', hN₁', hzN₁', hN₁'O, heq'⟩ :=
    exists_isScPlusSection_eqOn_nhds (A := A.cubeSEP 1) hbump' K'.isOpen_O
      (K'.isScPlus j).extendZero (isSection_extendZero K'.O (K'.s j)) (K'.mem_O hy')
  have heqS : EqOn Ŝ (K'.s j) N₁' := fun z hz =>
    (heq' hz).trans (extendZero_eqOn (K'.isScPlus j).1 (hN₁'O hz)).symm
  have hŜ' : (A.B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold 1)
      A.X.PObj)).IsScPlusSection Ŝ := hŜ
  obtain ⟨ŝ, hŝdef⟩ : ∃ ŝ : A.Obj → A.W, ŝ = prodSlice Ŝ q := ⟨_, rfl⟩
  have hŝ : A.B.IsScPlusSection ŝ := hŝdef ▸ hŜ'.cubeSlice q
  obtain ⟨N₁, hN₁def⟩ : ∃ N₁ : Set A.Obj,
      N₁ = {y' | ((q, y') : (A.cubeSEP 1).Obj) ∈ N₁'} ∩ K.O := ⟨_, rfl⟩
  have hN₁ : IsOpen N₁ := by
    rw [hN₁def]
    exact (hN₁'.preimage (continuous_const.prodMk continuous_id)).inter K.isOpen_O
  have hN₁O : N₁ ⊆ K.O := by rw [hN₁def]; exact inter_subset_right
  have hyN₁ : y ∈ N₁ := by rw [hN₁def]; exact ⟨hzN₁', K.mem_O hy⟩
  have heq : EqOn ŝ (K.s i) N₁ := fun y₁ hy₁ => by
    rw [hN₁def] at hy₁
    have h1 := congrArg (fun w : (A.cubeSEP 1).W => (cubeVal w).2) (heqS hy₁.1)
    have h2 := congrArg Prod.snd (hs y₁ hy₁.2 (hN₁'O hy₁.1))
    rw [hŝdef]
    exact h1.trans h2
  -- the charts
  obtain ⟨c, hc, hyc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧ y ∈ c.φ.source :=
    ⟨orChart A.B y, isChart_orChart y, mem_orChart y⟩
  have hb := mem_chart_corner q
  obtain ⟨q₀⟩ : Nonempty (pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)) :=
    ⟨cubeLiftEp (n := 1) f hf.1.1.1 (q, y)⟩
  have hc' : (A.cubeSEP 1).B.IsChart (ivChart (corner q) c q₀) := isChart_ivChart (corner q) hc q₀
  have hzc' : ((q, y) : (Fin 1 → unitInterval) × A.Obj) ∈ (ivChart (corner q) c q₀).φ.source :=
    mem_ivChart_source q₀ hyc hb
  obtain ⟨hx0, hgL, hnk, hA, hiff⟩ := K.mem_frames_iff_tangentOr hf₀ hsec o hŝ hN₁O heq hN₁ hy
    hyN₁ hc hyc
  obtain ⟨hz0, hGL, hnk', hA', hiff'⟩ := K'.mem_frames_iff_tangentOr
    (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
    (cubeOrientation hf hft hsec o) hŜ hN₁'O heqS hN₁' hy' hzN₁' hc' hzc'
  have hmin := isScPlusSection_minusSection hŝ
  have hmin' := isScPlusSection_minusSection hŜ
  have hg : A.B.IsScFredholmSection (Polyfold.sectionAdd A.P f (minusSection ŝ)) :=
    theorem_3_1_18_preprint hf₀ hmin
  have hG := theorem_3_1_18_preprint (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
    hmin'
  have hslice : prodSlice (P := A.P) (T := Fin 1 → unitInterval)
      (Polyfold.sectionAdd (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1) (minusSection Ŝ) :
        (A.cubeSEP 1).Obj → (A.cubeSEP 1).W) q =
      Polyfold.sectionAdd A.P f (minusSection ŝ) := by
    have hŜs : IsSection (pullbackProj A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)) Ŝ :=
      hŜ.1
    have h1 := prodSlice_sectionAdd_cubeLift (n := 1) (P := A.P) hf₀.isScSmooth.1
      (hŜs.sectionSmul (f := fun _ => (-1 : ℝ))) q
    rw [hŝdef]
    refine Eq.trans ?_ (h1.trans
      (congrArg (Polyfold.sectionAdd A.P f) (prodSlice_sectionSmul_const hŜs (-1) q)))
    rfl
  have hne := ChartPoint.linSet_nonempty (chartPtOf c hc hyc hys) hf₀ hys hsec
  -- the orientation `e ∧ o` in the product chart
  have hor : toChartOr hfc hzs (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀) hzc'
      (cubeOrientation hf hft hsec o (q, y) hzs) =
      ivOrOf (corner q) hc hyc hys hb q₀ hf₀ hfc hne (toChartOr hf₀ hys c hc hyc (o y hys)) := by
    have h := toChartOr_ivFirstFun hf₀ hfc hsec o (q, y) hzs (corner q) hb hc hyc q₀
      (isChart_ivChart (corner q) hc q₀) hzc' hne
    exact h.trans (DFunLike.congr_fun (ChartPoint.orTransfer_self _ hfc hzs) _)
  -- a basis of `ker (f − ŝ)'(y)`
  have hmemL := (chartPtOf c hc hyc hys).linZero_mem_linSet_of_sectionAdd hf₀ hmin hx0
  have : FiniteDimensional ℝ ((chartPtOf c hc hyc hys).c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z) := by
    have := ((chartPtOf c hc hyc hys).isFredholm_of_mem_linSet hf₀ _ hmemL).finite_ker
    exact (kerEquivOfMap ((chartPtOf c hc hyc hys).linZero hg hx0)
      (chartPtOf c hc hyc hys).T.subtypeL Subtype.val_injective
      ((chartPtOf c hc hyc hys).map_ker_linZero hg hx0)).finiteDimensional
  have hr₀ := (chartPtOf c hc hyc hys).tangentOr_orSectionAdd hf₀ hmin hx0 hgL
    (toChartOr hf₀ hys c hc hyc (o y hys))
  obtain ⟨bA⟩ : Nonempty (Basis (Fin (K.dim i)) ℝ ((chartPtOf c hc hyc hys).c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z)) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ hnk⟩
  have hna : wedge (fun l => bA l) hnk.symm ≠ 0 := wedge_basis_ne_zero' bA hnk.symm
  -- the two generators of the complement in `ker (f̃ − Ŝ)'(q, y)`
  obtain ⟨ν, ν', a', hna', hna'', hν1, hν1', ha', hpos, hneg⟩ :=
    exists_timeFirst_wedge_signed_ivOrLift (corner q) hc hyc _
    (exists_lift_of_smooth c hyc hys).choose_spec hb q₀ hzc' _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec
    (ivChart_lift_eq (corner q) _ (exists_lift_of_smooth c hyc hys).choose_spec q q₀ _
      (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec) hf₀ hfc hys hne
    (toChartOr hf₀ hys c hc hyc (o y hys)) hG hslice hg hz0 hx0 hgL hGL hmemL
    ((chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀)
      hzc' hzs).linZero_mem_linSet_of_sectionAdd hfc hmin' hz0)
    hnk (hnk'.trans hd) (fun l => bA l) hna
  -- tangent vectors of `Mᵢ` with chart vectors `a`
  have hαex : ∀ l, ∃ α ∈ A.X.PObj.submanifoldTangent (K.M i) y,
      chartVec (chartPtOf c hc hyc hys).c.isChart α = (bA l).1 := fun l =>
    (Set.ext_iff.1 hA (bA l).1).2 (bA l).2
  choose α hαT hαv using hαex
  have hαm : ∀ l, chartVec (chartPtOf c hc hyc hys).c.isChart (α l) ∈
      (chartPtOf c hc hyc hys).c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
        (chartPtOf c hc hyc hys).z := fun l =>
    mem_submodule_of_eq_of_mem (hαv l) (bA l).2
  have hαw : wedge (fun l => (⟨chartVec (chartPtOf c hc hyc hys).c.isChart (α l), hαm l⟩ :
      (chartPtOf c hc hyc hys).c.linKer (Polyfold.sectionAdd A.P f (minusSection ŝ))
        (chartPtOf c hc hyc hys).z)) hnk.symm = wedge (fun l => bA l) hnk.symm := by
    congr 1
    exact funext fun l => Subtype.ext (hαv l)
  have htO : α ∈ K.frames hf₀ hsec o i y ↔
      (chartPtOf c hc hyc hys).tangentOrOf hf₀ hg hx0 hgL hmemL
        (toChartOr hf₀ hys c hc hyc (o y hys)) = rayOfNeZero ℝ _ hna := by
    constructor
    · intro hF
      obtain ⟨-, hm', hne', hr'⟩ := (hiff α).1 hF
      exact hr₀.symm.trans (hr'.trans (rayOfNeZero_congr hαw _ _))
    · intro hr
      exact (hiff α).2 ⟨hαT, hαm, by rw [hαw]; exact hna,
        hr₀.trans (hr.trans (rayOfNeZero_congr hαw.symm _ _))⟩
  -- the generator for the sign of `α`
  obtain ⟨ν₁, hna₁, s, hsF, hν₁, hray'⟩ : ∃ ν₁, ∃ hna₁ : wedge (Fin.cons ν₁ a' :
      Fin (K.dim i + 1) → _) (hnk'.trans hd).symm ≠ 0, ∃ s : ℝ,
      ((s = 1 ∧ α ∈ K.frames hf₀ hsec o i y) ∨ (s = -1 ∧ α ∉ K.frames hf₀ hsec o i y)) ∧
      ((ν₁.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => s * ivSign (corner q)) ∧
      (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
        (isChart_ivChart (corner q) hc q₀) hzc' hzs).pertTangentOr hfc hmin' hz0 hGL
        (ivOrOf (corner q) hc hyc hys hb q₀ hf₀ hfc hne (toChartOr hf₀ hys c hc hyc (o y hys))) =
        rayOfNeZero ℝ _ hna₁ := by
    by_cases hF : α ∈ K.frames hf₀ hsec o i y
    · exact ⟨ν, hna', 1, Or.inl ⟨rfl, hF⟩, by rw [one_mul]; exact hν1, hpos (htO.1 hF)⟩
    · exact ⟨ν', hna'', -1, Or.inr ⟨rfl, hF⟩, by rw [neg_one_mul]; exact hν1',
        hneg fun h => hF (htO.2 h)⟩
  -- tangent vectors of `M̃ⱼ`
  obtain ⟨w, hwT, hwv⟩ : ∃ w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y),
      chartVec (ivChart (corner q) c q₀).isChart w = ν₁.1 :=
    (Set.ext_iff.1 hA' ν₁.1).2 ν₁.2
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
    obtain ⟨γ, hγ, hγv⟩ := (Set.ext_iff.1 hA' (a' l).1).2 (a' l).2
    have he : γ = (cubeFaceIncl A q).tangent.obj (α l) :=
      chartVec_injOn (ivChart (corner q) c q₀).isChart hzc' hγ.1 (hβb l)
        (hγv.trans (hβv l).symm)
    rw [← he]
    exact hγ
  -- the `t`-component of `w`
  have hτ : cylTimeComponent A q w = s := by
    have hbase : ((cubePolyfold 1).prod A.X.PObj).levelVal 1
        (((cubePolyfold 1).prod A.X.PObj).tangentProj w) = (q, y) := hwT.1
    have h := chartVec_prod_fst (P := A.X.PObj) (isChart_chart (corner q)) c.isChart (w := w)
      (by rw [hbase]; exact ⟨hb, hyc⟩)
    have h2 : (chartVec ((isChart_chart (corner q)).prod c.isChart) w).1 =
        fun _ => s * ivSign (corner q) := (congrArg Prod.fst hwv).trans hν₁
    change cubeTimeSign q * (chartVec (isChart_chart (corner q))
      (MPolyfold.tangentMap (isScSmoothMap_fst (cubePolyfold 1) A.X.PObj) w) : Fin 1 → ℝ) 0 = s
    rw [← h, h2, cubeTimeSign_eq_ivSign]
    change ivSign (corner q) * (s * ivSign (corner q)) = s
    rw [mul_comm s, ← mul_assoc, ivSign_mul_self, one_mul]
  refine ⟨α, hαT, s, w, hsF, hwT, hτ, ?_⟩
  -- the frame `(w, Tι_q α)`
  have hval : ∀ m : Fin (K.dim i + 1), chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m) =
      ((Fin.cons ν₁ a' : Fin (K.dim i + 1) → _) m).1 := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwv
    · exact hβv l
  have hTm : ∀ m : Fin (K.dim i + 1), (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
      Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) m ∈
      (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) := fun m => by
    refine Fin.cases ?_ (fun l => ?_) m
    · exact hwT
    · exact hβT l
  have hr₀' := (chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
    (isChart_ivChart (corner q) hc q₀) hzc' hzs).tangentOr_orSectionAdd hfc hmin' hz0 hGL
    (toChartOr hfc hzs (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀) hzc'
      (cubeOrientation hf hft hsec o (q, y) hzs))
  have hr₁ := hr₀'.trans ((congrArg ((chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀)
    (isChart_ivChart (corner q) hc q₀) hzc' hzs).pertTangentOr hfc hmin' hz0 hGL) hor).trans hray')
  have hw' := fun hm => wedge_mk_comp_finCast hd (Fin.cons ν₁ a' : Fin (K.dim i + 1) → _)
    (fun k : Fin (K'.dim j) => chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)))
    (fun k => hval (Fin.cast hd k)) hm (hnk'.trans hd).symm hnk'.symm
  have hm := fun k : Fin (K'.dim j) => mem_submodule_of_eq_of_mem (hval (Fin.cast hd k))
    ((Fin.cons ν₁ a' : Fin (K.dim i + 1) → _) (Fin.cast hd k)).2
  exact (hiff' _).2 ⟨fun k => hTm _, hm, fun h0 => hna₁ ((hw' hm).symm.trans h0),
    hr₁.trans (rayOfNeZero_congr (hw' hm).symm _ _)⟩

/-- **The tangent line of a curve of the cobordism over a signed point** (Corollary 15.4.4 for
Fredholm index `0`, p. 703; Remark 6.6.19).  In the situation of
`exists_signed_frame_cubeOrientation` with `dim Mᵢ = 0`: there is `w ∈ T_{(q, y)}M̃ⱼ` positive for
`(e ∧ o)_{(q, y)}` with `dt(w) = 1` if the point `y` of `Mᵢ` is positive (the orientation
`o_{i,y}` induced by `o` has a frame), and with `dt(w) = −1` if it is negative. -/
theorem exists_signed_generator_cubeOrientation (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) (q : Fin 1 → unitInterval)
    {Λ : A.W → ℚ≥0} {Λ' : (A.cubeSEP 1).W → ℚ≥0} {x : A.Obj} (K : KernelBranching A f Λ x)
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x)) (i : K.ι)
    (j : K'.ι) (h0 : K.dim i = 0) (h1 : K'.dim j = 1)
    (hs : ∀ y ∈ K.O, (q, y) ∈ K'.O → cubeVal (K'.s j (q, y)) = ((q, y), K.s i y))
    {y : A.Obj} (hy : y ∈ K.M i) (hy' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j) :
    ∃ (s : ℝ) (w : (A.cubeSEP 1).X.PObj.TangentSpace),
      ((s = 1 ∧ (K.frames hf.2 hsec o i y).Nonempty) ∨
        (s = -1 ∧ ¬ (K.frames hf.2 hsec o i y).Nonempty)) ∧
      w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y) ∧
      cylTimeComponent A q w = s ∧
      (fun _ => w) ∈ K'.frames (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
        (cubeOrientation hf hft hsec o) j (q, y) := by
  have hd : K'.dim j = K.dim i + 1 := by rw [h0, h1]
  obtain ⟨α, -, s, w, hsF, hwT, hτ, hfr⟩ :=
    exists_signed_frame_cubeOrientation hbump hf hft hsec hsec' o q K K' i j hd hs hy hy'
  have huniq : ∀ β : Fin (K.dim i) → A.X.PObj.TangentSpace, β = α := fun β =>
    funext fun l => (by have := l.2; omega : False).elim
  refine ⟨s, w, hsF.imp (fun h => ⟨h.1, α, h.2⟩)
    (fun h => ⟨h.1, fun ⟨β, hβ⟩ => h.2 (huniq β ▸ hβ)⟩), hwT, hτ, ?_⟩
  have he : (fun _ : Fin (K'.dim j) => w) =
      fun k => (Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k) := by
    funext k
    have hk0 : Fin.cast hd k = 0 := Fin.ext (by
      have := k.2
      change (k : ℕ) = 0
      omega)
    rw [hk0, Fin.cons_zero]
  rw [he]
  exact hfr

end SBLocalization

end Polyfold
