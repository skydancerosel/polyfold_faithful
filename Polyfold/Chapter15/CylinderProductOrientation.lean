import Polyfold.Chapter15.CylinderEndCanonical
import Polyfold.Chapter15.KernelFramesPerturbed
import Polyfold.Chapter6.IntervalSliceFrames

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703: the proof
of **Corollary 15.4.4** (2017: Corollary 15.2), with **Remark 6.6.19** (p. 276).

# The orientation of `f̃` on `[0, 1] × X` and the frames of the kernels on the ends

## The text, paraphrased

(p. 703) On the cylinder `[0, 1] × X` the section `f̃(t, x) = (t, f(x))` is oriented by the
standard orientation of `[0, 1]` followed by the orientation `o` of `f` (Remark 6.6.19).  Near
`(i, x)`, `i ∈ {0, 1}`, a sheet of the cobordism is `M̃ = {f̃ = s̃}`, its boundary is `{i} × M`
with `M = {f = s̃(i, ·)}`, and `ker (f̃ − s̃)'(i, y) = ℝ·(∂_t + u) ⊕ ker (f − s̃(i, ·))'(y)` is
oriented with the `ℝ`-factor first.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `cubeOrientation hf hft hsec o`: the family `(t, x) ↦ e ∧ o_x` of orientations of `f̃` on
  `[0, 1] × X` (Part I's `ivFirstFun`), as a family of orientations of the section functor
  `cubeLiftEp f` of the cylinder `A.cubeSEP 1`.
* `isSectionOrientation_cubeOrientation`: it is an orientation of `f̃` (Definition 6.6.16) if
  `o` is one of `f`.
* **`exists_timeFirst_frame_cubeOrientation`**: for local branching structures described by
  kernels `K` of `(f, Λ)` at `x` and `K̃` of `(f̃, Λ̃)` at `(q, x)`, sheets `Mᵢ = {f = sᵢ}`,
  `M̃ⱼ = {f̃ = s̃ⱼ}` with `s̃ⱼ(q, ·) = sᵢ` and `dim M̃ⱼ = dim Mᵢ + 1 ≥ 2`, and `y ∈ Mᵢ` with
  `(q, y) ∈ M̃ⱼ`: there are a frame `α` of `T_yMᵢ` positive for `o_y` and `w ∈ T_{(q, y)}M̃ⱼ`
  with `dt(w) > 0` such that `(w, Tι_q α)` is positive for `(e ∧ o)_{(q, y)}`.
* **`cylinderKernelFrameConvention_cubeOrientation`**: `CylinderKernelFrameConvention` for
  `õ = e ∧ o`, when `f` has a positive index at every point.

## Reading

For a sheet of dimension `0` with the negative orientation there is no positive frame, so the
statement is made for sheets of positive dimension; in Corollary 15.4.4 the sheets of the
perturbations have dimension `m + 1 ≥ 1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

universe u

/-- The wedge of a tuple reindexed along `Fin.cast`. -/
theorem wedge_comp_finCast {N : Type*} [AddCommGroup N] [Module ℝ N] {n' k : ℕ} (hd : n' = k)
    (v : Fin k → N) (h : k = finrank ℝ N) :
    wedge (fun i : Fin n' => v (Fin.cast hd i)) (hd.trans h) = wedge v h := by
  subst hd
  rfl

/-- The wedge of a tuple of vectors of a submodule given by their values, reindexed along
`Fin.cast`. -/
theorem wedge_mk_comp_finCast {M : Type*} [AddCommGroup M] [Module ℝ M] {N : Submodule ℝ M}
    {n' k : ℕ} (hd : n' = k) (u : Fin k → N) (v : Fin n' → M)
    (hv : ∀ i, v i = (u (Fin.cast hd i) : M)) (hm : ∀ i, v i ∈ N) (h : k = finrank ℝ N)
    (h' : n' = finrank ℝ N) : wedge (fun i => (⟨v i, hm i⟩ : N)) h' = wedge u h := by
  subst hd
  congr 1
  exact funext fun i => Subtype.ext (hv i)

theorem mem_submodule_of_eq_of_mem {M : Type*} [AddCommGroup M] [Module ℝ M] {N : Submodule ℝ M}
    {x y : M} (h : x = y) (hy : y ∈ N) : x ∈ N := h ▸ hy

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-! ### The orientation `e ∧ o` of `f̃` -/

/-- **The orientation `õ = e ∧ o` of `f̃` on the cylinder `[0, 1] × X`** (2021 p. 703 and Remark
6.6.19): `(t, x) ↦ e ∧ o_x`, `e` the standard direction of `[0, 1]`, as a family of orientations
of the section functor `f̃ = cubeLiftEp f` of `A.cubeSEP 1`. -/
def cubeOrientation (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy) :
    ∀ z (hz : z ∈ (A.cubeSEP 1).X.PObj.smoothSet),
      Orx (cubeLiftEp (n := 1) f hf.1.1.1)
        (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 z hz :=
  haveI := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  haveI := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  ivFirstFun hf.2 (hft.paramCube (n := 1)).toIsScFredholmSection hsec o

/-- **`õ = e ∧ o` is an orientation of `f̃` over `[0, 1] × X`** (Definition 6.6.16; 2021 Remark
6.6.19) for `X` tame with sc-smooth bump functions and `o` an orientation of `f`. -/
theorem isSectionOrientation_cubeOrientation (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o) :
    haveI := paracompactSpace_rn_prod (A.cubeSEP 1).X.PObj
    haveI := paracompactSpace_rn_pullback (A.cubeSEP 1).B
    IsSectionOrientation (cubeLiftEp (n := 1) f hf.1.1.1)
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      (cubeOrientation hf hft
        (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_prod ((cubePolyfold 1).prod A.X.PObj)
  have := paracompactSpace_rn_pullback (ivBundle A.B)
  exact isSectionOrientation_ivFirstFun hX hbump hft ho

/-! ### The frames of the kernels on an end of the cylinder -/

/-- `cubeTimeSign q` is the sign of the corner chart of `[0, 1]` at `q`. -/
theorem cubeTimeSign_eq_ivSign (q : Fin 1 → unitInterval) : cubeTimeSign q = ivSign (corner q) :=
  rfl

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid and the product chart point are unfolded in several places
/-- **The frame convention of the canonical orientations for `õ = e ∧ o`, at a pair of sheets**
(2021 p. 703, Remark 6.6.19 and the proof of Theorem 6.7.1).  Let `X` have sc-smooth bump
functions, `K` be a local branching structure of `(f, Λ)` at `x` described by kernels, `K̃` one
of `(f̃, Λ̃)` at `(q, x)`, and let the sheets `Mᵢ = {f = sᵢ}` of `K` and `M̃ⱼ = {f̃ = s̃ⱼ}` of `K̃`
satisfy `s̃ⱼ(q, ·) = sᵢ`, `dim M̃ⱼ = dim Mᵢ + 1` and `dim Mᵢ ≥ 1`.  For `y ∈ Mᵢ` with
`(q, y) ∈ M̃ⱼ` there are a frame `α` of `T_yMᵢ = ker (f − sᵢ)'(y)` positive for `o_y` and a vector
`w ∈ T_{(q, y)}M̃ⱼ = ker (f̃ − s̃ⱼ)'(q, y)` with `dt(w) = 1` such that `(w, Tι_q α)` is positive
for `(e ∧ o)_{(q, y)}`.  Proof: `sᵢ` and `s̃ⱼ` are germs of global sc⁺-sections `ŝ = Ŝ(q, ·)` and
`Ŝ`; the frames are those spanning Part I's tangent orientations of `f + (−ŝ)` and `f̃ + (−Ŝ)`
(`KernelBranching.mem_frames_iff_tangentOr`), and these are related by
`exists_timeFirst_wedge_ivOrLift`. -/
theorem exists_timeFirst_frame_cubeOrientation (hbump : A.X.PObj.AdmitsBumpFunctions)
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
  -- a positive frame of `ker (f − ŝ)'(y)`
  have : FiniteDimensional ℝ ((chartPtOf c hc hyc hys).c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z) :=
    Module.finite_of_finrank_pos (hnk.symm ▸ hpos)
  have : Nonempty (Fin (K.dim i)) := ⟨⟨0, hpos⟩⟩
  have hr₀ := (chartPtOf c hc hyc hys).tangentOr_orSectionAdd hf₀ hmin hx0 hgL
    (toChartOr hf₀ hys c hc hyc (o y hys))
  obtain ⟨bA, hbA⟩ : ∃ bA : Basis (Fin (K.dim i)) ℝ ((chartPtOf c hc hyc hys).c.linKer
      (Polyfold.sectionAdd A.P f (minusSection ŝ)) (chartPtOf c hc hyc hys).z),
      bA.orientation = pullOr hnk (LinearEquiv.refl ℝ _)
        ((chartPtOf c hc hyc hys).pertTangentOr hf₀ hmin hx0 hgL
          (toChartOr hf₀ hys c hc hyc (o y hys))) :=
    ⟨(Module.finBasisOfFinrankEq ℝ _ hnk).adjustToOrientation _,
      Basis.orientation_adjustToOrientation _ _⟩
  have hrA := (orientation_eq_pullOr_iff hnk (LinearEquiv.refl ℝ _) _ bA).1 hbA
  have hna : wedge (fun l => bA l) hnk.symm ≠ 0 :=
    wedge_equiv_ne_zero hnk (LinearEquiv.refl ℝ _) bA
  have ha : (chartPtOf c hc hyc hys).tangentOrOf hf₀ hg hx0 hgL
      ((chartPtOf c hc hyc hys).linZero_mem_linSet_of_sectionAdd hf₀ hmin hx0)
      (toChartOr hf₀ hys c hc hyc (o y hys)) = rayOfNeZero ℝ _ hna := hrA
  -- the frame of `ker (f̃ − Ŝ)'(q, y)`
  obtain ⟨ν, a', hna', hν1, ha', hray'⟩ := exists_timeFirst_wedge_ivOrLift (corner q) hc hyc _
    (exists_lift_of_smooth c hyc hys).choose_spec hb q₀ hzc' _
    (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec
    (ivChart_lift_eq (corner q) _ (exists_lift_of_smooth c hyc hys).choose_spec q q₀ _
      (exists_lift_of_smooth (ivChart (corner q) c q₀) hzc' hzs).choose_spec) hf₀ hfc hys hne
    (toChartOr hf₀ hys c hc hyc (o y hys)) hG hslice hg hz0 hx0 hgL hGL
    ((chartPtOf c hc hyc hys).linZero_mem_linSet_of_sectionAdd hf₀ hmin hx0)
    ((chartPtOf (B := ivBundle A.B) (ivChart (corner q) c q₀) (isChart_ivChart (corner q) hc q₀)
      hzc' hzs).linZero_mem_linSet_of_sectionAdd hfc hmin' hz0)
    hnk (hnk'.trans hd) (fun l => bA l) hna ha
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
  have hαF : α ∈ K.frames hf₀ hsec o i y :=
    (hiff α).2 ⟨hαT, hαm, by rw [hαw]; exact hna,
      hr₀.trans (hrA.trans (rayOfNeZero_congr hαw.symm _ _))⟩
  -- tangent vectors of `M̃ⱼ`
  obtain ⟨w, hwT, hwv⟩ : ∃ w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (K'.M j) (q, y),
      chartVec (ivChart (corner q) c q₀).isChart w = ν.1 :=
    (Set.ext_iff.1 hA' ν.1).2 ν.2
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
  have hw' := fun hm => wedge_mk_comp_finCast hd (Fin.cons ν a' : Fin (K.dim i + 1) → _)
    (fun k : Fin (K'.dim j) => chartVec (ivChart (corner q) c q₀).isChart
      ((Fin.cons w (fun l => (cubeFaceIncl A q).tangent.obj (α l)) :
        Fin (K.dim i + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) (Fin.cast hd k)))
    (fun k => hval (Fin.cast hd k)) hm (hnk'.trans hd).symm hnk'.symm
  have hm := fun k : Fin (K'.dim j) => mem_submodule_of_eq_of_mem (hval (Fin.cast hd k))
    ((Fin.cons ν a' : Fin (K.dim i + 1) → _) (Fin.cast hd k)).2
  exact (hiff' _).2 ⟨fun k => hTm _, hm, fun h0 => hna' ((hw' hm).symm.trans h0),
    hr₁.trans (rayOfNeZero_congr (hw' hm).symm _ _)⟩

/-- **`CylinderKernelFrameConvention` holds for `õ = e ∧ o`** (2021 p. 703, Remark 6.6.19), on
every end `q`, if `X` has sc-smooth bump functions and the sheets of the local branching
structures of `f` described by kernels have positive dimension (which holds if `f` has a
positive index at every point, `KernelBranching.dim_eq_of_isIndexAt`). -/
theorem cylinderKernelFrameConvention_cubeOrientation (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hdim : ∀ (Λ : A.W → ℚ≥0) (x : A.Obj) (K : KernelBranching A f Λ x) (i : K.ι), 0 < K.dim i)
    (q : Fin 1 → unitInterval) :
    CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) q :=
  fun Λ _ x K K' i j hd hs _ hy hy' =>
    exists_timeFirst_frame_cubeOrientation hbump hf hft hsec hsec' o q K K' i j hd
      (hdim Λ x K i) hs hy hy'

end SBLocalization

end Polyfold
