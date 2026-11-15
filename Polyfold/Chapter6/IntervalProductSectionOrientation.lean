import Polyfold.Chapter6.IntervalProductTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230): the orientation of `f̂(x, t) = f(x) + s(x, t)`
over the M-polyfold with boundary `[0, 1] × X` given by an orientation `o` of `f` and the
standard orientation of `[0, 1]`, as an orientation of the section `f̂` (Definition 6.6.16).

# `SectionOrientation.ivFirst`

## What is formalized

`[0, 1] × X` is `(cubePolyfold 1).prod PX`, a tame M-polyfold with the boundary `{0, 1} × X`
(`prod_cube_isTame`, `cubePolyfold_degIndex`); the sections are sections of the pull-back of `P`
to it, and `f̃ = cubeLift f` is tame sc-Fredholm (`IsScFredholmSectionTame.paramCube`).

* `ivOrOf_orTransfer`: the orientation `e ∧ o` of `f̃` does not depend on the chart of `X` nor on
  the chart of `[0, 1]`.
* `ivFirstFun o`: the map `(t, x) ↦ e ∧ o_x ∈ Or^{f̃}_{(t, x)}` on `[0, 1] × X`;
  `toChartOr_ivFirstFun`: read in any chart of `[0, 1] × X`, it is the transfer of `e ∧ o_x` read
  in the product chart over any chart of `X` and any chart of `[0, 1]` at the point.
* `isSectionOrientation_ivFirstFun`: **`(t, x) ↦ e ∧ o_x` is an orientation of `f̃` over
  `[0, 1] × X`** (Definition 6.6.16) when `o` is an orientation of `f`; the continuity is checked
  at every point, the boundary points `(0, x)` and `(1, x)` included.
* `SectionOrientation.ivFirst₀ o` (the orientation of `f̃`) and
  **`SectionOrientation.ivFirst o hS`** (the orientation of `f̂ = f̃ + S`, 2021 Remark 6.6.19,
  for an sc⁺-section `S` over `[0, 1] × X`).
* `SectionOrientation.toChartOr_ivFirst₀`, `ivFirst₀_apply_ivLin`: in the product chart
  `χ_b × φ_c` the orientation is `L̂ ↦ e ∧ o(L)`, where `e` is the direction of increasing `t`:
  the chart vector in the chart `t ↦ t`, minus the chart vector in the chart `t ↦ 1 − t`.

## Reading

The parameter is placed first, `[0, 1] × X`, as in the families of §6.6.  "The standard
orientation of `[0, 1]`" is the direction of increasing `t`.  The hypotheses `X` tame with
sc-smooth bump functions and tame germ data of `f` are those of `theorem_6_6_18_oriented`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

section IvIndep

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source) (b' : Fin 1 → Bool) (ht' : t ∈ (chart b').source)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **The orientation `e ∧ o` of `f̃` does not depend on the charts** of `X` and of `[0, 1]`
(`orTransfer_ivPt_ivOrFirst` for the zero section, through `Lin(f̃ + 0) = Lin(f̃)`). -/
theorem orTransfer_ivPt_ivOrFirst₀ (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f).Nonempty) (o : p.Or f hf) :
    (p.ivPt b ht q₀).orTransfer (p'.ivPt b' ht' q₀') hfc (prod_cube_mem_smoothSet_iff.2 hx)
        (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o) =
      p'.ivOrFirst₀ b' ht' q₀' hf hfc hx hne' (p.orTransfer p' hf hx o) :=
  (LineOrientation.conj_congrDetOn _ _ _ _ _ _ _ _ _ _ _).trans
    (congrArg ((p'.ivPt b' ht' q₀').orCongr (theorem_3_1_18_preprint hfc
        (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B))) hfc
      (p'.linSet_cubeLift_add_zero b' ht' q₀' hf))
      (p.orTransfer_ivPt_ivOrFirst p' b ht b' ht' q₀ q₀' hf hfc hx
        (StrongBundle.isScPlusSection_fiberZero (B := ivBundle B)) hne o))

end ChartPoint

/-- `ivOrLift` does not depend on the charts of `X` and of `[0, 1]`. -/
theorem ivOrLift_orTransfer (b b' : Fin 1 → Bool) {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') {x : X} (hx : x ∈ c.φ.source)
    (hx' : x ∈ c'.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x) (w : c'.φ.model.E 1)
    (hw : c'.φ.model.E.toBase 1 w = c'.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source) (ht' : t ∈ (chart b').source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z))
    (hxc' : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b' c' q₀').φ.source)
    (w' : (ivChart b' c' q₀').φ.model.E 1)
    (hw' : (ivChart b' c' q₀').φ.model.E.toBase 1 w' = (ivChart b' c' q₀').φ (t, x))
    (hww : w' = ((chart b' t : Fin 1 → ℝ), w)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty)
    (hne' : ((chartPt c' hc' hx' w hw).linSet f).Nonempty)
    (o : (chartPt c hc hx z hz).Or f hf) :
    (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z' hz').orTransfer
        (chartPt (B := ivBundle B) (ivChart b' c' q₀') (isChart_ivChart b' hc' q₀') hxc' w' hw')
        hfc (prod_cube_mem_smoothSet_iff.2 hxs)
        (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) =
      ivOrLift b' hc' hx' w hw ht' q₀' hxc' w' hw' hww hf hfc hxs hne'
        ((chartPt c hc hx z hz).orTransfer (chartPt c' hc' hx' w hw) hf hxs o) := by
  subst hzz hww
  exact (chartPt c hc hx z hz).orTransfer_ivPt_ivOrFirst₀ (chartPt c' hc' hx' w hw) b ht b' ht'
    q₀ q₀' hf hfc hxs hne hne' o

/-- `ivOrLift` for the lift `(χ_b(t), z)` is `ivOrFirst₀`: at `L̂ = ivLin L` it is `e ∧ o(L)`
(`ChartPoint.ivOrFirst₀_apply`). -/
theorem ivOrLift_eq_ivOrFirst₀ (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 ((chart b t : Fin 1 → ℝ), z) =
      (ivChart b c q₀).φ (t, x)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf) :
    ivOrLift b hc hx z hz ht q₀ hxc ((chart b t : Fin 1 → ℝ), z) hz' rfl hf hfc hxs hne o =
      (chartPt c hc hx z hz).ivOrFirst₀ b ht q₀ hf hfc hxs hne o :=
  rfl

/-- **`ivOrOf` does not depend on the chart of `X` nor on the chart of `[0, 1]`.** -/
theorem ivOrOf_orTransfer (b b' : Fin 1 → Bool) {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') {x : X} (hx : x ∈ c.φ.source)
    (hx' : x ∈ c'.φ.source) (hs : x ∈ PX.smoothSet) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source) (ht' : t ∈ (chart b').source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hne : ((chartPtOf c hc hx hs).linSet f).Nonempty)
    (hne' : ((chartPtOf c' hc' hx' hs).linSet f).Nonempty) (o : (chartPtOf c hc hx hs).Or f hf) :
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hx ht) (prod_cube_mem_smoothSet_iff.2 hs)).orTransfer
        (chartPtOf (B := ivBundle B) (ivChart b' c' q₀') (isChart_ivChart b' hc' q₀')
          (mem_ivChart_source q₀' hx' ht') (prod_cube_mem_smoothSet_iff.2 hs)) hfc
        (prod_cube_mem_smoothSet_iff.2 hs) (ivOrOf b hc hx hs ht q₀ hf hfc hne o) =
      ivOrOf b' hc' hx' hs ht' q₀' hf hfc hne'
        ((chartPtOf c hc hx hs).orTransfer (chartPtOf c' hc' hx' hs) hf hs o) :=
  ivOrLift_orTransfer b b' hc hc' hx hx' _ _ _ _ ht ht' q₀ q₀' _ _ _ _ _ _ _ _ hf hfc hs
    hne hne' o

end IvIndep

/-! ### The map `(t, x) ↦ e ∧ o_x` and its continuity -/

section IvAssembly

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P
    (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))]

/-- **The map `(t, x) ↦ e ∧ o_x` on `[0, 1] × X`** (2021 Remark 6.6.19): for a map
`y ↦ o_y ∈ Or_y^f`, the orientation `e ∧ o_x` of `f̃` at `(t, x)`, `e` the standard direction of
`[0, 1]`, made in the product chart over the chosen chart of `X` at `x` and the corner chart of
`[0, 1]` at `t`, and read in the chosen chart of `[0, 1] × X` at `(t, x)`. -/
def ivFirstFun (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) :
    ∀ z (hz : z ∈ ((cubePolyfold 1).prod PX).smoothSet),
      Orx (B := ivBundle B) (cubeLift (n := 1) f hf.isScSmooth.1) hfc z hz :=
  fun z hz => (toChartOr hfc hz
      (ivChart (corner z.1) (orChart B z.2) (cubeLift (n := 1) f hf.isScSmooth.1 z))
      (isChart_ivChart _ (isChart_orChart z.2) _)
      (mem_ivChart_source _ (mem_orChart z.2) (mem_chart_corner z.1))).symm
    (ivOrOf (corner z.1) (isChart_orChart z.2) (mem_orChart z.2)
      (prod_cube_mem_smoothSet_iff.1 hz) (mem_chart_corner z.1) _ hf hfc
      (ChartPoint.linSet_nonempty _ hf (prod_cube_mem_smoothSet_iff.1 hz) hsec)
      (o z.2 (prod_cube_mem_smoothSet_iff.1 hz)))

omit [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P
    (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))] in
/-- **`(t, x) ↦ e ∧ o_x` read in a chart `c'` of `[0, 1] × X`** is the transfer to `c'` of
`e ∧ (o_x read in c)` made in the product chart `χ_b × φ_c`, for any chart `c` of `X` at `x` and
any chart `χ_b` of `[0, 1]` at `t` (`ivOrOf_orTransfer`). -/
theorem toChartOr_ivFirstFun (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (z : (Fin 1 → unitInterval) × X) (hz : z ∈ ((cubePolyfold 1).prod PX).smoothSet)
    (b : Fin 1 → Bool) (hb : z.1 ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : z.2 ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    {c' : StrongBundleChart ((cubePolyfold 1).prod PX) (pullbackProj P Prod.snd)}
    (hc' : (ivBundle B).IsChart c') (hz' : z ∈ c'.φ.source)
    (hne : ((chartPtOf c hc hxc (prod_cube_mem_smoothSet_iff.1 hz)).linSet f).Nonempty) :
    toChartOr hfc hz c' hc' hz' (ivFirstFun hf hfc hsec o z hz) =
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) hz).orTransfer (chartPtOf c' hc' hz' hz) hfc hz
        (ivOrOf b hc hxc (prod_cube_mem_smoothSet_iff.1 hz) hb q₀ hf hfc hne
          (toChartOr hf (prod_cube_mem_smoothSet_iff.1 hz) c hc hxc
            (o z.2 (prod_cube_mem_smoothSet_iff.1 hz)))) := by
  have hs := prod_cube_mem_smoothSet_iff.1 hz
  have hne₀ := ChartPoint.linSet_nonempty (chartPtOf (orChart B z.2) (isChart_orChart z.2)
    (mem_orChart z.2) hs) hf hs hsec
  have h1 := toChartOr_eq_orTransfer hfc hz (ivFirstFun hf hfc hsec o z hz)
    (isChart_ivChart (corner z.1) (isChart_orChart z.2)
      (cubeLift (n := 1) f hf.isScSmooth.1 z)) hc'
    (mem_ivChart_source _ (mem_orChart z.2) (mem_chart_corner z.1)) hz'
  have h2 := ivOrOf_orTransfer (corner z.1) b (isChart_orChart z.2) hc (mem_orChart z.2) hxc hs
    (mem_chart_corner z.1) hb (cubeLift (n := 1) f hf.isScSmooth.1 z) q₀ hf hfc hne₀ hne
    (o z.2 hs)
  have h3 := ChartPoint.orTransfer_trans
    (chartPtOf (B := ivBundle B) (ivChart (corner z.1) (orChart B z.2)
      (cubeLift (n := 1) f hf.isScSmooth.1 z)) (isChart_ivChart _ (isChart_orChart z.2) _)
      (mem_ivChart_source _ (mem_orChart z.2) (mem_chart_corner z.1)) hz)
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
      (mem_ivChart_source q₀ hxc hb) hz) (chartPtOf c' hc' hz' hz) hfc hz
  refine h1.trans ?_
  refine (congrArg _ (Equiv.apply_symm_apply _ _)).trans ?_
  refine (DFunLike.congr_fun h3 _).symm.trans ?_
  exact congrArg ((chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
    (mem_ivChart_source q₀ hxc hb) hz).orTransfer (chartPtOf c' hc' hz' hz) hfc hz) h2

/-- **`(t, x) ↦ e ∧ o_x` is an orientation of `f̃` over `[0, 1] × X`** (2021 Remark 6.6.19 and
Definition 6.6.16) when `o` is an orientation of `f`.  At `z = (t, x)`, boundary points
included: over an orientable neighbourhood of `f̃` inside `dom χ_b × V` for the corner chart
`χ_b` at `t` and an orientable neighbourhood `V` of `f`, a push-forward of `f̃` along `γ` is the
transfer of the lift of a push-forward of `f` along `pr₂ ∘ γ` (`IsPush.ivLift`,
`IsPush.transfer`, the uniqueness of local push-forwards), which carries `e ∧ o` to `e ∧ o`. -/
theorem isSectionOrientation_ivFirstFun (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o) :
    IsSectionOrientation (B := ivBundle B) (cubeLift (n := 1) f hf.isScSmooth.1)
      (hf.paramCube (n := 1)).toIsScFredholmSection
      (ivFirstFun hf.toIsScFredholmSection (hf.paramCube (n := 1)).toIsScFredholmSection
        (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o) := by
  have hsec : B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump
  have hfT := hf.paramCube (n := 1)
  have hfc := hfT.toIsScFredholmSection
  have hX' : ((cubePolyfold 1).prod PX).IsTame := prod_cube_isTame hX
  have hbump' : ((cubePolyfold 1).prod PX).AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube hbump
  have hsec' : (ivBundle B).HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump'
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  have := paracompactSpace_rn_rn_prod ((cubePolyfold 1).prod PX)
  have := paracompactSpace_rn_rn_pullback (ivBundle B)
  refine (isSectionOrientation_iff hX' hbump' hfT hsec' _).2 fun x y a =>
    orFunctorMap_apply_eq_of_local hX' hbump' hfT hsec' _ (fun z hz => ?_) a
  have hs := prod_cube_mem_smoothSet_iff.1 hz
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hf hs
  obtain ⟨c', hc', U', V', hN'⟩ := exists_isOrientableNbhd hX' hbump' hfT hz
  have hUc := hN.hasLocalPropagation.subset
  set b₀ := corner z.1 with hb₀
  have hWo : IsOpen (Prod.fst ⁻¹' (chart b₀).source : Set ((Fin 1 → unitInterval) × X)) :=
    (chart b₀).isOpen_source.preimage continuous_fst
  have hU''o : IsOpen (U' ∩ Prod.snd ⁻¹' V ∩ Prod.fst ⁻¹' (chart b₀).source) :=
    (hN'.isOpen_U.inter (hN.isOpen_V.preimage continuous_snd)).inter hWo
  have hLP := hN'.hasLocalPropagation.mono
    (fun w hw => hw.1.1 : U' ∩ Prod.snd ⁻¹' V ∩ Prod.fst ⁻¹' (chart b₀).source ⊆ U')
  obtain ⟨V'', hV''o, hzV'', hV''U'', hpath⟩ :=
    exists_nhds_scPath hc' hU''o hLP.subset
      ⟨⟨hN'.subset hN'.mem, hN.mem⟩, mem_chart_corner z.1⟩
  refine ⟨c', hc', U' ∩ Prod.snd ⁻¹' V ∩ Prod.fst ⁻¹' (chart b₀).source, V'',
    ⟨hLP, hU''o, hV''o, hV''U'', hzV'', hpath⟩, ?_⟩
  intro γ hγs hγ y₁ y₂ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e' he'
  have q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
    cubeLift (n := 1) f hf.isScSmooth.1 z
  have hγs' : (rnPolyfold 1).IsScSmoothMap PX (Prod.snd ∘ γ) :=
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX).comp hγs
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (γ q).2 ∈ V := fun q hq => (hγ q hq).1.2
  have hγb : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (γ q).1 ∈ (chart b₀).source :=
    fun q hq => (hγ q hq).2
  have hx₁ : y₁.2 ∈ V := (hV''U'' hy₁).1.2
  have hx₂ : y₂.2 ∈ V := (hV''U'' hy₂).1.2
  have hb₁ : y₁.1 ∈ (chart b₀).source := (hV''U'' hy₁).2
  have hb₂ : y₂.1 ∈ (chart b₀).source := (hV''U'' hy₂).2
  have hxs₁ := prod_cube_mem_smoothSet_iff.1 hs₁
  have hxs₂ := prod_cube_mem_smoothSet_iff.1 hs₂
  have hne₁ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset hx₁)) hxs₁)
    hf.toIsScFredholmSection hxs₁ hsec
  have hne₂ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset hx₂)) hxs₂)
    hf.toIsScFredholmSection hxs₂ hsec
  obtain ⟨e, he⟩ := hN.hasLocalPropagation.exists_isPush (Prod.snd ∘ γ) hγs'
    (fun q hq => hN.subset (hγV q hq)) (congrArg Prod.snd h₀) (congrArg Prod.snd h₁)
    (hUc (hN.subset hx₁)) (hUc (hN.subset hx₂)) hxs₁ hxs₂
  have hcont := ho z.2 hs c hc U V hN (Prod.snd ∘ γ) hγs' (fun q hq => hN.subset (hγV q hq))
    hx₁ hx₂ hxs₁ hxs₂ (congrArg Prod.snd h₀) (congrArg Prod.snd h₁) e he
  obtain ⟨e₂, he₂, he₂o⟩ := he.ivLift hfc b₀ (fun q => (γ q).1) hγb q₀ (congrArg Prod.fst h₀)
    (congrArg Prod.fst h₁) hb₁ hb₂ hne₁ hne₂
  have ht := IsPush.transfer (isChart_ivChart b₀ hc q₀) hc' hγs
    (fun q hq => mem_ivChart_source q₀ (hUc (hN.subset (hγV q hq))) (hγb q hq))
    (fun q hq => hLP.subset (hγ q hq)) h₀ h₁
    (mem_ivChart_source q₀ (hUc (hN.subset hx₁)) hb₁)
    (mem_ivChart_source q₀ (hUc (hN.subset hx₂)) hb₂)
    (hLP.subset (hV''U'' hy₁)) (hLP.subset (hV''U'' hy₂)) hs₁ hs₂ he₂
  have heq := hLP.eq γ γ hγs hγs hγ hγ h₀ h₁ h₀ h₁ (hLP.subset (hV''U'' hy₁))
    (hLP.subset (hV''U'' hy₂)) hs₁ hs₂ e' _ he' ht
  have k₁ := toChartOr_ivFirstFun hf.toIsScFredholmSection hfc hsec o y₁ hs₁ b₀ hb₁ hc
    (hUc (hN.subset hx₁)) q₀ hc' (hLP.subset (hV''U'' hy₁)) hne₁
  have k₂ := toChartOr_ivFirstFun hf.toIsScFredholmSection hfc hsec o y₂ hs₂ b₀ hb₂ hc
    (hUc (hN.subset hx₂)) q₀ hc' (hLP.subset (hV''U'' hy₂)) hne₂
  subst heq
  refine (congrArg (fun w => ((chartPtOf (B := ivBundle B) (ivChart b₀ c q₀)
    (isChart_ivChart b₀ hc q₀) (mem_ivChart_source q₀ (hUc (hN.subset hx₂)) hb₂)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂) hfc hs₂)
      (e₂ (((chartPtOf (B := ivBundle B) (ivChart b₀ c q₀)
    (isChart_ivChart b₀ hc q₀) (mem_ivChart_source q₀ (hUc (hN.subset hx₁)) hb₁)
    hs₁).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₁)) hs₁) hfc hs₁).symm w)))
    k₁).trans ?_
  refine (congrArg (fun w => ((chartPtOf (B := ivBundle B) (ivChart b₀ c q₀)
    (isChart_ivChart b₀ hc q₀) (mem_ivChart_source q₀ (hUc (hN.subset hx₂)) hb₂)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂) hfc hs₂) (e₂ w))
    (Equiv.symm_apply_apply _ _)).trans ?_
  exact (congrArg ((chartPtOf (B := ivBundle B) (ivChart b₀ c q₀)
    (isChart_ivChart b₀ hc q₀) (mem_ivChart_source q₀ (hUc (hN.subset hx₂)) hb₂)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂) hfc hs₂)
      ((he₂o _).trans (congrArg _ hcont))).trans k₂.symm

end IvAssembly

/-! ### The orientation of `f̂ = f̃ + S` over `[0, 1] × X` -/

section IvMain

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **The orientation `e ∧ o` of `f̃(t, x) = f(x)` over the M-polyfold with boundary
`[0, 1] × X`** (2021 Remark 6.6.19, p. 276, for `s = 0`; Definition 6.6.16):
`(t, x) ↦ e ∧ o_x` (`ivFirstFun`), `e` the standard direction of `[0, 1]`, for an orientation `o`
of a tame `f` over a tame `X` with sc-smooth bump functions
(`isSectionOrientation_ivFirstFun`). -/
def SectionOrientation.ivFirst₀ (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection) :
    SectionOrientation (B := ivBundle B) (cubeLift (n := 1) f hf.isScSmooth.1)
      (hf.paramCube (n := 1)).toIsScFredholmSection :=
  haveI := paracompactSpace_rn_prod PX
  haveI := paracompactSpace_rn_pullback B
  haveI := paracompactSpace_rn_prod ((cubePolyfold 1).prod PX)
  haveI := paracompactSpace_rn_pullback (ivBundle B)
  ⟨ivFirstFun hf.toIsScFredholmSection (hf.paramCube (n := 1)).toIsScFredholmSection
      (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o.1,
    isSectionOrientation_ivFirstFun hX hbump hf o.2⟩

/-- **2021 Remark 6.6.19** (p. 276; preprint Remark 6.42) **over `[0, 1] × X`: the natural
orientation of `f̂ = f̃ + S` associated with an orientation `o` of `f` and the standard
orientation of `[0, 1]`**, as an orientation of the section `f̂` in the sense of Definition
6.6.16, for an sc⁺-section `S` of the pull-back of `P` to the M-polyfold with boundary
`[0, 1] × X`: the orientation `e ∧ o` of `f̃` (`ivFirst₀`), read as an orientation of `f̃ + S`
through `Or^{f̃} = Or^{f̃ + S}` (`SectionOrientation.sectionAdd`). -/
def SectionOrientation.ivFirst (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) :
    SectionOrientation (B := ivBundle B)
      (Polyfold.sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) :=
  (SectionOrientation.ivFirst₀ hX hbump hf o).sectionAdd hS

/-- **The orientation `e ∧ o` over `[0, 1] × X` in a product chart**: read in the product chart
`χ_b × φ_c`, for any chart `c` of `X` at `x` and any chart `χ_b` of `[0, 1]` at `t` (`t ↦ t` or
`t ↦ 1 − t`), `ivFirst₀ o` at `(t, x)` is `e ∧ (o_x read in c)` (`ivOrOf`), where `e` is the
direction of increasing `t`: at `L̂(σ, v) = Lv` its value is `e ∧ o(L)`
(`ivOrLift_eq_ivOrFirst₀`, `ChartPoint.ivOrFirst₀_apply`, with `ChartPoint.ivT`). -/
theorem SectionOrientation.toChartOr_ivFirst₀ (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    (z : (Fin 1 → unitInterval) × X) (hz : z ∈ ((cubePolyfold 1).prod PX).smoothSet)
    (b : Fin 1 → Bool) (hb : z.1 ∈ (chart b).source) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (hxc : z.2 ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    toChartOr (hf.paramCube (n := 1)).toIsScFredholmSection hz (ivChart b c q₀)
        (isChart_ivChart b hc q₀) (mem_ivChart_source q₀ hxc hb)
        ((SectionOrientation.ivFirst₀ hX hbump hf o).1 z hz) =
      ivOrOf b hc hxc (prod_cube_mem_smoothSet_iff.1 hz) hb q₀ hf.toIsScFredholmSection
        (hf.paramCube (n := 1)).toIsScFredholmSection
        (ChartPoint.linSet_nonempty _ hf.toIsScFredholmSection
          (prod_cube_mem_smoothSet_iff.1 hz)
          (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump))
        (toChartOr hf.toIsScFredholmSection (prod_cube_mem_smoothSet_iff.1 hz) c hc hxc
          (o.1 z.2 (prod_cube_mem_smoothSet_iff.1 hz))) := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_prod ((cubePolyfold 1).prod PX)
  have := paracompactSpace_rn_pullback (ivBundle B)
  have h := toChartOr_ivFirstFun hf.toIsScFredholmSection
    (hf.paramCube (n := 1)).toIsScFredholmSection
    (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o.1 z hz b hb hc hxc q₀
    (isChart_ivChart b hc q₀) (mem_ivChart_source q₀ hxc hb)
    (ChartPoint.linSet_nonempty _ hf.toIsScFredholmSection
      (prod_cube_mem_smoothSet_iff.1 hz)
      (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump))
  refine h.trans ?_
  rw [ChartPoint.orTransfer_self]
  rfl

end IvMain

end Polyfold
