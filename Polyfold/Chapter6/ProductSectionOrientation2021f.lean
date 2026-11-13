import Polyfold.Chapter6.ProductSectionOrientation2021e

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230): the orientation of `f̂(x, t) = f(x) + s(x, t)`
over `X × [0, 1]` given by an orientation `o` of `f`, as an orientation of the section `f̂`
(Definition 6.6.16).

# `SectionOrientation.prodFirst`

## What is formalized

* `ChartPoint.orTransfer_prodPt_prodOrFirst₀`, `prodOrOf_orTransfer`: the product orientation
  `e ∧ o` of `f̃` does not depend on the chart of `X`.
* `prodFirstFun o`: the map `(t, x) ↦ e ∧ o_x ∈ Or^{f̃}_{(t, x)}`; `toChartOr_prodFirstFun`: read
  in any chart of `ℝ¹ × X`, it is the transfer of `e ∧ o_x` read in the product chart over any
  chart of `X`.
* `isSectionOrientation_prodFirstFun`: **`(t, x) ↦ e ∧ o_x` is an orientation of `f̃`**
  (Definition 6.6.16) when `o` is an orientation of `f`.
* `SectionOrientation.prodFirst₀ o` (the orientation of `f̃`) and
  **`SectionOrientation.prodFirst o hS`** (the orientation of `f̂ = f̃ + S`, 2021 Remark 6.6.19).
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

section Indep

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **The product orientation of `f̃` does not depend on the chart of `X`**
(`orTransfer_prodPt_prodOrFirst` for the zero section, through `Lin(f̃ + 0) = Lin(f̃)`). -/
theorem orTransfer_prodPt_prodOrFirst₀ (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f).Nonempty) (o : p.Or f hf) :
    (p.prodPt t q₀).orTransfer (p'.prodPt t q₀') hf.param (prod_rn_mem_smoothSet_iff.2 hx)
        (p.prodOrFirst₀ t q₀ hf hx hne o) =
      p'.prodOrFirst₀ t q₀' hf hx hne' (p.orTransfer p' hf hx o) :=
  (LineOrientation.conj_congrDetOn _ _ _ _ _ _ _ _ _ _ _).trans
    (congrArg ((p'.prodPt t q₀').orCongr (theorem_3_1_18_preprint hf.param
        (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B))) hf.param
      (p'.linSet_paramLift_add_zero t q₀' hf))
      (p.orTransfer_prodPt_prodOrFirst p' t q₀ q₀' hf hx
        (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B)) hne o))

end ChartPoint

/-- `prodOrLift` does not depend on the chart of `X`. -/
theorem prodOrLift_orTransfer {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') {x : X} (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x) (w : c'.φ.model.E 1)
    (hw : c'.φ.model.E.toBase 1 w = c'.φ x) (t : Fin 1 → ℝ)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hxc : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c q₀).φ.source)
    (z' : (prodChart c q₀).φ.model.E 1)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 z' = (prodChart c q₀).φ (t, x))
    (hzz : z' = (t, z))
    (hxc' : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c' q₀').φ.source)
    (w' : (prodChart c' q₀').φ.model.E 1)
    (hw' : (prodChart c' q₀').φ.model.E.toBase 1 w' = (prodChart c' q₀').φ (t, x))
    (hww : w' = (t, w)) (hf : B.IsScFredholmSection f) (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty)
    (hne' : ((chartPt c' hc' hx' w hw).linSet f).Nonempty)
    (o : (chartPt c hc hx z hz).Or f hf) :
    (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z' hz').orTransfer
        (chartPt (B := prodBundle B) (prodChart c' q₀') (isChart_prodChart hc' q₀') hxc' w' hw')
        hf.param (prod_rn_mem_smoothSet_iff.2 hxs)
        (prodOrLift hc hx z hz t q₀ hxc z' hz' hzz hf hxs hne o) =
      prodOrLift hc' hx' w hw t q₀' hxc' w' hw' hww hf hxs hne'
        ((chartPt c hc hx z hz).orTransfer (chartPt c' hc' hx' w hw) hf hxs o) := by
  subst hzz hww
  exact (chartPt c hc hx z hz).orTransfer_prodPt_prodOrFirst₀ (chartPt c' hc' hx' w hw) t q₀ q₀'
    hf hxs hne hne' o

end Indep

/-! ### The map `(t, x) ↦ e ∧ o_x` and its continuity -/

section Assembly

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

omit [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- The local propagation property passes to subsets. -/
theorem HasLocalPropagation.mono {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {U U' : Set X} (h : HasLocalPropagation f hf c hc U) (hU : U' ⊆ U) :
    HasLocalPropagation f hf c hc U' where
  subset := hU.trans h.subset
  exists_isPush γ hγs hγ _ _ h₀ h₁ hx₀ hx₁ hs₀ hs₁ :=
    h.exists_isPush γ hγs (fun q hq => hU (hγ q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁
  eq γ₀ γ₁ hγ₀s hγ₁s hγ₀ hγ₁ _ _ h₀₀ h₀₁ h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁ :=
    h.eq γ₀ γ₁ hγ₀s hγ₁s (fun q hq => hU (hγ₀ q hq)) (fun q hq => hU (hγ₁ q hq)) h₀₀ h₀₁ h₁₀ h₁₁
      hx₀ hx₁ hs₀ hs₁ e₀ e₁ he₀ he₁

omit [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- **`prodOrOf` does not depend on the chart of `X`.** -/
theorem prodOrOf_orTransfer {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') {x : X} (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source)
    (hs : x ∈ PX.smoothSet) (t : Fin 1 → ℝ)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) (hf : B.IsScFredholmSection f)
    (hne : ((chartPtOf c hc hx hs).linSet f).Nonempty)
    (hne' : ((chartPtOf c' hc' hx' hs).linSet f).Nonempty) (o : (chartPtOf c hc hx hs).Or f hf) :
    (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
        (mem_prodChart_source q₀ hx t) (prod_rn_mem_smoothSet_iff.2 hs)).orTransfer
        (chartPtOf (B := prodBundle B) (prodChart c' q₀') (isChart_prodChart hc' q₀')
          (mem_prodChart_source q₀' hx' t) (prod_rn_mem_smoothSet_iff.2 hs)) hf.param
        (prod_rn_mem_smoothSet_iff.2 hs) (prodOrOf hc hx hs t q₀ hf hne o) =
      prodOrOf hc' hx' hs t q₀' hf hne'
        ((chartPtOf c hc hx hs).orTransfer (chartPtOf c' hc' hx' hs) hf hs o) :=
  prodOrLift_orTransfer hc hc' hx hx' _ _ _ _ t q₀ q₀' _ _ _ _ _ _ _ _ hf hs hne hne' o

/-- **The map `(t, x) ↦ e ∧ o_x`** (2021 Remark 6.6.19): for a map `y ↦ o_y ∈ Or_y^f`, the
product orientation of `f̃` at `(t, x)`, made in the product chart over the chosen chart of `X`
at `x` and read in the chosen chart of `ℝ¹ × X` at `(t, x)`. -/
def prodFirstFun (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) :
    ∀ z (hz : z ∈ ((rnPolyfold 1).prod PX).smoothSet),
      Orx (B := prodBundle B) (paramLift (n := 1) f hf.isScSmooth.1) hf.param z hz :=
  fun z hz => (toChartOr hf.param hz
      (prodChart (orChart B z.2) (paramLift (n := 1) f hf.isScSmooth.1 z))
      (isChart_prodChart (isChart_orChart z.2) _)
      (mem_prodChart_source _ (mem_orChart z.2) z.1)).symm
    (prodOrOf (isChart_orChart z.2) (mem_orChart z.2) (prod_rn_mem_smoothSet_iff.1 hz) z.1 _ hf
      (ChartPoint.linSet_nonempty _ hf (prod_rn_mem_smoothSet_iff.1 hz) hsec)
      (o z.2 (prod_rn_mem_smoothSet_iff.1 hz)))

omit [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- **`(t, x) ↦ e ∧ o_x` read in a chart `c'` of `ℝ¹ × X`** is the transfer to `c'` of
`e ∧ (o_x read in c)` made in the product chart over any chart `c` of `X` at `x`
(`prodOrOf_orTransfer`). -/
theorem toChartOr_prodFirstFun (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (z : (Fin 1 → ℝ) × X) (hz : z ∈ ((rnPolyfold 1).prod PX).smoothSet)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : z.2 ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    {c' : StrongBundleChart ((rnPolyfold 1).prod PX) (pullbackProj P Prod.snd)}
    (hc' : (prodBundle B).IsChart c') (hz' : z ∈ c'.φ.source)
    (hne : ((chartPtOf c hc hxc (prod_rn_mem_smoothSet_iff.1 hz)).linSet f).Nonempty) :
    toChartOr hf.param hz c' hc' hz' (prodFirstFun hf hsec o z hz) =
      (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
        (mem_prodChart_source q₀ hxc z.1) hz).orTransfer (chartPtOf c' hc' hz' hz) hf.param hz
        (prodOrOf hc hxc (prod_rn_mem_smoothSet_iff.1 hz) z.1 q₀ hf hne
          (toChartOr hf (prod_rn_mem_smoothSet_iff.1 hz) c hc hxc
            (o z.2 (prod_rn_mem_smoothSet_iff.1 hz)))) := by
  have hs := prod_rn_mem_smoothSet_iff.1 hz
  have hne₀ := ChartPoint.linSet_nonempty (chartPtOf (orChart B z.2) (isChart_orChart z.2)
    (mem_orChart z.2) hs) hf hs hsec
  have h1 := toChartOr_eq_orTransfer hf.param hz (prodFirstFun hf hsec o z hz)
    (isChart_prodChart (isChart_orChart z.2) (paramLift (n := 1) f hf.isScSmooth.1 z)) hc'
    (mem_prodChart_source _ (mem_orChart z.2) z.1) hz'
  have h2 := prodOrOf_orTransfer (isChart_orChart z.2) hc (mem_orChart z.2) hxc hs z.1
    (paramLift (n := 1) f hf.isScSmooth.1 z) q₀ hf hne₀ hne (o z.2 hs)
  have h3 := ChartPoint.orTransfer_trans
    (chartPtOf (B := prodBundle B) (prodChart (orChart B z.2)
      (paramLift (n := 1) f hf.isScSmooth.1 z)) (isChart_prodChart (isChart_orChart z.2) _)
      (mem_prodChart_source _ (mem_orChart z.2) z.1) hz)
    (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
      (mem_prodChart_source q₀ hxc z.1) hz) (chartPtOf c' hc' hz' hz) hf.param hz
  refine h1.trans ?_
  refine (congrArg _ (Equiv.apply_symm_apply _ _)).trans ?_
  refine (DFunLike.congr_fun h3 _).symm.trans ?_
  exact congrArg ((chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
    (mem_prodChart_source q₀ hxc z.1) hz).orTransfer (chartPtOf c' hc' hz' hz) hf.param hz) h2

/-- **`(t, x) ↦ e ∧ o_x` is an orientation of `f̃`** (2021 Remark 6.6.19 and Definition 6.6.16)
when `o` is an orientation of `f`: over an orientable neighbourhood of `f̃` inside `ℝ × V` for an
orientable neighbourhood `V ⊆ U` of `f`, a push-forward of `f̃` along `γ` is the transfer of the
lift of a push-forward of `f` along `pr₂ ∘ γ` (`IsPush.prodLift`, `IsPush.transfer`, the
uniqueness of local push-forwards), which carries `e ∧ o` to `e ∧ o`. -/
theorem isSectionOrientation_prodFirstFun (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o) :
    IsSectionOrientation (B := prodBundle B) (paramLift (n := 1) f hf.isScSmooth.1)
      hf.toIsScFredholmSection.param
      (prodFirstFun hf.toIsScFredholmSection
        (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o) := by
  have hsec : B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump
  have hX' : ((rnPolyfold 1).prod PX).IsTame := prod_rn_isTame hX
  have hbump' : ((rnPolyfold 1).prod PX).AdmitsBumpFunctions :=
    MPolyfold.admitsBumpFunctions_prod_rn hbump
  have hsec' : (prodBundle B).HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump'
  have := paracompactSpace_rn_rn_prod ((rnPolyfold 1).prod PX)
  have := paracompactSpace_rn_rn_pullback (prodBundle B)
  refine (isSectionOrientation_iff hX' hbump' hf.param hsec' _).2 fun x y a =>
    orFunctorMap_apply_eq_of_local hX' hbump' hf.param hsec' _ (fun z hz => ?_) a
  have hs := prod_rn_mem_smoothSet_iff.1 hz
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hf hs
  obtain ⟨c', hc', U', V', hN'⟩ := exists_isOrientableNbhd hX' hbump' hf.param hz
  have hUc := hN.hasLocalPropagation.subset
  have hU''o : IsOpen (U' ∩ Prod.snd ⁻¹' V) :=
    hN'.isOpen_U.inter (hN.isOpen_V.preimage continuous_snd)
  have hLP := hN'.hasLocalPropagation.mono (inter_subset_left : U' ∩ Prod.snd ⁻¹' V ⊆ U')
  obtain ⟨V'', hV''o, hzV'', hV''U'', hpath⟩ :=
    exists_nhds_scPath hc' hU''o hLP.subset ⟨hN'.subset hN'.mem, hN.mem⟩
  refine ⟨c', hc', U' ∩ Prod.snd ⁻¹' V, V'', ⟨hLP, hU''o, hV''o, hV''U'', hzV'', hpath⟩, ?_⟩
  intro γ hγs hγ y₁ y₂ hy₁ hy₂ hs₁ hs₂ h₀ h₁ e' he'
  have q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
    paramLift (n := 1) f hf.isScSmooth.1 z
  have hγs' : (rnPolyfold 1).IsScSmoothMap PX (Prod.snd ∘ γ) :=
    (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX).comp hγs
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (γ q).2 ∈ V := fun q hq => (hγ q hq).2
  have hx₁ : y₁.2 ∈ V := (hV''U'' hy₁).2
  have hx₂ : y₂.2 ∈ V := (hV''U'' hy₂).2
  have hxs₁ := prod_rn_mem_smoothSet_iff.1 hs₁
  have hxs₂ := prod_rn_mem_smoothSet_iff.1 hs₂
  have hne₁ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset hx₁)) hxs₁)
    hf.toIsScFredholmSection hxs₁ hsec
  have hne₂ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset hx₂)) hxs₂)
    hf.toIsScFredholmSection hxs₂ hsec
  obtain ⟨e, he⟩ := hN.hasLocalPropagation.exists_isPush (Prod.snd ∘ γ) hγs'
    (fun q hq => hN.subset (hγV q hq)) (congrArg Prod.snd h₀) (congrArg Prod.snd h₁)
    (hUc (hN.subset hx₁)) (hUc (hN.subset hx₂)) hxs₁ hxs₂
  have hcont := ho z.2 hs c hc U V hN (Prod.snd ∘ γ) hγs' (fun q hq => hN.subset (hγV q hq))
    hx₁ hx₂ hxs₁ hxs₂ (congrArg Prod.snd h₀) (congrArg Prod.snd h₁) e he
  obtain ⟨e₂, he₂, he₂o⟩ := he.prodLift (fun q => (γ q).1) q₀ (congrArg Prod.fst h₀)
    (congrArg Prod.fst h₁) hne₁ hne₂
  have ht := IsPush.transfer (isChart_prodChart hc q₀) hc' hγs
    (fun q hq => mem_prodChart_source q₀ (hUc (hN.subset (hγV q hq))) (γ q).1)
    (fun q hq => hLP.subset (hγ q hq)) h₀ h₁
    (mem_prodChart_source q₀ (hUc (hN.subset hx₁)) y₁.1)
    (mem_prodChart_source q₀ (hUc (hN.subset hx₂)) y₂.1)
    (hLP.subset (hV''U'' hy₁)) (hLP.subset (hV''U'' hy₂)) hs₁ hs₂ he₂
  have heq := hLP.eq γ γ hγs hγs hγ hγ h₀ h₁ h₀ h₁ (hLP.subset (hV''U'' hy₁))
    (hLP.subset (hV''U'' hy₂)) hs₁ hs₂ e' _ he' ht
  have k₁ := toChartOr_prodFirstFun hf.toIsScFredholmSection hsec o y₁ hs₁ hc
    (hUc (hN.subset hx₁)) q₀ hc' (hLP.subset (hV''U'' hy₁)) hne₁
  have k₂ := toChartOr_prodFirstFun hf.toIsScFredholmSection hsec o y₂ hs₂ hc
    (hUc (hN.subset hx₂)) q₀ hc' (hLP.subset (hV''U'' hy₂)) hne₂
  subst heq
  refine (congrArg (fun w => ((chartPtOf (B := prodBundle B) (prodChart c q₀)
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ (hUc (hN.subset hx₂)) y₂.1)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂)
      hf.toIsScFredholmSection.param hs₂)
      (e₂ (((chartPtOf (B := prodBundle B) (prodChart c q₀)
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ (hUc (hN.subset hx₁)) y₁.1)
    hs₁).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₁)) hs₁)
      hf.toIsScFredholmSection.param hs₁).symm w)))
    k₁).trans ?_
  refine (congrArg (fun w => ((chartPtOf (B := prodBundle B) (prodChart c q₀)
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ (hUc (hN.subset hx₂)) y₂.1)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂)
      hf.toIsScFredholmSection.param hs₂) (e₂ w))
    (Equiv.symm_apply_apply _ _)).trans ?_
  exact (congrArg ((chartPtOf (B := prodBundle B) (prodChart c q₀)
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ (hUc (hN.subset hx₂)) y₂.1)
    hs₂).orTransfer (chartPtOf c' hc' (hLP.subset (hV''U'' hy₂)) hs₂)
      hf.toIsScFredholmSection.param hs₂) ((he₂o _).trans (congrArg _ hcont))).trans k₂.symm

end Assembly

/-! ### The orientation of `f̂ = f̃ + S` -/

section Main

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

/-- **The orientation `e ∧ o` of `f̃(t, x) = f(x)` over `ℝ¹ × X`** (2021 Remark 6.6.19, p. 276,
for `s = 0`; Definition 6.6.16): `(t, x) ↦ e ∧ o_x` (`prodFirstFun`), for an orientation `o` of
a tame `f` over a tame `X` with sc-smooth bump functions (`isSectionOrientation_prodFirstFun`). -/
def SectionOrientation.prodFirst₀ (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection) :
    SectionOrientation (B := prodBundle B) (paramLift (n := 1) f hf.isScSmooth.1)
      hf.toIsScFredholmSection.param :=
  haveI := paracompactSpace_rn_prod PX
  haveI := paracompactSpace_rn_pullback B
  haveI := paracompactSpace_rn_rn_prod PX
  haveI := paracompactSpace_rn_rn_pullback B
  ⟨prodFirstFun hf.toIsScFredholmSection
      (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o.1,
    isSectionOrientation_prodFirstFun hX hbump hf o.2⟩

/-- **2021 Remark 6.6.19** (p. 276; preprint Remark 6.42): **the natural orientation of
`f̂ = f̃ + S` over `ℝ¹ × X` associated with an orientation `o` of `f`**, as an orientation of the
section `f̂` in the sense of Definition 6.6.16: the orientation `e ∧ o` of `f̃`
(`prodFirst₀`), read as an orientation of `f̃ + S` through `Or^{f̃} = Or^{f̃ + S}`
(`SectionOrientation.sectionAdd`). The text's `X × [0, 1]` is `ℝ¹ × X`, the parameter first; `hX`
and `hbump` are the hypotheses of `theorem_6_6_18_oriented`. -/
def SectionOrientation.prodFirst (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (prodBundle B).IsScPlusSection S) :
    SectionOrientation (B := prodBundle B)
      (Polyfold.sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f hf.isScSmooth.1) S)
      (theorem_3_1_18_preprint hf.toIsScFredholmSection.param hS) :=
  (SectionOrientation.prodFirst₀ hX hbump hf o).sectionAdd hS

end Main

end Polyfold
