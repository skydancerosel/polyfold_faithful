import Polyfold.Chapter15.ProductBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, products remark after
**Definition 15.3.3** (pp. 692–693): the levels `[0]` and `[1]` of the product strong bundle
`W × W' → X × X'` (gap G.160 (a), continued).

# The M-polyfolds `(W × W')[0]` and `(W × W')[1]`

## What is formalized

* `StrongBundle.isScSmoothMap_id_prod_zero`, `isScSmoothMap_id_prod_zero_symm`: the identity
  between `(W × W')[0]` (charts `Φ × Φ'` after the swap) and the product M-polyfold
  `W[0] × W'[0]` is sc-smooth in both directions; `isScSmoothMap_prodMap_zero` (products of
  sc-smooth maps of total spaces, on `[0]`).
* `StrongBundleChart.liftOne_prod`, `StrongBundle.mem_oneSet_prod` (`(W × W')_{0,1} =
  W_{0,1} × W'_{0,1}`), `StrongBundle.prodOneHomeomorph` (`(W × W')[1] ≅ W[1] × W'[1]` as
  topological spaces).
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v u' v'

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (X × X')] [ParacompactSpace (Y × Y')]

namespace StrongBundle

variable (B : StrongBundle PX P) (B' : StrongBundle PX' P')

/-! ### Level `[0]` -/

/-- The identity `(W × W')[0] → W[0] × W'[0]` is sc-smooth: in the charts `Φ × Φ'` and
`Φ[0] × Φ'[0]` it is the swap. -/
theorem isScSmoothMap_id_prod_zero :
    (B.prod B').toMPolyfold0.IsScSmoothMap (B.toMPolyfold0.prod B'.toMPolyfold0) id := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ continuousOn_id fun y _ => ?_
  obtain ⟨c, hc, h₁⟩ := B.atlas.cover y.1
  obtain ⟨c', hc', h₂⟩ := B'.atlas.cover y.2
  refine ⟨(c.prod c').toMChart (B.prod B').continuous,
    (c.toMChart B.continuous).prod (c'.toMChart B'.continuous),
    ((c.prod c').toMChart (B.prod B').continuous).source,
    (B.prod B').isChart_toMChart (prod_mem_charts B B' hc hc'),
    (B.isChart_toMChart hc).prod (B'.isChart_toMChart hc'),
    (c.prod c').isOpen_source (B.prod B').continuous, ⟨h₁, h₂⟩, fun z hz => ⟨mem_univ _, hz⟩,
    fun z hz => hz, ?_⟩
  rw [MChart.image_source]
  refine ((ScBanach.bundleSwapOp c.φ.model.E c'.φ.model.E c.F c'.F).isScSmoothRetractMap
    (c.prod c').isScRetract ?_).congr ?_
  · intro k hk
    rw [StrongBundleChart.prod_K] at hk
    exact hk
  · intro k hk
    change k ∈ (c.prod c').K at hk
    rw [StrongBundleChart.prod_K] at hk
    have k₁ : (bundleSwap k).1 ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hk.1
    have k₂ : (bundleSwap k).2 ∈ c'.toPartialEquiv.target := by rw [c'.target_eq]; exact hk.2
    change bundleSwap k = (c (c.toPartialEquiv.symm (bundleSwap k).1),
      c' (c'.toPartialEquiv.symm (bundleSwap k).2))
    rw [show c (c.toPartialEquiv.symm (bundleSwap k).1) = (bundleSwap k).1 from
      c.toPartialEquiv.right_inv k₁, show c' (c'.toPartialEquiv.symm (bundleSwap k).2) =
      (bundleSwap k).2 from c'.toPartialEquiv.right_inv k₂]

/-- The identity `W[0] × W'[0] → (W × W')[0]` is sc-smooth. -/
theorem isScSmoothMap_id_prod_zero_symm :
    (B.toMPolyfold0.prod B'.toMPolyfold0).IsScSmoothMap (B.prod B').toMPolyfold0 id := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ continuousOn_id fun y _ => ?_
  obtain ⟨c, hc, h₁⟩ := B.atlas.cover y.1
  obtain ⟨c', hc', h₂⟩ := B'.atlas.cover y.2
  refine ⟨(c.toMChart B.continuous).prod (c'.toMChart B'.continuous),
    (c.prod c').toMChart (B.prod B').continuous,
    ((c.toMChart B.continuous).prod (c'.toMChart B'.continuous)).source,
    (B.isChart_toMChart hc).prod (B'.isChart_toMChart hc'),
    (B.prod B').isChart_toMChart (prod_mem_charts B B' hc hc'),
    (c.prod c').isOpen_source (B.prod B').continuous, ⟨h₁, h₂⟩, fun z hz => ⟨mem_univ _, hz⟩,
    fun z hz => hz, ?_⟩
  rw [MChart.image_source]
  refine ((ScBanach.bundleSwapOp c.φ.model.E c.F c'.φ.model.E c'.F).isScSmoothRetractMap
    (c.isScRetract.prod c'.isScRetract) ?_).congr ?_
  · intro k hk
    change bundleSwap k ∈ (c.prod c').K
    rw [StrongBundleChart.prod_K]
    exact hk
  · intro k hk
    have k₁ : k.1 ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hk.1
    have k₂ : k.2 ∈ c'.toPartialEquiv.target := by rw [c'.target_eq]; exact hk.2
    change bundleSwap k = bundleSwap (c (c.toPartialEquiv.symm k.1),
      c' (c'.toPartialEquiv.symm k.2))
    rw [show c (c.toPartialEquiv.symm k.1) = k.1 from c.toPartialEquiv.right_inv k₁,
      show c' (c'.toPartialEquiv.symm k.2) = k.2 from c'.toPartialEquiv.right_inv k₂]

/-! ### The set `(W × W')_{0,1}` -/

omit [T2Space Y] [ParacompactSpace Y] [T2Space Y'] [ParacompactSpace Y'] [ParacompactSpace (Y × Y')]
  in
/-- In a product chart, `Φ[1] × Φ'[1]` is the swap of the pair of lifts. -/
lemma _root_.Polyfold.StrongBundleChart.liftOne_prod (c : StrongBundleChart PX P)
    (c' : StrongBundleChart PX' P') {y : Y × Y'} (h₁ : (c y.1).2 ∈ range (c.F.toBase 1))
    (h₂ : (c' y.2).2 ∈ range (c'.F.toBase 1)) :
    (c.prod c').liftOne y = bundleSwap (c.liftOne y.1, c'.liftOne y.2) := by
  change (_, invFun ((c.F.prod c'.F).toBase 1) ((c y.1).2, (c' y.2).2)) = _
  rw [ScBanach.invFun_prod_toBase_one h₁ h₂]
  rfl

/-- `(W × W')_{0,1} = W_{0,1} × W'_{0,1}`. -/
theorem mem_oneSet_prod {y : Y × Y'} :
    y ∈ (B.prod B').oneSet ↔ y.1 ∈ B.oneSet ∧ y.2 ∈ B'.oneSet := by
  obtain ⟨c, hc, h₁⟩ := B.atlas.cover y.1
  obtain ⟨c', hc', h₂⟩ := B'.atlas.cover y.2
  rw [(B.prod B').mem_oneSet_iff (prod_mem_charts B B' hc hc') ⟨h₁, h₂⟩, B.mem_oneSet_iff hc h₁,
    B'.mem_oneSet_iff hc' h₂]
  exact ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)

/-! ### Level `[1]`: `(W × W')[1] ≅ W[1] × W'[1]` -/

/-- The map `(W × W')[1] → W[1] × W'[1]`. -/
def prodOneFst (y : (B.prod B').One) : B.One × B'.One :=
  (B.oneMk ((B.prod B').oneVal y).1 ((B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem y)).1,
    B'.oneMk ((B.prod B').oneVal y).2 ((B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem y)).2)

/-- The map `W[1] × W'[1] → (W × W')[1]`. -/
def prodOneSnd (z : B.One × B'.One) : (B.prod B').One :=
  (B.prod B').oneMk (B.oneVal z.1, B'.oneVal z.2)
    ((B.mem_oneSet_prod B').2 ⟨B.oneVal_mem z.1, B'.oneVal_mem z.2⟩)

/-- `y ↦ Φ[1](y)` is continuous on the chart domain in `W[1]`. -/
lemma continuousOn_liftOne {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) :
    ContinuousOn (fun y : B.One => c.liftOne (B.oneVal y))
      {y : B.One | B.oneVal y ∈ c.toPartialEquiv.source} := by
  rw [continuousOn_iff']
  intro W hW
  refine ⟨{y : B.One | B.oneVal y ∈ c.toPartialEquiv.source ∧ c.liftOne (B.oneVal y) ∈ W},
    B.isOpen_one_basic hc hW, ?_⟩
  ext y
  exact ⟨fun h => ⟨⟨h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

lemma isOpen_one_source {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) :
    IsOpen {y : B.One | B.oneVal y ∈ c.toPartialEquiv.source} := by
  have := B.isOpen_one_basic hc (W := univ) isOpen_univ
  simpa using this

theorem continuous_prodOneFst : Continuous (B.prodOneFst B') := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨c, hc, W, hW, rfl⟩
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy₁, hyW⟩
    obtain ⟨c', hc', hy₂⟩ := B'.atlas.cover ((B.prod B').oneVal y).2
    have hm := (B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem y)
    have hW' : IsOpen (bundleSwap ⁻¹' (W ×ˢ (univ : Set ((c'.φ.model.E.prod c'.F.shift) 0)))) :=
      (hW.prod isOpen_univ).preimage continuous_bundleSwap
    refine ⟨_, ?_, (B.prod B').isOpen_one_basic (prod_mem_charts B B' hc hc') hW',
      ⟨⟨hy₁, hy₂⟩, ?_⟩⟩
    · rintro z ⟨⟨hz₁, hz₂⟩, hzW⟩
      have hm' := (B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem z)
      rw [StrongBundleChart.liftOne_prod c c' ((B.mem_oneSet_iff hc hz₁).1 hm'.1)
        ((B'.mem_oneSet_iff hc' hz₂).1 hm'.2)] at hzW
      exact ⟨hz₁, hzW.1⟩
    · rw [StrongBundleChart.liftOne_prod c c' ((B.mem_oneSet_iff hc hy₁).1 hm.1)
        ((B'.mem_oneSet_iff hc' hy₂).1 hm.2)]
      exact ⟨hyW, mem_univ _⟩
  · refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨c', hc', W, hW, rfl⟩
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hy₂, hyW⟩
    obtain ⟨c, hc, hy₁⟩ := B.atlas.cover ((B.prod B').oneVal y).1
    have hm := (B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem y)
    have hW' : IsOpen (bundleSwap ⁻¹' ((univ : Set ((c.φ.model.E.prod c.F.shift) 0)) ×ˢ W)) :=
      (isOpen_univ.prod hW).preimage continuous_bundleSwap
    refine ⟨_, ?_, (B.prod B').isOpen_one_basic (prod_mem_charts B B' hc hc') hW',
      ⟨⟨hy₁, hy₂⟩, ?_⟩⟩
    · rintro z ⟨⟨hz₁, hz₂⟩, hzW⟩
      have hm' := (B.mem_oneSet_prod B').1 ((B.prod B').oneVal_mem z)
      rw [StrongBundleChart.liftOne_prod c c' ((B.mem_oneSet_iff hc hz₁).1 hm'.1)
        ((B'.mem_oneSet_iff hc' hz₂).1 hm'.2)] at hzW
      exact ⟨hz₂, hzW.2⟩
    · rw [StrongBundleChart.liftOne_prod c c' ((B.mem_oneSet_iff hc hy₁).1 hm.1)
        ((B'.mem_oneSet_iff hc' hy₂).1 hm.2)]
      exact ⟨mem_univ _, hyW⟩

theorem continuous_prodOneSnd : Continuous (B.prodOneSnd B') := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨χ, ⟨c, hc, c', hc', rfl⟩, W, hW, rfl⟩
  set S : Set (B.One × B'.One) :=
    {y : B.One | B.oneVal y ∈ c.toPartialEquiv.source} ×ˢ
      {y : B'.One | B'.oneVal y ∈ c'.toPartialEquiv.source}
  have hS : IsOpen S := (B.isOpen_one_source hc).prod (B'.isOpen_one_source hc')
  have hg : ContinuousOn (fun z : B.One × B'.One =>
      bundleSwap (c.liftOne (B.oneVal z.1), c'.liftOne (B'.oneVal z.2))) S :=
    continuous_bundleSwap.comp_continuousOn
      (((B.continuousOn_liftOne hc).comp continuous_fst.continuousOn fun _ hz => hz.1).prodMk
        ((B'.continuousOn_liftOne hc').comp continuous_snd.continuousOn fun _ hz => hz.2))
  convert hg.isOpen_inter_preimage hS hW using 1
  ext z
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hW⟩
    have h₁' : B.oneVal z.1 ∈ c.toPartialEquiv.source := h₁
    have h₂' : B'.oneVal z.2 ∈ c'.toPartialEquiv.source := h₂
    refine ⟨⟨h₁', h₂'⟩, ?_⟩
    change (c.prod c').liftOne (B.oneVal z.1, B'.oneVal z.2) ∈ W at hW
    rwa [StrongBundleChart.liftOne_prod c c' (y := (B.oneVal z.1, B'.oneVal z.2))
      ((B.mem_oneSet_iff hc h₁').1 (B.oneVal_mem z.1))
      ((B'.mem_oneSet_iff hc' h₂').1 (B'.oneVal_mem z.2))] at hW
  · rintro ⟨⟨h₁, h₂⟩, hW⟩
    have h₁' : B.oneVal z.1 ∈ c.toPartialEquiv.source := h₁
    have h₂' : B'.oneVal z.2 ∈ c'.toPartialEquiv.source := h₂
    refine ⟨⟨h₁', h₂'⟩, ?_⟩
    change (c.prod c').liftOne (B.oneVal z.1, B'.oneVal z.2) ∈ W
    rwa [StrongBundleChart.liftOne_prod c c' (y := (B.oneVal z.1, B'.oneVal z.2))
      ((B.mem_oneSet_iff hc h₁').1 (B.oneVal_mem z.1))
      ((B'.mem_oneSet_iff hc' h₂').1 (B'.oneVal_mem z.2))]

/-- **`(W × W')[1] ≅ W[1] × W'[1]`** as topological spaces. -/
def prodOneHomeomorph : (B.prod B').One ≃ₜ B.One × B'.One where
  toFun := B.prodOneFst B'
  invFun := B.prodOneSnd B'
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := B.continuous_prodOneFst B'
  continuous_invFun := B.continuous_prodOneSnd B'

@[simp] lemma oneVal_prodOneHomeomorph_fst (y : (B.prod B').One) :
    B.oneVal (B.prodOneHomeomorph B' y).1 = ((B.prod B').oneVal y).1 := rfl

@[simp] lemma oneVal_prodOneHomeomorph_snd (y : (B.prod B').One) :
    B'.oneVal (B.prodOneHomeomorph B' y).2 = ((B.prod B').oneVal y).2 := rfl

omit [ParacompactSpace (X × X')] [ParacompactSpace (Y × Y')] in
/-- `W[1] × W'[1]` is paracompact (both factors are metrizable). -/
theorem paracompactSpace_prod_one : ParacompactSpace (B.One × B'.One) :=
  MPolyfold.paracompactSpace_prod B.toMPolyfold1 B'.toMPolyfold1

omit [T2Space Y] [ParacompactSpace Y] [T2Space Y'] [ParacompactSpace Y']
  [ParacompactSpace (Y × Y')] in
lemma _root_.Polyfold.StrongBundleChart.mem_strongShiftOne_prod_K (c : StrongBundleChart PX P)
    (c' : StrongBundleChart PX' P') {z : ((c.prod c').φ.model.E.prod (c.prod c').F.shift) 0} :
    z ∈ strongShiftOne (c.prod c').K ↔
      bundleSwap z ∈ strongShiftOne c.K ×ˢ strongShiftOne c'.K := by
  change z ∈ strongShiftOne (E := c.φ.model.E.prod c'.φ.model.E) (F := c.F.prod c'.F)
    (c.prod c').K ↔ _
  rw [StrongBundleChart.prod_K, strongShiftOne_bundleSwap_preimage]
  rfl

/-- The map `(W × W')[1] → W[1] × W'[1]` is sc-smooth (in the charts `(Φ × Φ')[1]` and
`Φ[1] × Φ'[1]` it is the swap). -/
theorem isScSmoothMap_prodOneHomeomorph :
    haveI := B.paracompactSpace_prod_one B'
    (B.prod B').toMPolyfold1.IsScSmoothMap (B.toMPolyfold1.prod B'.toMPolyfold1)
      (B.prodOneHomeomorph B') := by
  have := B.paracompactSpace_prod_one B'
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (B.prodOneHomeomorph B').continuous.continuousOn fun y _ => ?_
  obtain ⟨c, hc, h₁⟩ := B.atlas.cover ((B.prod B').oneVal y).1
  obtain ⟨c', hc', h₂⟩ := B'.atlas.cover ((B.prod B').oneVal y).2
  have hχ := prod_mem_charts B B' hc hc'
  set y₁ := (B.prodOneHomeomorph B' y).1
  set y₂ := (B.prodOneHomeomorph B' y).2
  refine ⟨oneChart hχ y, (oneChart hc y₁).prod (oneChart hc' y₂), (oneChart hχ y).source,
    (B.prod B').isChart_oneChart hχ y, (B.isChart_oneChart hc y₁).prod (B'.isChart_oneChart hc' y₂),
    (oneChart hχ y).isOpen_source, ⟨h₁, h₂⟩, fun z hz => ⟨mem_univ _, hz⟩,
    fun z hz => hz, ?_⟩
  rw [(oneChart hχ y).image_source]
  refine ((ScBanach.bundleSwapOp c.φ.model.E c'.φ.model.E c.F.shift c'.F.shift).isScSmoothRetractMap
    (c.prod c').isScRetract_one fun k hk =>
      (StrongBundleChart.mem_strongShiftOne_prod_K c c').1 hk).congr ?_
  intro k hk
  have hk' := (StrongBundleChart.mem_strongShiftOne_prod_K c c').1 hk
  have hv := oneChart_symm_apply hχ y hk
  change bundleSwap k = (c.liftOne ((B.prod B').oneVal ((oneChart hχ y).symm k)).1,
    c'.liftOne ((B.prod B').oneVal ((oneChart hχ y).symm k)).2)
  rw [hv]
  exact Prod.ext (liftOne_symm hk'.1).symm (liftOne_symm hk'.2).symm

/-- The map `W[1] × W'[1] → (W × W')[1]` is sc-smooth. -/
theorem isScSmoothMap_prodOneHomeomorph_symm :
    haveI := B.paracompactSpace_prod_one B'
    (B.toMPolyfold1.prod B'.toMPolyfold1).IsScSmoothMap (B.prod B').toMPolyfold1
      (B.prodOneHomeomorph B').symm := by
  have := B.paracompactSpace_prod_one B'
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (B.prodOneHomeomorph B').symm.continuous.continuousOn fun z _ => ?_
  obtain ⟨c, hc, h₁⟩ := B.atlas.cover (B.oneVal z.1)
  obtain ⟨c', hc', h₂⟩ := B'.atlas.cover (B'.oneVal z.2)
  have hχ := prod_mem_charts B B' hc hc'
  set y := (B.prodOneHomeomorph B').symm z
  refine ⟨(oneChart hc z.1).prod (oneChart hc' z.2), oneChart hχ y,
    ((oneChart hc z.1).prod (oneChart hc' z.2)).source,
    (B.isChart_oneChart hc z.1).prod (B'.isChart_oneChart hc' z.2),
    (B.prod B').isChart_oneChart hχ y,
    ((oneChart hc z.1).prod (oneChart hc' z.2)).isOpen_source, ⟨h₁, h₂⟩,
    fun w hw => ⟨mem_univ _, hw⟩, fun w hw => hw, ?_⟩
  rw [((oneChart hc z.1).prod (oneChart hc' z.2)).image_source]
  refine ((ScBanach.bundleSwapOp c.φ.model.E c.F.shift c'.φ.model.E c'.F.shift).isScSmoothRetractMap
    (c.isScRetract_one.prod c'.isScRetract_one) fun k hk =>
      (StrongBundleChart.mem_strongShiftOne_prod_K c c').2 hk).congr ?_
  intro k hk
  have v₁ := oneChart_symm_apply hc z.1 hk.1
  have v₂ := oneChart_symm_apply hc' z.2 hk.2
  have m₁ := c.toPartialEquiv.map_target (show (k.1.1, c.F.toBase 1 k.1.2) ∈
    c.toPartialEquiv.target by rw [c.target_eq]; exact hk.1)
  have m₂ := c'.toPartialEquiv.map_target (show (k.2.1, c'.F.toBase 1 k.2.2) ∈
    c'.toPartialEquiv.target by rw [c'.target_eq]; exact hk.2)
  change bundleSwap k = (c.prod c').liftOne
    (B.oneVal ((oneChart hc z.1).symm k.1), B'.oneVal ((oneChart hc' z.2).symm k.2))
  rw [v₁, v₂, StrongBundleChart.liftOne_prod c c' (y := (_, _))
    (by rw [c.toPartialEquiv.right_inv (by rw [c.target_eq]; exact hk.1)]; exact ⟨_, rfl⟩)
    (by rw [c'.toPartialEquiv.right_inv (by rw [c'.target_eq]; exact hk.2)]; exact ⟨_, rfl⟩),
    liftOne_symm hk.1, liftOne_symm hk.2]

end StrongBundle

end Polyfold
