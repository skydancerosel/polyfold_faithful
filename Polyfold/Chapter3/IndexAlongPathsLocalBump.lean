import Polyfold.Chapter3.IndexAlongPathsLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.1,
**Definition 6.2.1 (preprint 6.1)**: with sc-smooth bump functions, the reading with a locally defined
sc⁺-section (`IsIndexAtLocal`, `IndexAlongPathsLocal.lean`) agrees with the reading with a
global one (`IsIndexAt`, `IndexAlongPaths.lean`).  Round-trip item V3.98 (a); Findings, Chapter 3,
items 364 and 367.

# Definition 6.2.1 (preprint 6.1): local and global sections agree under bump functions

## What is formalized

* `Polyfold.StrongBundle.cutoffSection_mem_oneSet_of_isChart`,
  `StrongBundle.isScPlusSection_cutoffSection_of_isChart`: the cut-off of a local sc⁺-section
  (`cutoffSection`, Lemma 5.3.3 (preprint 5.11)) in a strong bundle chart of `P` which need not belong to the
  atlas (`IsChart`; through the chart `oneChartOf` of `Y[1]`).
* `Polyfold.StrongBundle.IsIndexAtLocal.isIndexAt` (**with bump functions, a local section of
  Definition 6.2.1 (preprint 6.1) gives a global one**): the local section `s` on `V` is restricted to
  `W = dom φ ∩ V` for a chart `φ` around `x`, read as `τ : O → F¹` in that chart, cut off by a bump
  `β` supported in `W` and equal to `1` near `x`; `f + β τ` vanishes at `x` and its linearization
  at `x` has the index of `(f|W + s)'(x)`, since the two sections agree where `β = 1`
  (`linAt_congr` in the chart restricted to that set, and the germ datum of `f + β τ` at `x`).
* `Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt` (**the two readings of Definition 6.2.1 (preprint 6.1)
  agree under bump functions**).

## What the text leaves implicit, and the choices made

* The text's "local sc⁺-section" and the global sections of Chapter 5 are never compared; the
  comparison needs the bump functions of Definition 5.3.1 (preprint 5.9) (the cut-off) and is only valid with them.
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

section CutoffIsChart

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {c : StrongBundleChart PX P} {β : X → ℝ} {τ : c.φ.model.E 0 → c.F 1}

/-- The cut-off section takes values in `Y_{0,1}` (for a chart of `P`, `mem_oneSet_iff_of_isChart`). -/
lemma cutoffSection_mem_oneSet_of_isChart (hc : B.IsChart c)
    (hτ : MapsTo (fun z => (z, τ z)) c.φ.model.O (strongShiftOne c.K)) (y : X) :
    cutoffSection c β τ y ∈ B.oneSet := by
  by_cases hy : y ∈ c.φ.source
  · rw [mem_oneSet_iff_of_isChart hc (cutoffSection_mem_source hτ hy),
      apply_cutoffSection hτ hy]
    exact ⟨_, rfl⟩
  · rw [cutoffSection, if_neg hy]; exact B.fiberZero_mem_oneSet y

/-- **The cut-off of a local sc⁺-section in a strong bundle chart of `P` is an sc⁺-section**
(`isScPlusSection_cutoffSection` for a chart compatible with the atlas, through `oneChartOf`). -/
theorem isScPlusSection_cutoffSection_of_isChart (hc : B.IsChart c)
    (hβ : PX.IsScSmoothMap realPolyfold β) (hβs : tsupport β ⊆ c.φ.source)
    (hτ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (fun z => (z, τ z))) :
    B.IsScPlusSection (cutoffSection c β τ) := by
  have hτm := hτ.mapsTo
  have hsec := isSection_cutoffSection (β := β) hτm
  set g : X → B.One := fun y => B.oneMk (cutoffSection c β τ y)
    (cutoffSection_mem_oneSet_of_isChart hc hτm y) with hg
  refine (B.isScPlusSection_iff _).2 ⟨hsec, g, rfl, ?_⟩
  refine MPolyfold.isScSmoothMap_of_local fun y => ?_
  by_cases hy : y ∈ c.φ.source
  · refine ⟨c.φ, oneChartOf hc (g y), c.φ.source, c.isChart, isChart_oneChartOf hc (g y),
      c.φ.isOpen_source, hy, subset_rfl,
      fun y' hy' => cutoffSection_mem_source hτm hy', ?_⟩
    rw [c.φ.image_source]
    have hβ1 := hβ.real_chart c.isChart
    have hmain : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
        (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
        (fun z => (z, β (c.φ.symm z) • τ z)) := by
      refine ⟨fun z hz => c.smul_mem_strongShiftOne (hτm hz) _, fun R hR => ?_⟩
      have hU := R.isScDomain
      have h1 := hτ.comp_isScSmooth R hR
      have h2 := (hβ1.comp_isScSmooth R hR).smul hU (h1.snd hU)
      exact (R.isScSmooth.scPair hU h2).congr hU fun _ _ => rfl
    refine hmain.congr fun z hz => ?_
    have hzs := c.φ.symm_mapsTo hz
    change (z, β (c.φ.symm z) • τ z) = c.liftOne (cutoffSection c β τ (c.φ.symm z))
    rw [liftOne_cutoffSection hτm hzs, c.φ.apply_symm_apply hz]
  · have hyt : y ∉ tsupport β := fun h => hy (hβs h)
    obtain ⟨c', hc', hyc'⟩ := exists_chart_mem B y
    set V := c'.φ.source ∩ (tsupport β)ᶜ with hV
    have hVo : IsOpen V := c'.φ.isOpen_source.inter (isClosed_tsupport β).isOpen_compl
    have hzero : ∀ y' ∈ V, cutoffSection c β τ y' = fiberZero P y' := fun y' hy' =>
      cutoffSection_eq_zero hτm (image_eq_zero_of_notMem_tsupport hy'.2)
    refine ⟨c'.φ, oneChart hc' (g y), V, c'.isChart, B.isChart_oneChart hc' (g y), hVo,
      ⟨hyc', hyt⟩, inter_subset_left, fun y' hy' => ?_, ?_⟩
    · change cutoffSection c β τ y' ∈ c'.toPartialEquiv.source
      exact c'.mem_source_of_proj (by rw [hsec y']; exact hy'.1)
    · have hret : IsScRetract c'.φ.model.E c'.φ.model.C (c'.φ '' V) :=
        c'.φ.isScRetract_image inter_subset_left hVo
      refine ((c'.φ.model.E.prodInlOp c'.F.shift).isScSmoothRetractMap hret
        fun z hz => ?_).congr ?_
      · change (z, c'.F.toBase 1 0) ∈ c'.K
        rw [map_zero]; exact c'.zero_mem_K (c'.φ.image_subset_model inter_subset_left hz)
      · rintro _ ⟨y', hy', rfl⟩
        change ((c'.φ y', 0) : (c'.φ.model.E.prod c'.F.shift) 0) =
          c'.liftOne (cutoffSection c β τ (c'.φ.symm (c'.φ y')))
        rw [c'.φ.symm_apply_apply hy'.1, hzero y' hy', liftOne_fiberZero hy'.1]

end StrongBundle

end CutoffIsChart

section Agree

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

set_option maxHeartbeats 800000 in
/-- **With bump functions, a local sc⁺-section of Definition 6.2.1 (preprint 6.1) gives a global one**: for
`ind(f, x) = i` with a local section `s` on `V`, the section `s` restricted to `W = dom φ ∩ V`
(`φ` a chart around `x`), read in the chart as `τ`, and cut off by a bump `β` supported in `W`
with `β = 1` near `x`, is a global sc⁺-section `f + βτ` of `P` vanishing at `x` whose
linearization at `x` has index `i`. -/
theorem StrongBundle.IsIndexAtLocal.isIndexAt (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSection f) {x : X} {i : ℤ} (hi : B.IsIndexAtLocal f x i) :
    B.IsIndexAt f x i := by
  classical
  obtain ⟨hf', V, hV, hxV, hiV⟩ := hi
  have hfs : IsSection P f := hf.isScSmooth.1
  -- the chart around `x` and `W = dom φ ∩ V`
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  set c' := c.restrictInter hV with hc'def
  have hc' : B.IsChart c' := (B.isChart_of_mem hc).restrictInter hV
  have hW : IsOpen c'.φ.source := c'.φ.isOpen_source
  have hWV : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  have hxW : x ∈ c'.φ.source := c.mem_restrictInter_source hV hxc hxV
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : Nonempty c'.φ.source := ⟨⟨x, hxW⟩⟩
  haveI := PX.paracompactSpace_subtype V
  haveI := PX.paracompactSpace_subtype c'.φ.source
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c'.φ.source → X))
    (PX.restrictOpen hW) B
  have hiW := StrongBundle.IsIndexAt.restrictOpen_of_subset hV hW hWV hf (w := ⟨x, hxW⟩) hiV
  obtain ⟨s, hs, hsx, hL⟩ := hiW
  set fW := restrictSection P c'.φ.source f hfs with hfWdef
  have hfW : (B.restrictOpen hW).IsScFredholmSection fW := hf.restrictOpen hW
  set q₀ : pullbackSpace P (Subtype.val : c'.φ.source → X) := s ⟨x, hxW⟩ with hq₀
  set cW := c'.restrictTo B.continuous hW subset_rfl q₀ with hcW
  have hcWmem : cW ∈ (B.restrictOpen hW).atlas.charts :=
    StrongBundle.restrictTo_mem_restrictOpen_atlas hW hc' subset_rfl q₀
  obtain ⟨hs1, hs2⟩ := hs.2 cW hcWmem
  -- the local section read in the chart
  set τ : c'.φ.model.E 0 → c'.F 1 := fun z => (StrongBundle.localRepOne cW s z).2 with hτdef
  have hsP : ∀ w : c'.φ.source, P (s w).1.2 = w.1 := fun w => by
    rw [StrongBundleChart.pullbackSpace_val_proj (s w)]
    exact congrArg Subtype.val (hs.1 w)
  have hτ : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ) (strongShiftOne c'.K)
      (fun z => (z, τ z)) := by
    refine hs2.congr fun z hz => ?_
    refine Prod.ext ?_ rfl
    change (c' (s ((c'.φ.restrictTo subset_rfl).symm z)).1.2).1 = z
    have hw : ((c'.φ.restrictTo (V := c'.φ.source) subset_rfl).symm z).1 = c'.φ.symm z :=
      MChart.restrictTo_symm_val _ hz
    rw [c'.fst_apply (by rw [hsP, hw]; exact c'.φ.symm_mapsTo hz), hsP, hw,
      c'.φ.apply_symm_apply hz]
  have hτm := hτ.mapsTo
  -- the bump
  obtain ⟨β, hβ, -, hβx, hβs, hβ1⟩ := proposition_5_5_3 hbump hW hxW
  set sX := StrongBundle.cutoffSection c' β τ with hsXdef
  have hsX : B.IsScPlusSection sX :=
    StrongBundle.isScPlusSection_cutoffSection_of_isChart hc' hβ hβs hτ
  -- where `β = 1`, the principal part of `sX` is that of `s`
  have hprinc : ∀ z ∈ c'.φ.model.O, β (c'.φ.symm z) = 1 →
      c'.principal sX z = cW.principal s z := by
    intro z hz hβz
    have hzs := c'.φ.symm_mapsTo hz
    change (c' (sX (c'.φ.symm z))).2 = (c' (s (cW.φ.symm z)).1.2).2
    rw [hsXdef, StrongBundle.apply_cutoffSection hτm hzs]
    change c'.F.toBase 1 (β (c'.φ.symm z) • τ (c'.φ (c'.φ.symm z))) = _
    rw [hβz, one_smul, c'.φ.apply_symm_apply hz]
    exact Function.invFun_eq (hs1 _ (cW.φ.symm_mapsTo hz))
  -- `f + sX` vanishes at `x`
  have hxW' : (⟨x, hxW⟩ : c'.φ.source) ∈ cW.φ.source := hxW
  have hzero : IsZeroAt P (sectionAdd P f sX) x := by
    have h0 := (cW.isZeroAt_iff (hfW.isScSmooth.1.sectionAdd hs.1) hxW').1 hsx
    rw [cW.principal_sectionAdd hfW.isScSmooth.1 hs.1 (cW.φ.mapsTo_model _ hxW')] at h0
    change cW.principal fW (c'.φ x) + cW.principal s (c'.φ x) = 0 at h0
    rw [c'.isZeroAt_iff (hfs.sectionAdd hsX.1) hxW,
      c'.principal_sectionAdd hfs hsX.1 (c'.φ.mapsTo_model x hxW),
      hprinc _ (c'.φ.mapsTo_model x hxW) (by rw [c'.φ.symm_apply_apply hxW]; exact hβx)]
    rw [StrongBundleChart.principal_restrictTo hW B.continuous subset_rfl q₀ hfs
      (c'.φ.mapsTo_model x hxW)] at h0
    exact h0
  refine ⟨sX, hsX, hzero, ?_⟩
  -- the index, through the germ datum of `f + sX` at `x`
  have hF := theorem_3_1_18_preprint hf hsX
  have hFW := theorem_3_1_18_preprint hfW hs
  have hxs : x ∈ PX.smoothSet := hF.mem_smoothSet_of_isZeroAt hzero
  obtain ⟨-, c₁, hc₁, hxc₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hF.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth hzero hc₁ hxc₁ hφ₁ h0₁
    hfill₁ hs₁ hs0₁ dc
  suffices hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q by rw [hid]; exact hd
  -- the chart restricted to the set where `β = 1`
  obtain ⟨U₁, hU₁sub, hU₁o, hxU₁⟩ := eventually_nhds_iff.1 hβ1
  set c'' := c'.restrictInter hU₁o with hc''def
  have hc'' : B.IsChart c'' := hc'.restrictInter hU₁o
  have hsub'' : c''.φ.source ⊆ c'.φ.source := fun y hy => hy.1
  have hxc'' : x ∈ c''.φ.source := ⟨hxW, hxU₁⟩
  set cW'' := c''.restrictTo B.continuous hW hsub'' q₀ with hcW''
  have hcW''c : (B.restrictOpen hW).IsChart cW'' :=
    StrongBundle.restrictOpen_isChart_restrictTo hW hc'' hsub'' q₀
  have hxW'' : (⟨x, hxW⟩ : c'.φ.source) ∈ cW''.φ.source := hxc''
  set z : c''.φ.model.E 1 := MPolyfold.levelLift c''.φ 1 x with hzdef
  have hz : c''.φ.model.E.toBase 1 z = c''.φ x :=
    PX.toBase_levelLift c''.isChart hxc'' (mem_iInter.1 hxs 1)
  have hzU : c''.φ.model.E.toBase 1 z ∈ c''.U := by
    rw [hz]
    exact mem_U_of_mem_O c''.isRetraction (c''.r_image ▸ c''.φ.mapsTo_model x hxc'')
  -- the two principal parts agree on `O''`
  have hr1 : IsSc1 c''.U (c''.principal (sectionAdd P f sX) ∘ r c''.R) :=
    hF.isScSmooth.isSc1_principal_comp_r hc''
  have hr2 : IsSc1 c''.U (cW''.principal (sectionAdd (pullbackProj P Subtype.val) fW s) ∘
      r c''.R) := hFW.isScSmooth.isSc1_principal_comp_r hcW''c
  have hcongr : ∀ v, linAt c''.U c''.R (c''.principal (sectionAdd P f sX)) z v =
      linAt c''.U c''.R (cW''.principal (sectionAdd (pullbackProj P Subtype.val) fW s)) z v := by
    intro v
    refine linAt_congr c''.relOpen hr1 hr2 (fun u hu => ?_)
      (show c''.φ.model.E.toBase 1 z ∈ c''.U from hzU) v
    have huO'' : u ∈ c''.φ.model.O := c''.r_image ▸ hu
    obtain ⟨y, hy, rfl⟩ := huO''
    have hyW : y ∈ c'.φ.source := hy.1
    have huO' : c'.φ y ∈ c'.φ.model.O := c'.φ.mapsTo_model y hyW
    have hβy : β (c'.φ.symm (c'.φ y)) = 1 := by
      rw [c'.φ.symm_apply_apply hyW]; exact hU₁sub y hy.2
    have hy' : (⟨y, hyW⟩ : c'.φ.source) ∈ cW''.φ.source := hy
    change c''.principal (sectionAdd P f sX) (c''.φ y) =
      cW''.principal (sectionAdd (pullbackProj P Subtype.val) fW s) (cW''.φ ⟨y, hyW⟩)
    rw [c''.principal_sectionAdd hfs hsX.1 (c''.φ.mapsTo_model y hy),
      cW''.principal_sectionAdd hfW.isScSmooth.1 hs.1 (cW''.φ.mapsTo_model _ hy')]
    change c''.principal f (c''.φ y) + c''.principal sX (c''.φ y) =
      cW''.principal fW (c''.φ y) + cW''.principal s (c''.φ y)
    rw [StrongBundleChart.principal_restrictTo hW B.continuous hsub'' q₀ hfs
      (c''.φ.mapsTo_model y hy)]
    change c'.principal f (c'.φ y) + c'.principal sX (c'.φ y) =
      c'.principal f (c'.φ y) + (c' (s ((c''.φ.restrictTo hsub'').symm (c'.φ y))).1.2).2
    rw [hprinc _ huO' hβy]
    change _ + (c' (s ((c'.φ.restrictTo subset_rfl).symm (c'.φ y))).1.2).2 = _
    have hpt : (c'.φ.restrictTo (V := c'.φ.source) subset_rfl).symm (c'.φ y) =
        (c''.φ.restrictTo hsub'').symm (c''.φ y) := by
      apply Subtype.ext
      have e1 := MChart.restrictTo_symm_val (V := c'.φ.source) (φ := c'.φ) subset_rfl huO'
      have e2 := MChart.restrictTo_symm_val (V := c'.φ.source) (φ := c''.φ) hsub''
        (c''.φ.mapsTo_model y hy)
      exact e1.trans e2.symm
    rw [hpt]
    rfl
  -- the index of `L` is `d` in `c''` and `i` in `cW''`
  have hmem : ∀ v : ↥(rangeS (scDeriv c''.U (r c''.R) z)),
      linAt c''.U c''.R (c''.principal (sectionAdd P f sX)) z v ∈
        rangeS (ρCLM c''.isRetraction hzU) := fun v => by
    obtain ⟨hD, -, -, hTK, -, -, -⟩ := StrongBundle.linAt_isScFredholm hF hzero hc'' hxc'' hz hzU
    have := hTK v.1 v.2
    rw [hD.toScOperator_zero] at this
    exact this
  set L := (linAt c''.U c''.R (c''.principal (sectionAdd P f sX)) z).codRestrict _ hmem with hL'
  have h1 := hd c'' hc'' hxc'' z hz hzU L fun _ => rfl
  have h2 := hL cW'' hcW''c hxW'' z hz hzU L fun v => hcongr v
  exact h2.2.symm.trans h1.2

/-- **The two readings of Definition 6.2.1 (preprint 6.1) agree under bump functions**: `ind(f, x) = i` with a
locally defined sc⁺-section iff with a global one. -/
theorem StrongBundle.isIndexAtLocal_iff_isIndexAt (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSection f) {x : X} {i : ℤ} :
    B.IsIndexAtLocal f x i ↔ B.IsIndexAt f x i :=
  ⟨fun h => h.isIndexAt hbump hf, fun h => h.isIndexAtLocal hf⟩

end Agree

end Polyfold
