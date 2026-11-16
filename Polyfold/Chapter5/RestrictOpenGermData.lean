import Polyfold.Chapter3.RestrictOpenGerms
import Polyfold.Chapter5.RestrictOpen

/-!
# Restrictions to open sets

Index, linearizations, sc-Fredholm germs and sections and tame charts restricted to open subsets and
to intersections, with the germ data of the restricted charts. The germ forms are in
`Chapter3/RestrictOpenGerms.lean`.
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff
noncomputable section
namespace Polyfold
universe u v
section ChartRestrict
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} (hV : IsOpen V) {c : StrongBundleChart PX P} {f : X → Y}
open StrongRetr

omit [T2Space Y] [ParacompactSpace Y] in
/-- `0 ∈ U` for the restricted chart `c|dom φ ∩ V` centred at `x ∈ V`. -/
lemma StrongBundleChart.zero_mem_restrictInter_U {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0)
    (hxV' : x ∈ V) : (0 : c.φ.model.E 0) ∈ (c.restrictInter hV).U := by
  rw [c.restrictInter_U]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxV
  refine ⟨mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O), ?_⟩
  change r c.R 0 ∈ c.φ '' (c.φ.source ∩ V)
  rw [r_eq_self c.isRetraction (c.r_image ▸ h0O)]
  exact ⟨x, ⟨hxV, hxV'⟩, hφ0⟩

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of `f` in `c|dom φ ∩ V` is that in `c`. -/
lemma StrongBundleChart.principal_restrictInter (f : X → Y) :
    (c.restrictInter hV).principal f = c.principal f := rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- The relatively open domain of the restricted chart is contained in that of the chart. -/
lemma StrongBundleChart.restrictInter_relOpen :
    IsRelOpenInQuadrant c.φ.model.E c.φ.model.C (c.restrictInter hV).U :=
  (c.restrictInter hV).relOpen

/-- **The germ data of Definition 3.1.11 (preprint 3.11) in `c` are germ data in `c|dom φ ∩ V`.** -/
theorem StrongBundleChart.germData_restrictInter {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0)
    (hxV' : x ∈ V) (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0}
    {s : c.φ.model.E 0 → c.F 1} (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))) :
    IsFillingGerm (c.restrictInter hV).relOpen (c.restrictInter hV).isRetraction
        (c.zero_mem_restrictInter_U hV hxV hφ0 hxV') ((c.restrictInter hV).principal f) g ∧
      IsScPlusGerm (c.restrictInter hV).φ.model.C (c.restrictInter hV).U s ∧
      IsConjugateToBasicGerm (c.restrictInter hV).U (fun u => g u - c.F.toBase 1 (s u)) := by
  have hsub := c.restrictInter_U_subset hV
  have h0' := c.zero_mem_restrictInter_U hV hxV hφ0 hxV'
  refine ⟨?_, hs.of_subset c.relOpen (c.restrictInter hV).relOpen h0', hconj.of_subset c.relOpen h0
    (c.restrictInter hV).relOpen hsub h0'⟩
  exact hfill.of_subset c.relOpen c.isRetraction (c.restrictInter hV).relOpen
    (c.restrictInter hV).isRetraction hsub h0 h0'

/-- The restriction of a tame chart to `dom φ ∩ V` is tame (`ScRetraction.restrict_isTame`). -/
theorem StrongBundle.IsTameChart.restrictInter (hc : B.IsTameChart c) :
    B.IsTameChart (c.restrictInter hV) :=
  ⟨hc.1.restrictInter hV, (c.isRetraction.baseRetraction c.relOpen).restrict_isTame
    (c.isOpen_restrictOpen (s := c.φ.source ∩ V) inter_subset_left
      (c.φ.isOpen_source.inter hV)) hc.2⟩

end ChartRestrict

section Transport
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V) {f : X → Y}
open StrongRetr

/-- **The germ data of `f` at `x ∈ V` in a chart `c` are germ data of `f|V` in the transported
restricted chart.** -/
theorem StrongBundleChart.germData_restrictTo (hP : Continuous P) (hf : IsSection P f) {c : StrongBundleChart PX P}
    {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (hxV' : x ∈ V)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)))
    (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    IsFillingGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).relOpen
        ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).isRetraction
        (c.zero_mem_restrictInter_U hV hxV hφ0 hxV')
        (((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).principal (restrictSection P V f hf)) g ∧
      IsScPlusGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).φ.model.C
        ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).U s ∧
      IsConjugateToBasicGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).U (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hfill', hs', hconj'⟩ := c.germData_restrictInter hV hxV hφ0 hxV' h0 hfill hs hconj
  refine ⟨?_, hs', hconj'⟩
  refine { hfill' with eq_on := ?_ }
  filter_upwards [hfill'.eq_on] with z hz hzO
  rw [← hz hzO]
  exact StrongBundleChart.principal_restrictTo hV hP _ q₀ hf
    (((c.restrictInter hV).r_image) ▸ hzO)

/-- **An sc-Fredholm germ at `x ∈ V` is an sc-Fredholm germ of `f|V`** (Definition 3.1.11 (preprint 3.11) on
`P|V`). -/
theorem StrongBundle.IsScFredholmGerm.restrictOpen (hf : IsSection P f) {x : X}
    (h : B.IsScFredholmGerm f x) (hxV : x ∈ V) :
    (B.restrictOpen hV).IsScFredholmGerm (restrictSection P V f hf) ⟨x, hxV⟩ := by
  obtain ⟨hxs, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf ⟨x, hxV⟩ with hq₀
  obtain ⟨hfill', hs', hconj'⟩ :=
    StrongBundleChart.germData_restrictTo hV B.continuous hf hxc hφ0 hxV h0 hfill hs hconj q₀
  refine ⟨(MPolyfold.mem_smoothSet_restrictOpen_iff hV _).2 hxs,
    (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀,
    StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV) _ q₀,
    c.mem_restrictInter_source hV hxc hxV, hφ0, c.zero_mem_restrictInter_U hV hxc hφ0 hxV, g, s,
    hfill', hs', hs0, hconj'⟩

/-- **An sc-Fredholm germ in a tame chart at `x ∈ V` is one of `f|V`** (Definition 3.6.3 (preprint 3.50) on
`P|V`). -/
theorem StrongBundle.IsScFredholmGermTame.restrictOpen (hf : IsSection P f) {x : X}
    (h : B.IsScFredholmGermTame f x) (hxV : x ∈ V) :
    (B.restrictOpen hV).IsScFredholmGermTame (restrictSection P V f hf) ⟨x, hxV⟩ := by
  obtain ⟨hxs, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf ⟨x, hxV⟩ with hq₀
  obtain ⟨hfill', hs', hconj'⟩ :=
    StrongBundleChart.germData_restrictTo hV B.continuous hf hxc hφ0 hxV h0 hfill hs hconj q₀
  refine ⟨(MPolyfold.mem_smoothSet_restrictOpen_iff hV _).2 hxs,
    (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀,
    ⟨StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV).1 _ q₀,
      (hc.restrictInter hV).2⟩,
    c.mem_restrictInter_source hV hxc hxV, hφ0, c.zero_mem_restrictInter_U hV hxc hφ0 hxV, g, s,
    hfill', hs', hs0, hconj'⟩

/-- **The restriction of an sc-Fredholm section to an open subset is an sc-Fredholm section**
(Definition 3.1.16 (preprint 3.14) on `P|V`). -/
theorem StrongBundle.IsScFredholmSection.restrictOpen (hf : B.IsScFredholmSection f) :
    (B.restrictOpen hV).IsScFredholmSection (restrictSection P V f hf.isScSmooth.1) where
  isScSmooth := hf.isScSmooth.restrictOpen hV
  regularizing := StrongBundle.regularizing_restrictOpen hV hf
  germ v hv :=
    (hf.germ v.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff hV v).1 hv)).restrictOpen hV _ v.2

/-- **The restriction of an sc-Fredholm section with tame germ data to an open subset has tame
germ data** (Definition 3.6.4 (preprint 3.51) on `P|V`). -/
theorem StrongBundle.IsScFredholmSectionTame.restrictOpen (hf : B.IsScFredholmSectionTame f) :
    (B.restrictOpen hV).IsScFredholmSectionTame (restrictSection P V f hf.isScSmooth.1) :=
  { hf.toIsScFredholmSection.restrictOpen hV with
    germTame := fun v hv =>
      (hf.germTame v.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff hV v).1 hv)).restrictOpen hV
        _ v.2 }

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P Subtype.val)] in

/-- The zeros of `f|V` are the zeros of `f` in `V`. -/
lemma isZeroAt_restrictSection_iff' (hf : IsSection P f) (v : V) :
    IsZeroAt (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf) v ↔
      IsZeroAt P f v.1 :=
  isZeroAt_restrictSection_iff hf v

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P Subtype.val)] in

/-- The restriction of `f + s` is `f|V + s|V` (fibrewise, `pullbackFiberEquiv`). -/
lemma restrictSection_sectionAdd {s : X → Y} (hf : IsSection P f) (hs : IsSection P s) :
    restrictSection P V (sectionAdd P f s) (hf.sectionAdd hs) =
      sectionAdd (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf)
        (restrictSection P V s hs) := by
  funext v
  set e := pullbackFiberEquiv P (Subtype.val : V → X) v with he
  have h1 : e ⟨restrictSection P V f hf v, rfl⟩ = ⟨f v.1, hf v.1⟩ := Subtype.ext rfl
  have h2 : e ⟨restrictSection P V s hs v, rfl⟩ = ⟨s v.1, hs v.1⟩ := Subtype.ext rfl
  have h3 := pullbackFiberEquiv_add P (Subtype.val : V → X) v
    ⟨restrictSection P V f hf v, rfl⟩ ⟨restrictSection P V s hs v, rfl⟩
  rw [h1, h2] at h3
  rw [sectionAdd_apply (isSection_restrictSection hf) (isSection_restrictSection hs)]
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change sectionAdd P f s v.1 = _
  rw [sectionAdd_apply hf hs]
  have := congrArg Subtype.val h3
  exact this.symm

/-- **The index of a germ datum of `f` at a zero `x ∈ V`, read on `P|V`**: `(f|V)'(x)` is Fredholm
of index `dim Pn − dim Q` in every chart of `P|V` (`isLinOfIndex_of_conjugationData` on `P|V`
for the transported germ datum, whose conjugation data have the same `Pn` and `Q`). -/
theorem StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData (hf : B.IsScSmoothSection f)
    {x : X} (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxc : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) :
    (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.1) ⟨x, hxV⟩
      (finrank ℝ dc.Pn - finrank ℝ dc.Q) := by
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf.1 ⟨x, hxV⟩ with hq₀
  have hsub := c.restrictInter_U_subset hV
  have h0' := c.zero_mem_restrictInter_U hV hxc hφ0 hxV
  obtain ⟨hfill', hs', -⟩ := StrongBundleChart.germData_restrictTo hV B.continuous hf.1 hxc hφ0 hxV h0 hfill hs
    (isConjugateToBasicGerm_iff_nonempty.2 ⟨dc⟩) q₀
  have hx0' : IsZeroAt (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf.1)
      ⟨x, hxV⟩ := (isZeroAt_restrictSection_iff' hf.1 _).2 hx0
  have := StrongBundle.isLinOfIndex_of_conjugationData (hf.restrictOpen hV) hx0'
    (StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV) _ q₀)
    (c.mem_restrictInter_source hV hxc hxV) hφ0 h0' hfill' hs' hs0
    (dc.ofSubset c.relOpen h0 (c.restrictInter hV).relOpen hsub h0')
  exact this

/-- **The index at a zero restricts to `P|V`**: if `f'(x)` is Fredholm of index `i` in every chart
of `P` (`IsLinOfIndex`), then `(f|V)'(x)` is Fredholm of index `i` in every chart of `P|V`. -/
theorem StrongBundle.IsLinOfIndex.restrictOpen (hf : B.IsScFredholmSection f) {x : X}
    (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {i : ℤ} (hi : B.IsLinOfIndex f x i) :
    (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i := by
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  obtain ⟨-, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := hf.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hx0 hc hxc hφ0 h0 hfill hs
    hs0 dc
  have hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q := hi.unique hf hx0 hd
  rw [hid]
  exact StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData hV hf.isScSmooth hx0 hxV hc hxc
    hφ0 h0 hfill hs hs0 dc

/-- **The index at a zero is determined on `P|V`**: if `(f|V)'(x)` is Fredholm of index `i` in
every chart of `P|V`, then `f'(x)` is Fredholm of index `i` in every chart of `P`. -/
theorem StrongBundle.IsLinOfIndex.of_restrictOpen (hf : B.IsScFredholmSection f) {x : X}
    (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {i : ℤ}
    (hi : (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i) :
    B.IsLinOfIndex f x i := by
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  obtain ⟨-, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := hf.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hx0 hc hxc hφ0 h0 hfill hs
    hs0 dc
  have hd' := StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData hV hf.isScSmooth hx0 hxV hc
    hxc hφ0 h0 hfill hs hs0 dc
  have hx0' : IsZeroAt (pullbackProj P (Subtype.val : V → X))
      (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ :=
    (isZeroAt_restrictSection_iff' hf.isScSmooth.1 _).2 hx0
  have hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q := hi.unique (hf.restrictOpen hV) hx0' hd'
  rw [hid]
  exact hd

/-- **Definition 6.2.1 (preprint 6.1) restricts to `P|V`**: `ind(f, x) = i` with a global sc⁺-section `s` gives
`ind(f|V, x) = i` with `s|V`. -/
theorem StrongBundle.IsIndexAt.restrictOpen (hf : B.IsScFredholmSection f) {x : X} (hxV : x ∈ V)
    {i : ℤ} (hi : B.IsIndexAt f x i) :
    (B.restrictOpen hV).IsIndexAt (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i := by
  obtain ⟨s, hs, hsx, hL⟩ := hi
  have hfs : IsSection P f := hf.isScSmooth.1
  refine ⟨restrictSection P V s hs.1, hs.restrictOpen hV, ?_, ?_⟩
  · rw [← restrictSection_sectionAdd hfs hs.1]
    exact (isZeroAt_restrictSection_iff' (hfs.sectionAdd hs.1) _).2 hsx
  · have := StrongBundle.IsLinOfIndex.restrictOpen hV (theorem_3_1_18_preprint hf hs) hsx hxV hL
    rwa [restrictSection_sectionAdd hfs hs.1] at this

end Transport
end Polyfold
end
