import Polyfold.Chapter3.IndexLocallyConstantLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.1,
**Definition 6.2.1 (preprint 6.1)** (the index of an sc-Fredholm germ at a smooth point, with a *locally defined*
sc⁺-section) and **Proposition 6.2.2 (preprint 6.2)** (stability of the index along sc-smooth paths,
pp. 200–203), **with the text's hypotheses**: tame germ data and no bump functions ("we do not
need a sc-smooth partition of unity").  Round-trip item V3.98 (a); Findings, Chapter 3, items
360–369.

# Definition 6.2.1 (preprint 6.1) with local sections, and Proposition 6.2.2 (preprint 6.2) without bump functions

## The text, paraphrased

(§6.1) At a smooth point `x` with `f(x) ≠ 0` "we take a local sc⁺-section `s` with `s(x) = f(x)`
(in a chart, `s(y) = R(y, f(x))`)" and linearize `f − s` at its zero `x`; the Fredholm property
and the index do not depend on `s`.  (Proposition 6.2.2 (preprint 6.2)) For a tame strong bundle, an sc-Fredholm
section `f` and an sc-smooth path `φ`, `ind(f, φ(t))` is constant.  *Proof.* Near `t₀` a locally
defined sc⁺-section `s(t, x)` of the pull-back with `s(t, φ(t)) = f(φ(t))` ("we do not need a
sc-smooth partition of unity"), the stabilization by finitely many sc⁺-sections `R(·, eᵢ)` in a
chart, the implicit function theorem and the index count.

## What is formalized

* `Polyfold.StrongBundle.IsIndexAtLocal B f x i` (**Definition 6.2.1 (preprint 6.1) with local sections**): there
  is an open `V ∋ x` and an sc⁺-section `s` of the restriction `P|V` (`StrongBundle.restrictOpen`)
  with `(f|V + s)(x) = 0` and `(f|V + s)'(x)` Fredholm of index `i` in every chart of `P|V`
  (`IsIndexAt` on `P|V`).  `IsIndexAt.isIndexAtLocal` (**a global section gives a local one**),
  `IsIndexAtLocal.unique` (**well defined**: two local sections are compared on the intersection
  of their domains, `IsIndexAt.restrictOpen_of_subset`, and `IsIndexAt.unique` on `P|V ∩ V'`),
  `StrongBundle.exists_isIndexAtLocal` (**`ind(f, x)` exists at every smooth point, without bump
  functions**: the section `R(·, f(x))` on the chart domain), `isIndexAtLocal_of_isZeroAt` (at a
  zero it is the index of `f'(x)`), `IsIndexAtLocal.isIndexAt` (**with bump functions the two
  readings agree**: the local section is cut off).
* `Polyfold.exists_isScPlusSection_pullback_of_path_of_bump` / `_of_chart`: the section along
  the path (E) with the cut-off as data / with no cut-off on a bundle with a chart over the
  whole base; `isLinOfIndex_paramLift_sectionAdd_eventually_const_of_sections` and
  `hasScPlusSectionsThrough_pullback_rn_of_chart` (the stabilizing sections on `ℝ × V`).
* **`Polyfold.proposition_6_2_2_local`** (**Proposition 6.2.2 (preprint 6.2) with the text's hypotheses**): for an
  sc-Fredholm section `f` with tame germ data (Definition 3.6.4 (preprint 3.51)) of a strong bundle `P : Y → X`
  (no bump functions) and an sc-smooth path `φ : ℝ → X`, `ind(f, φ(t))` (Definition 6.2.1 (preprint 6.1) with local
  sections, `IsIndexAtLocal`) is one integer for all `t`; `proposition_6_2_2_local'` states
  `ind(f, φ(0)) = ind(f, φ(1))` for any two values of the index.

## What the text leaves implicit, and the choices made

* **The local section of Definition 6.2.1 (preprint 6.1) is a section of `P|V`**, `V` an open neighbourhood of `x`
  (the text: "a local sc⁺-section"; in a chart, on the chart domain).  The index is defined on
  `P|V` by the global Definition 6.2.1 (preprint 6.1) of `IndexAlongPaths.lean` (`IsIndexAt`), so Theorem 3.1.18 (preprint 3.15) and
  the germ data on `P|V` (`RestrictOpenGerms.lean`) make it well defined; the comparison of two
  local sections on different domains needs the restriction to the intersection
  (`sectionRestrict`).
* **The proof of Proposition 6.2.2 (preprint 6.2)** is that of `IndexAlongPathsDevice.lean` run on the restriction
  `P|V` to the domain of a chart around `φ(t₀)`, where the sc⁺-sections of the text need no
  cut-off: the path is reparametrized into `V` (`exists_contDiff_eq_id_near_mapsTo`, as before),
  the section along the path is `exists_isScPlusSection_pullback_of_path_of_chart` with `β = 1`,
  the stabilizing sections on `ℝ × V` are `R(·, eᵢ)` in the product chart
  (`hasScPlusSectionsThrough_of_chart`), the local constancy along the zero set is
  `index_locally_constant_of_sections`, and the slice relation (S) is unchanged.  The hypotheses
  beyond the text: tame germ data in place of "tame strong bundle" (the project's reading of
  Definition 3.6.4 (preprint 3.51)), and paths on `ℝ` (an sc-smooth path on `[0, 1]` which extends to `ℝ` is
  covered; a path sc-smooth on `[0, 1]` only is not).
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Restricting a section of `P|V` to `P|W`, `W ⊆ V` -/

section SectionRestrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V W : Set X}

variable (P) in
omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The restriction of a section of `ι*Y → V` to `W ⊆ V`, as a section of `ι*Y → W`. -/
def sectionRestrict (hWV : W ⊆ V) (s : V → pullbackSpace P (Subtype.val : V → X))
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) :
    W → pullbackSpace P (Subtype.val : W → X) :=
  fun w => ⟨(w, (s ⟨w.1, hWV w.2⟩).1.2), by
    have h1 : P (s ⟨w.1, hWV w.2⟩).1.2 = ((s ⟨w.1, hWV w.2⟩).1.1).1 := (s ⟨w.1, hWV w.2⟩).2
    have h2 : (s ⟨w.1, hWV w.2⟩).1.1 = ⟨w.1, hWV w.2⟩ := hs _
    change P (s ⟨w.1, hWV w.2⟩).1.2 = w.1
    rw [h1, h2]⟩

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma isSection_sectionRestrict (hWV : W ⊆ V) {s : V → pullbackSpace P (Subtype.val : V → X)}
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) :
    IsSection (pullbackProj P (Subtype.val : W → X)) (sectionRestrict P hWV s hs) := fun _ => rfl

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
@[simp] lemma sectionRestrict_val (hWV : W ⊆ V) {s : V → pullbackSpace P (Subtype.val : V → X)}
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) (w : W) :
    (sectionRestrict P hWV s hs w).1.2 = (s ⟨w.1, hWV w.2⟩).1.2 := rfl

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The restriction of `f|V` to `W` is `f|W`. -/
lemma sectionRestrict_restrictSection (hWV : W ⊆ V) {f : X → Y} (hf : IsSection P f) :
    sectionRestrict P hWV (restrictSection P V f hf) (isSection_restrictSection hf) =
      restrictSection P W f hf := rfl

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `g(w) = 0` in `ι*Y → W` iff `g` is `0` at `w` in `ι*Y → V`. -/
lemma isZeroAt_sectionRestrict_iff (hWV : W ⊆ V) {g : V → pullbackSpace P (Subtype.val : V → X)}
    (hg : IsSection (pullbackProj P (Subtype.val : V → X)) g) (w : W) :
    IsZeroAt (pullbackProj P (Subtype.val : W → X)) (sectionRestrict P hWV g hg) w ↔
      IsZeroAt (pullbackProj P (Subtype.val : V → X)) g ⟨w.1, hWV w.2⟩ := by
  have h0W : fiberZero (pullbackProj P (Subtype.val : W → X)) w =
      ⟨(w, fiberZero P w.1), (0 : P ⁻¹' {w.1}).2⟩ := rfl
  have h0V : fiberZero (pullbackProj P (Subtype.val : V → X)) ⟨w.1, hWV w.2⟩ =
      ⟨(⟨w.1, hWV w.2⟩, fiberZero P w.1), (0 : P ⁻¹' {w.1}).2⟩ := rfl
  have h1 : (g ⟨w.1, hWV w.2⟩).1.1 = ⟨w.1, hWV w.2⟩ := hg _
  unfold IsZeroAt
  rw [h0W, h0V]
  constructor
  · intro h
    refine Subtype.ext (Prod.ext h1 ?_)
    exact congrArg (fun q : pullbackSpace P (Subtype.val : W → X) => q.1.2) h
  · intro h
    refine Subtype.ext (Prod.ext rfl ?_)
    exact congrArg (fun q : pullbackSpace P (Subtype.val : V → X) => q.1.2) h

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The restriction of `g + s` is `g|W + s|W` (fibrewise). -/
lemma sectionRestrict_sectionAdd (hWV : W ⊆ V) {g s : V → pullbackSpace P (Subtype.val : V → X)}
    (hg : IsSection (pullbackProj P (Subtype.val : V → X)) g)
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) :
    sectionRestrict P hWV (sectionAdd (pullbackProj P (Subtype.val : V → X)) g s) (hg.sectionAdd hs) =
      sectionAdd (pullbackProj P (Subtype.val : W → X)) (sectionRestrict P hWV g hg)
        (sectionRestrict P hWV s hs) := by
  funext w
  set v : V := ⟨w.1, hWV w.2⟩ with hv
  set eW := pullbackFiberEquiv P (Subtype.val : W → X) w with heW
  set eV := pullbackFiberEquiv P (Subtype.val : V → X) v with heV
  have hgW := isSection_sectionRestrict hWV hg
  have hsW := isSection_sectionRestrict hWV hs
  have h3 := pullbackFiberEquiv_add P (Subtype.val : W → X) w
    ⟨sectionRestrict P hWV g hg w, hgW w⟩ ⟨sectionRestrict P hWV s hs w, hsW w⟩
  have h4 := pullbackFiberEquiv_add P (Subtype.val : V → X) v ⟨g v, hg v⟩ ⟨s v, hs v⟩
  have e1 : eW ⟨sectionRestrict P hWV g hg w, hgW w⟩ = eV ⟨g v, hg v⟩ := Subtype.ext rfl
  have e2 : eW ⟨sectionRestrict P hWV s hs w, hsW w⟩ = eV ⟨s v, hs v⟩ := Subtype.ext rfl
  rw [e1, e2, ← h4] at h3
  apply Subtype.ext
  refine Prod.ext ((hgW.sectionAdd hsW) w).symm ?_
  change (sectionAdd (pullbackProj P (Subtype.val : V → X)) g s v).1.2 =
    (sectionAdd (pullbackProj P (Subtype.val : W → X)) (sectionRestrict P hWV g hg)
      (sectionRestrict P hWV s hs) w).1.2
  rw [sectionAdd_apply hg hs, sectionAdd_apply hgW hsW]
  exact (congrArg Subtype.val h3).symm

variable [Nonempty V] [ParacompactSpace V] [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]
  [Nonempty W] [ParacompactSpace W] [ParacompactSpace (pullbackSpace P (Subtype.val : W → X))]
  (hV : IsOpen V) (hW : IsOpen W) (hWV : W ⊆ V)

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]
  [ParacompactSpace (pullbackSpace P (Subtype.val : W → X))] in
/-- The principal part of `s|W` in a chart of `P` inside `W` is that of `s` in the same chart
inside `V`, on `O`. -/
lemma StrongBundleChart.principal_restrictTo_sectionRestrict (hP : Continuous P)
    {c : StrongBundleChart PX P} (hsub : c.φ.source ⊆ W)
    (q₀ : pullbackSpace P (Subtype.val : W → X)) (q₀' : pullbackSpace P (Subtype.val : V → X))
    {s : V → pullbackSpace P (Subtype.val : V → X)}
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) {z : c.φ.model.E 0}
    (hz : z ∈ c.φ.model.O) :
    (c.restrictTo hP hW hsub q₀).principal (sectionRestrict P hWV s hs) z =
      (c.restrictTo hP hV (hsub.trans hWV) q₀').principal s z := by
  change (c (s ⟨((c.φ.restrictTo hsub).symm z).1, _⟩).1.2).2 =
    (c (s ((c.φ.restrictTo (hsub.trans hWV)).symm z)).1.2).2
  have : (⟨((c.φ.restrictTo hsub).symm z).1, hWV ((c.φ.restrictTo hsub).symm z).2⟩ : V) =
      (c.φ.restrictTo (hsub.trans hWV)).symm z :=
    Subtype.ext (by rw [MChart.restrictTo_symm_val hsub hz,
      MChart.restrictTo_symm_val (hsub.trans hWV) hz])
  rw [this]

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]
  [ParacompactSpace (pullbackSpace P (Subtype.val : W → X))] in
/-- The lifted local representative of `s|W` is that of `s`, on `O`. -/
lemma StrongBundleChart.localRepOne_restrictTo_sectionRestrict (hP : Continuous P)
    {c : StrongBundleChart PX P} (hsub : c.φ.source ⊆ W)
    (q₀ : pullbackSpace P (Subtype.val : W → X)) (q₀' : pullbackSpace P (Subtype.val : V → X))
    {s : V → pullbackSpace P (Subtype.val : V → X)}
    (hs : IsSection (pullbackProj P (Subtype.val : V → X)) s) {z : c.φ.model.E 0}
    (hz : z ∈ c.φ.model.O) :
    StrongBundle.localRepOne (c.restrictTo hP hW hsub q₀) (sectionRestrict P hWV s hs) z =
      StrongBundle.localRepOne (c.restrictTo hP hV (hsub.trans hWV) q₀') s z := by
  simp only [StrongBundle.localRepOne]
  change ((c (s ⟨((c.φ.restrictTo hsub).symm z).1, _⟩).1.2).1, Function.invFun (c.F.toBase 1)
    (c (s ⟨((c.φ.restrictTo hsub).symm z).1, _⟩).1.2).2) =
    ((c (s ((c.φ.restrictTo (hsub.trans hWV)).symm z)).1.2).1, Function.invFun (c.F.toBase 1)
    (c (s ((c.φ.restrictTo (hsub.trans hWV)).symm z)).1.2).2)
  have : (⟨((c.φ.restrictTo hsub).symm z).1, hWV ((c.φ.restrictTo hsub).symm z).2⟩ : V) =
      (c.φ.restrictTo (hsub.trans hWV)).symm z :=
    Subtype.ext (by rw [MChart.restrictTo_symm_val hsub hz,
      MChart.restrictTo_symm_val (hsub.trans hWV) hz])
  rw [this]

/-- **An sc⁺-section of `P|V` restricts to an sc⁺-section of `P|W`**, `W ⊆ V` open. -/
theorem StrongBundle.IsScPlusSection.restrictOpen_of_subset {s : V → pullbackSpace P (Subtype.val : V → X)}
    (hs : (B.restrictOpen hV).IsScPlusSection s) :
    (B.restrictOpen hW).IsScPlusSection (sectionRestrict P hWV s hs.1) := by
  refine ⟨isSection_sectionRestrict hWV hs.1, ?_⟩
  rintro _ ⟨c, hc, hsub, q₀, rfl⟩
  set q₀' : pullbackSpace P (Subtype.val : V → X) :=
    ⟨(⟨q₀.1.1.1, hWV q₀.1.1.2⟩, q₀.1.2), q₀.2⟩ with hq₀'
  obtain ⟨h1, h2⟩ := hs.2 _ (StrongBundle.restrictTo_mem_restrictOpen_atlas hV hc
    (hsub.trans hWV) q₀')
  refine ⟨fun w hw => h1 ⟨w.1, hWV w.2⟩ hw, ?_⟩
  refine h2.congr fun z hz => ?_
  exact (StrongBundleChart.localRepOne_restrictTo_sectionRestrict hV hW hWV B.continuous hsub q₀
    q₀' hs.1 hz).symm

/-- **The index at a zero of a section of `P|V` restricts to `P|W`**, `W ⊆ V` open, for an
sc-Fredholm section `g` of `P|V` whose restriction is sc-Fredholm: through the germ datum of `g|W`
at `x` (`isLinOfIndex_of_conjugationData` on `P|W`) and the chart `c|dom φ ∩ W` of `P` around `x`,
in which the two linearizations agree (`linAt_congr`). -/
theorem StrongBundle.IsLinOfIndex.restrictOpen_of_subset {g : V → pullbackSpace P (Subtype.val : V → X)}
    (hg : (B.restrictOpen hV).IsScFredholmSection g)
    (hgW : (B.restrictOpen hW).IsScFredholmSection (sectionRestrict P hWV g hg.isScSmooth.1))
    {w : W} (hw0 : IsZeroAt (pullbackProj P (Subtype.val : W → X))
      (sectionRestrict P hWV g hg.isScSmooth.1) w) {i : ℤ}
    (hi : (B.restrictOpen hV).IsLinOfIndex g ⟨w.1, hWV w.2⟩ i) :
    (B.restrictOpen hW).IsLinOfIndex (sectionRestrict P hWV g hg.isScSmooth.1) w i := by
  have hgs := hg.isScSmooth.1
  have hws : w ∈ (PX.restrictOpen hW).smoothSet := hgW.mem_smoothSet_of_isZeroAt hw0
  obtain ⟨-, c₂, hc₂, hwc₂, hφ₂, h0₂, g₂, s₂, hfill₂, hs₂, hs0₂, hconj₂⟩ := hgW.germ w hws
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₂
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hgW.isScSmooth hw0 hc₂ hwc₂ hφ₂ h0₂
    hfill₂ hs₂ hs0₂ dc
  suffices hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q by rw [hid]; exact hd
  -- a chart of `P` around `w` inside `W`
  obtain ⟨c, hc, hwc⟩ := StrongBundle.exists_chart_mem B w.1
  set c' := c.restrictInter hW with hc'def
  have hc' : B.IsChart c' := (B.isChart_of_mem hc).restrictInter hW
  have hsub : c'.φ.source ⊆ W := c.restrictInter_source_subset hW
  have hwc' : w.1 ∈ c'.φ.source := c.mem_restrictInter_source hW hwc w.2
  set q₀ : pullbackSpace P (Subtype.val : W → X) := sectionRestrict P hWV g hgs w with hq₀
  set q₀' : pullbackSpace P (Subtype.val : V → X) := g ⟨w.1, hWV w.2⟩ with hq₀'
  set cW := c'.restrictTo B.continuous hW hsub q₀ with hcW
  set cV := c'.restrictTo B.continuous hV (hsub.trans hWV) q₀' with hcV
  have hcW' : (B.restrictOpen hW).IsChart cW :=
    StrongBundle.restrictOpen_isChart_restrictTo hW hc' hsub q₀
  have hcV' : (B.restrictOpen hV).IsChart cV :=
    StrongBundle.restrictOpen_isChart_restrictTo hV hc' (hsub.trans hWV) q₀'
  -- the level-`1` point over `φ(w)`
  set z : c'.φ.model.E 1 := MPolyfold.levelLift cW.φ 1 w with hzdef
  have hz : c'.φ.model.E.toBase 1 z = cW.φ w :=
    (PX.restrictOpen hW).toBase_levelLift (MPolyfold.isChart_restrictTo hW c'.isChart hsub) hwc'
      (mem_iInter.1 hws 1)
  have hzU : c'.φ.model.E.toBase 1 z ∈ c'.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c'.isRetraction (c'.r_image ▸ c'.φ.mapsTo_model w.1 hwc')
  -- the two linearizations agree
  have hr1 : IsSc1 c'.U (cW.principal (sectionRestrict P hWV g hgs) ∘ StrongRetr.r c'.R) :=
    hgW.isScSmooth.isSc1_principal_comp_r hcW'
  have hr2 : IsSc1 c'.U (cV.principal g ∘ StrongRetr.r c'.R) :=
    hg.isScSmooth.isSc1_principal_comp_r hcV'
  have hcongr : ∀ x, linAt c'.U c'.R (cW.principal (sectionRestrict P hWV g hgs)) z x =
      linAt c'.U c'.R (cV.principal g) z x := by
    intro x
    refine linAt_congr c'.relOpen hr1 hr2 (fun u hu => ?_) ?_ x
    · exact StrongBundleChart.principal_restrictTo_sectionRestrict hV hW hWV B.continuous hsub q₀
        q₀' hgs (c'.r_image ▸ hu)
    · show c'.φ.model.E.toBase 1 z ∈ c'.U
      exact hzU
  -- the index in `cW` is `d`, the index in `cV` is `i`
  have hmem : ∀ x : ↥(rangeS (scDeriv c'.U (StrongRetr.r c'.R) z)),
      linAt c'.U c'.R (cW.principal (sectionRestrict P hWV g hgs)) z x ∈
        rangeS (StrongRetr.ρCLM c'.isRetraction hzU) := fun x => by
    obtain ⟨hD, -, -, hTK, -, -, -⟩ :=
      StrongBundle.linAt_isScFredholm hgW hw0 hcW' hwc' hz hzU
    have := hTK x.1 x.2
    rw [hD.toScOperator_zero] at this
    exact this
  set L := (linAt c'.U c'.R (cW.principal (sectionRestrict P hWV g hgs)) z).codRestrict _ hmem
    with hL
  have h1 := hd cW hcW' hwc' _ hz hzU L fun _ => rfl
  have h2 := hi cV hcV' hwc' _ hz hzU L fun x => hcongr x
  exact h2.2.symm.trans h1.2

/-- **Definition 6.2.1 (preprint 6.1) on `P|V` restricts to `P|W`**, `W ⊆ V` open. -/
theorem StrongBundle.IsIndexAt.restrictOpen_of_subset {f : X → Y}
    (hf : B.IsScFredholmSection f) {w : W} {i : ℤ}
    (hi : (B.restrictOpen hV).IsIndexAt (restrictSection P V f hf.isScSmooth.1)
      ⟨w.1, hWV w.2⟩ i) :
    (B.restrictOpen hW).IsIndexAt (restrictSection P W f hf.isScSmooth.1) w i := by
  obtain ⟨s, hs, hsx, hL⟩ := hi
  have hfs := hf.isScSmooth.1
  have hfV := hf.restrictOpen hV
  have hfW := hf.restrictOpen hW
  have hgV := theorem_3_1_18_preprint hfV hs
  have hgW := theorem_3_1_18_preprint hfW (hs.restrictOpen_of_subset hV hW hWV)
  refine ⟨sectionRestrict P hWV s hs.1, hs.restrictOpen_of_subset hV hW hWV, ?_, ?_⟩
  · rw [← sectionRestrict_restrictSection hWV hfs, ← sectionRestrict_sectionAdd]
    exact (isZeroAt_sectionRestrict_iff hWV _ w).2 hsx
  · have hgW' : (B.restrictOpen hW).IsScFredholmSection (sectionRestrict P hWV
        (sectionAdd (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hfs) s)
        hgV.isScSmooth.1) := by
      rw [sectionRestrict_sectionAdd hWV (isSection_restrictSection hfs) hs.1,
        sectionRestrict_restrictSection hWV hfs]
      exact hgW
    have hw0 : IsZeroAt (pullbackProj P (Subtype.val : W → X)) (sectionRestrict P hWV
        (sectionAdd (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hfs) s)
        hgV.isScSmooth.1) w := (isZeroAt_sectionRestrict_iff hWV _ w).2 hsx
    have := StrongBundle.IsLinOfIndex.restrictOpen_of_subset hV hW hWV hgV hgW' hw0 hL
    rwa [sectionRestrict_sectionAdd hWV (isSection_restrictSection hfs) hs.1,
      sectionRestrict_restrictSection hWV hfs] at this

end SectionRestrict

/-! ### Definition 6.2.1 (preprint 6.1) with local sections -/

section IndexAtLocal

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

variable (B) in
/-- **Definition 6.2.1 (preprint 6.1) with a locally defined sc⁺-section** (the text's "we take a local
sc⁺-section `s` with `s(x) = f(x)`"): the sc-Fredholm germ `(f, x)` has **index `i`** if there is
an open `V ∋ x` and an sc⁺-section `s` of the restriction `P|V` with `(f|V + s)(x) = 0` and
`(f|V + s)'(x)` Fredholm of index `i` in every chart of `P|V` (`IsIndexAt` on `P|V`).  By
`IsIndexAtLocal.unique` the index does not depend on `V` and `s`. -/
def StrongBundle.IsIndexAtLocal (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ (hf : IsSection P f) (V : Set X) (hV : IsOpen V) (hx : x ∈ V),
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    haveI := PX.paracompactSpace_subtype V
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
    (B.restrictOpen hV).IsIndexAt (restrictSection P V f hf) ⟨x, hx⟩ i

/-- **A global sc⁺-section gives a local one**: `IsIndexAt f x i → IsIndexAtLocal f x i`
(`V = X`). -/
theorem StrongBundle.IsIndexAt.isIndexAtLocal (hf : B.IsScFredholmSection f) {x : X} {i : ℤ}
    (hi : B.IsIndexAt f x i) : B.IsIndexAtLocal f x i := by
  refine ⟨hf.isScSmooth.1, univ, isOpen_univ, mem_univ x, ?_⟩
  haveI : Nonempty ↥(univ : Set X) := ⟨⟨x, mem_univ x⟩⟩
  haveI := PX.paracompactSpace_subtype (univ : Set X)
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : ↥(univ : Set X) → X))
    (PX.restrictOpen isOpen_univ) B
  exact hi.restrictOpen isOpen_univ hf (mem_univ x)

/-- **Definition 6.2.1 (preprint 6.1) with local sections is well defined**: two local sc⁺-sections `s` on `V`
and `s'` on `V'` give the same index — both restrict to `V ∩ V'`
(`IsIndexAt.restrictOpen_of_subset`), where `IsIndexAt.unique` applies. -/
theorem StrongBundle.IsIndexAtLocal.unique (hf : B.IsScFredholmSection f) {x : X} {i j : ℤ}
    (hi : B.IsIndexAtLocal f x i) (hj : B.IsIndexAtLocal f x j) : i = j := by
  obtain ⟨hf', V, hV, hxV, hiV⟩ := hi
  obtain ⟨hf'', V', hV', hxV', hjV'⟩ := hj
  set W := V ∩ V' with hWdef
  have hW : IsOpen W := hV.inter hV'
  have hxW : x ∈ W := ⟨hxV, hxV'⟩
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : Nonempty V' := ⟨⟨x, hxV'⟩⟩
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI := PX.paracompactSpace_subtype V
  haveI := PX.paracompactSpace_subtype V'
  haveI := PX.paracompactSpace_subtype W
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : V' → X)) (PX.restrictOpen hV') B
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : W → X)) (PX.restrictOpen hW) B
  have h1 := StrongBundle.IsIndexAt.restrictOpen_of_subset hV hW (inter_subset_left (t := V'))
    hf (w := ⟨x, hxW⟩) hiV
  have h2 := StrongBundle.IsIndexAt.restrictOpen_of_subset hV' hW (inter_subset_right (s := V))
    hf (w := ⟨x, hxW⟩) hjV'
  exact h1.unique (hf.restrictOpen hW) h2

/-- **At a zero, the local index is the index of `f'(x)`.** -/
theorem StrongBundle.isIndexAtLocal_of_isZeroAt (hf : B.IsScFredholmSection f) {x : X}
    (hx : IsZeroAt P f x) {i : ℤ} (hi : B.IsLinOfIndex f x i) : B.IsIndexAtLocal f x i :=
  (StrongBundle.isIndexAt_of_isZeroAt hf.isScSmooth.1 hx hi).isIndexAtLocal hf

/-- **`ind(f, x)` exists at every smooth point, without bump functions** (Definition 6.2.1 (preprint 6.1) with the
text's local section): in a chart `c` around `x`, the sc⁺-section `s(y) = −R(φ(y), Φ(f(x))₂)` of
`P|dom φ` has `s(x) = −f(x)` (`hasScPlusSectionsThrough_of_chart`), and `(f + s)'(x)` is Fredholm
by Theorem 3.1.18 (preprint 3.15) and the germ data of `f + s` at `x` on `P|dom φ`. -/
theorem StrongBundle.exists_isIndexAtLocal (hf : B.IsScFredholmSection f) {x : X}
    (hx : x ∈ PX.smoothSet) : ∃ i : ℤ, B.IsIndexAtLocal f x i := by
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  have hV : IsOpen c.φ.source := c.φ.isOpen_source
  haveI : Nonempty c.φ.source := ⟨⟨x, hxc⟩⟩
  haveI := PX.paracompactSpace_subtype c.φ.source
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen hV) B
  have hfs : IsSection P f := hf.isScSmooth.1
  set BV := B.restrictOpen hV with hBV
  set fV := restrictSection P c.φ.source f hfs with hfV
  have hfV' : BV.IsScFredholmSection fV := hf.restrictOpen hV
  set cV := c.restrictTo B.continuous hV subset_rfl (fV ⟨x, hxc⟩) with hcV
  have hcVmem : cV ∈ BV.atlas.charts :=
    StrongBundle.restrictTo_mem_restrictOpen_atlas hV (B.isChart_of_mem hc) subset_rfl _
  have hsrc : cV.φ.source = univ := eq_univ_of_forall fun v => v.2
  have hsec := StrongBundle.hasScPlusSectionsThrough_of_chart hcVmem hsrc
  have hxs : (⟨x, hxc⟩ : c.φ.source) ∈ (PX.restrictOpen hV).smoothSet :=
    (MPolyfold.mem_smoothSet_restrictOpen_iff hV _).2 hx
  have he : fV ⟨x, hxc⟩ ∈ BV.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => hfV'.isScSmooth.2.mapsTo_levelSet m (mem_iInter.1 hxs m)
  obtain ⟨s₀, hs₀, hs₀x⟩ := hsec _ hxs _ he (hfV'.isScSmooth.1 _)
  set s := sectionSmul (pullbackProj P (Subtype.val : c.φ.source → X)) (fun _ => (-1 : ℝ)) s₀
    with hsdef
  have hs : BV.IsScPlusSection s := hs₀.smul_left (isScSmoothMap_real_const (-1))
  have hzero : IsZeroAt (pullbackProj P (Subtype.val : c.φ.source → X))
      (sectionAdd (pullbackProj P (Subtype.val : c.φ.source → X)) fV s) ⟨x, hxc⟩ := by
    unfold IsZeroAt
    rw [sectionAdd_apply hfV'.isScSmooth.1 hs.1]
    have h1 : (⟨s ⟨x, hxc⟩, hs.1 _⟩ : pullbackProj P (Subtype.val : c.φ.source → X) ⁻¹' {_}) =
        (-1 : ℝ) • ⟨s₀ ⟨x, hxc⟩, hs₀.1 _⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) hs₀.1 _)
    have h2 : (⟨s₀ ⟨x, hxc⟩, hs₀.1 _⟩ : pullbackProj P (Subtype.val : c.φ.source → X) ⁻¹' {_}) =
        ⟨fV ⟨x, hxc⟩, hfV'.isScSmooth.1 _⟩ := Subtype.ext hs₀x
    rw [h1, h2, neg_one_smul, add_neg_cancel]
    rfl
  have hF := theorem_3_1_18_preprint hfV' hs
  obtain ⟨-, c₁, hc₁, hxV₁, hφ₁, h0₁, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hF.germ _ hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  exact ⟨_, hfs, c.φ.source, hV, hxc, s, hs, hzero,
    StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth hzero hc₁ hxV₁ hφ₁ h0₁ hfill ht₀
      ht₀0 dc⟩

/-- **A locally constant local index along a map from a preconnected space is constant**
(`isIndexAt_const_of_forall_eventually` for `IsIndexAtLocal`). -/
theorem isIndexAtLocal_const_of_forall_eventually (hf : B.IsScFredholmSection f) {T : Type*}
    [TopologicalSpace T] [PreconnectedSpace T] {φ : T → X}
    (h : ∀ t, ∃ i : ℤ, ∀ᶠ t' in 𝓝 t, B.IsIndexAtLocal f (φ t') i) :
    ∃ i : ℤ, ∀ t, B.IsIndexAtLocal f (φ t) i := by
  classical
  choose ind hind using h
  have hlc : IsLocallyConstant ind := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    filter_upwards [hind t] with t' ht'
    exact ((hind t').self_of_nhds).unique hf ht'
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨0, fun t => (IsEmpty.false t).elim⟩
  refine ⟨ind t₀, fun t => ?_⟩
  rw [← hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ t) (mem_univ t₀)]
  exact (hind t).self_of_nhds

end IndexAtLocal

/-! ### The section along the path, with the cut-off as data -/

section Device

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}

variable [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

set_option maxHeartbeats 800000 in
/-- **The text's sc⁺-section along the path (E), with the chart and the cut-off as data** (the
proof of `exists_isScPlusSection_pullback_of_path`): for an sc-smooth section `f`, an sc-smooth
path `φ : ℝⁿ → X`, a strong bundle chart `c` of the atlas around `φ(t₀)` and an sc-smooth `β₂`
supported in `dom φ_c` and equal to `1` near `φ(t₀)`, there is an sc⁺-section `S` of `π*P` with
`f̃ + S = 0` along the graph of `φ` near `t₀`.  With bump functions, `β₂` is a bump; on the
restriction `P|V` to a chart domain, `β₂ = 1` (`exists_isScPlusSection_pullback_of_path_of_chart`). -/
theorem exists_isScPlusSection_pullback_of_path_of_bump {f : X → Y}
    (hf : B.IsScSmoothSection f) {φ : (Fin n → ℝ) → X}
    (hφ : (rnPolyfold n).IsScSmoothMap PX φ) (t₀ : Fin n → ℝ) {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hxc : φ t₀ ∈ c.φ.source) {β₂ : X → ℝ}
    (hβ₂ : PX.IsScSmoothMap realPolyfold β₂) (hβ₂s : tsupport β₂ ⊆ c.φ.source)
    (hβ₂1 : ∀ᶠ y in 𝓝 (φ t₀), β₂ y = 1) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (t, φ t) := by
  classical
  have hfs : IsSection P f := hf.1
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  -- a reparametrization of the path into the domain of the chart
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (c.φ.isOpen_source.preimage hφc) t₀ hxc
  obtain ⟨σ, hσ, hσid, hσball⟩ := exists_contDiff_eq_id_near_mapsTo t₀ hε
  set ψ : (Fin n → ℝ) → X := φ ∘ σ with hψdef
  have hψ : (rnPolyfold n).IsScSmoothMap PX ψ := hφ.comp (isScSmoothMap_rn_of_contDiff hσ)
  have hψc : ∀ t, ψ t ∈ c.φ.source := fun t => hball (hσball t)
  -- the curve `g(a) = Φ(f(ψ(a)))` is sc-smooth into `E ⊕ F`, hence into `E¹ ⊕ F¹`
  have hfψ : (rnPolyfold n).IsScSmoothMap B.toMPolyfold0 (f ∘ ψ) := hf.2.comp hψ
  have h1 := hfψ.smooth (rnChart n 0) (c.toMChart B.continuous) (isChart_rnChart 0)
    (B.isChart_toMChart hc) univ isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    (fun t _ => c.mem_source_of_proj (by rw [Function.comp_apply, hfs]; exact hψc t))
  rw [← rnChart_source 0, (rnChart n 0).image_source, rnChart_model_O] at h1
  set g : (Fin n → ℝ) → (c.φ.model.E.prod c.F) 0 := fun a => c (f (ψ (a + 0))) with hgdef
  have hg : IsScSmooth (E := rnSc n) (F := c.φ.model.E.prod c.F) univ g :=
    h1.comp_isScSmooth (ScRetraction.id (rn_relOpen_univ n)) (image_id _)
  have hg1 := hg.shift (isScDomain_univ _)
  have hlv : (rnSc n).lvlSet (univ : Set ((rnSc n) 0)) 1 = univ := by
    ext a; exact ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩
  rw [hlv] at hg1
  have hg1' : IsScSmooth (E := rnSc n) (F := c.φ.model.E.shift.prod c.F.shift) univ
      (fun a => levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a) := hg1
  set ê₁ : (Fin n → ℝ) → c.F 1 :=
    fun a => (levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a).2 with hê₁def
  have hê₁ : IsScSmooth (E := rnSc n) (F := c.F.shift) univ ê₁ := hg1'.snd (isScDomain_univ _)
  have hê₁base : ∀ a, c.F.toBase 1 (ê₁ a) = (c (f (ψ a))).2 := fun a => by
    have h := IsSc0.toBase_levelMap (hg 0) (m := 1) (x := a)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase] at h
    have h2 := congrArg Prod.snd h
    exact h2.trans (by simp only [hgdef, add_zero])
  -- the product chart at `t₀` over `c`
  set d := PullbackChartData.ofProd c t₀ with hd
  set q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) := paramLift f hfs (t₀, φ t₀)
    with hq₀
  set pc := d.toChart q₀ with hpc
  have hpcmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  -- the local section `τ(a, u) = −R[1](u, ê₁(a + t₀))₂`
  set τ : ((rnSc n).prod c.φ.model.E) 0 → c.F 1 :=
    fun z => -(shiftFiber c.R (z.2, ê₁ (z.1 + t₀))).2 with hτdef
  have hRfib : ∀ u ∈ c.U, ∀ b, (c.R (u, c.F.toBase 1 (ê₁ b))).2 ∈ range (c.F.toBase 1) :=
    fun u hu b => (c.isRetraction.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩ _
      ⟨ê₁ b, rfl⟩).2
  have hτbase : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z.2 ∈ c.U →
      c.F.toBase 1 (τ z) = -(c.R (z.2, c.F.toBase 1 (ê₁ (z.1 + t₀)))).2 := fun z hz => by
    simp only [hτdef, map_neg, shiftFiber]
    rw [Function.invFun_eq (hRfib z.2 hz _)]
  -- `(z, τ(z)) ∈ K[1]` for `z ∈ ℝⁿ × O`
  have hτK : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z ∈ univ ×ˢ c.φ.model.O →
      (z, c.F.toBase 1 (τ z)) ∈ pc.K := fun z hz => by
    have hz2 : z.2 ∈ c.φ.model.O := hz.2
    have hzU : z.2 ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hz2)
    change _ ∈ pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)
    rw [d.image_eq_Kg]
    refine ⟨by rw [d.RZ_retract]; exact hz, ?_⟩
    have hgz : d.g z = z.2 := by
      change c.φ (c.φ.symm z.2) = z.2
      exact c.φ.apply_symm_apply hz2
    rw [hgz, hτbase z hzU]
    set h := c.F.toBase 1 (ê₁ (z.1 + t₀)) with hh
    have hR : c.R (z.2, h) ∈ c.K := ⟨_, ⟨hzU, mem_univ _⟩, rfl⟩
    have hr : (c.R (z.2, h)).1 = z.2 :=
      (c.isRetraction.fst_independent z.2 hzU h 0).trans
        (StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hz2))
    have hmem : (z.2, (c.R (z.2, h)).2) ∈ c.K := by
      have : (z.2, (c.R (z.2, h)).2) = c.R (z.2, h) := Prod.ext hr.symm rfl
      rw [this]; exact hR
    have := c.smul_mem_K hmem (-1)
    rwa [neg_one_smul] at this
  have hτ : IsScSmoothRetractMap pc.φ.model.E pc.φ.model.C pc.φ.model.O
      (pc.φ.model.E.prod pc.F.shift) (pc.φ.model.C ×ˢ univ) (strongShiftOne pc.K)
      (fun z => (z, τ z)) := by
    refine ⟨fun z hz => hτK z hz, fun R hR => ?_⟩
    · have hU := R.isScDomain
      set R' : pc.φ.model.E 0 → ((rnSc n).prod c.φ.model.E) 0 := fun w => R w with hR'def
      have hRO : ∀ w ∈ R.U, R' w ∈ univ ×ˢ c.φ.model.O := fun w hw => by
        change R w ∈ pc.φ.model.O
        rw [← hR]; exact R.apply_mem_retract hw
      have hRsm : IsScSmooth (E := pc.φ.model.E) (F := (rnSc n).prod c.φ.model.E) R.U R' :=
        R.isScSmooth
      have hadd : IsScSmooth (E := pc.φ.model.E) (F := rnSc n) R.U
          (fun w => (R' w).1 + t₀) :=
        (hRsm.fst hU).add hU (isScSmooth_const_of_mem_smooth hU
          ((rnSc n).mem_smooth_iff.2 fun m => ⟨t₀, ScBanach.const_toBase _ m _⟩))
      have hpair : IsScSmooth (E := pc.φ.model.E) (F := c.φ.model.E.prod c.F.shift) R.U
          (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) :=
        IsScSmooth.scPair hU (hRsm.snd hU)
          (IsScSmooth.comp hU (isScDomain_univ _) hê₁ hadd (mapsTo_univ _ _))
      have hmaps : MapsTo (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) R.U (c.U ×ˢ univ) :=
        fun w hw => ⟨StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ (hRO w hw).2),
          mem_univ _⟩
      have hsf := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
        c.isRetraction.isScSmooth_one hpair hmaps
      have hτR : IsScSmooth (E := pc.φ.model.E) (F := c.F.shift) R.U (τ ∘ R) :=
        ((hsf.snd hU).neg hU).congr hU fun _ _ => rfl
      exact (R.isScSmooth.scPair hU hτR).congr hU fun _ _ => rfl
  -- the bump `β(t, x) = β₂(x)`
  set β : (Fin n → ℝ) × X → ℝ := fun p => β₂ p.2 with hβdef
  have hβ : ((rnPolyfold n).prod PX).IsScSmoothMap realPolyfold β :=
    hβ₂.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)
  have hβs : tsupport β ⊆ pc.φ.source := by
    have : tsupport β ⊆ Prod.snd ⁻¹' tsupport β₂ :=
      closure_minimal (fun p hp => subset_closure (show β₂ p.2 ≠ 0 from hp))
        (isClosed_closure.preimage continuous_snd)
    exact fun p hp => ⟨mem_univ _, hβ₂s (this hp)⟩
  set S := StrongBundle.cutoffSection pc β τ with hSdef
  have hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S :=
    StrongBundle.isScPlusSection_cutoffSection hpcmem hβ hβs hτ
  refine ⟨S, hS, ?_⟩
  have hGs : IsSection (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := n) f hfs) S) :=
    (isSection_pullbackLift _).sectionAdd hS.1
  filter_upwards [hσid, hφc.continuousAt.eventually hβ₂1] with t hσt hβt
  have hxt : φ t ∈ c.φ.source := by
    have := hψc t
    simp only [hψdef, Function.comp_apply, hσt] at this
    exact this
  rw [isZeroAt_pullback_iff_pullbackSlice hGs t (φ t), pullbackSlice_sectionAdd_paramLift hfs hS.1 t]
  have hsl : IsSection P (Polyfold.pullbackSlice S t) := hS.1.pullbackSlice t
  refine (c.isZeroAt_iff (hfs.sectionAdd hsl) hxt).2 ?_
  change (c (sectionAdd P f (Polyfold.pullbackSlice S t) (c.φ.symm (c.φ (φ t))))).2 = 0
  rw [c.φ.symm_apply_apply hxt, sectionAdd_apply hfs hsl, c.snd_add hxt]
  -- the fibre component of the slice at `φ(t)`
  have hty : (t, φ t) ∈ pc.φ.source := ⟨mem_univ _, hxt⟩
  have hSval : (c (Polyfold.pullbackSlice S t (φ t))).2 =
      c.F.toBase 1 (β (t, φ t) • τ (pc.φ (t, φ t))) :=
    congrArg Prod.snd (StrongBundle.apply_cutoffSection hτ.mapsTo hty)
  change (c (f (φ t))).2 + (c (Polyfold.pullbackSlice S t (φ t))).2 = 0
  rw [hSval, show β (t, φ t) = 1 from hβt, one_smul]
  have hpcφ : pc.φ (t, φ t) = (t - t₀, c.φ (φ t)) := rfl
  rw [hpcφ, hτbase _ (StrongRetr.mem_U_of_mem_O c.isRetraction
    (c.r_image ▸ c.φ.mapsTo_model _ hxt))]
  change (c (f (φ t))).2 + -(c.R (c.φ (φ t), c.F.toBase 1 (ê₁ (t - t₀ + t₀)))).2 = 0
  rw [sub_add_cancel, hê₁base t]
  have hψt : ψ t = φ t := by simp [hψdef, hσt]
  rw [hψt]
  have hK : (c.φ (φ t), (c (f (φ t))).2) ∈ c.R '' (c.U ×ˢ univ) := by
    have h := c.toPartialEquiv.map_source (c.mem_source_of_proj (by rw [hfs]; exact hxt))
    rw [c.target_eq] at h
    have e : c (f (φ t)) = (c.φ (φ t), (c (f (φ t))).2) :=
      Prod.ext (by rw [c.fst_apply (by rw [hfs]; exact hxt), hfs]) rfl
    exact e ▸ h
  have hρ := StrongRetr.ρ_eq_self_of_mem_K c.isRetraction
    (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model _ hxt)) hK
  change (c.R (c.φ (φ t), (c (f (φ t))).2)).2 = (c (f (φ t))).2 at hρ
  rw [hρ]
  exact add_neg_cancel _


/-- **The section along the path on a bundle with a chart over the whole base, without
cut-off** (`β = 1`): the text's `s(t, x) = R(x, f(φ(t)))`. -/
theorem exists_isScPlusSection_pullback_of_path_of_chart {f : X → Y}
    (hf : B.IsScSmoothSection f) {φ : (Fin n → ℝ) → X}
    (hφ : (rnPolyfold n).IsScSmoothMap PX φ) (t₀ : Fin n → ℝ) {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hsrc : c.φ.source = univ) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (t, φ t) :=
  exists_isScPlusSection_pullback_of_path_of_bump hf hφ t₀ hc (hsrc ▸ mem_univ _)
    (isScSmoothMap_real_const 1) (by rw [hsrc]; exact subset_univ _)
    (Eventually.of_forall fun _ => rfl)

/-- **The stabilizing sections on `ℝⁿ × X` without bump functions**: if `P` has a chart of the
atlas over the whole base, so has `π*P` (the product chart), hence `π*P` has sc⁺-sections through
every smooth fibre point (`R(·, e)` in the product chart). -/
theorem hasScPlusSectionsThrough_pullback_rn_of_chart {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hsrc : c.φ.source = univ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).HasScPlusSectionsThrough := by
  set pc := (PullbackChartData.ofProd (n := n) c 0).toChart
    (paramLift (n := n) (fiberZero P) (proj_fiberZero P) (0, c.φ.symm 0)) with hpc
  have hpcmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨PullbackChartData.ofProd (n := n) c 0, _, hc, rfl⟩
  have hsrc' : pc.φ.source = univ :=
    eq_univ_of_forall fun p => ⟨mem_univ _, show p.2 ∈ c.φ.source by rw [hsrc]; exact mem_univ _⟩
  exact StrongBundle.hasScPlusSectionsThrough_of_chart hpcmem hsrc'

end Device

/-! ### Proposition 6.2.2 (preprint 6.2) with the text's hypotheses -/

section Prop62

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The index of `f̃ + S` is constant along the graph, from sections through the fibre
points** (`isLinOfIndex_paramLift_sectionAdd_eventually_const` with `HasScPlusSectionsThrough` of
`π*P` in place of the bump functions). -/
theorem isLinOfIndex_paramLift_sectionAdd_eventually_const_of_sections
    [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    (hsec : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).HasScPlusSectionsThrough)
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    {φ : (Fin 1 → ℝ) → X} {t₀ : Fin 1 → ℝ} (hφ : ContinuousAt φ t₀)
    (hz : ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t)) :
    ∃ i : ℤ, ∀ᶠ t in 𝓝 t₀, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, φ t) i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ := index_locally_constant_of_sections hsec
    (theorem_3_1_18_tame hf.param hS) hz.self_of_nhds
  refine ⟨i, ?_⟩
  filter_upwards [hz, (continuousAt_id.prodMk hφ).preimage_mem_nhds (hVo.mem_nhds hxV)]
    with t ht htV
  exact hall _ htV ht

/-- **Proposition 6.2.2 (preprint 6.2) near `t₀`, on the restriction to a chart domain**: let `f` have tame germ
data and `φ : ℝ → X` be sc-smooth.  Then for every `t₀` there is `i` with
`ind(f, φ(t)) = i` (Definition 6.2.1 (preprint 6.1) with local sections) for all `t` near `t₀`.  The text's
device on `P|V`, `V = dom φ_c` for a chart `c` around `φ(t₀)`: the path reparametrized into `V`,
the section along the path without cut-off, the stabilizing sections `R(·, eᵢ)` in the product
chart, the local constancy along the zero set and the slice relation. -/
theorem isIndexAtLocal_eventually_const_of_path (hf : B.IsScFredholmSectionTame f)
    {φ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) (t₀ : Fin 1 → ℝ) :
    ∃ i : ℤ, ∀ᶠ t in 𝓝 t₀, B.IsIndexAtLocal f (φ t) i := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  -- the chart around `φ(t₀)`, its domain `V`, and the bundle `P|V`
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B (φ t₀)
  have hV : IsOpen c.φ.source := c.φ.isOpen_source
  haveI : Nonempty c.φ.source := ⟨⟨φ t₀, hxc⟩⟩
  haveI := PX.paracompactSpace_subtype c.φ.source
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen hV) B
  set PV := PX.restrictOpen hV with hPV
  set BV := B.restrictOpen hV with hBV
  set fV := restrictSection P c.φ.source f hfs with hfVdef
  have hfV : BV.IsScFredholmSectionTame fV := hf.restrictOpen hV
  haveI := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PV
  haveI := paracompactSpace_pullbackSpace
    (f := (Prod.snd : (Fin 1 → ℝ) × c.φ.source → c.φ.source)) ((rnPolyfold 1).prod PV) BV
  -- the reparametrized path, with values in `V`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (c.φ.isOpen_source.preimage hφc) t₀ hxc
  obtain ⟨σ, hσ, hσid, hσball⟩ := exists_contDiff_eq_id_near_mapsTo t₀ hε
  set ψ : (Fin 1 → ℝ) → X := φ ∘ σ with hψdef
  have hψ : (rnPolyfold 1).IsScSmoothMap PX ψ := hφ.comp (isScSmoothMap_rn_of_contDiff hσ)
  have hψc : ∀ t, ψ t ∈ c.φ.source := fun t => hball (hσball t)
  set ψV : (Fin 1 → ℝ) → c.φ.source := fun t => ⟨ψ t, hψc t⟩ with hψVdef
  have hψV : (rnPolyfold 1).IsScSmoothMap PV ψV :=
    MPolyfold.IsScSmoothMap.codRestrict_restrictOpen hV hψ hψc
  have hψVc : Continuous ψV := continuousOn_univ.1 hψV.continuousOn
  -- the chart `c|V` of `P|V`, over the whole base
  set cV := c.restrictTo B.continuous hV subset_rfl (fV ⟨φ t₀, hxc⟩) with hcV
  have hcVmem : cV ∈ BV.atlas.charts :=
    StrongBundle.restrictTo_mem_restrictOpen_atlas hV (B.isChart_of_mem hc) subset_rfl _
  have hsrc : cV.φ.source = univ := eq_univ_of_forall fun v => v.2
  -- the section along the path, the sections through the fibre points, the index
  obtain ⟨S, hS, hz⟩ :=
    exists_isScPlusSection_pullback_of_path_of_chart hfV.isScSmooth hψV t₀ hcVmem hsrc
  have hsec := hasScPlusSectionsThrough_pullback_rn_of_chart (n := 1) hcVmem hsrc
  obtain ⟨i, hi⟩ := isLinOfIndex_paramLift_sectionAdd_eventually_const_of_sections hsec hfV hS
    hψVc.continuousAt hz
  refine ⟨i - 1, ?_⟩
  filter_upwards [hz, hi, hσid] with t ht hti hσt
  have hφtV : φ t ∈ c.φ.source := by have := hψc t; simpa [hψdef, hσt] using this
  have hpt : ψV t = ⟨φ t, hφtV⟩ := Subtype.ext (by simp [hψVdef, hψdef, hσt])
  have h := StrongBundle.isIndexAt_of_pullback_isLinOfIndex hfV.toIsScFredholmSection hS ht hti
  rw [hpt] at h
  exact ⟨hfs, c.φ.source, hV, hφtV, h⟩

/-- **Proposition 6.2.2 (preprint 6.2) (stability of the index along sc-smooth paths), with the text's
hypotheses**: let `f` be an sc-Fredholm section with tame germ data (Definition 3.6.4 (preprint 3.51)) of a strong
bundle `P : Y → X` — no bump functions — and `φ : ℝ → X` an sc-smooth path.  Then
`ind(f, φ(t))` (Definition 6.2.1 (preprint 6.1) with a locally defined sc⁺-section, `IsIndexAtLocal`) is one
integer for all `t`; in particular `ind(f, φ(0)) = ind(f, φ(1))`.  The proof is the text's:
near each `t₀` the device of `IndexAlongPathsDevice.lean` on the restriction of `P` to the domain
of a chart around `φ(t₀)` (`isIndexAtLocal_eventually_const_of_path`), where the sc⁺-sections of
the text need no cut-off ("we do not need a sc-smooth partition of unity"), and the
preconnectedness of `ℝ` (`isIndexAtLocal_const_of_forall_eventually`). -/
theorem proposition_6_2_2_local (hf : B.IsScFredholmSectionTame f) {φ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAtLocal f (φ t) i :=
  isIndexAtLocal_const_of_forall_eventually hf.toIsScFredholmSection fun t₀ =>
    isIndexAtLocal_eventually_const_of_path hf hφ t₀

/-- **Proposition 6.2.2 (preprint 6.2), the text's form**: `ind(f, φ(0)) = ind(f, φ(1))` for any two values `i`,
`j` of the local index at the ends of the path (`IsIndexAtLocal.unique`). -/
theorem proposition_6_2_2_local' (hf : B.IsScFredholmSectionTame f) {φ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) {i j : ℤ}
    (hi : B.IsIndexAtLocal f (φ 0) i) (hj : B.IsIndexAtLocal f (φ 1) j) : i = j := by
  obtain ⟨k, hk⟩ := proposition_6_2_2_local hf hφ
  exact (hi.unique hf.toIsScFredholmSection (hk 0)).trans
    ((hk 1).unique hf.toIsScFredholmSection hj)

end Prop62

end Polyfold
