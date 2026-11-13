import Polyfold.Chapter6.CobordismOrientationEnds2021c
import Polyfold.Chapter6.CobordismRelativeForms2021b

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.7, p. 278–279 (proof
of **Theorem 6.7.1**; preprint Theorem 6.43) and **Remark 6.6.19**, p. 276: the orientation
`e ∧ o₀` of the cobordism `S_F` is the product orientation `e ∧ o_{S_i}` on its two ends.

# The orientation of the cobordism on its ends

* `IsInducedSectionOrientation o₀ og`: the orientation `og` of a section `g` with
  `Lin(g, x) = Lin(f₀, x)` has the values of the orientation `o₀` of `f₀` (the text's
  "orientation of `f₀ + s` coming from `o₀`", Theorem 6.6.18, last paragraph); it holds for
  `o₀.sectionAdd` and is stable under `sectionAdd`.
* `solReadOrOpen_prodFirst_iff`: on a product end, the reading of the orientation `e ∧ o₀` of
  `F = f̃₀ + Ŝ` in the corner coordinates `κ.prodRn` is the standard orientation of `ℝ^{k+1}`
  iff the reading of `og` in `κ` is the standard orientation of `ℝ^k`.
* `isEndProductOrientation_cobOr`: `cobOr` is the product orientation on an end
  `(a, b) × S_{f+s}` of `S_F^{k+1}` (`ProductEnd.IsEndProductOrientation`).
* `cobordismOrientation_of_induced`, `cobordismOrientationHyp`: 4b's `CobordismOrientation`, and
  `CobordismOrientationHyp` for parts (1) and (2) of Theorem 6.7.1.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Orientations with the values of a given orientation -/

section Induced

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f₀ g : X → Y}

/-- **The orientation `og` of `g` has the values of the orientation `o₀` of `f₀`**: in every
chart at every smooth point `x`, `Lin(g, x) = Lin(f₀, x)` and the two orientations of `DET`
over this set agree (Theorem 6.6.18, last paragraph, p. 276: the orientation of `f₀ + s` coming
from `o₀`). -/
def IsInducedSectionOrientation {hf₀ : B.IsScFredholmSection f₀} (o₀ : SectionOrientation f₀ hf₀)
    {hg : B.IsScFredholmSection g} (og : SectionOrientation g hg) : Prop :=
  ∀ (x : X) (hxs : x ∈ PX.smoothSet) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    (hxc : x ∈ c.φ.source),
    ∃ hlin : (chartPtOf c hc hxc hxs).linSet g = (chartPtOf c hc hxc hxs).linSet f₀,
      ∀ (L : ↥(chartPtOf c hc hxc hxs).T →L[ℝ] ↥(chartPtOf c hc hxc hxs).K)
        (hL : L ∈ (chartPtOf c hc hxc hxs).linSet g),
        toChartOr hg hxs c hc hxc (og.1 x hxs) ⟨L, hL⟩ =
          toChartOr hf₀ hxs c hc hxc (o₀.1 x hxs) ⟨L, hlin ▸ hL⟩

theorem IsInducedSectionOrientation.refl {hf₀ : B.IsScFredholmSection f₀}
    (o₀ : SectionOrientation f₀ hf₀) : IsInducedSectionOrientation o₀ o₀ :=
  fun _ _ _ _ _ => ⟨rfl, fun _ _ => rfl⟩

/-- The orientation of `g + s` inherited from `og` has the values of `o₀` when `og` does. -/
theorem IsInducedSectionOrientation.sectionAdd {hf₀ : B.IsScFredholmSection f₀}
    {o₀ : SectionOrientation f₀ hf₀} {hg : B.IsScFredholmSection g}
    {og : SectionOrientation g hg} (h : IsInducedSectionOrientation o₀ og) {s : X → Y}
    (hs : B.IsScPlusSection s) : IsInducedSectionOrientation o₀ (og.sectionAdd hs) := by
  intro x hxs c hc hxc
  obtain ⟨hlin, hval⟩ := h x hxs c hc hxc
  have hlin' := (chartPtOf c hc hxc hxs).linSet_sectionAdd hg.isScSmooth.1 hs
  refine ⟨hlin'.trans hlin, fun L hL => ?_⟩
  have e1 := toChartOr_orSectionAdd hg hs hxs (og.1 x hxs) c hc hxc
  have e2 := (chartPtOf c hc hxc hxs).orSectionAdd_apply hg hs
    (toChartOr hg hxs c hc hxc (og.1 x hxs)) hL
  exact ((congrFun (congrArg Subtype.val e1) ⟨L, hL⟩).trans e2).trans (hval L (hlin' ▸ hL))

end Induced

/-! ### The readings on a product end -/

section Reading

open MPolyfold MPolyfold.CornerCoords

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

/-- **The orientation `e ∧ o₀` of `F = f̃₀ + Ŝ` on a product end, in coordinates** (2021
Remark 6.6.19, p. 276; proof of Theorem 6.7.1, p. 278): let `S_F ∩ Ω' = (a, b) × (S_g ∩ Ω)` and
`F = g̃` over `(a, b)`, and let the orientation `og` of `g` have the values of `o₀`. At
`(t, y)`, `t ∈ (a, b)`, the orientation `SectionOrientation.prodFirst o₀` of `F` read in the
corner coordinates `κ.prodRn` (and the product chart over `c`) is the standard orientation of
`ℝ^{k+1}` iff `og` read in `κ` (and `c`) is the standard orientation of `ℝ^k`. -/
theorem solReadOrOpen_prodFirst_iff (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hŜ : (prodBundle B).IsScPlusSection Ŝ) {Ω' : Set ((Fin 1 → ℝ) × X)} [Fact (IsOpen Ω')]
    [ParacompactSpace ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')]
    {hY' : ((rnPolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')}
    {k : ℕ}
    (hgp' : ∀ z ∈ solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω',
      (prodBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) z)
    (hidx' : ∀ z ∈ solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω',
      (prodBundle B).IsLinOfIndex
        (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) z
        (k + 1 : ℕ))
    {g : X → Y} (hgt : B.IsScFredholmSectionTame g)
    (og : SectionOrientation g hgt.toIsScFredholmSection) {Ω : Set X} [Fact (IsOpen Ω)]
    [ParacompactSpace ↥(solutionSet P g ∩ Ω)] {hY : PX.IsSubMPolyfold (solutionSet P g ∩ Ω)}
    (hgp : ∀ x ∈ solutionSet P g ∩ Ω, B.IsGeneralPositionGerm g x)
    (hidx : ∀ y ∈ solutionSet P g ∩ Ω, B.IsLinOfIndex g y k) {a b : ℝ} (hab : a < b)
    (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b →
      (z ∈ solutionSet (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
        (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω' ↔ z.2 ∈ solutionSet P g ∩ Ω))
    (x₀ : ↥(solutionSet P g ∩ Ω))
    (hFg : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b →
      sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ z =
        paramLift (n := 1) g hgt.isScSmooth.1 z)
    (hInd : IsInducedSectionOrientation o₀ og) (κ : CornerCoords (subPolyfold hY) k)
    (y : ↥(solutionSet P g ∩ Ω)) (t : Fin 1 → ℝ) (ht : t 0 ∈ Ioo a b)
    (hmem : ((t, y.1) : (Fin 1 → ℝ) × X) ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')
    (hyκ : y ∈ κ.s)
    (hxκ' : (⟨(t, y.1), hmem⟩ : ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')) ∈
        (κ.prodRn hY' hab hend x₀).s)
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (d : PX.SubData (solutionSet P g ∩ Ω)) (a₀ : ↥(solutionSet P g ∩ Ω))
    (hyσ : y ∈ (subChart d c.isChart a₀).source)
    (d' : ((rnPolyfold 1).prod PX).SubData (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω'))
    (a₀' : ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω'))
    (hxσ' : (⟨(t, y.1), hmem⟩ : ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')) ∈
        (subChart d' (prodChart c q₀).isChart a₀').source) :
    solReadOrOpen (theorem_3_1_18_tame hf₀.param hŜ) (κ.prodRn hY' hab hend x₀)
        (SectionOrientation.prodFirst hX hbump hf₀ o₀ hŜ) hgp' hidx' (isChart_prodChart hc q₀)
        d' a₀' hxκ' hxσ' = stdOrientation (k + 1) ↔
      solReadOrOpen hgt κ og hgp hidx hc d a₀ hyκ hyσ = stdOrientation k := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have hys : y.1 ∈ PX.smoothSet := hgt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt y.2.1
  have hyc : y.1 ∈ c.φ.source := d.shrink_subset_source c.φ hyσ
  have hzs : ((t, y.1) : (Fin 1 → ℝ) × X) ∈ ((rnPolyfold 1).prod PX).smoothSet :=
    prod_rn_mem_smoothSet_iff.2 hys
  have hF := theorem_3_1_18_tame hf₀.param hŜ
  obtain ⟨hlin, hval⟩ := hInd y.1 hys c hc hyc
  have hmemg : (chartPtOf c hc hyc hys).linZero hgt.toIsScFredholmSection y.2.1 ∈
      (chartPtOf c hc hyc hys).linSet f₀ :=
    hlin ▸ (chartPtOf c hc hyc hys).linZero_mem_linSet hgt.toIsScFredholmSection y.2.1
  have hne : ((chartPtOf c hc hyc hys).linSet f₀).Nonempty := ⟨_, hmemg⟩
  have T2 := (chartPtOf c hc hyc hys).tangentOr_eq_tangentOrOf hf₀.toIsScFredholmSection
    hgt.toIsScFredholmSection y.2.1 (hgp y.1 y.2).isLinSurjAt hmemg _ _ (hval _ _)
  have T1 := tangentOr_toChartOr_prodFirst hX hbump hf₀ o₀ hŜ hys hc hyc q₀ hmem.1
    (hgp' _ hmem).isLinSurjAt hne
  have hz0g : IsZeroAt (pullbackProj P Prod.snd) (paramLift (n := 1) g hgt.isScSmooth.1)
      (t, y.1) := by
    have h := hmem.1
    unfold IsZeroAt at h ⊢
    rw [← hFg _ ht]
    exact h
  have hE := (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
    (mem_prodChart_source q₀ hyc t) hzs).linZero_congr_of_eventuallyEq
    hF.toIsScFredholmSection hgt.toIsScFredholmSection.param hmem.1 hz0g
    (Filter.eventually_of_mem ((isOpen_Ioo.preimage ((continuous_apply 0).comp
      continuous_fst)).mem_nhds ht) fun z hz => hFg z hz)
  have hproj : endProj (solutionSet P g ∩ Ω) x₀ (⟨(t, y.1), hmem⟩ : ↥(solutionSet
      (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
        (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩ Ω')) = y :=
    Subtype.ext (endProj_val x₀ y.2)
  unfold solReadOrOpen
  refine (iff_of_eq (congrArg (fun r => pullOr finrank_euclideanSpace_fin _ r =
    stdOrientation (k + 1)) T1)).trans ?_
  refine Iff.trans ?_ (iff_of_eq (congrArg (fun r => pullOr finrank_euclideanSpace_fin _ r =
    stdOrientation k) T2)).symm
  refine pullOr_tangentOrOf_prodOrLift_iff hc hyc _ (exists_lift_of_smooth c hyc hys).choose_spec
    t q₀ (mem_prodChart_source q₀ hyc t) _ (exists_lift_of_smooth (prodChart c q₀)
      (mem_prodChart_source q₀ hyc t) hzs).choose_spec
    (prodChart_lift_eq _ (exists_lift_of_smooth c hyc hys).choose_spec t q₀ _
      (exists_lift_of_smooth (prodChart c q₀) (mem_prodChart_source q₀ hyc t) hzs).choose_spec)
    hf₀.toIsScFredholmSection hys hne _ hgt.toIsScFredholmSection y.2.1
    (hgp y.1 y.2).isLinSurjAt hmemg hF.toIsScFredholmSection hmem.1 (hgp' _ hmem).isLinSurjAt
    ((chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
      (mem_prodChart_source q₀ hyc t) hzs).linZero_mem_linSet_of_sectionAdd
      hf₀.toIsScFredholmSection.param hŜ hmem.1) hz0g hE _ _ fun s w => ?_
  refine ((coe_solKerEquiv_open hF (κ.prodRn hY' hab hend x₀) (isChart_prodChart hc q₀) d' a₀'
    hxκ' hxσ' _ _ _ (consE s w)).trans (modelDeriv_prodRn hY' hab hend x₀ κ c q₀ d a₀ d' a₀'
    hxκ' hxσ' (hproj.symm ▸ hyσ) ((κ.prodRn hY' hab hend x₀).toBase_zOf _)
    (z := κ.zOf y) (by rw [hproj]; exact κ.toBase_zOf y) (consE s w))).trans
    (Prod.ext rfl ?_)
  symm
  exact coe_solKerEquiv_open hgt κ hc d a₀ hyκ hyσ (hgp y.1 y.2)
    (chartPtOf c hc hyc hys).toBase_z (finrank_linKer_of hgt y.2.1 (hgp y.1 y.2) (hidx y.1 y.2)
      hc hyc _ (chartPtOf c hc hyc hys).toBase_z) w

end Reading

/-! ### The orientation of the cobordism on a product end -/

section Ends

open MPolyfold StrongBundle MPolyfold.CornerCoords

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
  {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
  (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection) {σ₀ σ₁ : X → Y}
  {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 σ₀ σ₁ Ŝ) (k : ℕ)

/-- **The orientation of the cobordism is the product orientation on an end** (2021
Remark 6.6.19, p. 276; proof of Theorem 6.7.1, p. 278): let `S_F^{k+1} = (a, b) × S_{f+s}^k`
and `F = (f + s)~` over `(a, b)`, for an admissible `s` for `f`, and let the orientation
`o.sectionAdd` of `f + s` have the values of `o₀`. Then the orientation `cobOr` of `S_F^{k+1}`
given by `e ∧ o₀` is `e ∧ o_{S_{f+s}}` on this end, the time direction first
(`ProductEnd.IsEndProductOrientation`). -/
theorem isEndProductOrientation_cobOr {f : X → Y} (hf : B.IsScFredholmSectionTame f)
    {N : B.One → ℝ} {U : Set X} {s : X → Y} (hs : B.IsAdmissible f N U s)
    (o : SectionOrientation f hf.toIsScFredholmSection)
    (hInd : IsInducedSectionOrientation o₀ (o.sectionAdd hs.isScPlusSection)) {a b : ℝ}
    (hab : a < b)
    (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b →
      (z ∈ cobPart hf₀ Ŝ k ↔ z.2 ∈ B.solPart f s k))
    (hFg : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b →
      homotopySection f₀ hf₀.isScSmooth.1 Ŝ z = paramLift (n := 1) (sectionAdd P f s)
        (hf.isScSmooth.1.sectionAdd hs.isScPlusSection.1) z)
    (x₀ : ↥(B.solPart f s k)) :
    letI := solPartChartedSpace hX hf hs k
    letI := cobChartedSpace hX hf₀ hC k
    (productEndOfSub (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀
      (hasCornerStructureOfDim_solPart hX hf hs k) (hasCornerStructureOfDim_cobPart hX hf₀ hC k)
      rfl rfl).IsEndProductOrientation (cobOr hX hbump hf₀ o₀ hC k) (solPartOr hX hf hs o k) := by
  let _ := solPartChartedSpace hX hf hs k
  let _ := cobChartedSpace hX hf₀ hC k
  have : Fact (IsOpen (B.solIndexNbhd f s k)) := ⟨isOpen_solIndexNbhd_of_isAdmissible hf hs k⟩
  have : Fact (IsOpen (cobIndexNbhd hf₀ Ŝ k)) := ⟨isOpen_cobIndexNbhd hf₀ hC k⟩
  have : ParacompactSpace ↥(solutionSet P (sectionAdd P f s) ∩ B.solIndexNbhd f s k) :=
    PX.paracompactSpace_subtype _
  have : ParacompactSpace ↥(solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hf₀.isScSmooth.1) Ŝ) ∩
        cobIndexNbhd hf₀ Ŝ k) := ((rnPolyfold 1).prod PX).paracompactSpace_subtype _
  have hcs := hasCornerStructureOfDim_solPart hX hf hs k
  have hY := isSubMPolyfold_solPart hf hs k
  have hY' := isSubMPolyfold_cobPart hf₀ hC k
  intro y₀ x hx
  set κ := (hcs.exists_cornerCoords y₀).choose with hκdef
  have hκ : chartAt (EuclideanQuadrant k) y₀ = κ.toQuadrantChart := chartAt_eq_of_eq hcs rfl y₀
  revert hx
  rw [hκ]
  intro hx
  have heq := endChart_eqOnSource (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀ κ
  have hxκ' : x ∈ (κ.prodRn (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀).s := by
    have h := heq.1 ▸ hx
    exact h
  have h1 : orientationIn (I := 𝓠 (k + 1))
      (endChart (endPH hab hend x₀) a b κ.toQuadrantChart) x (cobOr hX hbump hf₀ o₀ hC k x) =
      orientationIn (I := 𝓠 (k + 1))
        (κ.prodRn (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀).toQuadrantChart x
        (cobOr hX hbump hf₀ o₀ hC k x) := by
    unfold orientationIn
    rw [chartChangeDeriv_eq_of_eqOnSource_right heq _
      (mem_chart_source (EuclideanQuadrant (k + 1)) x) hx]
  refine (iff_of_eq (congrArg (· = stdOrientation (k + 1)) h1)).trans ?_
  obtain ⟨⟨t, x'⟩, hxm⟩ := x
  obtain ⟨ht, hyκ0⟩ := (mem_prodRn_s (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀ κ).1 hxκ'
  have hx'm : x' ∈ B.solPart f s k := (hend (t, x') ht).1 hxm
  have hproj : endProj (B.solPart f s k) x₀ (⟨(t, x'), hxm⟩ : ↥(cobPart hf₀ Ŝ k)) =
      ⟨x', hx'm⟩ := Subtype.ext (endProj_val x₀ hx'm)
  rw [hproj] at hyκ0
  have key : ∀ w : ↥(B.solPart f s k), w = ⟨x', hx'm⟩ →
      (orientationIn (I := 𝓠 (k + 1))
          (κ.prodRn (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀).toQuadrantChart
          (⟨(t, x'), hxm⟩ : ↥(cobPart hf₀ Ŝ k))
          (cobOr hX hbump hf₀ o₀ hC k ⟨(t, x'), hxm⟩) = stdOrientation (k + 1) ↔
        orientationIn (I := 𝓠 k) κ.toQuadrantChart w (solPartOr hX hf hs o k w) =
          stdOrientation k) := by
    rintro _ rfl
    have hyc := mem_orChart (B := B) x'
    have hyσ : (⟨x', hx'm⟩ : ↥(B.solPart f s k)) ∈
        (subChart (hY.data hx'm) (orChart B x').isChart ⟨x', hx'm⟩).source :=
      (hY.data hx'm).mem_shrink (orChart B x').φ hx'm (hY.mem_data_V hx'm) hyc
    have hxσ' : (⟨(t, x'), hxm⟩ : ↥(cobPart hf₀ Ŝ k)) ∈
        (subChart (hY'.data hxm) (prodChart (orChart B x')
          (homotopySection f₀ hf₀.isScSmooth.1 Ŝ (t, x'))).isChart ⟨(t, x'), hxm⟩).source :=
      (hY'.data hxm).mem_shrink (prodChart (orChart B x') _).φ hxm (hY'.mem_data_V hxm)
        (mem_prodChart_source _ hyc t)
    have h2 := orientationIn_solOr_open (Ω := cobIndexNbhd hf₀ Ŝ k)
      (inst := cobChartedSpace hX hf₀ hC k)
      (theorem_3_1_18_tame hf₀.param hC.isScPlusSection)
      (κ.prodRn (isSubMPolyfold_cobPart hf₀ hC k) hab hend x₀)
      (SectionOrientation.prodFirst hX hbump hf₀ o₀ hC.isScPlusSection)
      (fun z hz => hC.gp z hz.1) (fun z hz => cobIndexNbhd_isLinOfIndex hf₀ hC k z hz.2 hz.1)
      (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl
      (isChart_prodChart (isChart_orChart x') (homotopySection f₀ hf₀.isScSmooth.1 Ŝ (t, x')))
      (hY'.data hxm) ⟨(t, x'), hxm⟩ hxκ' hxσ'
    have h3 := orientationIn_solOr_open (Ω := B.solIndexNbhd f s k)
      (inst := solPartChartedSpace hX hf hs k)
      (theorem_3_1_18_tame hf hs.isScPlusSection) κ (o.sectionAdd hs.isScPlusSection)
      (fun x hx => hs.gp x hx.1)
      (fun y hy => isLinOfIndex_of_mem_solIndexNbhd hf hs k y hy.2 hy.1) hcs rfl
      (isChart_orChart x') (hY.data hx'm) ⟨x', hx'm⟩ hyκ0 hyσ
    refine (iff_of_eq (congrArg (· = stdOrientation (k + 1)) h2)).trans
      (Iff.trans ?_ (iff_of_eq (congrArg (· = stdOrientation k) h3)).symm)
    exact solReadOrOpen_prodFirst_iff hX hbump hf₀ o₀ hC.isScPlusSection _ _
      (theorem_3_1_18_tame hf hs.isScPlusSection) (o.sectionAdd hs.isScPlusSection) _ _ hab hend
      x₀ hFg hInd κ ⟨x', hx'm⟩ t ht hxm hyκ0 hxκ' (isChart_orChart x') _ _ _ hyσ _ _ hxσ'
  exact key _ hproj

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- The `t`-constant lifts of equal sections are equal. -/
theorem paramLift_congr {g g' : X → Y} (h : g = g') (hg : IsSection P g) (hg' : IsSection P g')
    (z : (Fin 1 → ℝ) × X) : paramLift (n := 1) g hg z = paramLift (n := 1) g' hg' z := by
  subst h; rfl

include hbump in
/-- **The orientation of the cobordism `S_F`** (2021 Remark 6.6.19, p. 276; proof of
Theorem 6.7.1, p. 278; gap G.66): 4b's `CobordismOrientation` holds for cobordism data between
`f₀ + s₀` and `f₀ + σ₁ = f₁ + s₁` as soon as the orientation `o₁.sectionAdd` of `f₁ + s₁` has
the values of `o₀` (`IsInducedSectionOrientation`). The orientation is `cobOr`, given by
`e ∧ o₀`; on the ends `(0, 1/8) × S₀` and `(7/8, 1) × S₁` it is `e ∧ o_{S_i}`
(`isEndProductOrientation_cobOr`). -/
theorem cobordismOrientation_of_induced {N₀ : B.One → ℝ} {U₀ : Set X} {s₀ : X → Y}
    (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀) {f₁ : X → Y} (hf₁ : B.IsScFredholmSectionTame f₁)
    {N₁ : B.One → ℝ} {U₁ : Set X} {s₁ : X → Y} (hs₁ : B.IsAdmissible f₁ N₁ U₁ s₁)
    (o₁ : SectionOrientation f₁ hf₁.toIsScFredholmSection)
    (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ σ₁ Ŝ)
    (h₁ : sectionAdd P f₀ σ₁ = sectionAdd P f₁ s₁) (k : ℕ)
    (hInd : IsInducedSectionOrientation o₀ (o₁.sectionAdd hs₁.isScPlusSection)) :
    CobordismOrientation hX hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k :=
  cobordismOrientation_of_ends hX hbump hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k
    (fun x₀ => isEndProductOrientation_cobOr hX hbump hf₀ o₀ hC k hf₀ hs₀ o₀
      ((IsInducedSectionOrientation.refl o₀).sectionAdd hs₀.isScPlusSection) (by norm_num)
      (cobPart_end_left hf₀ hs₀ hC k) (fun _ hz => hC.eq_paramLift_left hz.2.le) x₀)
    (fun x₀ => isEndProductOrientation_cobOr hX hbump hf₀ o₀ hC k hf₁ hs₁ o₁ hInd (by norm_num)
      (cobPart_end_right hf₀ hf₁ hs₁ hC h₁ k)
      (fun z hz => (hC.eq_paramLift_right hz.1.le).trans (paramLift_congr h₁ _ _ z)) x₀)

end Ends

/-! ### `CobordismOrientationHyp` -/

section Hyp

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **The orientation of the cobordisms of the proof of 2021 Theorem 6.7.1** (Remark 6.6.19,
p. 276; proof of Theorem 6.7.1, p. 278–279; gap G.66): `CobordismOrientationHyp` holds, for `X`
tame with sc-smooth bump functions. In part (1) both ends carry `o.sectionAdd`; in part (2) the
right end carries `(o₀.sectionAdd S(1, ·)).sectionAdd s₁`, which has the values of `o₀`. -/
theorem cobordismOrientationHyp (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) :
    CobordismOrientationHyp B hX := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  refine ⟨fun f hf o N U s₀ s₁ hs₀ hs₁ Ŝ hC k =>
    cobordismOrientation_of_induced hX hbump hf o hs₀ hf hs₁ o hC rfl k
      ((IsInducedSectionOrientation.refl o).sectionAdd hs₁.isScPlusSection), ?_⟩
  intro f₀ hf₀ o₀ S hf₁ o₁ hHB N₀ U₀ s₀ hs₀ N₁ U₁ s₁ hs₁ Ŝ hC h₁ k
  obtain ⟨hH, rfl⟩ := hHB
  exact cobordismOrientation_of_induced hX hbump hf₀ o₀ hs₀ hf₁ hs₁ _ hC h₁ k
    (((IsInducedSectionOrientation.refl o₀).sectionAdd hH.slice_one).sectionAdd hs₁.isScPlusSection)

end Hyp

end Polyfold
