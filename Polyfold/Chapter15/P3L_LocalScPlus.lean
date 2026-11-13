import Polyfold.Chapter13.P3M_ScPlusSectionOn
import Polyfold.Chapter15.P3T_LinearizationIntrinsic
import Polyfold.Chapter3.RestrictOpenGerms
import Polyfold.Chapter3.TameGermsAddG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2 (pp. 688–690), preparation: the sections `f − sᵢ` of the proof of Theorem 15.2.2 (2017:
Theorem 15.2) as sc-Fredholm sections of the restricted bundle `W|O`.

# Local sc⁺-sections on the restriction `W|O`

## The text, paraphrased

(Proof of Theorem 15.2.2, p. 689) For a local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on an
open `U'(x)`, the section `f − sᵢ` is an sc-Fredholm section near `x`, and the implicit function
theorem (Theorem 3.6.8) applies to it.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsScPlusSectionOn.principal_mem_range_of_isChart`,
  `IsScPlusSectionOn.isScSmoothRetractMap_localRepOne_of_isChart`: a local sc⁺-section on the
  open set `O` (Definition 13.2.1, `IsScPlusSectionOn`) is an sc⁺-section in every strong bundle
  chart of `P` (compatible with the atlas, not only the charts of the atlas) whose domain lies in
  `O` — the local form of Part I's `IsScPlusSection.principal_mem_range`,
  `IsScPlusSection.isScSmoothRetractMap_one`.
* `IsScPlusSectionOn.restrictOpen`: **a local sc⁺-section on `O` is a (global) sc⁺-section of
  the restriction `W|O`** (Part I's `StrongBundle.restrictOpen`, the pull-back along `O → X`).
* `subSec f s O`: the global section `f + (−1)·s` (with `s` extended by `0` off `O`); on `O` it
  is `f − s`: `principal_subSec`, `isZeroAt_subSec_iff`.
* `subRestrict hO f s`: its restriction to `W|O`, and
  **`isScFredholmSectionTame_subRestrict`**: for an sc-Fredholm section `f` with germ data in tame
  charts (`IsScFredholmSectionTame`, the reading of Part I's Theorem 3.6.8, rows V3.85, V3.103) and
  a local sc⁺-section `s` on `O`, `f − s` is an sc-Fredholm section of `W|O` with germ data in
  tame charts (Part I's Theorem 3.1.18, `theorem_3_1_18_tame`, on `W|O`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr

variable {A : SEP.{u}}

/-! ### Local sc⁺-sections in compatible charts -/

/-- The principal part of a local sc⁺-section on `O` takes values in `F₁` in every strong bundle
chart of `P` with domain in `O` (the local form of `IsScPlusSection.principal_mem_range`). -/
theorem IsScPlusSectionOn.principal_mem_range_of_isChart {s : A.Obj → A.W} {O : Set A.Obj}
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.Obj} (hx : x ∈ c.φ.source) :
    (c (s x)).2 ∈ range (c.F.toBase 1) := by
  obtain ⟨c', hc', hsx⟩ := A.B.atlas.cover (s x)
  have hxV' : x ∈ c'.φ.source := by
    rw [c'.source_eq, mem_preimage, hs.1 x (hsub hx)] at hsx; exact hsx
  have h1 : (c' (s x)).2 ∈ range (c'.F.toBase 1) := hs.mem_range hc' ⟨hsub hx, hxV'⟩
  have h2 := (hc c' hc').2.2.2.2.2 (c' (s x))
    ⟨s x, ⟨hsx, c.mem_source_of_proj (by rw [hs.1 x (hsub hx)]; exact hx)⟩, rfl⟩ h1
  rw [c'.transition_apply c hsx] at h2
  exact h2

/-- `Φ(s(φ⁻¹ z))[1] = (z, ŝ₁(z))` on `O` for a section on the domain of the chart. -/
theorem localRepOne_eq_of_sub {s : A.Obj → A.W} {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ O) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    localRepOne c s z = (z, c.principalLift s z) := by
  rw [c.localRepOne_eq s z]
  refine Prod.ext ?_ rfl
  have hzV : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  change (c (s (c.φ.symm z))).1 = z
  rw [c.fst_apply (by rw [hsec _ (hsub hzV)]; exact hzV), hsec _ (hsub hzV),
    c.φ.apply_symm_apply hz]

/-- **A local sc⁺-section on `O` is an sc⁺-section in every strong bundle chart of `P` with domain
in `O`**: its representative `O → K[1]` is sc-smooth (the local form of
`IsScPlusSection.isScSmoothRetractMap_one`; the chart need not belong to the atlas). -/
theorem IsScPlusSectionOn.isScSmoothRetractMap_localRepOne_of_isChart {s : A.Obj → A.W}
    {O : Set A.Obj} (hs : IsScPlusSectionOn A s O) (hO : IsOpen O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (localRepOne c s) := by
  have hP := A.B.continuous
  have hsec : ∀ y ∈ O, A.P (s y) = y := hs.1
  have hmaps : MapsTo (fun z => (z, c.principalLift s z)) c.φ.model.O (strongShiftOne c.K) := by
    intro z hz
    have hzV : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
    change (z, c.F.toBase 1 (c.principalLift s z)) ∈ c.K
    have hpr : c.principal s z ∈ range (c.F.toBase 1) :=
      hs.principal_mem_range_of_isChart hc hsub hzV
    rw [StrongBundleChart.principalLift, Function.invFun_eq hpr]
    have happ : c (s (c.φ.symm z)) = (z, c.principal s z) := apply_localSection hsec hsub hz
    rw [← happ, ← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hsec _ (hsub hzV)]; exact hzV), rfl⟩
  have hmain : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (fun z => (z, c.principalLift s z)) := by
    refine IsScSmoothRetractMap.of_locally hmaps fun z hz => ?_
    set x := c.φ.symm z with hx
    have hxV : x ∈ c.φ.source := c.φ.symm_mapsTo hz
    obtain ⟨c', hc', hsx⟩ := A.B.atlas.cover (s x)
    have hxV' : x ∈ c'.φ.source := by
      rw [c'.source_eq, mem_preimage, hsec x (hsub hxV)] at hsx; exact hsx
    obtain ⟨W, hW, hWeq⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
      inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
    refine ⟨W, hW, ?_, ?_⟩
    · have : z ∈ c.φ '' (c.φ.source ∩ c'.φ.source) := ⟨x, ⟨hxV, hxV'⟩, c.φ.apply_symm_apply hz⟩
      rw [hWeq] at this; exact this.2
    rw [← hWeq]
    have hcomp : c.φ.Compatible c'.φ := c.isChart.compatible c'.isChart (P := A.X.PObj)
    have h1 : IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ.overlap c'.φ) c'.φ.model.E
        c'.φ.model.C (c'.φ.overlap c.φ) (c.φ.transition c'.φ) :=
      hcomp.1.mono_target (c.φ.transition_mapsTo c'.φ)
    have h2 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C (c'.φ.overlap c.φ)
        (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ) (strongShiftOne (c'.overlap c))
        (StrongBundle.localRepOne c' s) := by
      have hL := hs.isScSmoothRetractMap_localRepOne hO hc' x
      have hret := c'.φ.isScRetract_image (s := O ∩ c'.φ.source) inter_subset_right
        (hO.inter c'.φ.isOpen_source)
      have hsubov : c'.φ.overlap c.φ ⊆ c'.φ '' (O ∩ c'.φ.source) := by
        rintro _ ⟨y, hy, rfl⟩; exact ⟨y, ⟨hsub hy.2, hy.1⟩, rfl⟩
      refine (hL.mono_source hret hsubov).mono_target ?_
      rintro _ ⟨y, hy, rfl⟩
      have hy1 : (c' (s y)).2 ∈ range (c'.F.toBase 1) := hs.mem_range hc' ⟨hsub hy.2, hy.1⟩
      have hrep : StrongBundle.localRepOne c' s (c'.φ y) =
          ((c' (s y)).1, Function.invFun (c'.F.toBase 1) (c' (s y)).2) := by
        rw [StrongBundle.localRepOne, c'.φ.symm_apply_apply hy.1]
      change ((StrongBundle.localRepOne c' s (c'.φ y)).1,
        c'.F.toBase 1 (StrongBundle.localRepOne c' s (c'.φ y)).2) ∈ c'.overlap c
      rw [hrep]
      simp only [Function.invFun_eq hy1, Prod.mk.eta]
      exact ⟨s y, ⟨c'.mem_source_of_proj (by rw [hsec y (hsub hy.2)]; exact hy.1),
        c.mem_source_of_proj (by rw [hsec y (hsub hy.2)]; exact hy.2)⟩, rfl⟩
    have h3 : IsScSmoothRetractMap (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
        (strongShiftOne (c'.overlap c)) (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
        (strongShiftOne c.K) (shiftFiber (c'.transition c)) := by
      refine (hc c' hc').2.2.2.1.mono_target ?_
      intro p hp
      have := (hc c' hc').2.2.2.1.mapsTo hp
      change (_, _) ∈ c.overlap c' at this
      change (_, _) ∈ c.K
      rw [← c.image_source]
      exact image_mono inter_subset_left this
    have hret : IsScRetract (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
        (strongShiftOne (c'.overlap c)) := c'.isScRetract_overlap_one c hP
    refine ((h3.comp h2 hret).comp h1 (c'.φ.isScRetract_overlap c.φ)).congr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply]
    rw [c.φ.transition_apply c'.φ hy.1]
    have hsy : s y ∈ c'.toPartialEquiv.source :=
      c'.mem_source_of_proj (by rw [hsec y (hsub hy.1)]; exact hy.2)
    have hy1 : (c' (s y)).2 ∈ range (c'.F.toBase 1) := hs.mem_range hc' ⟨hsub hy.1, hy.2⟩
    have hrep : StrongBundle.localRepOne c' s (c'.φ y) =
        ((c' (s y)).1, Function.invFun (c'.F.toBase 1) (c' (s y)).2) := by
      rw [StrongBundle.localRepOne, c'.φ.symm_apply_apply hy.2]
    rw [hrep]
    unfold shiftFiber
    simp only [Function.invFun_eq hy1, Prod.mk.eta]
    have hcs : c (s y) = (c.φ y, c.principal s (c.φ y)) := by
      have := apply_localSection hsec hsub (c.φ.mapsTo_model y hy.1)
      rwa [c.φ.symm_apply_apply hy.1] at this
    rw [c'.transition_apply c hsy, hcs]
    rfl
  exact hmain.congr fun z hz => (localRepOne_eq_of_sub hsec hsub hz).symm

/-! ### The restriction to `W|O` -/

section Restrict

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

/-- **A local sc⁺-section on `O` is an sc⁺-section of the restriction `W|O`** (for a global
section `s` of `P`; only its values on `O` matter). -/
theorem IsScPlusSectionOn.restrictOpen {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O)
    (hsec : IsSection A.P s) :
    (A.B.restrictOpen hO).IsScPlusSection (restrictSection A.P O s hsec) := by
  refine ⟨isSection_restrictSection hsec, ?_⟩
  rintro _ ⟨c, hc, hsub, q₀, rfl⟩
  refine ⟨fun v hv => ?_, ?_⟩
  · change (c (s v.1)).2 ∈ range (c.F.toBase 1)
    exact hs.principal_mem_range_of_isChart hc hsub hv
  · have h := hs.isScSmoothRetractMap_localRepOne_of_isChart hO hc hsub
    exact h.congr fun z hz =>
      (StrongBundleChart.localRepOne_restrictTo hO A.B.continuous hsub q₀ hsec hz).symm

end Restrict

/-! ### The section `f − s` -/

/-- **The section `f − s`**: `f + (−1)·s` with `s` extended by `0` off `O` (a global section of
`P`; on `O` it is `f − s`). -/
def subSec (f s : A.Obj → A.W) (O : Set A.Obj) : A.Obj → A.W :=
  Polyfold.sectionAdd A.P f (Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O s))

theorem isSection_subSec {f : A.Obj → A.W} (hf : IsSection A.P f) (s : A.Obj → A.W)
    (O : Set A.Obj) : IsSection A.P (subSec f s O) :=
  hf.sectionAdd (isSection_extendZero O s).sectionSmul

/-- The principal part of `f − s` in a chart with domain in `O` is `f̂ − ŝ`. -/
theorem principal_subSec {f s : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ O) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.principal (subSec f s O) z = c.principal f z - c.principal s z := by
  have hzV : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  unfold subSec
  rw [c.principal_sectionAdd hf (isSection_extendZero O s).sectionSmul hz,
    principal_sectionSmul_const c (isSection_extendZero O s) (-1) hz]
  have he : c.principal (extendZero O s) z = c.principal s z := by
    unfold StrongBundleChart.principal
    rw [← extendZero_eqOn hsec (hsub hzV)]
  rw [he, neg_one_smul, sub_eq_add_neg]

/-- On `O`, `f − s` vanishes exactly where `f = s`. -/
theorem isZeroAt_subSec_iff {f s : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {y : A.Obj} (hy : y ∈ O) :
    IsZeroAt A.P (subSec f s O) y ↔ f y = s y := by
  have hs' : A.P (extendZero O s y) = y := isSection_extendZero O s y
  have hey : extendZero O s y = s y := (extendZero_eqOn hsec hy).symm
  have hval : subSec f s O y = (((⟨f y, hf y⟩ : A.P ⁻¹' {y}) +
      ((-1 : ℝ) • (⟨extendZero O s y, hs'⟩ : A.P ⁻¹' {y})) : A.P ⁻¹' {y}) : A.W) := by
    unfold subSec
    rw [sectionAdd_apply hf (isSection_extendZero O s).sectionSmul]
    congr 2
    exact Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) (isSection_extendZero O s) y)
  have hsy : (⟨extendZero O s y, hs'⟩ : A.P ⁻¹' {y}) = ⟨s y, hsec y hy⟩ := Subtype.ext hey
  unfold IsZeroAt
  rw [hval, hsy, neg_one_smul, ← sub_eq_add_neg]
  constructor
  · intro h
    have h' : ((⟨f y, hf y⟩ : A.P ⁻¹' {y}) - ⟨s y, hsec y hy⟩ : A.P ⁻¹' {y}) = 0 :=
      Subtype.ext h
    exact congrArg Subtype.val (sub_eq_zero.1 h')
  · intro h
    have h' : (⟨f y, hf y⟩ : A.P ⁻¹' {y}) = ⟨s y, hsec y hy⟩ := Subtype.ext h
    rw [h', sub_self]
    rfl

section RestrictSub

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

/-- **The section `f − s` of the restriction `W|O`.** -/
def subRestrict (f s : A.Obj → A.W) (hf : IsSection A.P f) :
    O → pullbackSpace A.P (Subtype.val : O → A.Obj) :=
  restrictSection A.P O (subSec f s O) (isSection_subSec hf s O)

include hO in
/-- **`f − s` is an sc-Fredholm section of `W|O` with germ data in tame charts**, for an
sc-Fredholm section `f` with germ data in tame charts and a local sc⁺-section `s` on `O`
(Part I's Theorem 3.1.18, `theorem_3_1_18_tame`, applied on `W|O` to `f|O` and `(−s)|O`). -/
theorem isScFredholmSectionTame_subRestrict {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O) :
    (A.B.restrictOpen hO).IsScFredholmSectionTame
      (subRestrict (O := O) f s hft.isScSmooth.1) := by
  have hf := hft.isScSmooth.1
  have he : IsSection A.P (extendZero O s) := isSection_extendZero O s
  have ht : IsScPlusSectionOn A (Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O s)) O :=
    hs.extendZero.sectionSmul_const hO he (-1)
  have htr := ht.restrictOpen hO he.sectionSmul
  have hfr := hft.restrictOpen hO
  have h := theorem_3_1_18_tame hfr htr
  unfold subRestrict subSec
  rw [restrictSection_sectionAdd hf he.sectionSmul]
  exact h

end RestrictSub

end SBLocalization

end Polyfold
