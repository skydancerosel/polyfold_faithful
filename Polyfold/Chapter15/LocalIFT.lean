import Polyfold.Chapter15.LocalScPlus
import Polyfold.Chapter5.GeneralPosition
import Polyfold.Chapter3.GlobalIFTNearbyOntoG
import Polyfold.Chapter3.GlobalIFTIndexG
import Polyfold.Chapter3.SolutionTangentKernel
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter9.Symmetric
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2 (pp. 688–690), preparation: the implicit function theorem of Part I (Theorem 3.6.8) for the
sections `f − sᵢ` of a local sc⁺-section structure, and the passage between the operators
`(f − sᵢ)'(x) : T_xX → W_x` of `T(f,Λ)(x)` (§15.1) and Part I's chart linearizations.

# The local solution sets `{f = sᵢ}`

## The text, paraphrased

(Proof of Theorem 15.2.2, p. 689) Since `(f − sᵢ)'(x)` is onto, the implicit function theorem
gives a neighbourhood `Uᵢ(x)` on which `{f = sᵢ}` is a submanifold and `(f − sᵢ)'(y)` is onto at
its points.  (Theorem 15.2.5, p. 690) The same at a boundary point when the kernel is in good
position, by Theorem 3.6.8.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `subDeriv c f s z = D((f̂ − ŝ) ∘ r)(z) : E → F`, the chart operator of `(f − s)'`, and
  `ChartOnto c L z` (it maps `T_zO` onto the fibre `K_z`).
* **`surjective_toIntr_subDeriv_iff`**: at a point `x ∈ X₁` with `f(x) = s(x)`, the intrinsic
  operator `(f − s)'(x) = Φ_x⁻¹ ∘ D((f̂ − ŝ) ∘ r)(φ(x)) ∘ Tφ : T_xX → W_x` of §15.1 (`toIntr`) is
  onto iff `ChartOnto` holds in the chart.
* `isLinSurjAt_subRestrict`, `chartOnto_of_isLinSurjAt_subRestrict`: `ChartOnto` in a chart `c`
  with domain in `O` is Part I's "`(f − s)'(x)` onto" (`IsLinSurjAt`) for the section `f − s` of
  the restriction `W|O`.
* **`exists_solutionSet_of_isGoodPosition`** (the step of Theorems 15.2.2 and 15.2.5): if
  `f − s` is in good position at `x` (Part I's Definition 3.6.6 on `W|O`, `IsGoodPositionGermTame`),
  then there is an open `V ∋ x` inside the chart domain with `{y ∈ V | f(y) = s(y)}` a smooth
  finite-dimensional submanifold of `X` (Definition 4.2.1), every such `y` smooth, `f − s` in good
  position at `y` and `ChartOnto` at `y`.
* **`exists_solutionSet_interior`**: the interior case: at `x` with `d_X(x) = 0`, "`ChartOnto` at
  `x`" suffices (Part I's `isGoodPositionGerm_of_isLinSurjAt`).

All of this needs `f` to have germ data in tame charts (`IsScFredholmSectionTame`), the reading
under which Part I's Theorem 3.6.8 holds (rows V3.85, V3.103; with the 2021 untamed notion it does
not hold as we read it, `theorem_3_6_8_untamed_not`, `theorem_3_1_22_untamed_not`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold

variable {A : SEP.{u}}

/-! ### Chart operators -/

/-- **The chart operator of `(f − s)'(z)`**: `D((f̂ − ŝ) ∘ r)(z) : E₀ → F₀`. -/
def subDeriv (c : StrongBundleChart A.X.PObj A.P) (f s : A.Obj → A.W) (z : c.φ.model.E 1) :
    c.φ.model.E 0 →L[ℝ] c.F 0 :=
  scDeriv c.U ((fun y => c.principal f y - c.principal s y) ∘ r c.R) z

/-- **`L` maps `T_zO` onto the fibre `K_z`** (Part I's "`f'(x)` onto", read in the chart `c` at
the level-`1` point `z`). -/
def ChartOnto (c : StrongBundleChart A.X.PObj A.P) (L : c.φ.model.E 0 →L[ℝ] c.F 0)
    (z : c.φ.model.E 1) : Prop :=
  ∀ k, (c.φ.model.E.toBase 1 z, k) ∈ c.K → ∃ v ∈ rangeS (scDeriv c.U (r c.R) z), L v = k

/-- `(f̂ − ŝ) ∘ r` is sc¹ on `U`. -/
theorem isSc1_sub_comp_r {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f) {s : A.Obj → A.W}
    {O : Set A.Obj} (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) :
    IsSc1 c.U ((fun y => c.principal f y - c.principal s y) ∘ r c.R) :=
  ((isScSmooth_principal_comp_r hf hc).sub c.relOpen.isScDomain
    (hs.isScSmooth_principal_comp_r hc hsub)).isSc1

/-! ### The intrinsic operator and the chart -/

/-- **`(f − s)'(x)` onto, intrinsically and in the chart**: for `x ∈ X₁` in the domain of a chart
`c` with domain in `O` and `f(x) = s(x)`, the operator `toIntr c hx (subDeriv c f s z)` of
`T(f,Λ)(x)` (§15.1) is onto `W_x` iff `D((f̂ − ŝ) ∘ r)(z)` maps `T_zO` onto `K_z`, `z` over
`φ(x)`. -/
theorem surjective_toIntr_subDeriv_iff {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hfs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x)) :
    Surjective (toIntr c hx (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)))) ↔
      ChartOnto c (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)))
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) := by
  set y := A.X.PObj.levelVal 1 x with hy
  set z := levelLift c.φ 1 y with hz
  have ha : c.φ.model.E.toBase 1 z = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, ha]; exact c.φ.mapsTo_model y hx)
  -- the operator equals that of the global section `subSec f s O`
  have hsecs : ∀ w ∈ O, A.P (s w) = w := hs.1
  set g := subSec f s O with hg
  have hgs : IsSection A.P g := isSection_subSec hf.1 s O
  have hgrep : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal g z)) := by
    refine (isScSmoothRetractMap_sectionSubOn hf hs hc hsub).congr fun w hw => ?_
    change (w, c.principal (sectionSubOn f s O) w) = (w, c.principal g w)
    rw [principal_sectionSubOn hf.1 hsecs hsub hw, principal_subSec hf.1 hsecs hsub hw]
  have hg1 : IsSc1 c.U (c.principal g ∘ r c.R) := by
    have := hgrep.comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact ((this.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hD : subDeriv c f s z = scDeriv c.U (c.principal g ∘ r c.R) z := by
    refine scDeriv_eq_of_eqOn_relOpen c.relOpen (isSc1_sub_comp_r hf hs hc hsub) hg1 subset_rfl
      subset_rfl (fun u hu => ?_) hzU
    change c.principal f (r c.R u) - c.principal s (r c.R u) = c.principal g (r c.R u)
    rw [principal_subSec hf.1 hsecs hsub (c.r_mem_O hu)]
  have h0 : IsZeroAt A.P g y := (isZeroAt_subSec_iff hf.1 hsecs (hsub hx)).2 hfs
  have hrange : ∀ α, chartOp c hx (subDeriv c f s z) α ∈ LinearMap.range (c.fiberLin hx) := by
    intro α; rw [hD]; exact chartOp_mem_range hgs hgrep hx h0 α
  constructor
  · intro hsurj k hk
    rw [ha] at hk
    obtain ⟨w, hw⟩ := c.mem_range_fiberLin hx hk
    obtain ⟨α, hα⟩ := hsurj w
    have h1 := fiberLin_toIntr c hx hrange α
    rw [hα, hw, chartOp_apply] at h1
    exact ⟨_, (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx α).2,
      h1.symm⟩
  · intro hon w
    have hk : (c.φ.model.E.toBase 1 z, c.fiberLin hx w) ∈ c.K := by
      rw [ha, ← c.apply_fiberLin hx w, ← c.image_source]
      exact ⟨_, c.fiberLin_src hx w, rfl⟩
    obtain ⟨v, hv, hvk⟩ := hon _ hk
    have hvT : v ∈ tangentFiberModel c.isChart hx := (c.mem_tangentFiberModel_iff_rangeS hx v).2 hv
    refine ⟨(tangentFiberEquiv c.isChart hx).symm ⟨v, hvT⟩, c.fiberLin_injective hx ?_⟩
    rw [fiberLin_toIntr c hx hrange, chartOp_apply, Equiv.apply_symm_apply]
    exact hvk

/-! ### The restriction to `W|O` -/

section Restrict

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

include hO in
/-- The chart operator of `f − s` on `W|O`, in the transported chart, is `D((f̂ − ŝ) ∘ r)`. -/
theorem scDeriv_restrictTo_subRestrict {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj))
    {z : c.φ.model.E 1} (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    scDeriv c.U ((c.restrictTo A.B.continuous hO hsub q₀).principal
        (subRestrict (O := O) f s hft.isScSmooth.1) ∘ r c.R) z = subDeriv c f s z := by
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hcV : (A.B.restrictOpen hO).IsChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    restrictOpen_isChart_restrictTo hO hc hsub q₀
  have h1 := StrongBundle.isSc1_principal_comp_r hgO.isScSmooth hcV
  refine scDeriv_eq_of_eqOn_relOpen c.relOpen h1 (isSc1_sub_comp_r hft.isScSmooth hs hc hsub)
    subset_rfl subset_rfl (fun u hu => ?_) hzU
  have huO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu
  have e1 := StrongBundleChart.principal_restrictTo hO A.B.continuous hsub q₀
    (isSection_subSec hft.isScSmooth.1 s O) huO
  have e2 := principal_subSec hft.isScSmooth.1 hs.1 hsub huO
  exact e1.trans e2

include hO in
/-- **`ChartOnto` is Part I's `IsLinSurjAt` on `W|O`**: in a chart `c` with domain in `O`, if
`D((f̂ − ŝ) ∘ r)(z)` maps `T_zO` onto `K_z` at some `z` over `φ(x)`, then `(f − s)|O` has
surjective linearization at `x` (`IsLinSurjAt`, Theorems 3.1.22, 3.6.10). -/
theorem isLinSurjAt_subRestrict {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) {x : A.Obj} (hx : x ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hon : ChartOnto c (subDeriv c f s z) z) :
    (A.B.restrictOpen hO).IsLinSurjAt (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨x, hsub hx⟩ := by
  set q₀ := subRestrict (O := O) f s hft.isScSmooth.1 ⟨x, hsub hx⟩
  have hcV : (A.B.restrictOpen hO).IsChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    restrictOpen_isChart_restrictTo hO hc hsub q₀
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, hz]; exact c.φ.mapsTo_model x hx)
  refine ⟨c.restrictTo A.B.continuous hO hsub q₀, hcV, hx, z, hz, fun k hk => ?_⟩
  have hk' : (c.φ.model.E.toBase 1 z, k) ∈ c.K := by rw [hz]; exact hk
  obtain ⟨v, hv, hvk⟩ := hon k hk'
  refine ⟨⟨v, hv⟩, ?_⟩
  have e := scDeriv_restrictTo_subRestrict hO hft hs hc hsub q₀ hzU
  exact (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L v) e).trans hvk

include hO in
/-- **The converse**: Part I's `IsLinSurjAt` for `(f − s)|O` at a zero gives `ChartOnto` in every
chart `c` with domain in `O` around `x`, at every `z` over `φ(x)`
(`IsLinSurjAt.linAt_surjective`, the chart independence). -/
theorem chartOnto_of_isLinSurjAt_subRestrict {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {x : A.Obj} (hx : x ∈ c.φ.source) (hfs : f x = s x)
    (h : (A.B.restrictOpen hO).IsLinSurjAt (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨x, hsub hx⟩)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ x) :
    ChartOnto c (subDeriv c f s z) z := by
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  set q₀ := subRestrict (O := O) f s hft.isScSmooth.1 ⟨x, hsub hx⟩
  have hcV : (A.B.restrictOpen hO).IsChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    restrictOpen_isChart_restrictTo hO hc hsub q₀
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, hz]; exact c.φ.mapsTo_model x hx)
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s hft.isScSmooth.1) ⟨x, hsub hx⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs.1 (hsub hx)).2 hfs
  intro k hk
  rw [hz] at hk
  obtain ⟨⟨v, hv⟩, hvk⟩ := h.linAt_surjective hgO.isScSmooth h0 hcV hx hz k hk
  refine ⟨v, hv, ?_⟩
  have e := scDeriv_restrictTo_subRestrict hO hft hs hc hsub q₀ hzU
  exact (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L v) e).symm.trans hvk

end Restrict

/-! ### The local solution sets -/

/-- **The local solution set of `f = s` at a point in good position** (the step of Theorems
15.2.2 and 15.2.5, by Part I's Theorem 3.6.8 on `W|O`): if `(f − s)|O` is in good position at `x`
(`IsGoodPositionGermTame`, Definition 3.6.6 in a tame chart), there is an open `V ∋ x` inside the
domain of `c` such that `{y ∈ V | f(y) = s(y)}` is a smooth finite-dimensional submanifold of
`X` (Definition 4.2.1), and at each of its points `y` the section `(f − s)|O` is in good position,
`y` is smooth and `D((f̂ − ŝ) ∘ r)` maps onto `K` at every `z` over `φ(y)`. -/
theorem exists_solutionSet_of_isGoodPosition {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.Obj} (hx : x ∈ c.φ.source) (hfs : f x = s x)
    [Nonempty O] [ParacompactSpace O]
    [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]
    (hgp : (A.B.restrictOpen hO).IsGoodPositionGermTame (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨x, hsub hx⟩) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
      A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s y} ∧
      ∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        (∀ hyO : y ∈ O, (A.B.restrictOpen hO).IsGoodPositionGermTame
          (subRestrict (O := O) f s hft.isScSmooth.1) ⟨y, hyO⟩) ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y → ChartOnto c (subDeriv c f s z) z := by
  have hf := hft.isScSmooth.1
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hzero : ∀ y : O, IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s hf) y ↔ f y.1 = s y.1 := fun y => by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact isZeroAt_subSec_iff hf hs.1 y.2
  obtain ⟨Vx, hVxo, hxVx, hall, -⟩ := theorem_3_6_8' hgO hgp ((hzero ⟨x, hsub hx⟩).2 hfs)
  set W : Set O := Vx ∩ Subtype.val ⁻¹' c.φ.source with hW
  have hWo : IsOpen W := hVxo.inter (c.φ.isOpen_source.preimage continuous_subtype_val)
  have hSW := StrongBundle.isSmoothSubmanifold_solutionSet_inter hgO.isScSmooth.1 hWo
    (fun y hy hy0 => hall y hy.1 hy0)
  have himg := hSW.image_of_isScDiffeoOn (MPolyfold.isScDiffeoOn_subtypeVal (P := A.X.PObj) hO)
    (subset_univ _)
  refine ⟨Subtype.val '' W, hO.isOpenMap_subtype_val W hWo, ⟨⟨x, hsub hx⟩, ⟨hxVx, hx⟩, rfl⟩,
    ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩; exact hy.2
  · convert himg using 1
    ext y
    constructor
    · rintro ⟨⟨v, hvW, rfl⟩, hfy⟩; exact ⟨v, ⟨(hzero v).2 hfy, hvW⟩, rfl⟩
    · rintro ⟨v, ⟨hv0, hvW⟩, rfl⟩; exact ⟨⟨v, hvW, rfl⟩, (hzero v).1 hv0⟩
  · rintro y ⟨v, hvW, rfl⟩ hfy
    have hv0 := (hzero v).2 hfy
    have hgpv := hall v hvW.1 hv0
    refine ⟨(MPolyfold.mem_smoothSet_restrictOpen_iff hO v).1
      (hgO.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hv0), fun _ => hgpv, fun z hz => ?_⟩
    exact chartOnto_of_isLinSurjAt_subRestrict hO hft hs hc hsub hvW.2 hfy
      (hgpv.isGoodPositionGerm.isLinSurjAt hgO.isScSmooth) hz

/-- **The local solution set of `f = s` at an interior point** (the step of Theorem 15.2.2, by
Part I's Theorem 3.6.8 on `W|O`): if `d_X(x) = 0`, `f(x) = s(x)` and `D((f̂ − ŝ) ∘ r)(z)` maps
`T_zO` onto `K_z` (`(f − s)'(x)` onto), there is an open `V ∋ x` inside the domain of `c` such that
`{y ∈ V | f(y) = s(y)}` is a smooth finite-dimensional submanifold of `X` and at each of its
points `y` (smooth points) `(f − s)'(y)` is onto. -/
theorem exists_solutionSet_interior {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) {x : A.Obj}
    (hx : x ∈ c.φ.source) (hfs : f x = s x) (hd : A.X.PObj.degIndex x = 0)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hon : ChartOnto c (subDeriv c f s z) z) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
      A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s y} ∧
      ∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y → ChartOnto c (subDeriv c f s z) z := by
  have : Nonempty O := ⟨⟨x, hsub hx⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hf := hft.isScSmooth.1
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf)
      ⟨x, hsub hx⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hf hs.1 (hsub hx)).2 hfs
  have hd' : (A.X.PObj.restrictOpen hO).degIndex ⟨x, hsub hx⟩ = 0 := by
    rw [MPolyfold.degIndex_restrictOpen A.X.PObj hO]; exact hd
  have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hgO h0 hd'
    (isLinSurjAt_subRestrict hO hft hs hc hsub hx hz hon)
  obtain ⟨V, hVo, hxV, hVc, hS, hall⟩ :=
    exists_solutionSet_of_isGoodPosition hft hO hs hc hsub hx hfs hgp
  exact ⟨V, hVo, hxV, hVc, hS, fun y hy hfy =>
    ⟨(hall y hy hfy).1, (hall y hy hfy).2.2⟩⟩

end SBLocalization

end Polyfold
