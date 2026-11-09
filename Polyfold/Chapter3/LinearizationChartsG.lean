import Polyfold.Chapter3.LinearizationCharts
import Polyfold.Chapter3.GoodPositionGermG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I: the chart
independence of the linearization at a zero (the local form of Definition 2.5.8 (preprint 2.38)) and the assembly
of Definition 3.6.6 (preprint 3.53) at a zero from a chart which is not centred at it, **in the text's germ
reading** of Definition 3.1.11 (preprint 3.11) (phase 2): the fillings are sc-smooth germs (`IsFillingGerm`) on germs
of neighbourhoods whose levels may shrink, so their linearizations are the values of derivative
families (`IsSc1GermWith G g Dg`), and good position is `IsGoodPositionAtGerm` at `Dg(0)`.

# The linearization of a section at a zero, in charts, germ reading

## The text, paraphrased

See `LinearizationCharts.lean`: (before Definition 3.1.4 (preprint 3.4)) "`Tg(0) = Tf(0)` on `T₀O`"; (proof of
Theorem 3.6.8 (preprint 3.54), last paragraph) the argument at `x₀` is repeated at a zero `y` in a chart centred at
`y`.

## What is formalized

* **The bridge to filling germs**: `scDeriv_comp_r_eq_germ` (`D(f̂ ∘ r)(z) = Dg(z) ∘ Dr(z)` at a
  level-`1` point `z ∈ G₁` of the retract, for a germ `g` agreeing with `f̂` on `O` near `z`, with
  `r(0) = 0`), `linAt_eq_germDeriv` (`Lin(z) = Dg(z)` on `T_zO`), and
  `IsFillingGerm.fillerRestrict_eq_linAt` (at a central zero `Lin(0)` is the `Tf̃(0)` of a filling
  germ, `fillerRestrict` for `Dg(0)`), the germ forms of `scDeriv_comp_r_eq_of_eventuallyEq`,
  `linAt_eq_scDeriv` and `IsFilledVersion.fillerRestrict_eq_linAt`.
* **The assembly of Definition 3.6.6 (preprint 3.53), germ reading, in a given centred chart `c'`** (filling germ
  `g'` with a derivative family `Dg'` on `G' ⊆ U'`):
  `StrongBundle.isGoodPositionAtGerm_of_linAt_surj` (from the linearization `Lin(z)` in a chart `c`
  around `y`, onto `K_z`, kernel in good position) and
  `StrongBundle.isGoodPositionAtGerm_of_linAt_dense` (range of `Lin(z)` containing `ρ(z)F_∞`, with
  `Dg'(0)` Fredholm as hypothesis — Proposition 3.6.5 (preprint 3.52) for germs); with the data in `c` a filling
  germ `g` on `G` with `z ∈ G₁` instead of `Lin(z)`: `StrongBundle.isGoodPositionAtGerm_of_chart`
  and `StrongBundle.isGoodPositionAtGerm_of_chart_dense` (the germ form of
  `isGoodPositionAt_of_chart_dense`).
* **Section level**: `StrongBundle.isGoodPositionGerm_of_linAt_surj` and
  `StrongBundle.isGoodPositionGerm_of_chart`: if `(f, y)` is an sc-Fredholm germ in the germ
  reading (`IsScFredholmGerm`), `f(y) = 0`, and the linearization in some chart around `y` is onto
  with kernel in good position, then `(f, y)` is in good position in the germ reading
  (`IsGoodPositionGerm`) — the germ forms of `isGoodPositionGerm_of_linAt_surj_wholeChart` and
  `isGoodPositionGerm_of_chart_wholeChart`.

## What the text leaves implicit, and the choices made

* **The point `z` must lie in the germ.**  `Dg(z)` of a germ `g` on `G` is meaningful only for
  `z ∈ G₁`; the non-centred chart of `isGoodPositionAt_of_chart_dense` (whose `g` was sc¹ on the
  whole `U`) therefore carries the hypothesis `z ∈ G₁` in the germ form.  The chain rule for
  `g ∘ r` along the germ `r⁻¹(G)` needs `r(0) = 0`, i.e. `0 ∈ O` (the germ `g` lives at the centre
  `0` of `c`); both hold in the consumers, where `z` is the level-`1` lift of a nearby zero
  (Findings, Chapter 3, item 278 (e)).
* **The surjectivity of `Tf̃'(0)` from a dense subset needs the closed range**, i.e. Proposition
  3.52 in the chart `c'`; in the germ reading that is Proposition 3.6.5 (preprint 3.52) for germs (Stage 1 B,
  `proposition_3_6_5_local`), not imported here: the `_dense` forms take `IsFredholm (Dg' 0)`
  as hypothesis.  With the surjectivity of `Lin(z)` onto `K_z` itself no closed range is needed
  (`_surj`, `_of_chart`): `Lin'(0) = Γ ∘ Lin(z) ∘ A⁻¹` is then onto `K'_0`.  The section-level
  `_dense`/`_of_linAt` forms (`isGoodPositionGerm_of_chart_dense`, `isGoodPositionGerm_of_linAt`)
  are therefore not stated here; they are the chart-level theorems plus Proposition 3.6.5 (preprint 3.52) for germs.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

/-! ### The bridge `Lin(z) = Dg(z)` for a germ -/

section LinGerm

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

open StrongRetr

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
include hU hR

/-- **The bridge to filling germs** (germ reading, phase 2; the germ form of
`scDeriv_comp_r_eq_of_eventuallyEq`, the text's "`Tg(0) = Tf(0)` on `T₀O`" before Definition 3.1.4 (preprint 3.4),
at a level-`1` point `z` of the germ): if `g` is an sc¹-germ on `G₁` with derivative family `Dg`,
`r(0) = 0`, `z ∈ G₁` with `ι z ∈ O`, and `g` agrees with `f̂` on `O` near `ι z`, then
`D(f̂ ∘ r)(z) = Dg(z) ∘ Dr(z)`: `g ∘ r` is an sc¹-germ on `r⁻¹(G₁)` with the family
`Dg(r(x)) ∘ Dr(x)` (`IsSc1GermWith.comp_preimage`), `z ∈ r⁻¹(G₁)` because `r(z) = z`,
`g ∘ r = f̂ ∘ r` near `z`, and the derivative within `r⁻¹(G₁)` at `z` is unique. -/
theorem scDeriv_comp_r_eq_germ (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R)) {Dg : E 1 → E 0 →L[ℝ] F 0}
    (hg : IsSc1GermWith G₁ g Dg) {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U) (hzG : z ∈ G₁.U 1)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x) :
    scDeriv U (fb ∘ r R) z = (Dg z).comp (scDeriv U (r R) z) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hr : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have hr0 : r R 0 = 0 := r_eq_self hR h0O
  have hrC : MapsTo (r R) U C := fun u hu => hU.subset_quadrant (r_mem hR hu)
  have hzU : E.toBase 1 z ∈ U := mem_U_of_mem_O hR hzO
  have hz1 : z ∈ E.lvlSet U 1 := hzU
  set G' := (ScNbhdGerm.ofSet hU.relOpen h0).preimage G₁ (hr.isSc0.isSc0Germ hU.relOpen h0) hr0
    hrC with hG'
  have hgr := hg.comp_preimage hQ hU.relOpen h0 hr hr0 hrC
  have hlev : levelMap (r R) 1 z = z :=
    levelMap_eq_of_toBase_eq (by rw [r_eq_self hR hzO])
  have hzG' : z ∈ G'.U 1 := ⟨hz1, by rw [hlev]; exact hzG⟩
  have hG'U : G'.U 1 ⊆ E.lvlSet U 1 := fun x hx => hx.1
  have h1 := hgr.hasFDerivWithinAt z hzG'
  rw [hlev] at h1
  have h2 := (hfr.isSc1With_scDeriv.hasFDerivWithinAt z hz1).mono hG'U
  -- `g ∘ r = f̂ ∘ r` on `U` near `ι z`
  have hev : ((g ∘ r R) ∘ E.toBase 1) =ᶠ[𝓝[G'.U 1] z] ((fb ∘ r R) ∘ E.toBase 1) := by
    have hrc : Tendsto (r R) (𝓝[U] (E.toBase 1 z)) (𝓝 (E.toBase 1 z)) := by
      have := hr.isSc0.continuousOn_base (E.toBase 1 z) hzU
      rwa [ContinuousWithinAt, r_eq_self hR hzO] at this
    have hA : ∀ᶠ y in 𝓝[U] (E.toBase 1 z), r R y ∈ r R '' U → fb (r R y) = g (r R y) :=
      hrc.eventually heq
    have hB : ∀ᶠ y in 𝓝[U] (E.toBase 1 z), (g ∘ r R) y = (fb ∘ r R) y := by
      filter_upwards [hA, self_mem_nhdsWithin] with y hy hyU
      exact (hy ⟨y, hyU, rfl⟩).symm
    have ht : Tendsto (E.toBase 1) (𝓝[G'.U 1] z) (𝓝[U] (E.toBase 1 z)) :=
      tendsto_nhdsWithin_iff.2 ⟨((E.toBase 1).continuous.tendsto z).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun x hx => hG'U hx⟩
    exact ht.eventually hB
  have h2' := h2.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hzG')
  have huniq := (G'.uniqueDiffWithinAt hQ 1 hzG').eq h1 h2'
  exact (ContinuousLinearMap.ext_of_toBase_one fun w => by
    have := congrArg (fun L : E 1 →L[ℝ] F 0 => L w) huniq
    simpa using this).symm

/-- **On `T_zO`, `Lin(z) = Dg(z)`** for a germ `g` with derivative family `Dg`, `z ∈ G₁`, agreeing
with `f̂` on `O` near `ι z` (germ reading, phase 2; the germ form of `linAt_eq_scDeriv`). -/
theorem linAt_eq_germDeriv (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U) {fb g : E 0 → F 0}
    (hfr : IsSc1 U (fb ∘ r R)) {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U) (hzG : z ∈ G₁.U 1)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (x : ↥(rangeS (scDeriv U (r R) z))) : linAt U R fb z x = Dg z x := by
  obtain ⟨_, w, rfl⟩ := x
  rw [linAt_apply, scDeriv_comp_r_eq_germ hU hR h0 h0O hfr hg hzO hzG heq]
  change Dg z (scDeriv U (r R) z (scDeriv U (r R) z w)) = Dg z (scDeriv U (r R) z w)
  rw [scDeriv_r_idem_at hU hR hzO]

omit hR in
/-- **At a central zero, `Lin(0)` is the `Tf̃(0)` of a filling germ** (germ reading, phase 2; the
germ form of `IsFilledVersion.fillerRestrict_eq_linAt`): for a filling germ `g` of `f̂` with a
derivative family `Dg` on a germ `G₁`, `Tf̃(0)x = Dg(0)x = Lin(0)x` on `T₀O`. -/
theorem IsFillingGerm.fillerRestrict_eq_linAt (hR : IsStrongBundleRetraction U R)
    {h0 : (0 : E 0) ∈ U} (h0O : (0 : E 0) ∈ r R '' U) {fb g : E 0 → F 0}
    (hfill : IsFillingGerm hU hR h0 fb g) (hfr : IsSc1 U (fb ∘ r R))
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x))
    (x : ↥(rangeS (scDeriv U (r R) 0))) :
    (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1 x : F 0) = linAt U R fb 0 x := by
  rw [fillerRestrict_apply, linAt_eq_germDeriv hU hR h0 h0O hfr hg (by rw [map_zero]; exact h0O)
    (G₁.zero_mem 1) (by rw [map_zero]; exact hfill.eq_on)]

end LinGerm

/-! ### Definition 3.6.6 (preprint 3.53) at a zero, from a non-centred chart, germ reading -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- The principal part of a section composed with the retraction is sc¹ on `U` (the section is
sc-smooth). -/
lemma StrongBundle.IsScSmoothSection.principal_comp_r_isSc1 (hf : B.IsScSmoothSection f)
    {d : StrongBundleChart PX P} (hd : B.IsChart d) : IsSc1 d.U (d.principal f ∘ r d.R) := by
  have h1 := (hf.isScSmoothRetractMap hd).comp_isScSmooth
    (d.isRetraction.baseRetraction d.relOpen) d.base_retract
  exact ((h1.snd d.relOpen.isScDomain).congr d.relOpen.isScDomain fun _ _ => rfl).isSc1

/-- **The kernel condition of Definition 3.6.6 (preprint 3.53), germ reading, from a non-centred chart**
(phase 2): with the chart change `A`, `Γ` of `linAt_chart_change` between a chart `c` around the
zero `y` (at the level-`1` point `z` over `φ(y)`) and the chart `c'` centred at `y`, carrying a
filling germ `g'` with a derivative family `Dg'` on `G' ⊆ U'`: if the kernel of `Lin(z)` is in good
position to `C_{φ(y)}` inside `T_zO`, then `ker Dg'(0)` is in good position to `C'` inside `T₀O'`
(`IsInGoodPositionIn.transport`, and `ker Dg'(0) = ker Tf̃'(0) ⊆ T₀O'` by condition (3) of the
filling germ, `IsFillingGerm.ker_deriv_le_range`). -/
theorem StrongBundle.isInGoodPositionIn_ker_germ_of_linAt (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    {G' : ScNbhdGerm c'.φ.model.E c'.φ.model.C} (hG'U : G'.U 0 ⊆ c'.U)
    {Dg' : c'.φ.model.E 1 → c'.φ.model.E 0 →L[ℝ] c'.F 0} (hg' : IsSc1GermWith G' g' Dg') :
    IsInGoodPositionIn c'.φ.model.E (rangeS (scDeriv c'.U (r c'.R) 0)) c'.φ.model.C
      (LinearMap.ker (Dg' 0 : c'.φ.model.E 0 →ₗ[ℝ] c'.F 0)) := by
  classical
  obtain ⟨n', Wq', T', hT'⟩ := c'.relOpen.isPartialQuadrant
  have hz' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = c'.φ y := by rw [map_zero, hφ0]
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by rw [c.r_image]; exact hzOO
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have h0O' : (0 : c'.φ.model.E 0) ∈ r c'.R '' c'.U := by
    rw [c'.r_image, ← hφ0]; exact c'.φ.mapsTo_model y hyV'
  have hzO' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ r c'.R '' c'.U := by
    rw [map_zero]; exact h0O'
  have hzU' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ c'.U := by rw [map_zero]; exact h0U'
  obtain ⟨A, Γ, hconj, hcone⟩ := linAt_chart_change c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hyV hyV' hy0 hz hz' hzU hzU'
    T hT T' hT'
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hf.1 (c.r_image ▸ hx)
  have hfK' : ∀ x ∈ r c'.R '' c'.U, (x, c'.principal f x) ∈ c'.R '' (c'.U ×ˢ univ) :=
    fun x hx => c'.principal_mem_K hf.1 (c'.r_image ▸ hx)
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]; exact (c.isZeroAt_iff hf.1 hyV).1 hy0
  have hfb0' : c'.principal f 0 = 0 := by
    have := (c'.isZeroAt_iff hf.1 hyV').1 hy0; rwa [hφ0] at this
  have hg'0 : g' 0 = 0 := by rw [← hfill'.eq_on.self_of_nhds h0O', hfb0']
  have hbr' : ∀ x : ↥(rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal f) 0 x = Dg' 0 x := fun x =>
    linAt_eq_germDeriv c'.relOpen c'.isRetraction h0U' h0O' (hf.principal_comp_r_isSc1 hc') hg'
      hzO' (G'.zero_mem 1) (by rw [map_zero]; exact hfill'.eq_on) x
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.principal_comp_r_isSc1 hc) hfK hzO hfz x⟩
  have hker' := hker.transport A (C' := c'.φ.model.C) (fun x => by
    have := hcone x
    rwa [hz, map_zero, partialQuadrantAtWith_zero, ← hT'] at this)
  convert hker' using 1
  have hkerT : LinearMap.ker (Dg' 0 : c'.φ.model.E 0 →ₗ[ℝ] c'.F 0) ≤
      rangeS (scDeriv c'.U (r c'.R) 0) :=
    hfill'.ker_deriv_le_range hG'U hg' hg'0 h0O' hfK'
  ext w
  constructor
  · intro hw
    have hwT := hkerT hw
    rw [mem_transportSub]
    set x := A.symm ⟨w, hwT⟩ with hxdef
    have hAx : A x = ⟨w, hwT⟩ := A.apply_symm_apply _
    refine ⟨x, ⟨x, ?_, rfl⟩, by rw [hAx]⟩
    have h1 := hconj x ⟨_, hmem x⟩ rfl
    rw [hAx, hbr'] at h1
    have hw0 : Dg' 0 w = 0 := hw
    rw [hw0] at h1
    have h2 : (⟨_, hmem x⟩ : ↥(rangeS (ρCLM c.isRetraction hzU))) = 0 :=
      Γ.map_eq_zero_iff.1 (Subtype.ext h1)
    exact congrArg Subtype.val h2
  · intro hw
    obtain ⟨x, ⟨x', hx'ker, hx'x⟩, hxw⟩ := (mem_transportSub A).1 hw
    have hxx' : x' = x := Subtype.ext hx'x
    subst hxx'
    have hk0 : (⟨_, hmem x'⟩ : ↥(rangeS (ρCLM c.isRetraction hzU))) = 0 := Subtype.ext hx'ker
    have h1 := hconj x' ⟨_, hmem x'⟩ rfl
    rw [hk0, ContinuousLinearEquiv.map_zero, Submodule.coe_zero, hbr'] at h1
    change Dg' 0 w = 0
    rw [← hxw]; exact h1.symm

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from the linearization in a non-centred chart onto `K_z`, germ
reading** (phase 2; the chart-level germ form of `isGoodPositionGerm_of_linAt_surj_wholeChart`): if
`Lin(z) : T_zO → K_z` (`linAt`) in a chart `c` around the zero `y` is onto `K_z` and its kernel is
in good position to `C_{φ(y)}` inside `T_zO`, then in every chart `c'` centred at `y` carrying a
filling germ `g'` with a derivative family `Dg'` on `G' ⊆ U'` the germ is in good position at
`Dg'(0)` (`IsGoodPositionAtGerm`).  No Fredholm property is needed: `Lin'(0) = Γ ∘ Lin(z) ∘ A⁻¹`
(`linAt_chart_change`) is onto `K'_0`, and `Lin'(0) = Dg'(0)` on `T₀O'`. -/
theorem StrongBundle.isGoodPositionAtGerm_of_linAt_surj (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    {G' : ScNbhdGerm c'.φ.model.E c'.φ.model.C} (hG'U : G'.U 0 ⊆ c'.U)
    {Dg' : c'.φ.model.E 1 → c'.φ.model.E 0 →L[ℝ] c'.F 0} (hg' : IsSc1GermWith G' g' Dg') :
    IsGoodPositionAtGerm c'.relOpen c'.isRetraction h0U' (Dg' 0) := by
  classical
  refine ⟨?_, StrongBundle.isInGoodPositionIn_ker_germ_of_linAt hf hy0 hc hyV hz T hT hker hc' hyV'
    hφ0 h0U' hfill' hG'U hg'⟩
  obtain ⟨n', Wq', T', hT'⟩ := c'.relOpen.isPartialQuadrant
  have hz' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = c'.φ y := by rw [map_zero, hφ0]
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by rw [c.r_image]; exact hzOO
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have h0O' : (0 : c'.φ.model.E 0) ∈ r c'.R '' c'.U := by
    rw [c'.r_image, ← hφ0]; exact c'.φ.mapsTo_model y hyV'
  have hzO' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ r c'.R '' c'.U := by
    rw [map_zero]; exact h0O'
  have hzU' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ c'.U := by rw [map_zero]; exact h0U'
  obtain ⟨A, Γ, hconj, -⟩ := linAt_chart_change c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hyV hyV' hy0 hz hz' hzU hzU'
    T hT T' hT'
  have hbr' : ∀ x : ↥(rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal f) 0 x = Dg' 0 x := fun x =>
    linAt_eq_germDeriv c'.relOpen c'.isRetraction h0U' h0O' (hf.principal_comp_r_isSc1 hc') hg'
      hzO' (G'.zero_mem 1) (by rw [map_zero]; exact hfill'.eq_on) x
  intro k' hk'
  have hk'' : k' ∈ rangeS (ρCLM c'.isRetraction hzU') := by
    rw [mem_rangeS_ρCLM_iff c'.isRetraction hzO' hzU', map_zero]
    exact (mem_rangeS_ρCLM_iff c'.isRetraction h0O' h0U').1 hk'
  set k := Γ.symm ⟨k', hk''⟩ with hkdef
  have hkK : (c.φ y, (k : c.F 0)) ∈ c.K := by
    have h := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 k.2
    have e : ((c.φ.model.E.toBase 1 z, (k : c.F 0)) : c.φ.model.E 0 × c.F 0) =
        (c.φ y, (k : c.F 0)) := Prod.ext hz rfl
    rw [← e]; exact h
  obtain ⟨x, hx⟩ := hsurj _ hkK
  have h1 := hconj x k hx.symm
  rw [hbr', hkdef, Γ.apply_symm_apply] at h1
  exact ⟨A x, (A x).2, h1.symm⟩

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from the linearization in a non-centred chart, germ reading**
(phase 2; the chart-level germ form of `isGoodPositionGerm_of_linAt`, with the dense range
`ρ(z)F_∞` of `Lin(z)`): as `isGoodPositionAtGerm_of_linAt_surj`, with the range of `Lin(z)`
containing `ρ(z)k̂` for every smooth `k̂ ∈ F_∞`, and `Dg'(0)` Fredholm (Proposition 3.6.5 (preprint 3.52) in the
chart `c'`, germ reading — a hypothesis here, `proposition_3_6_5_local` of Stage 1 B): the
range of `Tf̃'(0)` is closed and contains the dense image under `Γ` of `ρ(z)F_∞`. -/
theorem StrongBundle.isGoodPositionAtGerm_of_linAt_dense (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x, linAt c.U c.R (c.principal f) z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    {G' : ScNbhdGerm c'.φ.model.E c'.φ.model.C} (hG'U : G'.U 0 ⊆ c'.U)
    {Dg' : c'.φ.model.E 1 → c'.φ.model.E 0 →L[ℝ] c'.F 0} (hg' : IsSc1GermWith G' g' Dg')
    (hDgF' : IsFredholm (Dg' 0)) :
    IsGoodPositionAtGerm c'.relOpen c'.isRetraction h0U' (Dg' 0) := by
  classical
  refine ⟨?_, StrongBundle.isInGoodPositionIn_ker_germ_of_linAt hf hy0 hc hyV hz T hT hker hc' hyV'
    hφ0 h0U' hfill' hG'U hg'⟩
  obtain ⟨n', Wq', T', hT'⟩ := c'.relOpen.isPartialQuadrant
  have hz' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = c'.φ y := by rw [map_zero, hφ0]
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by rw [c.r_image]; exact hzOO
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have h0O' : (0 : c'.φ.model.E 0) ∈ r c'.R '' c'.U := by
    rw [c'.r_image, ← hφ0]; exact c'.φ.mapsTo_model y hyV'
  have hzO' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ r c'.R '' c'.U := by
    rw [map_zero]; exact h0O'
  have hzU' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ c'.U := by rw [map_zero]; exact h0U'
  obtain ⟨A, Γ, hconj, -⟩ := linAt_chart_change c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hyV hyV' hy0 hz hz' hzU hzU'
    T hT T' hT'
  have hfK' : ∀ x ∈ r c'.R '' c'.U, (x, c'.principal f x) ∈ c'.R '' (c'.U ×ˢ univ) :=
    fun x hx => c'.principal_mem_K hf.1 (c'.r_image ▸ hx)
  have hfb0' : c'.principal f 0 = 0 := by
    have := (c'.isZeroAt_iff hf.1 hyV').1 hy0; rwa [hφ0] at this
  have hg'0 : g' 0 = 0 := by rw [← hfill'.eq_on.self_of_nhds h0O', hfb0']
  have hbr' : ∀ x : ↥(rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal f) 0 x = Dg' 0 x := fun x =>
    linAt_eq_germDeriv c'.relOpen c'.isRetraction h0U' h0O' (hf.principal_comp_r_isSc1 hc') hg'
      hzO' (G'.zero_mem 1) (by rw [map_zero]; exact hfill'.eq_on) x
  -- the closed range of `Tf̃'(0)` (Proposition 3.1.5 (preprint 3.5) for the filling germ, `Dg'(0)` Fredholm)
  obtain ⟨h1, -, hFiff, -⟩ :=
    hfill'.proposition_3_1_5 c'.relOpen c'.isRetraction h0U' hg'0 h0O' hfK' hG'U hg'
  have hTF := hFiff.2 hDgF'
  set q := ρCLM c'.isRetraction h0U' with hq
  have hqidem : ∀ k, q (q k) = q k := ρCLM_idem c'.isRetraction h0U' h0O'
  set S : Set (c'.F 0) := Subtype.val '' (range (fillerRestrict (scDeriv c'.U (r c'.R) 0) q
    (Dg' 0) h1)) with hSdef
  have hSc : IsClosed S :=
    (isClosed_range_of_idem q hqidem).isClosedEmbedding_subtypeVal.isClosedMap _
      hTF.isClosed_range
  have hSmem : ∀ k ∈ S, ∃ x ∈ rangeS (scDeriv c'.U (r c'.R) 0), Dg' 0 x = k := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, x.2, rfl⟩
  -- the dense image of `ρ(z)F_∞`
  set ψ : c.F 0 → c'.F 0 := fun k =>
    (Γ ⟨ρ c.R (c.φ.model.E.toBase 1 z) k, ⟨k, rfl⟩⟩ : c'.F 0) with hψ
  have hψc : Continuous ψ :=
    continuous_subtype_val.comp (Γ.continuous.comp
      ((ρ_continuous c.isRetraction hzU).subtype_mk _))
  have hψS : ψ '' (c.F.smooth : Set (c.F 0)) ⊆ S := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨x, hx⟩ := hsurj k hk
    have hlin : ((⟨ρ c.R (c.φ.model.E.toBase 1 z) k, ⟨k, rfl⟩⟩ :
        ↥(rangeS (ρCLM c.isRetraction hzU))) : c.F 0) =
        linAt c.U c.R (c.principal f) z x := by
      change ρ c.R (c.φ.model.E.toBase 1 z) k = _
      rw [hz]; exact hx.symm
    have := hconj x _ hlin
    rw [hbr'] at this
    exact ⟨fillerRestrict _ q _ h1 (A x), ⟨_, rfl⟩, by
      rw [fillerRestrict_apply]; exact this.symm⟩
  have hψrange : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), k ∈ range ψ := by
    intro k hk
    refine ⟨(Γ.symm ⟨k, hk⟩ : c.F 0), ?_⟩
    have hfix : ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0) =
        (Γ.symm ⟨k, hk⟩ : c.F 0) := by
      obtain ⟨k₀, hk₀⟩ := (Γ.symm ⟨k, hk⟩).2
      rw [← hk₀]
      exact ρ_ρ c.isRetraction hzO k₀
    change (Γ ⟨ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0), _⟩ : c'.F 0) = k
    have : (⟨ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0), ⟨_, rfl⟩⟩ :
        ↥(rangeS (ρCLM c.isRetraction hzU))) = Γ.symm ⟨k, hk⟩ := Subtype.ext hfix
    rw [this, Γ.apply_symm_apply]
  intro k hk
  apply hSmem
  have hk' : k ∈ rangeS (ρCLM c'.isRetraction hzU') := by
    rw [mem_rangeS_ρCLM_iff c'.isRetraction hzO' hzU', map_zero]
    exact (mem_rangeS_ρCLM_iff c'.isRetraction h0O' h0U').1 hk
  obtain ⟨k₀, rfl⟩ := hψrange k hk'
  have hcl : ψ k₀ ∈ closure (ψ '' (c.F.smooth : Set (c.F 0))) :=
    image_closure_subset_closure_image hψc ⟨k₀, (c.F.dense_smooth 0) k₀, rfl⟩
  exact hSc.closure_subset_iff.2 hψS hcl

/-- The data in the non-centred chart `c` given by a germ `g` (on `G`, `z ∈ G₁`, `0 ∈ O`) agreeing
with `f̂` near `φ(y)`, translated to `Lin(z)`: `Lin(z) = Dg(z)` on `T_zO`, so the kernel of
`Lin(z)`, as a subspace of `E₀`, is `ker Dg(z) ∩ T_zO` (germ reading, phase 2). -/
theorem StrongBundle.linAt_eq_germDeriv_chart (hf : B.IsScSmoothSection f) {y : X}
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U)
    {g : c.φ.model.E 0 → c.F 0} {G : ScNbhdGerm c.φ.model.E c.φ.model.C}
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg) (hzG : z ∈ G.U 1)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x) :
    (∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)), linAt c.U c.R (c.principal f) z x = Dg z x) ∧
      (LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype =
        LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (r c.R) z) := by
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyV
  have hbr : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x = Dg z x := fun x =>
    linAt_eq_germDeriv c.relOpen c.isRetraction h0U h0O (hf.principal_comp_r_isSc1 hc) hg hzO hzG
      (by rw [hz, c.r_image]; exact hfg) x
  refine ⟨hbr, ?_⟩
  ext w
  simp only [Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Submodule.mem_map, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hbr]
    exact ⟨hx, x.2⟩
  · rintro ⟨hw, hwT⟩
    exact ⟨⟨w, hwT⟩, by rw [hbr]; exact hw, rfl⟩

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from a filling germ in a non-centred chart, germ reading**
(phase 2; the germ form of `isGoodPositionAt_of_chart_dense` with the surjectivity of `Dg(z)` onto
`K_z`): let `c` be a chart around the zero `y` with `0 ∈ O`, `g` an sc¹-germ on `G ⊆ U` with a
derivative family `Dg` (e.g. a filling germ at the centre of `c`), agreeing with `f̂` on `O` near
`φ(y)`, and `z ∈ G₁` over `φ(y)` (**the point must lie in the germ**).  If `Dg(z)` maps `T_zO`
onto `K_z` and `ker Dg(z) ∩ T_zO` is in good position to `C_{φ(y)}` inside `T_zO`, then in every
chart `c'` centred at `y` with a filling germ `g'` and a derivative family `Dg'` on `G' ⊆ U'` the
germ is in good position at `Dg'(0)`.  This is the form the reading of the good position in a tame
chart needs (`IsGoodPositionGermWholeChart.toTame`: there `z = 0` and `K_0` is the whole target). -/
theorem StrongBundle.isGoodPositionAtGerm_of_chart (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U)
    {g : c.φ.model.E 0 → c.F 0} {G : ScNbhdGerm c.φ.model.E c.φ.model.C}
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg) (hzG : z ∈ G.U 1)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x ∈ rangeS (scDeriv c.U (r c.R) z), Dg z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (r c.R) z)))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    {G' : ScNbhdGerm c'.φ.model.E c'.φ.model.C} (hG'U : G'.U 0 ⊆ c'.U)
    {Dg' : c'.φ.model.E 1 → c'.φ.model.E 0 →L[ℝ] c'.F 0} (hg' : IsSc1GermWith G' g' Dg') :
    IsGoodPositionAtGerm c'.relOpen c'.isRetraction h0U' (Dg' 0) := by
  obtain ⟨hbr, hkereq⟩ := StrongBundle.linAt_eq_germDeriv_chart hf hc hyV hz h0U h0O hg hzG hfg
  refine StrongBundle.isGoodPositionAtGerm_of_linAt_surj hf hy0 hc hyV hz T hT (fun k hk => ?_)
    (hkereq ▸ hker) hc' hyV' hφ0 h0U' hfill' hG'U hg'
  obtain ⟨x, hxT, hx⟩ := hsurj k hk
  exact ⟨⟨x, hxT⟩, by rw [hbr]; exact hx⟩

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from a filling germ in a non-centred chart, germ reading, dense
form** (phase 2; the germ form of `isGoodPositionAt_of_chart_dense`): as
`isGoodPositionAtGerm_of_chart`, with the range of `Dg(z)|_{T_zO}` containing `ρ(z)k̂` for every
smooth `k̂ ∈ F_∞`, and `Dg'(0)` Fredholm (Proposition 3.6.5 (preprint 3.52) in `c'`, germ reading: a hypothesis
here). -/
theorem StrongBundle.isGoodPositionAtGerm_of_chart_dense (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U)
    {g : c.φ.model.E 0 → c.F 0} {G : ScNbhdGerm c.φ.model.E c.φ.model.C}
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg) (hzG : z ∈ G.U 1)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x ∈ rangeS (scDeriv c.U (r c.R) z),
      Dg z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (r c.R) z)))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    {G' : ScNbhdGerm c'.φ.model.E c'.φ.model.C} (hG'U : G'.U 0 ⊆ c'.U)
    {Dg' : c'.φ.model.E 1 → c'.φ.model.E 0 →L[ℝ] c'.F 0} (hg' : IsSc1GermWith G' g' Dg')
    (hDgF' : IsFredholm (Dg' 0)) :
    IsGoodPositionAtGerm c'.relOpen c'.isRetraction h0U' (Dg' 0) := by
  obtain ⟨hbr, hkereq⟩ := StrongBundle.linAt_eq_germDeriv_chart hf hc hyV hz h0U h0O hg hzG hfg
  refine StrongBundle.isGoodPositionAtGerm_of_linAt_dense hf hy0 hc hyV hz T hT (fun k hk => ?_)
    (hkereq ▸ hker) hc' hyV' hφ0 h0U' hfill' hG'U hg' hDgF'
  obtain ⟨x, hxT, hx⟩ := hsurj k hk
  exact ⟨⟨x, hxT⟩, by rw [hbr]; exact hx⟩

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from the linearization in a non-centred chart, for a section,
germ reading** (phase 2; the germ form of `isGoodPositionGerm_of_linAt_surj_wholeChart`): if `(f, y)` is an
sc-Fredholm germ in the germ reading (`IsScFredholmGerm`), `f(y) = 0`, and in some chart `c`
around `y` the linearization `Lin(z) : T_zO → K_z` is onto with kernel in good position to
`C_{φ(y)}` inside `T_zO`, then `(f, y)` is in good position in the germ reading
(`IsGoodPositionGerm`), in the chart centred at `y` given by `IsScFredholmGerm`. -/
theorem StrongBundle.isGoodPositionGerm_of_linAt_surj (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGerm f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype)) :
    B.IsGoodPositionGerm f y := by
  obtain ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', hs', hs0', hconj'⟩ := hy
  obtain ⟨G', hG'U, hg'sm, -⟩ := hfill'.germ
  have hg' := (hg'sm 1).isSc1.isSc1GermWith_scDerivGerm
  exact ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', hs', hs0', hconj', G', scDerivGerm G' g',
    hG'U, hg', StrongBundle.isGoodPositionAtGerm_of_linAt_surj hf hy0 hc hyV hz T hT hsurj hker hc'
      hyV' hφ0 h0U' hfill' hG'U hg'⟩

/-- **Definition 3.6.6 (preprint 3.53) at a zero, from a filling germ in a non-centred chart, for a section, germ
reading** (phase 2; the germ form of `isGoodPositionGerm_of_chart_wholeChart`): as
`isGoodPositionGerm_of_linAt_surj`, with the data in `c` given by a germ `g` on `G` (derivative
family `Dg`, `z ∈ G₁`, `0 ∈ O`) agreeing with `f̂` near `φ(y)`, `Dg(z)(T_zO) ⊇ K_z` and
`ker Dg(z) ∩ T_zO` in good position to `C_{φ(y)}` inside `T_zO`. -/
theorem StrongBundle.isGoodPositionGerm_of_chart (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGerm f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U)
    {g : c.φ.model.E 0 → c.F 0} {G : ScNbhdGerm c.φ.model.E c.φ.model.C}
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg) (hzG : z ∈ G.U 1)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x ∈ rangeS (scDeriv c.U (r c.R) z), Dg z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (r c.R) z))) :
    B.IsGoodPositionGerm f y := by
  obtain ⟨hbr, hkereq⟩ := StrongBundle.linAt_eq_germDeriv_chart hf hc hyV hz h0U h0O hg hzG hfg
  refine StrongBundle.isGoodPositionGerm_of_linAt_surj hf hy hy0 hc hyV hz T hT (fun k hk => ?_)
    (hkereq ▸ hker)
  obtain ⟨x, hxT, hx⟩ := hsurj k hk
  exact ⟨⟨x, hxT⟩, by rw [hbr]; exact hx⟩

end Bundle

end Polyfold
