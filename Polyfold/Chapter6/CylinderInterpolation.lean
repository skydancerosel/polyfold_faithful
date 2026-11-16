import Polyfold.Chapter5.CylinderPerturbation
import Polyfold.Chapter6.ProductOrientation
import Polyfold.Chapter6.SolutionOrientationCharts

/-!
# Interpolation of perturbations on the cylinder

The interpolated perturbation `cylInterp` on the cylinder, its pull-back slices, the general
position of the parametrized lift, and the cobordism they give (`exists_cobordism`). The cylinder
perturbations are in `Chapter5/CylinderPerturbation.lean`.
-/

open Set Filter Topology Function MeasureTheory
noncomputable section
namespace Polyfold
universe u v
section ParamLift
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y} {m : ℕ}
open StrongRetr
variable [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

set_option maxHeartbeats 1600000 in
-- the product chart `(r ↦ r − r₀) × c` centred at `(r₀, y)`
/-- **General position of the lift** (2021 Definition 5.3.9, p. 220, for the section
`g̃(t, x) = g(x)` of the pull-back to `ℝᵐ × X`): if `(g, y)` is in general position, then
`(g̃, (r₀, y))` is in general position for every `r₀`. *Proof*: in the product chart
`(r ↦ r − r₀) × c` centred at `(r₀, y)`, `Lin_{g̃}(0)(a, u) = Lin_g(0)u`, so the surjectivity and
`ker + T^R = T` pass from `c` (`isParamGP_elim0_of_isGeneralPositionGerm`) to the product chart,
and the chart criterion `isGeneralPositionGerm_of_sup_eq` concludes. -/
theorem isGeneralPositionGerm_paramLift (hgFt : B.IsScFredholmSectionTame g) {y : X}
    (hy0 : IsZeroAt P g y) (hgp : B.IsGeneralPositionGerm g y) (r₀ : Fin m → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramLift g hgFt.isScSmooth.1) (r₀, y) := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have h0s : ∀ _ : Fin m, B.IsScPlusSection (fiberZero P) := fun _ =>
    StrongBundle.isScPlusSection_fiberZero
  rw [paramLift_eq_paramSection_zero hgFt.isScSmooth.1]
  have hFt := theorem_3_1_21_tame hgFt h0s
  set F := paramSection g hgFt.isScSmooth.1 (fun _ : Fin m => fiberZero P)
    (fun i => (h0s i).1) with hF
  have hz0 : IsZeroAt (pullbackProj P Prod.snd) F (r₀, y) := by
    rw [hF, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g _ (fun _ : Fin m => fiberZero P)
      (fun _ => isSection_fiberZero) r₀) y
    rw [paramSlice_zeroFamily]; exact hy0
  obtain ⟨-, c, hc, hyV, hφ0, -⟩ := hgFt.germTame y (hgF.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hP := isParamGP_elim0_of_isGeneralPositionGerm hgFt hy0 hc hyV hφ0 T hT hgp
  set q₀ := F (r₀, y) with hq₀
  set c' := (PullbackChartData.ofProd c r₀).toChart q₀ with hc'
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart c' :=
    (PullbackChartData.ofProd c r₀).isChart_toChart B _ hc.1 q₀
  have hc'T : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsTameChart c' :=
    ⟨hc'B, PullbackChartData.ofProd_isTame c r₀ q₀ hc.2⟩
  have hyV' : (r₀, y) ∈ c'.φ.source := ⟨mem_univ _, hyV⟩
  have hc'0 : c'.φ (r₀, y) = 0 := ofProd_apply_eq_zero c r₀ q₀ hφ0
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hT' : c'.φ.model.C = (prodPresentation (rnPres m) T) 0 ⁻¹'
      quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
    prod_eq_prodPresentation (rnPres m) T (rnPres_eq (m := m)) hT
  have hmin : minimalSubspaceWith (prodPresentation (rnPres m) T)
      (0 : ((rnSc m).prod c.φ.model.E) 0) =
      (⊤ : Submodule ℝ (Fin m → ℝ)).prod (minimalSubspaceWith T 0) := by
    rw [minimalSubspaceWith_prodPresentation]
    simp only [Prod.fst_zero, Prod.snd_zero, minimalSubspaceWith_rnPres]
  have htan : ∀ w : (Fin m → ℝ) × c.φ.model.E 0,
      w ∈ rangeS (scDeriv c'.U (r c'.R) 0) ↔ w.2 ∈ rangeS (scDeriv c.U (r c.R) 0) := fun w =>
    PullbackChartData.ofProd_mem_tangent_iff c r₀ q₀ 0 (u := 0) (by rw [map_zero]; exact h0U) w
  -- the linearization in the product chart
  have hz0' : ∀ u ∈ c.φ.model.O, c.principal (fiberZero P) u = 0 := fun u hu =>
    c.snd_fiberZero (c.φ.symm_mapsTo hu)
  have hlin : ∀ (w : (Fin m → ℝ) × c.φ.model.E 0) (hw : w ∈ rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal F) 0 ⟨w, hw⟩ =
        linAt c.U c.R (c.principal g) 0 ⟨w.2, (htan w).1 hw⟩ := by
    intro w hw
    rw [hF, linAt_paramSection hgF h0s hc.1 h0O r₀ q₀ hw]
    have hgs := hgFt.isScSmooth.isSc1_principal_comp_r hc.1
    have heq : EqOn (c.principal g ∘ r c.R) ((fun u => c.principal g u +
        ∑ i, r₀ i • c.principal (fiberZero P) u) ∘ r c.R) c.U := fun u hu => by
      simp only [Function.comp_apply, hz0' _ (c.r_mem_O hu), smul_zero, Finset.sum_const_zero,
        add_zero]
    have h0lvl : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
      rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
    rw [linAt_congr c.relOpen (hgs.congr heq) hgs (fun u hu => by
      obtain ⟨u', hu', rfl⟩ := hu
      simp only [hz0' _ (c.r_mem_O hu'), smul_zero, Finset.sum_const_zero, add_zero]) h0lvl]
    simp only [hz0' 0 h0O, smul_zero, Finset.sum_const_zero, add_zero]
    rfl
  -- (i): surjectivity
  have hsurj : ∀ k, (c'.φ (r₀, y), k) ∈ c'.K →
      ∃ x, linAt c'.U c'.R (c'.principal F) 0 x = k := by
    intro k hk
    rw [hc'0] at hk
    obtain ⟨u, a, hua⟩ := hP.1 k ((mem_K_ofProd_zero_iff c r₀ q₀ h0O k).1 hk)
    have hw : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ rangeS (scDeriv c'.U (r c'.R) 0) :=
      (htan _).2 u.2
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [hlin _ hw]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hua
    exact hua
  -- (ii): `ker + T^R = T`
  set R' := c'.isRetraction.baseRetraction c'.relOpen with hR'
  have hsup : c'.linKer F 0 ⊔ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 =
      LinearMap.range (scDeriv R'.U R' 0 : c'.φ.model.E 0 →ₗ[ℝ] c'.φ.model.E 0) := by
    refine le_antisymm (sup_le (c'.linKer_le _ 0) inf_le_left) fun v hv => ?_
    have hv2 : v.2 ∈ rangeS (scDeriv c.U (r c.R) 0) :=
      PullbackChartData.ofProd_mem_tangent c r₀ q₀ h0U hv
    obtain ⟨u, a, hua, hwu⟩ := hP.2 ⟨v.2, hv2⟩
    have hk : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ rangeS (scDeriv c'.U (r c'.R) 0) :=
      (htan _).2 u.2
    have hkK : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ c'.linKer F 0 := by
      refine (c'.mem_linKer_iff _ 0 _).2 ⟨hk, ?_⟩
      rw [hlin _ hk]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hua
      exact hua
    let k : c'.φ.model.E 0 := ((0 : Fin m → ℝ), (u : c.φ.model.E 0))
    have hrest : v - k ∈ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 := by
      refine ⟨Submodule.sub_mem _ hv hk, ?_⟩
      have hb0' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = 0 := map_zero _
      rw [hb0']
      change v - k ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
        (0 : ((rnSc m).prod c.φ.model.E) 0)
      rw [hmin]
      exact ⟨Submodule.mem_top, hwu⟩
    have : v = k + (v - k) := by abel
    rw [this]
    exact Submodule.add_mem_sup hkK hrest
  exact isGeneralPositionGerm_of_sup_eq hFt hz0 hc'T hyV' hc'0 (prodPresentation (rnPres m) T)
    hT' hsurj hsup

end ParamLift

section CylinderSections
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

/-- **The interpolation `ŝ(t, x) = (1 − χ(t))·s₀(x) + χ(t)·s₁(x)`** of two sections over `ℝ¹ × X`
(`χ = cylCut`). -/
def cylInterp (s₀ s₁ : X → Y) (h₀ : IsSection P s₀) (h₁ : IsSection P s₁) :
    (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
  sectionAdd (pullbackProj P Prod.snd)
    (sectionSmul (pullbackProj P Prod.snd) (fun z => 1 - cylCut (z.1 0)) (constLift s₀ h₀))
    (sectionSmul (pullbackProj P Prod.snd) (fun z => cylCut (z.1 0)) (constLift s₁ h₁))

variable {s₀ s₁ : X → Y} (h₀ : IsSection P s₀) (h₁ : IsSection P s₁)
omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

lemma isSection_cylInterp : IsSection (pullbackProj P Prod.snd) (cylInterp s₀ s₁ h₀ h₁) :=
  ((isSection_constLift s₀ h₀).sectionSmul).sectionAdd (isSection_constLift s₁ h₁).sectionSmul

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

/-- The slices of `ŝ`: `ŝ(t, ·) = (1 − χ(t))·s₀ + χ(t)·s₁`. -/
lemma pullbackSlice_cylInterp (t : Fin 1 → ℝ) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t =
      sectionAdd P (sectionSmul P (fun _ => 1 - cylCut (t 0)) s₀)
        (sectionSmul P (fun _ => cylCut (t 0)) s₁) := by
  rw [cylInterp, pullbackSlice_sectionAdd (isSection_constLift s₀ h₀).sectionSmul
      (isSection_constLift s₁ h₁).sectionSmul,
    pullbackSlice_sectionSmul (isSection_constLift s₀ h₀),
    pullbackSlice_sectionSmul (isSection_constLift s₁ h₁), pullbackSlice_constLift,
    pullbackSlice_constLift]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

lemma pullbackSlice_cylInterp_apply (t : Fin 1 → ℝ) (x : X) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t x =
      (((1 - cylCut (t 0)) • (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) + cylCut (t 0) • ⟨s₁ x, h₁ x⟩ :
        P ⁻¹' {x}) : Y) := by
  rw [pullbackSlice_cylInterp, sectionAdd_sectionSmul_apply h₀ h₁]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

/-- `ŝ(t, ·) = s₀` for `t ≤ 3/16`. -/
lemma pullbackSlice_cylInterp_of_le {t : Fin 1 → ℝ} (ht : t 0 ≤ 3 / 16) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t = s₀ := by
  funext x
  rw [pullbackSlice_cylInterp_apply, cylCut_of_le ht]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

/-- `ŝ(t, ·) = s₁` for `t ≥ 13/16`. -/
lemma pullbackSlice_cylInterp_of_ge {t : Fin 1 → ℝ} (ht : 13 / 16 ≤ t 0) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t = s₁ := by
  funext x
  rw [pullbackSlice_cylInterp_apply, cylCut_of_ge ht]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in

/-- `ŝ(t, x) = 0` where `s₀(x) = s₁(x) = 0`. -/
lemma isZeroAt_pullbackSlice_cylInterp {x : X} (hx₀ : IsZeroAt P s₀ x) (hx₁ : IsZeroAt P s₁ x)
    (t : Fin 1 → ℝ) : IsZeroAt P (pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t) x := by
  have e₀ : (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hx₀
  have e₁ : (⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hx₁
  unfold IsZeroAt
  rw [pullbackSlice_cylInterp_apply, e₀, e₁, smul_zero, smul_zero, add_zero]
  rfl

/-- `N(ŝ(t, x)) ≤ 1` when `N(s₀(x)), N(s₁(x)) ≤ 1` (a convex combination). -/
lemma auxLe_pullbackSlice_cylInterp {N : B.One → ℝ} (hN : B.IsAuxNorm N) {x : X}
    (hx₀ : B.AuxLe N (s₀ x) 1) (hx₁ : B.AuxLe N (s₁ x) 1) (t : Fin 1 → ℝ) :
    B.AuxLe N (pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t x) 1 := by
  rw [pullbackSlice_cylInterp]
  refine (hN.auxLe_sectionAdd h₀.sectionSmul h₁.sectionSmul (hN.auxLe_sectionSmul h₀ _ hx₀)
    (hN.auxLe_sectionSmul h₁ _ hx₁)).mono (le_of_eq ?_)
  show |1 - cylCut (t 0)| * 1 + |cylCut (t 0)| * 1 = 1
  rw [abs_of_nonneg (sub_nonneg.2 (cylCut_le_one _)), abs_of_nonneg (cylCut_nonneg _)]
  ring

end CylinderSections

section Cobordism
open scoped ContDiff
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

/-- `ŝ = (1 − χ)·s̃₀ + χ·s̃₁` is an sc⁺-section of `π*P` for sc⁺-sections `s₀, s₁`
(`IsScPlusSection.smul_left`, `IsScPlusSection.add`, `isScPlusSection_constLift`). -/
theorem isScPlusSection_cylInterp {s₀ s₁ : X → Y} (h₀ : B.IsScPlusSection s₀)
    (h₁ : B.IsScPlusSection s₁) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (cylInterp s₀ s₁ h₀.1 h₁.1) :=
  ((isScPlusSection_constLift h₀).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => 1 - cylCut (r 0))
      (contDiff_const.sub (contDiff_cylCut.comp (contDiff_apply ℝ ℝ 0))))).add
    ((isScPlusSection_constLift h₁).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => cylCut (r 0)) (contDiff_cylCut.comp (contDiff_apply ℝ ℝ 0))))

variable {f : X → Y}

/-- **General position where the perturbation is `t`-constant**: if the slices of `T` near the
zero `z` (on an open `O ∋ z`) are those of an sc⁺-section `s` with `(f + s, x)` in general position
at every zero, then `(f̃ + T, z)` is in general position (`f̃ + T = (f + s)~` on `O`,
`isGeneralPositionGerm_paramLift`, `isGeneralPositionGerm_congr_nhds`). -/
theorem isGeneralPositionGerm_paramLift_add_of_eq (hf : B.IsScFredholmSectionTame f)
    {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection T)
    {s : X → Y} (hs : B.IsScPlusSection s) {O : Set ((Fin 1 → ℝ) × X)} (hO : IsOpen O)
    (hTO : ∀ w ∈ O, pullbackSlice T w.1 w.2 = s w.2)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    {z : (Fin 1 → ℝ) × X} (hzO : z ∈ O)
    (hz : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) T) z) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) T) z := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have hg := theorem_3_1_18_tame hf hs
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  have heq : ∀ w ∈ O, paramLift (sectionAdd P f s) hg.isScSmooth.1 w =
      sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) T w := by
    intro w hw
    refine (eq_paramLift_of_pullbackSlice (hL.sectionAdd hT.1) _ ?_).symm
    rw [pullbackSlice_sectionAdd_paramLift hfs hT.1]
    exact sectionAdd_congr_right hfs (hT.1.pullbackSlice w.1) hs.1 (hTO w hw)
  have hzL : IsZeroAt (pullbackProj P Prod.snd)
      (paramLift (n := 1) (sectionAdd P f s) hg.isScSmooth.1) z :=
    (isZeroAt_congr (heq z hzO)).2 hz
  have hz' : IsZeroAt P (sectionAdd P f s) z.2 :=
    (isZeroAt_pullback_iff_pullbackSlice (isSection_pullbackLift _) z.1 z.2).1 hzL
  exact isGeneralPositionGerm_congr_nhds hg.param (theorem_3_1_18_tame hf.param hT) hzL hO hzO
    heq (isGeneralPositionGerm_paramLift hg hz' (hgp z.2 hz') z.1)

/-- **The cobordism between two admissible sections** (2021 Remark 5.3.8, p. 219, and the proof of
Theorem 6.7.1, p. 278; preprint Remark 5.16 and Theorem 6.43), in the form used for Theorem 6.7.1:
let `X` be tame with sc-smooth bump functions, `f` an sc-Fredholm section (tame germ data), `N` an
auxiliary norm and `U ⊇ S_f` open with `cl{x ∈ U | N(f(x)) ≤ 2}` compact (the margin of
`exists_adapted_margin`). For `s₀, s₁ ∈ allowableSections N U` with `f + sᵢ` in general position
at every zero there is an sc⁺-section `S` of the pull-back to `ℝ¹ × X` with `S(t, ·) = s₀` for
`t ≤ 1/8`, `S(t, ·) = s₁` for `t ≥ 7/8`, `S = 0` over `X ∖ U`, `N(S) ≤ 2`, `f̃ + S` in general
position at every zero, and the zeros of `f̃ + S` over every `[a, b]` compact. The text's
cobordism is a section of the bundle over `[0, 1] × X`; here it lives on `ℝ¹ × X` and is
stationary near the ends (reading D2 of the plan). *Proof*: `S = ŝ + p`, `ŝ = (1 − χ)s̃₀ + χs̃₁`,
`p` from `theorem_5_3_10_relative_hyp` for `G = f̃ + ŝ`, the pulled-back norm, `W = (1/8, 7/8) × U`
and `K` the zeros over `[3/16, 13/16]`; off `K` the section `G` is `(f + sᵢ)~` near its zeros. -/
theorem exists_cobordism (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {N : B.One → ℝ} (hN : B.IsAuxNorm N) {U : Set X}
    (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hcpt : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 2})) {s₀ s₁ : X → Y}
    (hs₀ : s₀ ∈ B.allowableSections N U) (hs₁ : s₁ ∈ B.allowableSections N U)
    (hgp₀ : ∀ x, IsZeroAt P (sectionAdd P f s₀) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₀) x)
    (hgp₁ : ∀ x, IsZeroAt P (sectionAdd P f s₁) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₁) x) :
    ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
      (∀ t : Fin 1 → ℝ, t 0 ≤ 1 / 8 → pullbackSlice S t = s₀) ∧
      (∀ t : Fin 1 → ℝ, 7 / 8 ≤ t 0 → pullbackSlice S t = s₁) ∧
      (∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice S z.1) z.2) ∧
      (∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice S z.1 z.2) 2) ∧
      (∀ z, IsZeroAt (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) z) ∧
      ∀ a b : ℝ, IsCompact {z ∈ solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) |
        z.1 0 ∈ Icc a b} := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨hs₀p, hs₀U, hs₀N⟩ := hs₀
  obtain ⟨hs₁p, hs₁U, hs₁N⟩ := hs₁
  have hs₀N' : ∀ x, B.AuxLe N (s₀ x) 1 := fun x => ⟨hs₀p.mem_oneSet x, hs₀N x _⟩
  have hs₁N' : ∀ x, B.AuxLe N (s₁ x) 1 := fun x => ⟨hs₁p.mem_oneSet x, hs₁N x _⟩
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  -- the interpolation `ŝ` and `G = f̃ + ŝ`
  set ŝ := cylInterp s₀ s₁ hs₀p.1 hs₁p.1 with hŝdef
  have hŝ := isScPlusSection_cylInterp (B := B) hs₀p hs₁p
  have hŝU : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice ŝ z.1) z.2 :=
    fun z hz => isZeroAt_pullbackSlice_cylInterp hs₀p.1 hs₁p.1
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hs₀U hz)
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hs₁U hz) z.1
  have hŝN : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice ŝ z.1 z.2) 1 := fun z =>
    auxLe_pullbackSlice_cylInterp hs₀p.1 hs₁p.1 hN (hs₀N' z.2) (hs₁N' z.2) z.1
  have hGt := theorem_3_1_18_tame (hf.param (n := 1)) hŝ
  have hN₁ := hN.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)
  -- `W = (1/8, 7/8) × U` and the compact `K` of the zeros over `[3/16, 13/16]`
  set W : Set ((Fin 1 → ℝ) × X) := {z | z.1 0 ∈ Ioo (1 / 8 : ℝ) (7 / 8) ∧ z.2 ∈ U} with hWdef
  have hWo : IsOpen W :=
    (isOpen_Ioo.preimage continuous_fst_apply_zero).inter (hU.preimage continuous_snd)
  set K := {z ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) |
    z.1 0 ∈ Icc (3 / 16 : ℝ) (13 / 16)} with hKdef
  have hK : IsCompact K := isCompact_slab_paramLift_add hf hN hSU hcpt hŝ hŝU
    (fun z => (hŝN z).mono one_le_two) _ _
  have hKW : K ⊆ W := fun z hz =>
    ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩,
      mem_of_isZeroAt_paramLift_add hfs hŝ.1 hSU hŝU hz.1⟩
  -- off `K`, `G` is `(f + sᵢ)~` near its zeros
  have hgpK : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) z → z ∉ K →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) z := by
    intro z hz hzK
    have ht : z.1 0 < 3 / 16 ∨ 13 / 16 < z.1 0 := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hzK ⟨hz, h⟩
    rcases ht with ht | ht
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf hŝ hs₀p
        (isOpen_lt continuous_fst_apply_zero continuous_const)
        (fun w hw => congrFun (pullbackSlice_cylInterp_of_le hs₀p.1 hs₁p.1
          (le_of_lt (hw : w.1 0 < 3 / 16))) w.2) hgp₀ ht hz
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf hŝ hs₁p
        (isOpen_lt continuous_const continuous_fst_apply_zero)
        (fun w hw => congrFun (pullbackSlice_cylInterp_of_ge hs₀p.1 hs₁p.1
          (le_of_lt (hw : 13 / 16 < w.1 0))) w.2) hgp₁ ht hz
  -- the compact `cl{z ∈ W | N(G(z)) ≤ 1}`
  have hcpt₁ : IsCompact (closure {z ∈ W |
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).AuxLe
        (B.pullbackAuxNorm (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX) N)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ z) 1}) := by
    refine ((isCompact_Icc (a := fun _ : Fin 1 => (1 / 8 : ℝ)) (b := fun _ => 7 / 8)).prod
      hcpt).of_isClosed_subset isClosed_closure (closure_minimal ?_
        (isClosed_Icc.prod isClosed_closure))
    rintro z ⟨hzW, hzN⟩
    refine ⟨mem_Icc_of_apply_zero ⟨hzW.1.1.le, hzW.1.2.le⟩, subset_closure ⟨hzW.2, ?_⟩⟩
    have h1 := (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 hzN
    have := auxLe_of_auxLe_paramLift_add hfs hN hŝ.1 h1 (hŝN z)
    exact this.mono (by norm_num)
  -- the perturbation `p`
  obtain ⟨p, hp, hpW, hpN, hgpp⟩ := theorem_5_3_10_relative_hyp (prod_rn_isTame hX)
    (MPolyfold.admitsBumpFunctions_prod_rn hbump) hGt hN₁ hWo hK hKW hgpK hcpt₁ one_pos
  have hpZ : ∀ z ∉ W, IsZeroAt P (pullbackSlice p z.1) z.2 := fun z hz =>
    (isZeroAt_pullback_iff_pullbackSlice hp.1 z.1 z.2).1
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hpW hz)
  have hpN' : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice p z.1 z.2) 1 := fun z =>
    (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 (hpN z)
  have hslice : ∀ t, pullbackSlice (sectionAdd (pullbackProj P Prod.snd) ŝ p) t =
      sectionAdd P (pullbackSlice ŝ t) (pullbackSlice p t) := fun t =>
    pullbackSlice_sectionAdd hŝ.1 hp.1 t
  have hp0 : ∀ t : Fin 1 → ℝ, t 0 ∉ Ioo (1 / 8 : ℝ) (7 / 8) → pullbackSlice p t = fiberZero P :=
    fun t ht => funext fun x => hpZ (t, x) fun h => ht h.1
  have hS := hŝ.add hp
  refine ⟨sectionAdd (pullbackProj P Prod.snd) ŝ p, hS, fun t ht => ?_, fun t ht => ?_,
    fun z hz => ?_, fun z => ?_, fun z hz => ?_, fun a b => ?_⟩
  · rw [hslice, hp0 t fun h => by linarith [h.1],
      pullbackSlice_cylInterp_of_le hs₀p.1 hs₁p.1 (by linarith), sectionAdd_fiberZero hs₀p.1]
  · rw [hslice, hp0 t fun h => by linarith [h.2],
      pullbackSlice_cylInterp_of_ge hs₀p.1 hs₁p.1 (by linarith), sectionAdd_fiberZero hs₁p.1]
  · have h1 := hŝU z hz
    have h2 := hpZ z fun h => hz h.2
    unfold IsZeroAt at h1 h2 ⊢
    rw [hslice, sectionAdd_apply (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1)]
    have e₁ : (⟨pullbackSlice ŝ z.1 z.2, hŝ.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
      Subtype.ext h1
    have e₂ : (⟨pullbackSlice p z.1 z.2, hp.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
      Subtype.ext h2
    rw [e₁, e₂, add_zero]
    rfl
  · rw [hslice]
    exact (hN.auxLe_sectionAdd (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1) (hŝN z)
      (hpN' z)).mono (by norm_num)
  · rw [← sectionAdd_assoc hL hŝ.1 hp.1] at hz ⊢
    exact hgpp z hz
  · have hSU' : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U →
        IsZeroAt P (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) ŝ p) z.1) z.2 := by
      intro z hz
      have h1 := hŝU z hz
      have h2 := hpZ z fun h => hz h.2
      unfold IsZeroAt at h1 h2 ⊢
      rw [hslice, sectionAdd_apply (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1)]
      have e₁ : (⟨pullbackSlice ŝ z.1 z.2, hŝ.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
        Subtype.ext h1
      have e₂ : (⟨pullbackSlice p z.1 z.2, hp.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
        Subtype.ext h2
      rw [e₁, e₂, add_zero]
      rfl
    refine isCompact_slab_paramLift_add hf hN hSU hcpt hS hSU' (fun z => ?_) a b
    rw [hslice]
    exact (hN.auxLe_sectionAdd (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1) (hŝN z)
      (hpN' z)).mono (by norm_num)

end Cobordism
end Polyfold
end
