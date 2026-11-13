import Polyfold.Chapter3.LinearizationCharts
import Polyfold.Chapter2.TangentSpaceLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.1, Theorem 3.1.22
(preprint 3.19), p. 100, and the linearization `f'(y)` of a section at a zero (before
Definition 3.1.4): the chain rule behind the chart independence of `f'(y)`, with the operators
named.

# The chart change of `Lin(z)` with explicit operators

`linAt_chart_change` (`Chapter3/LinearizationCharts`) gives isomorphisms `A`, `Γ` with
`Γ ∘ Lin(z) = Lin'(z') ∘ A` but keeps them existential.  For the intrinsic linearization
`f'(y) : T_yX → Y_y` (`LinearizationIntrinsic`) we need them named: `A` is the derivative
`D(τ ∘ r_W)(z)` of the base transition `τ = φ' ∘ φ⁻¹` composed with a retraction `r_W` onto the
overlap, and `Γ` is the fibre operator `transitionFiberCLM`.  `linAt_chart_change_key` states this;
its proof is the first half of the proof of `linAt_chart_change`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

section ChartChangeKey

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f : X → Y}

open StrongRetr

/-- **The chain rule for `Lin(z)` under a change of strong bundle charts, with the operators
named.**  In the setting of `linAt_chart_change`: there is a retraction `r_W` with retract the base
overlap `φ(V ∩ V') = O ∩ W` (`W` open) such that for all `v`,
`D(f̂' ∘ r')(z') (D(τ ∘ r_W)(z) v) = Γ(z) (D(f̂ ∘ r)(z) v)`, with `Γ(z)` the fibre operator of the
transition (`transitionFiberCLM`). -/
theorem linAt_chart_change_key (c c' : StrongBundleChart PX P) (hf : IsSection P f)
    (hΘ : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c'))
    (hfc : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z)))
    (hfc' : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) c'.K (fun z => (z, c'.principal f z)))
    {y : X} (hyV : y ∈ c.φ.source) (hyV' : y ∈ c'.φ.source) (hy0 : IsZeroAt P f y)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    (hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O)
    (hzV' : c.φ.symm (c.φ.model.E.toBase 1 z) ∈ c'.φ.source) :
    ∃ Rw : ScRetraction c.φ.model.E c.φ.model.C, Rw.retract = c.φ.overlap c'.φ ∧
      (∃ W, IsOpen W ∧ c.φ.overlap c'.φ = c.φ.model.O ∩ W) ∧
      ∀ v, scDeriv c'.U (c'.principal f ∘ r c'.R) z'
          (scDeriv Rw.U (c.φ.transition c'.φ ∘ Rw) z v) =
        c.transitionFiberCLM c' hzOO hzV' (scDeriv c.U (c.principal f ∘ r c.R) z v) := by
  classical
  -- the base charts are compatible (both are charts of `X`)
  have hbase : c.φ.Compatible c'.φ := c.isChart.compatible c'.isChart (P := PX)
  obtain ⟨W, hWo, hW⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
    inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
  obtain ⟨W', hWo', hW'⟩ := c'.φ.exists_isOpen_image_eq (s := c'.φ.source ∩ c.φ.source)
    inter_subset_left (c'.φ.isOpen_source.inter c.φ.isOpen_source)
  set Rb := c.isRetraction.baseRetraction c.relOpen with hRb
  set Rb' := c'.isRetraction.baseRetraction c'.relOpen with hRb'
  set Rw := Rb.restrict hWo with hRwdef
  set Rw' := Rb'.restrict hWo' with hRw'def
  have hRw : Rw.retract = c.φ.overlap c'.φ := by
    rw [ScRetraction.restrict_retract, c.base_retract]; exact hW.symm
  have hRw' : Rw'.retract = c'.φ.overlap c.φ := by
    rw [ScRetraction.restrict_retract, c'.base_retract]; exact hW'.symm
  set τ := c.φ.transition c'.φ with hτdef
  set τ' := c'.φ.transition c.φ with hτ'def
  have hdiff : Rw.IsDiffeoGerm Rw' τ τ' :=
    { isSc1 := (hbase.1.comp_isScSmooth Rw hRw).isSc1
      isSc1_inv := (hbase.2.comp_isScSmooth Rw' hRw').isSc1
      mapsTo := by rw [hRw, hRw']; exact c.φ.transition_mapsTo c'.φ
      mapsTo_inv := by rw [hRw, hRw']; exact c'.φ.transition_mapsTo c.φ
      left_inv := by
        rw [hRw]; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c.φ.transition_apply c'.φ hy₁.1, c'.φ.transition_apply c.φ hy₁.2]
      right_inv := by
        rw [hRw']; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c'.φ.transition_apply c.φ hy₁.1, c.φ.transition_apply c'.φ hy₁.2] }
  -- the points
  have hyO : c.φ y ∈ c.φ.overlap c'.φ := c.φ.mem_overlap c'.φ hyV hyV'
  have hyO' : c'.φ y ∈ c'.φ.overlap c.φ := c'.φ.mem_overlap c.φ hyV' hyV
  have hx : z ∈ c.φ.model.E.lvlSet Rw.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hRw]; exact hyO
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyV
  have hzO' : c'.φ.model.E.toBase 1 z' ∈ r c'.R '' c'.U := by
    rw [hz', c'.r_image]; exact c'.φ.mapsTo_model y hyV'
  have hzOO' : c'.φ.model.E.toBase 1 z' ∈ c'.φ.model.O := by
    rw [hz']; exact c'.φ.mapsTo_model y hyV'
  have hzV : c'.φ.symm (c'.φ.model.E.toBase 1 z') ∈ c.φ.source := by
    rw [hz', c'.φ.symm_apply_apply hyV']; exact hyV
  have hτz : τ (c.φ.model.E.toBase 1 z) = c'.φ.model.E.toBase 1 z' := by
    rw [hz, hτdef, c.φ.transition_apply c'.φ hyV, hz']
  have hτz' : τ' (c'.φ.model.E.toBase 1 z') = c.φ.model.E.toBase 1 z := by
    rw [hz', hτ'def, c'.φ.transition_apply c.φ hyV', hz]
  have hlev : levelMap (τ ∘ Rw) 1 z = z' := by
    apply levelMap_eq_of_toBase_eq
    change c'.φ.model.E.toBase 1 z' = τ (r c.R (c.φ.model.E.toBase 1 z))
    rw [r_eq_self c.isRetraction hzO, hτz]
  have hz1 : z ∈ c.φ.model.E.lvlSet Rw.U 1 := Rw.lvlSet_retract_subset 1 hx
  have hRwU : Rw.U ⊆ c.U := inter_subset_left
  have hRwU' : Rw'.U ⊆ c'.U := inter_subset_left
  have hx' : z' ∈ c'.φ.model.E.lvlSet Rw'.retract 1 := by rw [← hlev]; exact hdiff.image_mem hx
  have hz1' : z' ∈ c'.φ.model.E.lvlSet Rw'.U 1 := Rw'.lvlSet_retract_subset 1 hx'
  -- derivatives of `r`, `f̂ ∘ r` on the restricted domains
  have hr1 : IsSc1 c.U (r c.R) := (r_isScSmooth c.relOpen c.isRetraction).isSc1
  have hr1' : IsSc1 c'.U (r c'.R) := (r_isScSmooth c'.relOpen c'.isRetraction).isSc1
  have hDr : scDeriv Rw.U Rw z = scDeriv c.U (r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen Rw.isSc1 hr1 subset_rfl hRwU (fun _ _ => rfl) hz1
  have hDr' : scDeriv Rw'.U Rw' z' = scDeriv c'.U (r c'.R) z' :=
    scDeriv_eq_of_eqOn_relOpen Rw'.relOpen Rw'.isSc1 hr1' subset_rfl hRwU' (fun _ _ => rfl) hz1'
  have hσsm : IsScSmooth c.U (scPair (r c.R) (c.principal f ∘ r c.R)) :=
    (hfc.comp_isScSmooth Rb c.base_retract).congr c.relOpen.isScDomain fun _ _ => rfl
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) :=
    ((hσsm.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hσsm' : IsScSmooth c'.U (scPair (r c'.R) (c'.principal f ∘ r c'.R)) :=
    (hfc'.comp_isScSmooth Rb' c'.base_retract).congr c'.relOpen.isScDomain fun _ _ => rfl
  have hfr' : IsSc1 c'.U (c'.principal f ∘ r c'.R) :=
    ((hσsm'.snd c'.relOpen.isScDomain).congr c'.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hrRw : IsSc1 Rw.U (r c.R) := hr1.of_subset hRwU
  have hfrRw : IsSc1 Rw.U (c.principal f ∘ r c.R) := hfr.of_subset hRwU
  have hDfr : scDeriv Rw.U (c.principal f ∘ r c.R) z = scDeriv c.U (c.principal f ∘ r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hfrRw hfr subset_rfl hRwU (fun _ _ => rfl) hz1
  -- the retraction onto the overlap of `K` and the transition `Θ`
  set RK := (c.isRetraction.toScRetraction c.relOpen).restrict (hWo.prod isOpen_univ) with hRKdef
  have hRK : RK.retract = c.overlap c' := by
    rw [ScRetraction.restrict_retract]; exact (c.overlap_eq_inter_prod c' hW).symm
  have hRKapp : ∀ p, RK p = c.R p := fun _ => rfl
  have hΘs : IsScSmooth (F := c'.φ.model.E.prod c'.F) RK.U (c.transition c' ∘ RK) :=
    hΘ.comp_isScSmooth RK hRK
  set Φ : (c.φ.model.E.prod c.F) 0 → c'.F 0 := fun p => ((c.transition c' ∘ RK) p).2 with hΦdef
  have hΦ : IsSc1 RK.U Φ := (hΘs.snd RK.isScDomain).isSc1
  -- the fibre operator `Γ(z)` and the vanishing of `Φ` on the zero section
  set Γt := c.transitionFiberCLM c' hzOO hzV' with hΓt
  have hzW : c.φ.model.E.toBase 1 z ∈ W := by
    have : c.φ.model.E.toBase 1 z ∈ c.φ.model.O ∩ W := by rw [← hW, hz]; exact hyO
    exact this.2
  have hRz : ∀ k, c.R (c.φ.model.E.toBase 1 z, k) =
      (c.φ.model.E.toBase 1 z, ρ c.R (c.φ.model.E.toBase 1 z) k) := fun k => by
    rw [apply_eq c.isRetraction hzU, r_eq_self c.isRetraction hzO]
  have hzD : ∀ k : c.F 0, ((c.φ.model.E.toBase 1 z, k) : (c.φ.model.E.prod c.F) 0) ∈ RK.U :=
    fun k => ⟨⟨hzU, mem_univ _⟩, by
      change c.R (c.φ.model.E.toBase 1 z, k) ∈ W ×ˢ univ
      rw [hRz]; exact ⟨hzW, mem_univ _⟩⟩
  have hSD : ∀ u ∈ Rw.U, ((u, 0) : (c.φ.model.E.prod c.F) 0) ∈ RK.U := fun u hu =>
    ⟨⟨hu.1, mem_univ _⟩, ⟨hu.2, mem_univ _⟩⟩
  have hΓ : ∀ k, Φ (c.φ.model.E.toBase 1 z, k) = Γt k := fun k => by
    rw [hΓt, StrongBundleChart.transitionFiberCLM_apply]
    change (c.transition c' (c.R (c.φ.model.E.toBase 1 z, k))).2 = _
    rw [hRz]
  have hzero : ∀ u ∈ Rw.U, Φ (u, 0) = 0 := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    have hR0 : c.R (u, 0) = (r c.R u, 0) := by
      rw [apply_eq c.isRetraction hu.1, (ρ_isLinear c.isRetraction hu.1).map_zero]
    have hK0 : (r c.R u, (0 : c.F 0)) ∈ c.K := by
      rw [← hR0]; exact ⟨(u, 0), ⟨hu.1, mem_univ _⟩, rfl⟩
    change (c.transition c' (c.R (u, 0))).2 = 0
    rw [hR0]
    exact c.transition_snd_zero c' hK0 (c.φ.symm_mem_of_mem_overlap c'.φ hru)
  -- the section in the chart and the main identity
  set σ := scPair (r c.R) (c.principal f ∘ r c.R) with hσdef
  have hσmem : ∀ u ∈ Rw.U, ∃ y₁, y₁ ∈ c.φ.source ∧ y₁ ∈ c'.φ.source ∧ r c.R u = c.φ y₁ ∧
      σ u = c (f y₁) ∧ σ u ∈ RK.retract := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    obtain ⟨y₁, ⟨hy₁, hy₁'⟩, hy₁u⟩ := hru
    have hσu : σ u = c (f y₁) := by
      change (r c.R u, c.principal f (r c.R u)) = c (f y₁)
      rw [← hy₁u, c.apply_section' hf hy₁]
    refine ⟨y₁, hy₁, hy₁', hy₁u.symm, hσu, ?_⟩
    rw [hRK, hσu]
    exact ⟨f y₁, ⟨c.mem_source_of_proj (by rw [hf]; exact hy₁),
      c'.mem_source_of_proj (by rw [hf]; exact hy₁')⟩, rfl⟩
  have hmapsσ : MapsTo σ Rw.U RK.U := fun u hu => by
    obtain ⟨-, -, -, -, -, h⟩ := hσmem u hu
    exact RK.retract_subset h
  have hσ1 : IsSc1 Rw.U σ := (hσsm.of_subset Rw.isScDomain hRwU).isSc1
  have hEq : EqOn ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) (Φ ∘ σ) Rw.U := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hru, hσu, hσK⟩ := hσmem u hu
    have hτu : τ (r c.R u) = c'.φ y₁ := by rw [hru, hτdef, c.φ.transition_apply c'.φ hy₁]
    have hr' : r c'.R (c'.φ y₁) = c'.φ y₁ :=
      r_eq_self c'.isRetraction (by rw [c'.r_image]; exact c'.φ.mapsTo_model y₁ hy₁')
    change c'.principal f (r c'.R (τ (r c.R u))) = (c.transition c' (RK (σ u))).2
    rw [RK.apply_eq_self_of_mem_retract hσK, hσu]
    change _ = (c' (c.toPartialEquiv.symm (c (f y₁)))).2
    rw [c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hf]; exact hy₁)),
      c'.apply_section' hf hy₁', hτu, hr']
  have hmapsτ : MapsTo (τ ∘ Rw) Rw.U c'.U := fun u hu => (hdiff.mapsTo_U hu).1
  have hℓ : IsSc1 Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) :=
    (theorem_1_3_1' Rw.isScDomain c'.relOpen.isScDomain hdiff.isSc1 hfr' hmapsτ).1
  have hΦσ : IsSc1 Rw.U (Φ ∘ σ) :=
    (theorem_1_3_1' Rw.isScDomain RK.isScDomain hσ1 hΦ hmapsσ).1
  have hDeq : scDeriv Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) z = scDeriv Rw.U (Φ ∘ σ) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hℓ hΦσ subset_rfl subset_rfl hEq hz1
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]; exact (c.isZeroAt_iff hf hyV).1 hy0
  have hlevσ : levelMap σ 1 z = ((z, 0) : (c.φ.model.E.prod c.F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change (c.φ.model.E.toBase 1 z, (0 : c.F 0)) =
      (r c.R (c.φ.model.E.toBase 1 z), c.principal f (r c.R (c.φ.model.E.toBase 1 z)))
    rw [r_eq_self c.isRetraction hzO, hfz]
  have key : ∀ v, scDeriv c'.U (c'.principal f ∘ r c'.R) z' (scDeriv Rw.U (τ ∘ Rw) z v) =
      Γt (scDeriv c.U (c.principal f ∘ r c.R) z v) := by
    intro v
    have h1 := scDeriv_comp_apply' Rw.relOpen c'.relOpen hdiff.isSc1 hfr' hmapsτ hz1 v
    rw [hlev] at h1
    have h2 := scDeriv_comp_apply' Rw.relOpen RK.relOpen hσ1 hΦ hmapsσ hz1 v
    rw [hlevσ, hσdef, scDeriv_scPair Rw.relOpen hrRw hfrRw hz1, ContinuousLinearMap.prod_apply,
      scDeriv_fiber_of_vanishing Rw.relOpen hΦ hz1 hSD hzD hzero Γt hΓ] at h2
    rw [h1, hDeq, ← h2, hDfr]
  exact ⟨Rw, hRw, ⟨W, hWo, by rw [← hRw, ScRetraction.restrict_retract, c.base_retract]⟩, key⟩

end ChartChangeKey

end Polyfold
