import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_9

/-! Round trip for V12_9 (2021 Theorem 12.2.7, pp. 574–576: extension of auxiliary norms from
the boundary).

The item lists `theorem_12_2_7` (the theorem as printed) and the pieces of its proof:
`theorem_12_2_7_hyp` (the theorem without tameness, with the local extension step as the
hypothesis `HasLocalExtensions`), `theorem_12_2_7_hyp_witness`, `hasLocalExtensions_of_isTame`,
the Part I local step `exists_localExtension_of_isTame`, `isLocalAuxNorm_retractNorm`,
`retractNorm_eq`, `MPolyfold.exists_retraction_boundary`, and small lemmas
(`IsAuxNorm.isAuxNormOn`, `hasLocalExtensions_of_isAuxNorm`, `tgt_mem_boundary_iff`,
`isOpen_compl_boundary`, `IsLocalAuxNorm.mono`).  `A` is the conjunction of their types at
universe `0` (`.{0, 0}` for the Part I lemmas with two universes).

* `A_to_B`: `theorem_12_2_7` is `B` (B's extra pullback-paracompactness instance unused).
* `B_to_A`: `theorem_12_2_7` from `B` (the pullback instance from
  `StrongBundle.paracompactSpace_pullback`).  The other conjuncts do not follow from `B`
  (`theorem_12_2_7_hyp` has no tameness, the local step no paracompactness of `|X|`); they are
  re-proved outright by copying the project's proofs, which use only non-item lemmas
  (`retractNorm` machinery, `boundaryShift` lemmas, Theorem 12.2.2's `avgNorm`/`transNorm`/`glueNorm`
  lemmas, `theorem_12_2_2`).
-/

namespace RoundTrip.V12_9
open Polyfold
open Set Filter Topology Function TopologicalSpace

universe u v

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_7.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.hasLocalExtensions_of_isTame.{0}) ∧
  (type_of% @Polyfold.StrongBundle.exists_localExtension_of_isTame.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.isLocalAuxNorm_retractNorm.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.retractNorm_eq.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_retraction_boundary.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_7_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_7_hyp_witness.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsAuxNorm.isAuxNormOn.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.hasLocalExtensions_of_isAuxNorm.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tgt_mem_boundary_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOpen_compl_boundary.{0}) ∧
  (type_of% @Polyfold.StrongBundle.IsLocalAuxNorm.mono.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_2_7.{0}, @Polyfold.EpStrongBundle.hasLocalExtensions_of_isTame.{0}, @Polyfold.StrongBundle.exists_localExtension_of_isTame.{0, 0}, @Polyfold.StrongBundle.isLocalAuxNorm_retractNorm.{0, 0}, @Polyfold.StrongBundle.retractNorm_eq.{0, 0}, @Polyfold.MPolyfold.exists_retraction_boundary.{0}, @Polyfold.EpStrongBundle.theorem_12_2_7_hyp.{0}, @Polyfold.EpStrongBundle.theorem_12_2_7_hyp_witness.{0}, @Polyfold.EpStrongBundle.IsAuxNorm.isAuxNormOn.{0}, @Polyfold.EpStrongBundle.hasLocalExtensions_of_isAuxNorm.{0}, @Polyfold.EpGroupoid.tgt_mem_boundary_iff.{0}, @Polyfold.EpGroupoid.isOpen_compl_boundary.{0}, @Polyfold.StrongBundle.IsLocalAuxNorm.mono.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E hT hX N hN
  exact h hT hX hN

/-! ### The proof's pieces, re-proved outright (the project's proofs, copied) -/

section Retraction
open Polyfold.MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

theorem exists_retraction_boundary' (hP : P.IsTame) {x₀ : X} (hx₀ : x₀ ∈ P.boundary) :
    ∃ (V : Set X) (ρ : X → X), IsOpen V ∧ x₀ ∈ V ∧ ContinuousOn ρ V ∧
      MapsTo ρ V P.boundary ∧ ∀ y ∈ V ∩ P.boundary, ρ y = y := by
  obtain ⟨ψ, hψ, hx₀ψ, htame⟩ := IsTame.exists_chart P hP x₀
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := ψ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ z ∈ ψ.source, P.degIndex z = degIndexWith T (ψ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hψ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (ψ.apply_mem_C hz)]
  have hbd : ∀ z ∈ ψ.source, z ∈ P.boundary ↔ ∃ i, (T 0 (ψ z)).1 i = 0 := fun z hz => by
    change 1 ≤ P.degIndex z ↔ _
    rw [hdeg z hz, one_le_degIndexWith_iff]
  obtain ⟨i₀, -⟩ := (hbd x₀ hx₀ψ).1 hx₀
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  set q := boundaryShift T hne with hq
  have hqC : ∀ z, q z ∈ ψ.model.C := fun z => by
    rw [hT]; exact mem_quadrant_boundaryShift T hne z
  obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
  set V := ψ.source ∩ ψ ⁻¹' (q ⁻¹' V₀) with hV
  have hVo : IsOpen V := ψ.continuousOn_toFun.isOpen_inter_preimage ψ.isOpen_source
    (hV₀.preimage (continuous_boundaryShift T hne))
  have hqU : ∀ y ∈ V, q (ψ y) ∈ R.U := fun y hy => by
    rw [hUV]; exact ⟨hy.2, hqC _⟩
  have hRO' : ∀ y ∈ V, R (q (ψ y)) ∈ ψ.model.O := fun y hy => by
    rw [← hRO]; exact R.apply_mem_retract (hqU y hy)
  -- the points of `V ∩ ∂X` are fixed by `q`
  have hfixq : ∀ y ∈ ψ.source, y ∈ P.boundary → q (ψ y) = ψ y := fun y hy hyb => by
    obtain ⟨i, hi⟩ := (hbd y hy).1 hyb
    have hyC := ψ.apply_mem_C hy
    rw [hT] at hyC
    exact boundaryShift_eq_self T hne hyC hi
  have hx₀V : x₀ ∈ V := by
    refine ⟨hx₀ψ, ?_⟩
    change q (ψ x₀) ∈ V₀
    rw [hfixq x₀ hx₀ψ hx₀]
    have : ψ x₀ ∈ R.U := R.retract_subset (hRO ▸ ψ.mapsTo_model x₀ hx₀ψ)
    rw [hUV] at this; exact this.1
  refine ⟨V, fun y => ψ.symm (R (q (ψ y))), hVo, hx₀V, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · -- continuity
    have h1 : ContinuousOn (fun y => q (ψ y)) V :=
      (continuous_boundaryShift T hne).comp_continuousOn
        (ψ.continuousOn_toFun.mono inter_subset_left)
    have h2 : ContinuousOn (fun y => R (q (ψ y))) V :=
      R.isSc1.isSc0.continuousOn_base.comp h1 hqU
    exact ψ.continuousOn_invFun.comp h2 hRO'
  · -- values in `∂X`
    have hmem := ψ.symm_mapsTo (hRO' y hy)
    refine (hbd _ hmem).2 ?_
    rw [ψ.apply_symm_apply (hRO' y hy), ← one_le_degIndexWith_iff]
    have hqUy := hqU y hy
    have h1 := hR.degIndex_apply _ hqUy
    rw [degIndex_eq T hT (R.U_subset_C (R.mapsTo hqUy)), degIndex_eq T hT (R.U_subset_C hqUy)]
      at h1
    rw [h1, one_le_degIndexWith_iff]
    exact exists_coord_boundaryShift_eq_zero T hne _
  · -- the identity on `V ∩ ∂X`
    change ψ.symm (R (q (ψ y))) = y
    rw [hfixq y hy.1.1 hy.2, R.apply_eq_self_of_mem_retract (hRO ▸ ψ.mapsTo_model y hy.1.1),
      ψ.symm_apply_apply hy.1.1]

end Retraction

section PartI
open Polyfold.MPolyfold Polyfold.StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

theorem mono' {V V' : Set X} {M : B.One → ℝ}
    (h : B.IsLocalAuxNorm V M) (hV : V' ⊆ V) : B.IsLocalAuxNorm V' M :=
  ⟨h.continuousOn.mono fun _ hw => hV hw, fun y hy => h.seminorm y (hV hy),
    fun w y hy h1 h2 => h.tendsto w y (hV hy) h1 h2⟩

section LocalAux

variable {c : StrongBundleChart PX P} (hc : B.IsChart c) (y₀ : B.One)

theorem isLocalAuxNorm_retractNorm' {A V : Set X} (hV : IsOpen V) (hVc : V ⊆ c.φ.source)
    {ρ : X → X} (hρ : ContinuousOn ρ V) (hρA : MapsTo ρ V A) (hρc : MapsTo ρ V c.φ.source)
    {N : B.One → ℝ} (hNc : ContinuousOn N {w | P (B.oneVal w) ∈ A})
    (hNs : ∀ y ∈ A, B.IsFiberSeminorm N y)
    (hN2 : ∀ (w : ℕ → B.One) (y : X), y ∈ A → (∀ k, P (B.oneVal (w k)) ∈ A) →
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
        Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y))) :
    B.IsLocalAuxNorm V (retractNorm hc y₀ ρ N) := by
  set Φ := oneChartOf hc y₀ with hΦ
  set S := {w : B.One | P (B.oneVal w) ∈ V}
  have hPc : Continuous fun w : B.One => P (B.oneVal w) := B.continuous.comp B.continuous_oneVal
  set u : B.One → c.φ.model.E 0 := fun w => c.φ (ρ (P (B.oneVal w))) with hu
  set z : B.One → (c.φ.model.E.prod c.F.shift) 0 := fun w => (u w, chartFibMap c (u w) (Φ w).2)
    with hz
  set T : B.One → B.One := fun w => Φ.symm (z w) with hT
  have huO : ∀ w ∈ S, u w ∈ c.φ.model.O := fun w hw => c.φ.mapsTo_model _ (hρc hw)
  have hzK : ∀ w ∈ S, z w ∈ strongShiftOne c.K := fun w hw => mem_K_chartFibMap (huO w hw) _
  have hPT : ∀ w ∈ S, P (B.oneVal (T w)) = ρ (P (B.oneVal w)) := fun w hw =>
    proj_oneChartOf_symm hc y₀ (hρc hw) (hzK w hw)
  have hMT : ∀ w, retractNorm hc y₀ ρ N w = N (T w) + ‖(Φ w).2 - (z w).2‖ := fun _ => rfl
  have hSsrc : ∀ w ∈ S, w ∈ Φ.source := fun w hw => (mem_oneChartOf_source hc y₀).2 (hVc hw)
  -- continuity of the pieces
  have hΦc : ContinuousOn Φ S := Φ.continuousOn_toFun.mono hSsrc
  have huc : ContinuousOn u S :=
    c.φ.continuousOn_toFun.comp (hρ.comp hPc.continuousOn fun _ hw => hw) fun _ hw => hρc hw
  have hzc : ContinuousOn z S := by
    have h1 : ContinuousOn (fun w => shiftFiber c.R (u w, (Φ w).2)) S :=
      continuousOn_shiftFiber_R.comp (huc.prodMk (continuous_snd.comp_continuousOn hΦc))
        fun w hw => ⟨mem_U_of_mem_O (huO w hw), mem_univ _⟩
    exact h1.congr fun w hw => (shiftFiber_eq_chartFibMap (huO w hw) _).symm
  have hTc : ContinuousOn T S := Φ.continuousOn_invFun.comp hzc hzK
  refine ⟨?_, fun y hy => ?_, fun w y hyV hy hM => ?_⟩
  · -- continuity of `N'` on `W_{0,1}|V`
    have h1 : ContinuousOn (fun w => N (T w)) S :=
      hNc.comp hTc fun w hw => by
        change P (B.oneVal (T w)) ∈ A
        rw [hPT w hw]; exact hρA hw
    have h2 : ContinuousOn (fun w => ‖(Φ w).2 - (z w).2‖) S :=
      continuous_norm.comp_continuousOn
        ((continuous_snd.comp_continuousOn hΦc).sub (continuous_snd.comp_continuousOn hzc))
    exact (h1.add h2).congr fun w _ => hMT w
  · -- seminorms on the fibres
    exact isFiberSeminorm_retractNorm (hVc hy) (hρc hy) (hNs _ (hρA hy))
  · -- condition (2)
    have hev : ∀ᶠ k in atTop, w k ∈ S := hy.eventually (hV.mem_nhds hyV)
    have hnn1 : ∀ᶠ k in atTop, 0 ≤ N (T (w k)) := hev.mono fun k hk => by
      have hs := hNs _ (hρA hk)
      rw [← hPT _ hk] at hs
      exact hs.nonneg (B.ofOne (T (w k)))
    have hle : ∀ᶠ k in atTop, N (T (w k)) ≤ retractNorm hc y₀ ρ N (w k) :=
      Eventually.of_forall fun k => by rw [hMT]; exact le_add_of_nonneg_right (norm_nonneg _)
    have hN0 : Tendsto (fun k => N (T (w k))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM hnn1 hle
    have hle2 : ∀ᶠ k in atTop, ‖(Φ (w k)).2 - (z (w k)).2‖ ≤ retractNorm hc y₀ ρ N (w k) :=
      hnn1.mono fun k hk => by rw [hMT]; linarith
    have hD0 : Tendsto (fun k => ‖(Φ (w k)).2 - (z (w k)).2‖) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM
        (Eventually.of_forall fun _ => norm_nonneg _) hle2
    -- `T(w_k) → 0_{ρ(y)}`, through condition (2) of `N` on a tail of the sequence
    have hρt : Tendsto (fun k => ρ (P (B.oneVal (w k)))) atTop (𝓝 (ρ y)) :=
      (hρ.continuousAt (hV.mem_nhds hyV)).tendsto.comp hy
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
    have hTt : Tendsto (fun k => T (w k)) atTop (𝓝 (B.zeroOne (ρ y))) := by
      rw [← tendsto_add_atTop_iff_nat K₀]
      refine hN2 (fun k => T (w (k + K₀))) (ρ y) (hρA hyV)
        (fun k => by rw [hPT _ (hK₀ _ (Nat.le_add_left _ _))]; exact hρA (hK₀ _ (by omega)))
        ?_ ((tendsto_add_atTop_iff_nat K₀).2 hN0)
      have := (tendsto_add_atTop_iff_nat K₀).2 hρt
      refine this.congr fun k => ?_
      rw [hPT _ (hK₀ _ (by omega))]
    -- read in the chart: `A(u_k)h_k → 0` in `F₁`
    have hρyc : ρ y ∈ c.φ.source := hρc hyV
    have h0src : B.zeroOne (ρ y) ∈ Φ.source :=
      (mem_oneChartOf_source hc y₀).2 (by rw [proj_oneVal_zeroOne B]; exact hρyc)
    have hΦT : Tendsto (fun k => Φ (T (w k))) atTop (𝓝 (c.φ (ρ y), 0)) := by
      have := (Φ.continuousOn_toFun.continuousAt (Φ.isOpen_source.mem_nhds h0src)).tendsto.comp
        hTt
      rwa [oneChartOf_apply, oneVal_zeroOne B, liftOne_fiberZero hρyc] at this
    have hA0 : Tendsto (fun k => (z (w k)).2) atTop (𝓝 0) := by
      have := (continuous_snd.tendsto _).comp hΦT
      refine this.congr' ?_
      filter_upwards [hev] with k hk
      change (Φ (Φ.symm (z (w k)))).2 = (z (w k)).2
      rw [Φ.apply_symm_apply (hzK _ hk)]
    have hh0 : Tendsto (fun k => (Φ (w k)).2) atTop (𝓝 0) := by
      have h1 := (tendsto_zero_iff_norm_tendsto_zero.2 hD0).add hA0
      rw [add_zero] at h1
      exact h1.congr fun k => sub_add_cancel _ _
    have hyc : y ∈ c.φ.source := hVc hyV
    have h1 : Tendsto (fun k => (Φ (w k)).1) atTop (𝓝 (c.φ y)) := by
      have := (c.φ.continuousOn_toFun.continuousAt (c.φ.isOpen_source.mem_nhds hyc)).tendsto.comp
        hy
      refine this.congr' ?_
      filter_upwards [hev] with k hk
      rw [oneChartOf_apply, fst_liftOne (hVc hk)]; rfl
    have hy0src : B.zeroOne y ∈ Φ.source :=
      (mem_oneChartOf_source hc y₀).2 (by rw [proj_oneVal_zeroOne B]; exact hyc)
    refine Φ.tendsto_of_tendsto_apply hy0src (hev.mono fun _ hk => hSsrc _ hk) ?_
    rw [oneChartOf_apply, oneVal_zeroOne B, liftOne_fiberZero hyc]
    exact h1.prodMk_nhds hh0

theorem retractNorm_eq' {A V : Set X} (hVc : V ⊆ c.φ.source) {ρ : X → X}
    (hfix : ∀ y ∈ V ∩ A, ρ y = y) (N : B.One → ℝ) {w : B.One} (hw : P (B.oneVal w) ∈ V ∩ A) :
    retractNorm hc y₀ ρ N w = N w :=
  retractNorm_eq_of_fix N (hVc hw.1) (hfix _ hw)

end LocalAux

theorem exists_localExtension_of_isTame' (hP : PX.IsTame) {N : B.One → ℝ}
    (hNc : ContinuousOn N {w | P (B.oneVal w) ∈ PX.boundary})
    (hNs : ∀ y ∈ PX.boundary, B.IsFiberSeminorm N y)
    (hN2 : ∀ (w : ℕ → B.One) (y : X), y ∈ PX.boundary → (∀ k, P (B.oneVal (w k)) ∈ PX.boundary) →
      Tendsto (fun k => P (B.oneVal (w k))) atTop (𝓝 y) →
        Tendsto (fun k => N (w k)) atTop (𝓝 0) → Tendsto w atTop (𝓝 (B.zeroOne y)))
    {x₀ : X} (hx₀ : x₀ ∈ PX.boundary) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∃ M : B.One → ℝ,
      B.IsLocalAuxNorm V M ∧ ∀ w : B.One, P (B.oneVal w) ∈ V ∩ PX.boundary → M w = N w := by
  obtain ⟨V₁, ρ, hV₁, hx₀V₁, hρ, hρA, hfix⟩ := exists_retraction_boundary' PX hP hx₀
  obtain ⟨c, hcm, hx₀c⟩ := exists_chart_mem B x₀
  have hc := B.isChart_of_mem hcm
  set V := (V₁ ∩ c.φ.source) ∩ ρ ⁻¹' c.φ.source
  have hVo : IsOpen V :=
    (hρ.mono inter_subset_left).isOpen_inter_preimage (hV₁.inter c.φ.isOpen_source)
      c.φ.isOpen_source
  have hρx₀ : ρ x₀ = x₀ := hfix x₀ ⟨hx₀V₁, hx₀⟩
  have hx₀V : x₀ ∈ V := ⟨⟨hx₀V₁, hx₀c⟩, by rw [mem_preimage, hρx₀]; exact hx₀c⟩
  have hVc : V ⊆ c.φ.source := fun y hy => hy.1.2
  refine ⟨V, hVo, hx₀V, retractNorm hc (B.zeroOne x₀) ρ N, ?_, fun w hw => ?_⟩
  · exact isLocalAuxNorm_retractNorm' hc _ hVo hVc (hρ.mono fun y hy => hy.1.1)
      (fun y hy => hρA hy.1.1) (fun y hy => hy.2) hNc hNs hN2
  · exact retractNorm_eq' hc _ hVc (fun y hy => hfix y ⟨hy.1.1.1, hy.2⟩) N hw

end PartI

section Boundary

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

theorem tgt_mem_boundary_iff' (φ : Mor) :
    X.tgt φ ∈ X.PObj.boundary ↔ X.src φ ∈ X.PObj.boundary := by
  change 1 ≤ X.PObj.degIndex (X.tgt φ) ↔ 1 ≤ X.PObj.degIndex (X.src φ)
  rw [← X.degIndex_tgt φ, X.degIndex_src φ]

theorem isOpen_compl_boundary' : IsOpen X.PObj.boundaryᶜ := by
  have h : X.PObj.boundaryᶜ = {x | X.PObj.degIndex x < 1} := by
    ext x; simp [MPolyfold.boundary]
  rw [h]; exact X.PObj.isOpen_setOf_degIndex_lt 1

end Boundary

section Ep
open Polyfold.EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {E : EpStrongBundle X B}

theorem isAuxNormOn' {N : B.One → ℝ} (hN : E.IsAuxNorm N) (A : Set Obj) :
    E.IsAuxNormOn A N :=
  ⟨hN.isAuxNorm.continuous.continuousOn, fun y _ => hN.isAuxNorm.fiber y,
    fun w y _ _ h1 h2 => hN.isAuxNorm.tendsto_zeroOne w y h1 h2,
    fun h k φ hk _ hh => hN.map_μ h k φ hk hh⟩

theorem theorem_12_2_7_hyp' (h : X.HasParacompactOrbitSpace) {N : B.One → ℝ}
    (hN : E.IsAuxNormOn X.PObj.boundary N) (hloc : HasLocalExtensions X B N) :
    ∃ Ñ : B.One → ℝ, E.IsAuxNorm Ñ ∧
      ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → Ñ w = N w := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  have : ParacompactSpace X.OrbitSpace := h
  have := X.theorem_7_3_1_metrizable h
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_3_exists (B := B)
  have hdata : ∀ x : Obj, ∃ (R : X.NaturalRep x) (M : B.One → ℝ), B.IsLocalAuxNorm R.U M ∧
      (x ∈ X.PObj.boundary → ∀ w : B.One, P (B.oneVal w) ∈ R.U ∩ X.PObj.boundary → M w = N w) ∧
      (x ∉ X.PObj.boundary → R.U ⊆ X.PObj.boundaryᶜ) := by
    intro x
    by_cases hx : x ∈ X.PObj.boundary
    · obtain ⟨V, hVo, hxV, M, hM, hMN⟩ := hloc x hx
      obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hVo hxV
      exact ⟨R, M, mono' hM hRV, fun _ w hw => hMN w ⟨hRV hw.1, hw.2⟩, fun h' => absurd hx h'⟩
    · obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x (isOpen_compl_boundary' X) hx
      exact ⟨R, N₀, hN₀.isLocalAuxNorm _, fun h' => absurd h' hx, fun _ => hRV⟩
  choose R M hM hMN hRint using hdata
  have hM' : ∀ x, B.IsLocalAuxNorm (R x).U (E.avgNorm (R x) (M x)) := fun x =>
    E.isLocalAuxNorm_avgNorm (R x) (hM x)
  have hinv : ∀ x g w, P (B.oneVal w) ∈ (R x).U →
      E.avgNorm (R x) (M x) (E.actOne ((R x).Γ g) w) = E.avgNorm (R x) (M x) w :=
    fun x g w hw => E.avgNorm_actOne (R x) (M x) g hw
  obtain ⟨β, hβ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun x => X.π '' X.satSet (R x).U)
    (fun x => by rw [EpGroupoid.image_π_satSet]; exact X.proposition_7_1_8 _ (R x).isOpen_U)
    fun z _ => by
      obtain ⟨y, rfl⟩ := X.surjective_π z
      exact mem_iUnion.2 ⟨y, y, EpGroupoid.subset_satSet _ (R y).mem_U, rfl⟩
  set T : Obj → B.One → ℝ := fun x => E.transNorm (R x) (E.avgNorm (R x) (M x)) with hT
  refine ⟨glueNorm β T, isAuxNorm_glueNorm (E := E) (U := fun x => X.satSet (R x).U)
    (fun x => EpGroupoid.isOpen_satSet (R x).isOpen_U)
    (fun x => EpGroupoid.isSaturated_satSet _) hβ
    (fun x => isLocalAuxNorm_transNorm (hM' x) (hinv x))
    (fun x h k ψ hk _ hh => transNorm_μ (hinv x) h k ψ hk hh), fun w hw => ?_⟩
  -- over `∂X` every nonzero term of the glued norm is `β_x · N`
  have key : ∀ x, β x (X.π (P (B.oneVal w))) * T x w = β x (X.π (P (B.oneVal w))) * N w := by
    intro x
    by_cases hβ0 : β x (X.π (P (B.oneVal w))) = 0
    · rw [hβ0, zero_mul, zero_mul]
    have hyU : P (B.oneVal w) ∈ X.satSet (R x).U :=
      EpGroupoid.mem_of_π_mem_image (EpGroupoid.isSaturated_satSet _) (hβ x (subset_tsupport _ hβ0))
    have hxb : x ∈ X.PObj.boundary := by
      by_contra hx
      obtain ⟨φ, hφs, hφt⟩ := hyU
      exact hRint x hx hφt ((tgt_mem_boundary_iff' X φ).2 (hφs ▸ hw))
    congr 1
    change E.transNorm (R x) (E.avgNorm (R x) (M x)) w = N w
    rw [transNorm, if_pos hyU]
    have hφs := X.src_selMor (R x).U (P (B.oneVal w))
    set v := E.actOne (X.selMor (R x).U) w with hv
    have hPv : P (B.oneVal v) = X.tgt (X.selMor (R x).U (P (B.oneVal w))) := E.P_actOne hφs
    have hvU : P (B.oneVal v) ∈ (R x).U := hPv ▸ X.tgt_selMor_mem hyU
    have hvb : P (B.oneVal v) ∈ X.PObj.boundary :=
      hPv ▸ (tgt_mem_boundary_iff' X _).2 (hφs.symm ▸ hw)
    have hNv : N v = N w := hN.map_μ v w _ hφs.symm hw (E.oneVal_actOne_of_eq hφs.symm)
    have hterm : ∀ g, M x (E.actOne ((R x).Γ g) v) = N w := fun g => by
      have hs := (R x).src_Γ g _ hvU
      have hgb : P (B.oneVal (E.actOne ((R x).Γ g) v)) ∈ X.PObj.boundary := by
        rw [E.P_actOne hs]; exact (tgt_mem_boundary_iff' X _).2 (hs.symm ▸ hvb)
      rw [hMN x hxb _ ⟨E.actOne_Γ_mem (R x) g hvU, hgb⟩,
        hN.map_μ _ v _ hs.symm hvb (E.oneVal_actOne_of_eq hs.symm), hNv]
    have := Fintype.ofFinite (X.Isotropy x)
    rw [avgNorm, finsum_congr hterm, finsum_eq_sum_of_fintype, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      inv_mul_cancel_left₀ (card_isotropy_pos X (x := x)).ne']
  rw [glueNorm, finsum_congr key, ← finsum_mul, β.sum_eq_one (mem_univ _), one_mul]

theorem hasLocalExtensions_of_isAuxNorm' {N : B.One → ℝ} (hN : E.IsAuxNorm N) :
    HasLocalExtensions X B N := fun _ _ =>
  ⟨univ, isOpen_univ, mem_univ _, N, hN.isAuxNorm.isLocalAuxNorm univ, fun _ _ => rfl⟩

theorem theorem_12_2_7_hyp_witness' (h : X.HasParacompactOrbitSpace) :
    ∃ N : B.One → ℝ, E.IsAuxNormOn X.PObj.boundary N ∧ HasLocalExtensions X B N := by
  obtain ⟨N, hN⟩ := E.theorem_12_2_2 h
  exact ⟨N, isAuxNormOn' hN _, hasLocalExtensions_of_isAuxNorm' hN⟩

theorem hasLocalExtensions_of_isTame' (hX : X.IsTame) {N : B.One → ℝ}
    (hN : E.IsAuxNormOn X.PObj.boundary N) : HasLocalExtensions X B N := fun _ hx =>
  exists_localExtension_of_isTame' hX hN.continuousOn
    (fun y hy => (hN.fiber y hy).isFiberSeminorm) hN.tendsto_zeroOne hx

end Ep

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @hasLocalExtensions_of_isTame'.{0}, @exists_localExtension_of_isTame'.{0, 0},
    @isLocalAuxNorm_retractNorm'.{0, 0}, @retractNorm_eq'.{0, 0}, @exists_retraction_boundary'.{0},
    @theorem_12_2_7_hyp'.{0}, @theorem_12_2_7_hyp_witness'.{0}, @isAuxNormOn'.{0},
    @hasLocalExtensions_of_isAuxNorm'.{0}, @tgt_mem_boundary_iff'.{0}, @isOpen_compl_boundary'.{0},
    @mono'.{0, 0}⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hT hX N hN
  have := B.paracompactSpace_pullback X.PMor X.src
  exact hB Obj Mor X W P B E hT hX N hN

#rt_check RoundTrip.V12_9.A_to_B [Polyfold.EpStrongBundle.theorem_12_2_7,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_localExtension_of_isTame,
  Polyfold.StrongBundle.isLocalAuxNorm_retractNorm,
  Polyfold.StrongBundle.retractNorm_eq,
  Polyfold.MPolyfold.exists_retraction_boundary,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp_witness,
  Polyfold.EpStrongBundle.IsAuxNorm.isAuxNormOn,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isAuxNorm,
  Polyfold.EpGroupoid.tgt_mem_boundary_iff,
  Polyfold.EpGroupoid.isOpen_compl_boundary,
  Polyfold.StrongBundle.IsLocalAuxNorm.mono]
#rt_check RoundTrip.V12_9.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_7,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_localExtension_of_isTame,
  Polyfold.StrongBundle.isLocalAuxNorm_retractNorm,
  Polyfold.StrongBundle.retractNorm_eq,
  Polyfold.MPolyfold.exists_retraction_boundary,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp_witness,
  Polyfold.EpStrongBundle.IsAuxNorm.isAuxNormOn,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isAuxNorm,
  Polyfold.EpGroupoid.tgt_mem_boundary_iff,
  Polyfold.EpGroupoid.isOpen_compl_boundary,
  Polyfold.StrongBundle.IsLocalAuxNorm.mono]
#rt_overlap RoundTrip.V12_9.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_7,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isTame,
  Polyfold.StrongBundle.exists_localExtension_of_isTame,
  Polyfold.StrongBundle.isLocalAuxNorm_retractNorm,
  Polyfold.StrongBundle.retractNorm_eq,
  Polyfold.MPolyfold.exists_retraction_boundary,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp,
  Polyfold.EpStrongBundle.theorem_12_2_7_hyp_witness,
  Polyfold.EpStrongBundle.IsAuxNorm.isAuxNormOn,
  Polyfold.EpStrongBundle.hasLocalExtensions_of_isAuxNorm,
  Polyfold.EpGroupoid.tgt_mem_boundary_iff,
  Polyfold.EpGroupoid.isOpen_compl_boundary,
  Polyfold.StrongBundle.IsLocalAuxNorm.mono]

end RoundTrip.V12_9
