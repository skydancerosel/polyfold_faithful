import Polyfold.Chapter6.ScContractible
import Polyfold.Chapter6.PathsInterval

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 263 and 272:
**Proposition 6.6.3 (1′) on `[0, 1]`**, the homotopies with fixed end points used in the proof of
Theorem 6.6.11 and in Theorem 6.6.13, with parameters in `[0, 1]²` (product M-polyfold with
boundary).  Gap G.65, rows V6.32, V6.48.

# Homotopies on `[0, 1]²` in a chart

## The text, paraphrased

(Proof of Theorem 6.6.11, p. 272) Two sc-smooth paths in `U` from `x₀` to `x₁` are sc-smoothly
homotopic in `U` with the end points fixed (from (1) of Proposition 6.6.3); the homotopy class of
a path `[0, 1] → X` is the class of Theorem 6.6.13.

## What is formalized

* `chartSegment φ R (σ, (y₀, y₁)) = φ⁻¹(r(φ(y₀) + σ (φ(y₁) − φ(y₀))))` for `σ ∈ [0, 1]`.
* `isScSmoothOn_chartSegment`: it is sc-smooth on `[0, 1] × (U × U)` (product M-polyfold with
  boundary `unitIntervalPolyfold.prod (PX.prod PX)`), `U = φ⁻¹(B_ε(u₀))` with `B_ε(u₀) ∩ C` in the
  domain of `r`.  In the charts `t` and `1 − t` of `[0, 1]` the representative is
  `(v, a, b) ↦ r(a + s(v)(b − a))`, `s(v) = v` or `1 − v`; the segment stays in `C` because the
  parameter stays in `[0, 1]`, which is why the parameter space is `[0, 1]` and not `ℝ` here.
* **`exists_isScHomotopyI`** (Proposition 6.6.3 (1′) on `[0, 1]`): every point `x` has, inside
  any neighbourhood `N`, an open neighbourhood `U` such that any two sc-smooth paths
  `γ₀, γ₁ : [0, 1] → U` with the same end points are joined by an sc-smooth `H : [0, 1]² → N`
  (`unitSquarePolyfold`) with `H(0, ·) = γ₀`, `H(1, ·) = γ₁`, `H(·, 0) = γ₀(0)`,
  `H(·, 1) = γ₀(1)`: exactly the hypotheses of `orTransportI_eq_of_homotopy`.
* **`proposition_6_6_3_interval`**: Proposition 6.6.3 as printed in 2021 with (1) (parameter
  `[0, 1]`), (1′) for paths on `[0, 1]` with homotopies on `[0, 1]²`, (2), and (3), (4) as in
  `proposition_6_6_3`, for one `U`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open MPolyfold UnitInterval

section Segment

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- The segment from `y₀` to `y₁` in the chart `φ`, retracted by `r`, at the time `σ ∈ [0, 1]`. -/
def chartSegment (φ : MChart X) (R : ScRetraction φ.model.E φ.model.C)
    (p : unitInterval × (X × X)) : X :=
  φ.symm (R (φ p.2.1 + (p.1 : ℝ) • (φ p.2.2 - φ p.2.1)))

/-- **The segment map is sc-smooth on `[0, 1] × (U × U)`** for `U = φ⁻¹(B_ε(u₀))` with
`B_ε(u₀) ∩ C` in the domain of the retraction. -/
theorem isScSmoothOn_chartSegment [ParacompactSpace (X × X)]
    [ParacompactSpace (unitInterval × (X × X))] {φ : MChart X} (hφ : PX.IsChart φ)
    {R : ScRetraction φ.model.E φ.model.C} (hR : R.retract = φ.model.O) {u₀ : φ.model.E 0}
    {ε : ℝ} (hεU : ∀ u ∈ Metric.ball u₀ ε, u ∈ φ.model.C → u ∈ R.U) :
    (unitIntervalPolyfold.prod (PX.prod PX)).IsScSmoothOn PX (chartSegment φ R)
      (univ ×ˢ ((φ.source ∩ φ ⁻¹' Metric.ball u₀ ε) ×ˢ (φ.source ∩ φ ⁻¹' Metric.ball u₀ ε))) := by
  classical
  set U : Set X := φ.source ∩ φ ⁻¹' Metric.ball u₀ ε with hUdef
  have hUo : IsOpen U :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball
  have hOR : ∀ {u}, u ∈ φ.model.O → u ∈ R.retract := fun hu => hR ▸ hu
  have hRO : ∀ {u}, u ∈ R.U → R u ∈ φ.model.O := fun hu => hR ▸ R.apply_mem_retract hu
  have hOC : ∀ {u}, u ∈ φ.model.O → u ∈ φ.model.C := fun hu =>
    R.relOpen.relOpen.elim fun _ h => (h.2 ▸ R.retract_subset (hOR hu)).2
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  -- the segment stays in `B_ε(u₀) ∩ C ⊆ dom r`
  have hseg : ∀ {a b}, a ∈ φ.model.O ∩ Metric.ball u₀ ε → b ∈ φ.model.O ∩ Metric.ball u₀ ε →
      ∀ {σ : ℝ}, σ ∈ Icc (0 : ℝ) 1 → a + σ • (b - a) ∈ R.U := fun ha hb σ hσ =>
    hεU _ ((convex_ball u₀ ε).add_smul_sub_mem ha.2 hb.2 hσ)
      (hCconv.add_smul_sub_mem (hOC ha.1) (hOC hb.1) hσ)
  have hφU : ∀ {y}, y ∈ U → φ y ∈ φ.model.O ∩ Metric.ball u₀ ε := fun hy =>
    ⟨φ.mapsTo_model _ hy.1, hy.2⟩
  have hσI : ∀ σ : unitInterval, (σ : ℝ) ∈ Icc (0 : ℝ) 1 := fun σ => σ.2
  have hVo : IsOpen (univ ×ˢ (U ×ˢ U) : Set (unitInterval × (X × X))) :=
    isOpen_univ.prod (hUo.prod hUo)
  have hmapsR : MapsTo (fun p : unitInterval × (X × X) =>
      φ p.2.1 + (p.1 : ℝ) • (φ p.2.2 - φ p.2.1)) (univ ×ˢ (U ×ˢ U)) R.U := fun p hp =>
    hseg (hφU hp.2.1) (hφU hp.2.2) (hσI p.1)
  -- continuity
  have hc : ContinuousOn (chartSegment φ R) (univ ×ˢ (U ×ˢ U)) := by
    have hφ1 : ContinuousOn (fun p : unitInterval × (X × X) => φ p.2.1) (univ ×ˢ (U ×ˢ U)) :=
      φ.continuousOn_toFun.comp (continuous_fst.comp continuous_snd).continuousOn
        fun p hp => hp.2.1.1
    have hφ2 : ContinuousOn (fun p : unitInterval × (X × X) => φ p.2.2) (univ ×ˢ (U ×ˢ U)) :=
      φ.continuousOn_toFun.comp (continuous_snd.comp continuous_snd).continuousOn
        fun p hp => hp.2.2.1
    have h1 : ContinuousOn (fun p : unitInterval × (X × X) =>
        φ p.2.1 + (p.1 : ℝ) • (φ p.2.2 - φ p.2.1)) (univ ×ˢ (U ×ˢ U)) :=
      hφ1.add ((continuous_subtype_val.comp continuous_fst).continuousOn.smul (hφ2.sub hφ1))
    exact φ.continuousOn_invFun.comp (R.isSc1.isSc0.continuousOn_base.comp h1 hmapsR)
      fun p hp => hRO (hmapsR hp)
  refine IsScSmoothOn.of_exists_charts hVo hc fun p hp => ?_
  -- one chart `χ` of `[0, 1]` around `p.1`, with `χ⁻¹(v) = s(v)` on `[0, 1)`
  have key : ∀ (χ : MChart unitInterval), unitIntervalPolyfold.IsChart χ →
      p.1 ∈ χ.source → ∀ (Rχ : ScRetraction χ.model.E χ.model.C), Rχ.retract = χ.model.O →
      ∀ s : χ.model.E 0 → ℝ, IsScSmooth (E := χ.model.E) (F := ScBanach.const ℝ) univ s →
      (∀ v ∈ χ.model.O, ((χ.symm v : unitInterval) : ℝ) = s v) →
      ∃ (ψ : MChart (unitInterval × (X × X))) (ψ' : MChart X) (V : Set (unitInterval × (X × X))),
        (unitIntervalPolyfold.prod (PX.prod PX)).IsChart ψ ∧ PX.IsChart ψ' ∧ IsOpen V ∧ p ∈ V ∧
        V ⊆ univ ×ˢ (U ×ˢ U) ∩ ψ.source ∧ MapsTo (chartSegment φ R) V ψ'.source ∧
        IsScSmoothRetractMap ψ.model.E ψ.model.C (ψ '' V) ψ'.model.E ψ'.model.C ψ'.model.O
          (ψ' ∘ chartSegment φ R ∘ ψ.symm) := by
    intro χ hχ hpχ Rχ hRχ s hs hχs
    set ψ := χ.prod (φ.prod φ) with hψdef
    set V : Set (unitInterval × (X × X)) := χ.source ×ˢ (U ×ˢ U) with hVdef
    refine ⟨ψ, φ, V, IsChart.prod hχ (IsChart.prod hφ hφ), hφ,
      χ.isOpen_source.prod (hUo.prod hUo), ⟨hpχ, hp.2⟩,
      fun q hq => ⟨⟨mem_univ _, hq.2⟩, hq.1, hq.2.1.1, hq.2.2.1⟩,
      fun q hq => φ.symm_mapsTo (hRO (hmapsR ⟨mem_univ _, hq.2⟩)), ?_⟩
    set Rb := R.restrict (W := Metric.ball u₀ ε) Metric.isOpen_ball with hRbdef
    set Rp := Rχ.prod (Rb.prod Rb) with hRpdef
    set O₁ : Set (ψ.model.E 0) :=
      χ.model.O ×ˢ ((φ.model.O ∩ Metric.ball u₀ ε) ×ˢ (φ.model.O ∩ Metric.ball u₀ ε))
      with hO₁def
    have hRb : Rb.retract = φ.model.O ∩ Metric.ball u₀ ε := by
      rw [hRbdef, ScRetraction.restrict_retract, hR]
    have hRp : Rp.retract = O₁ := by
      rw [hRpdef, ScRetraction.prod_retract, ScRetraction.prod_retract, hRb, hRχ]
    set F : ψ.model.E 0 → φ.model.E 0 := fun z => R (z.2.1 + s z.1 • (z.2.2 - z.2.1))
      with hFdef
    have hsI : ∀ v ∈ χ.model.O, s v ∈ Icc (0 : ℝ) 1 := fun v hv => hχs v hv ▸ hσI _
    have hFeq : ∀ z ∈ O₁, (φ ∘ chartSegment φ R ∘ ψ.symm) z = F z := fun z hz => by
      change φ (φ.symm (R (φ (φ.symm z.2.1) +
        ((χ.symm z.1 : unitInterval) : ℝ) • (φ (φ.symm z.2.2) - φ (φ.symm z.2.1))))) = F z
      rw [φ.apply_symm_apply hz.2.1.1, φ.apply_symm_apply hz.2.2.1, hχs _ hz.1,
        φ.apply_symm_apply (hRO (hseg hz.2.1 hz.2.2 (hsI _ hz.1)))]
    have hbig : IsScSmoothRetractMap ψ.model.E ψ.model.C O₁ φ.model.E φ.model.C φ.model.O
        (φ ∘ chartSegment φ R ∘ ψ.symm) := by
      refine (isScSmoothRetractMap_iff_exists ⟨Rp, hRp⟩).2 ⟨fun z hz => ?_, Rp, hRp, ?_⟩
      · rw [hFeq z hz]
        exact hRO (hseg hz.2.1 hz.2.2 (hsI _ hz.1))
      · have hU := Rp.isScDomain
        have hRpO : ∀ z ∈ Rp.U, Rp z ∈ O₁ := fun z hz => hRp ▸ Rp.apply_mem_retract hz
        have hid := isScSmooth_id hU
        have h2 := hid.snd hU
        have ha : IsScSmooth (F := φ.model.E) Rp.U fun z => R z.2.1 :=
          IsScSmooth.comp hU R.isScDomain R.isScSmooth (h2.fst hU) fun z hz => hz.2.1.1
        have hb : IsScSmooth (F := φ.model.E) Rp.U fun z => R z.2.2 :=
          IsScSmooth.comp hU R.isScDomain R.isScSmooth (h2.snd hU) fun z hz => hz.2.2.1
        have hsz : IsScSmooth (F := ScBanach.const ℝ) Rp.U fun z => s (Rχ z.1) :=
          IsScSmooth.comp hU (isScDomain_univ _) hs
            (IsScSmooth.comp hU Rχ.isScDomain Rχ.isScSmooth (hid.fst hU) fun z hz => hz.1)
            (mapsTo_univ _ _)
        have h4 : IsScSmooth (F := φ.model.E) Rp.U
            fun z => R z.2.1 + s (Rχ z.1) • (R z.2.2 - R z.2.1) :=
          ha.add hU (hsz.smul hU (hb.sub hU ha))
        have h5 : IsScSmooth (F := φ.model.E) Rp.U fun z => F (Rp z) :=
          IsScSmooth.comp hU R.isScDomain R.isScSmooth h4 fun z hz =>
            hseg (hRpO z hz).2.1 (hRpO z hz).2.2 (hsI _ (hRpO z hz).1)
        exact h5.congr hU fun z hz => (hFeq (Rp z) (hRpO z hz)).symm
    refine hbig.mono_source ⟨Rp, hRp⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨χ.mapsTo_model _ hq.1, hφU hq.2.1, hφU hq.2.2⟩
  have hU1 := isScDomain_univ (rnSc 1)
  rcases mem_leftChart_or_rightChart p.1 with h | h
  · exact key leftChart isChart_leftChart h (ScRetraction.id isRelOpen_modelO) (image_id _)
      (fun v => v 0)
      (IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU1
        (contDiff_apply ℝ ℝ (0 : Fin 1)).contDiffOn)
      fun v hv => projIcc_val_of_mem hv
  · exact key rightChart isChart_rightChart h (ScRetraction.id isRelOpen_modelO) (image_id _)
      (fun v => 1 - v 0)
      (IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU1
        (contDiff_const.sub (contDiff_apply ℝ ℝ (0 : Fin 1))).contDiffOn)
      fun v hv => projIcc_one_sub_val_of_mem hv

/-- **Proposition 6.6.3 (1′) on `[0, 1]`**: every point `x` has, inside any neighbourhood `N`, an
open neighbourhood `U` such that two sc-smooth paths `γ₀, γ₁ : [0, 1] → U` with the same end
points are joined by an sc-smooth homotopy `H : [0, 1]² → N` with the end points fixed:
`H(τ, t) = φ⁻¹(r(φ(γ₀(t)) + τ (φ(γ₁(t)) − φ(γ₀(t)))))` in a chart around `x`. -/
theorem exists_isScHomotopyI (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧
      ∀ γ₀ γ₁ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap PX γ₀ →
        unitIntervalPolyfold.IsScSmoothMap PX γ₁ → (∀ t, γ₀ t ∈ U) → (∀ t, γ₁ t ∈ U) →
        γ₀ 0 = γ₁ 0 → γ₀ 1 = γ₁ 1 →
        ∃ H : unitInterval × unitInterval → X, unitSquarePolyfold.IsScSmoothMap PX H ∧
          (∀ t, H (0, t) = γ₀ t) ∧ (∀ t, H (1, t) = γ₁ t) ∧ (∀ τ, H (τ, 0) = γ₀ 0) ∧
          (∀ τ, H (τ, 1) = γ₀ 1) ∧ ∀ q, H q ∈ N := by
  classical
  let _ := MPolyfold.paracompactSpace_prod PX PX
  let _ := MPolyfold.paracompactSpace_prod unitIntervalPolyfold (PX.prod PX)
  obtain ⟨φ, hφ, hxφ⟩ := PX.exists_isChart_mem_source x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set u₀ := φ x with hu₀def
  have hOR : ∀ {u}, u ∈ φ.model.O → u ∈ R.retract := fun hu => hR ▸ hu
  have hRO : ∀ {u}, u ∈ R.U → R u ∈ φ.model.O := fun hu => hR ▸ R.apply_mem_retract hu
  have hu₀O : u₀ ∈ φ.model.O := φ.mapsTo_model _ hxφ
  have hu₀U : u₀ ∈ R.U := R.retract_subset (hOR hu₀O)
  have hRu₀ : R u₀ = u₀ := R.apply_eq_self_of_mem_retract (hOR hu₀O)
  obtain ⟨O', hO'o, hO'⟩ := R.relOpen.relOpen
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hu₀U
    rw [hO'] at this
    exact this.1)
  obtain ⟨N₀, hN₀N, hN₀o, hxN₀⟩ := mem_nhds_iff.1 hN
  have hcont : ContinuousWithinAt (fun w => φ.symm (R w)) R.U u₀ :=
    ((φ.continuousOn_invFun (R u₀) (hRO hu₀U)).comp
      (R.isSc1.isSc0.continuousOn_base u₀ hu₀U) fun w hw => hRO hw)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.1 (hcont.preimage_mem_nhdsWithin
    (by
      rw [hRu₀, show φ.symm u₀ = x from φ.symm_apply_apply hxφ]
      exact hN₀o.mem_nhds hxN₀))
  set ε' := min δ ε with hε'def
  have hε' : 0 < ε' := lt_min hδ hε
  have hεU : ∀ u ∈ Metric.ball u₀ ε', u ∈ φ.model.C → u ∈ R.U := fun u hu hC => by
    rw [hO']; exact ⟨hδO' (Metric.ball_subset_ball (min_le_left _ _) hu), hC⟩
  set U : Set X := φ.source ∩ φ ⁻¹' Metric.ball u₀ ε' with hUdef
  have hUo : IsOpen U :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball
  have hOC : ∀ {u}, u ∈ φ.model.O → u ∈ φ.model.C := fun hu =>
    (hO' ▸ R.retract_subset (hOR hu)).2
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  have hseg : ∀ {y₀ y₁}, y₀ ∈ U → y₁ ∈ U → ∀ {σ : ℝ}, σ ∈ Icc (0 : ℝ) 1 →
      φ.symm (R (φ y₀ + σ • (φ y₁ - φ y₀))) ∈ N₀ := fun h₀ h₁ σ hσ => by
    have hb := (convex_ball u₀ ε').add_smul_sub_mem h₀.2 h₁.2 hσ
    exact hεN ⟨Metric.ball_subset_ball (min_le_right _ _) hb, hεU _ hb
      (hCconv.add_smul_sub_mem (hOC (φ.mapsTo_model _ h₀.1)) (hOC (φ.mapsTo_model _ h₁.1)) hσ)⟩
  have hfix : ∀ {y}, y ∈ U → φ.symm (R (φ y)) = y := fun hy => by
    rw [R.apply_eq_self_of_mem_retract (hOR (φ.mapsTo_model _ hy.1)), φ.symm_apply_apply hy.1]
  have hxU : x ∈ U := ⟨hxφ, Metric.mem_ball_self hε'⟩
  have hUN : U ⊆ N := fun y hy => by
    have h := hseg hy hy (σ := 0) ⟨le_rfl, zero_le_one⟩
    rw [zero_smul, add_zero, hfix hy] at h
    exact hN₀N h
  refine ⟨U, hUo, hxU, hUN, fun γ₀ γ₁ hγ₀ hγ₁ hγ₀U hγ₁U h0 h1 => ?_⟩
  set j : unitInterval × unitInterval → unitInterval × (X × X) :=
    fun q => (q.1, (γ₀ q.2, γ₁ q.2)) with hjdef
  have hj : unitSquarePolyfold.IsScSmoothMap (unitIntervalPolyfold.prod (PX.prod PX)) j :=
    IsScSmoothOn.prodMk (isScSmoothMap_fst unitIntervalPolyfold unitIntervalPolyfold)
      (IsScSmoothOn.prodMk (hγ₀.comp (isScSmoothMap_snd unitIntervalPolyfold unitIntervalPolyfold))
        (hγ₁.comp (isScSmoothMap_snd unitIntervalPolyfold unitIntervalPolyfold)))
  have hS := isScSmoothOn_chartSegment (PX := PX) hφ hR hεU
  have hval : ∀ q : unitInterval × unitInterval, (chartSegment φ R ∘ j) q =
      φ.symm (R (φ (γ₀ q.2) + (q.1 : ℝ) • (φ (γ₁ q.2) - φ (γ₀ q.2)))) := fun _ => rfl
  refine ⟨chartSegment φ R ∘ j, hS.comp hj fun q _ => ⟨mem_univ _, hγ₀U _, hγ₁U _⟩,
    fun t => ?_, fun t => ?_, fun τ => ?_, fun τ => ?_, fun q => ?_⟩
  · rw [hval, Set.Icc.coe_zero, zero_smul, add_zero, hfix (hγ₀U t)]
  · rw [hval, Set.Icc.coe_one, one_smul, add_sub_cancel, hfix (hγ₁U t)]
  · rw [hval, ← h0, sub_self, smul_zero, add_zero, hfix (hγ₀U 0)]
  · rw [hval, ← h1, sub_self, smul_zero, add_zero, hfix (hγ₀U 1)]
  · exact hN₀N (hseg (hγ₀U _) (hγ₁U _) q.1.2)

end Segment

/-! ### Proposition 6.6.3 with (1) and (1′) on `[0, 1]` -/

section Proposition

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Proposition 6.6.3 (2021 p. 263) with parameters in `[0, 1]`**: every smooth point `x` has
open neighbourhoods `U′ ⊆ U ⊆ W` in the domain of one chart `c` of the atlas with (1) `U′` is
sc-smoothly contractible in `U` to `x` (parameter `[0, 1]`), (1′) any two sc-smooth paths
`[0, 1] → U` with the same end points are joined by an sc-smooth homotopy `[0, 1]² → W` with the
end points fixed, (2) `{y ∈ cl(U) | f(y) = 0}` is compact, (3) sections along families in `W`
(as in `proposition_6_6_3`). -/
theorem proposition_6_6_3_interval [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (unitInterval × X)] (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSection f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (U' U W : Set X) (c : StrongBundleChart PX P) (H : unitInterval × X → X),
      IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ IsScContraction PX U' U x H ∧
      IsOpen U ∧ IsOpen W ∧ x ∈ U ∧ U ⊆ W ∧ c ∈ B.atlas.charts ∧ W ⊆ c.φ.source ∧
      (∀ γ₀ γ₁ : unitInterval → X, unitIntervalPolyfold.IsScSmoothMap PX γ₀ →
        unitIntervalPolyfold.IsScSmoothMap PX γ₁ → (∀ t, γ₀ t ∈ U) → (∀ t, γ₁ t ∈ U) →
        γ₀ 0 = γ₁ 0 → γ₀ 1 = γ₁ 1 →
        ∃ Φ : unitInterval × unitInterval → X, unitSquarePolyfold.IsScSmoothMap PX Φ ∧
          (∀ t, Φ (0, t) = γ₀ t) ∧ (∀ t, Φ (1, t) = γ₁ t) ∧ (∀ τ, Φ (τ, 0) = γ₀ 0) ∧
          (∀ τ, Φ (τ, 1) = γ₀ 1) ∧ ∀ q, Φ q ∈ W) ∧
      IsCompact {y ∈ closure U | IsZeroAt P f y} ∧
      (∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
        (Φ : (Fin n → ℝ) → X), (rnPolyfold n).IsScSmoothMap PX Φ →
        (∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ W) →
        ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
          (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) ∧
          ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ q' ∈ Icc (0 : Fin n → ℝ) 1, Φ q = Φ q' →
            ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2) := by
  obtain ⟨U, W, c, hUo, hWo, hxU, hUW, hc, hWc, -, h2, h3, -⟩ := proposition_6_6_3 hbump hf hx
  obtain ⟨U₁, hU₁o, hxU₁, hU₁W, hU₁⟩ := exists_isScHomotopyI (PX := PX) x (hWo.mem_nhds (hUW hxU))
  set U₂ := U ∩ U₁ with hU₂def
  have hU₂o : IsOpen U₂ := hUo.inter hU₁o
  have hxU₂ : x ∈ U₂ := ⟨hxU, hxU₁⟩
  obtain ⟨U', hU'o, hxU', hU'U, H, hH⟩ := exists_isScContraction hx (hU₂o.mem_nhds hxU₂)
  refine ⟨U', U₂, W, c, H, hU'o, hxU', hU'U, hH, hU₂o, hWo, hxU₂,
    inter_subset_left.trans hUW, hc, hWc,
    fun γ₀ γ₁ hγ₀ hγ₁ hγ₀U hγ₁U h0 h1 =>
      hU₁ γ₀ γ₁ hγ₀ hγ₁ (fun t => (hγ₀U t).2) (fun t => (hγ₁U t).2) h0 h1, ?_, h3⟩
  refine h2.of_isClosed_subset (isClosed_closure.inter (isClosed_solutionSet hf.isScSmooth)) ?_
  rintro y ⟨hy, hy0⟩
  exact ⟨closure_mono inter_subset_left hy, hy0⟩

end Proposition

end Polyfold
