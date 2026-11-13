import Polyfold.Chapter6.OrientableNbhd
import Polyfold.Chapter6.GapP1_UnitIntervalSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 263:
**Proposition 6.6.3 (1)**, "`U′ ⊂ U` is sc-smoothly contractible in `U` to the point `x`"
(2017 Proposition 6.12 (1); preprint Proposition 6.28 (1): "`U` is sc-smoothly contractible").
Gap G.61, row V6.32.

# Sc-smooth contractibility (Proposition 6.6.3 (1))

## The text, paraphrased

(2021, p. 263) Every smooth point `x` has two open neighbourhoods `U` and `U′` with (1) `U′ ⊂ U`
is sc-smoothly contractible in `U` to `x`, and (2)–(4).  *Proof*: in strong bundle coordinates
`x = 0`, `O = r(V)`; for a convex open `V′ ∋ 0` in `V`, `r̂(t, y) = r(t y)` retracts
`O′ = r(V′)` to `x` while staying in `O`; shrinking keeps this.

## The reading

The 2021 text asks for a contraction of the smaller `U′` inside `U`, not of `U` in itself (the
preprint's reading, recorded in `OrientableNbhd.lean`).  That form holds, for every open
neighbourhood `U` of `x`: in a chart around `x` with retraction `r` and `u₀ = φ(x)` take
`U′ = φ⁻¹(B_ε(u₀))` with `B_ε(u₀) ∩ C` in the domain of `r` and `φ⁻¹(r(B_ε(u₀) ∩ C)) ⊆ U`
(continuity of `r` and `φ⁻¹` at level `0`); then
`H(t, y) = φ⁻¹(r(u₀ + t (φ(y) − u₀)))` is the contraction.  The text's segment `t y` from `0`
is the segment from `u₀ = φ(x)`; the text's `r̂(t, y) = r(t y)` restricted to `O′` is `H`.
Smoothness of `x` is used: the constant `u₀` must be a smooth point of `E` for `H` to be
sc-smooth.

## What is formalized

* `IsScContraction PX U′ U x H`: `H : [0, 1] × X → X` is sc-smooth on `[0, 1] × U′` (product
  M-polyfold `unitIntervalPolyfold.prod PX`), `H([0, 1] × U′) ⊆ U`, `H(0, ·) = x`,
  `H(1, ·) = id` on `U′`, and `H(t, x) = x`.  `IsScContractionRn` is the same with parameter
  `t ∈ ℝ` (`rnPolyfold 1`, decision D2), with `H(t, ·) = x` for `t ≤ 0` and `= id` for `t ≥ 1`.
* `exists_isScContractionRn`: for smooth `x` and any neighbourhood `N` of `x`, an open `U′ ∋ x`,
  `U′ ⊆ N`, contractible in `N` to `x` (parameter in `ℝ`, reparametrized by
  `Real.smoothTransition`).
* **`exists_isScContraction`**: the same with parameter in `[0, 1]` (composition with the
  sc-smooth inclusion `[0, 1] → ℝ`, `isScSmoothMap_unitInterval_val`).
* **`proposition_6_6_3_one`** (Proposition 6.6.3 as printed in 2021, with (1)): the
  neighbourhood `U` of `proposition_6_6_3` with (2)–(4), together with an open `U′ ∋ x` that is
  sc-smoothly contractible in `U` to `x`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open MPolyfold

section Contraction

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

variable (PX) in
/-- **`U′` is sc-smoothly contractible in `U` to `x`** (Proposition 6.6.3 (1), 2021 p. 263),
with parameter `t ∈ ℝ`: `H : ℝ × X → X` sc-smooth on `ℝ × U′`, with values in `U`, `H(t, y) = x`
for `t ≤ 0`, `H(t, y) = y` for `t ≥ 1`, and `H(t, x) = x`. -/
structure IsScContractionRn [ParacompactSpace ((Fin 1 → ℝ) × X)] (U' U : Set X) (x : X)
    (H : (Fin 1 → ℝ) × X → X) : Prop where
  isScSmoothOn : ((rnPolyfold 1).prod PX).IsScSmoothOn PX H (univ ×ˢ U')
  mapsTo : ∀ t, ∀ y ∈ U', H (t, y) ∈ U
  zero : ∀ t : ℝ, t ≤ 0 → ∀ y ∈ U', H (pt1 t, y) = x
  one : ∀ t : ℝ, 1 ≤ t → ∀ y ∈ U', H (pt1 t, y) = y
  fix : ∀ t, H (t, x) = x

variable (PX) in
/-- **`U′` is sc-smoothly contractible in `U` to `x`** (Proposition 6.6.3 (1), 2021 p. 263):
`H : [0, 1] × X → X` sc-smooth on `[0, 1] × U′` (product M-polyfold), with values in `U`,
`H(0, ·) = x` and `H(1, ·) = id` on `U′`, and `H(t, x) = x`. -/
structure IsScContraction [ParacompactSpace (unitInterval × X)] (U' U : Set X) (x : X)
    (H : unitInterval × X → X) : Prop where
  isScSmoothOn : (unitIntervalPolyfold.prod PX).IsScSmoothOn PX H (univ ×ˢ U')
  mapsTo : ∀ t, ∀ y ∈ U', H (t, y) ∈ U
  zero : ∀ y ∈ U', H (0, y) = x
  one : ∀ y ∈ U', H (1, y) = y
  fix : ∀ t, H (t, x) = x

/-- **Proposition 6.6.3 (1), parameter in `ℝ`**: every smooth `x` has, inside any neighbourhood
`N`, an open neighbourhood `U′` that is sc-smoothly contractible in `N` to `x`:
`H(t, y) = φ⁻¹(r(u₀ + ρ(t)(φ(y) − u₀)))` in a chart, `ρ = Real.smoothTransition`. -/
theorem exists_isScContractionRn [ParacompactSpace ((Fin 1 → ℝ) × X)] {x : X}
    (hx : x ∈ PX.smoothSet) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ N ∧ ∃ H, IsScContractionRn PX U' N x H := by
  classical
  obtain ⟨φ, hφ, hxφ⟩ := PX.exists_isChart_mem_source x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set u₀ := φ x with hu₀def
  have hOR : ∀ {u}, u ∈ φ.model.O → u ∈ R.retract := fun hu => hR ▸ hu
  have hRO : ∀ {u}, u ∈ R.U → R u ∈ φ.model.O := fun hu => hR ▸ R.apply_mem_retract hu
  have hu₀O : u₀ ∈ φ.model.O := φ.mapsTo_model _ hxφ
  have hu₀U : u₀ ∈ R.U := R.retract_subset (hOR hu₀O)
  have hRu₀ : R u₀ = u₀ := R.apply_eq_self_of_mem_retract (hOR hu₀O)
  have hu₀sm : u₀ ∈ φ.model.E.smooth :=
    φ.model.E.mem_smooth_iff.2 fun m => (PX.mem_levelSet_iff hφ hxφ).1 (mem_iInter.1 hx m)
  obtain ⟨O', hO'o, hO'⟩ := R.relOpen.relOpen
  have hUC : R.U ⊆ φ.model.C := by rw [hO']; exact inter_subset_right
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hu₀U
    rw [hO'] at this
    exact this.1)
  -- an open `N₀ ∋ x` inside `N` and the chart domain
  obtain ⟨N₀, hN₀N, hN₀o, hxN₀⟩ := mem_nhds_iff.1 hN
  -- `φ⁻¹ ∘ r` maps `B_ε(u₀) ∩ dom r` into `N₀ ∩ dom φ`
  have hRc : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  have hcont : ContinuousWithinAt (fun w => φ.symm (R w)) R.U u₀ :=
    ((φ.continuousOn_invFun (R u₀) (hRO hu₀U)).comp (hRc u₀ hu₀U) fun w hw => hRO hw)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.1 (hcont.preimage_mem_nhdsWithin
    (by
      rw [hRu₀, show φ.symm u₀ = x from φ.symm_apply_apply hxφ]
      exact hN₀o.mem_nhds hxN₀))
  set ε' := min δ ε with hε'def
  have hε' : 0 < ε' := lt_min hδ hε
  set U' : Set X := φ.source ∩ φ ⁻¹' Metric.ball u₀ ε' with hU'def
  have hU'o : IsOpen U' :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball
  have hxU' : x ∈ U' := ⟨hxφ, Metric.mem_ball_self hε'⟩
  set ρ : ℝ → ℝ := Real.smoothTransition with hρdef
  have hρI : ∀ s : ℝ, ρ s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- the segment from `u₀` lies in `B_ε'(u₀) ∩ C ⊆ dom r`
  have hseg : ∀ {u}, u ∈ φ.model.O → u ∈ Metric.ball u₀ ε' → ∀ s : ℝ,
      u₀ + ρ s • (u - u₀) ∈ Metric.ball u₀ ε' ∩ R.U := fun {u} hu hub s => by
    have hb : u₀ + ρ s • (u - u₀) ∈ Metric.ball u₀ ε' :=
      (convex_ball u₀ ε').add_smul_sub_mem (Metric.mem_ball_self hε') hub (hρI s)
    refine ⟨hb, ?_⟩
    rw [hO']
    exact ⟨hδO' (Metric.ball_subset_ball (min_le_left _ _) hb),
      hCconv.add_smul_sub_mem (hUC hu₀U) (hUC (R.retract_subset (hOR hu))) (hρI s)⟩
  have hsegN : ∀ {w}, w ∈ Metric.ball u₀ ε' ∩ R.U → φ.symm (R w) ∈ N₀ := fun hw =>
    hεN ⟨Metric.ball_subset_ball (min_le_right _ _) hw.1, hw.2⟩
  have hφU' : ∀ {y}, y ∈ U' → φ y ∈ φ.model.O := fun hy => φ.mapsTo_model _ hy.1
  have hU'N : U' ⊆ N := fun y hy => by
    have h := hsegN (hseg (hφU' hy) hy.2 1)
    rw [hρdef, Real.smoothTransition.one, one_smul, add_sub_cancel,
      R.apply_eq_self_of_mem_retract (hOR (hφU' hy)), φ.symm_apply_apply hy.1] at h
    exact hN₀N h
  -- the contraction
  set H : (Fin 1 → ℝ) × X → X := fun p => φ.symm (R (u₀ + ρ (p.1 0) • (φ p.2 - u₀)))
    with hHdef
  refine ⟨U', hU'o, hxU', hU'N, H, ⟨?_, fun t y hy => hN₀N (hsegN (hseg (hφU' hy) hy.2 _)),
    fun t ht y _ => ?_, fun t ht y hy => ?_, fun t => ?_⟩⟩
  · -- sc-smoothness, in the product chart `id × φ`
    have hVo : IsOpen (univ ×ˢ U' : Set ((Fin 1 → ℝ) × X)) := isOpen_univ.prod hU'o
    have hHc : ContinuousOn H (univ ×ˢ U') := by
      have h1 : ContinuousOn (fun p : (Fin 1 → ℝ) × X => u₀ + ρ (p.1 0) • (φ p.2 - u₀))
          (univ ×ˢ U') :=
        continuousOn_const.add (((Real.smoothTransition.continuous.comp
          ((continuous_apply 0).comp continuous_fst)).continuousOn).smul
          ((φ.continuousOn_toFun.comp continuous_snd.continuousOn
            fun p hp => hp.2.1).sub continuousOn_const))
      have hmaps : MapsTo (fun p : (Fin 1 → ℝ) × X => u₀ + ρ (p.1 0) • (φ p.2 - u₀))
          (univ ×ˢ U') R.U := fun p hp => (hseg (hφU' hp.2) hp.2.2 _).2
      exact φ.continuousOn_invFun.comp (hRc.comp h1 hmaps) fun p hp => hRO (hmaps hp)
    refine IsScSmoothOn.of_exists_charts hVo hHc fun p hp => ?_
    refine ⟨(rnChart 1 0).prod φ, φ, univ ×ˢ U', IsChart.prod (isChart_rnChart 0) hφ, hφ, hVo,
      hp, fun q hq => ⟨hq, mem_univ _, hq.2.1⟩,
      fun q hq => φ.symm_mapsTo (hRO (hseg (hφU' hq.2) hq.2.2 _).2), ?_⟩
    -- the representative on the retract `ℝ × (O ∩ B_ε'(u₀))`
    set Rp := (ScRetraction.id (rn_relOpen_univ 1)).prod (R.restrict Metric.isOpen_ball)
      with hRpdef
    have hRp : Rp.retract = univ ×ˢ (φ.model.O ∩ Metric.ball u₀ ε') := by
      rw [hRpdef, ScRetraction.prod_retract, ScRetraction.restrict_retract, hR]
      congr 1
      exact image_id _
    set F : ((rnChart 1 0).prod φ).model.E 0 → φ.model.E 0 :=
      fun z => R (u₀ + ρ (z.1 0) • (z.2 - u₀)) with hFdef
    have hFeq : ∀ z : ((rnChart 1 0).prod φ).model.E 0, z.2 ∈ φ.model.O ∩ Metric.ball u₀ ε' →
        (φ ∘ H ∘ ((rnChart 1 0).prod φ).symm) z = F z := fun z hz => by
      change φ (φ.symm (R (u₀ + ρ ((z.1 + 0) 0) • (φ (φ.symm z.2) - u₀)))) = F z
      rw [add_zero, φ.apply_symm_apply hz.1,
        φ.apply_symm_apply (hRO (hseg hz.1 hz.2 _).2)]
    have hbig : IsScSmoothRetractMap ((rnChart 1 0).prod φ).model.E ((rnChart 1 0).prod φ).model.C
        (univ ×ˢ (φ.model.O ∩ Metric.ball u₀ ε')) φ.model.E φ.model.C φ.model.O
        (φ ∘ H ∘ ((rnChart 1 0).prod φ).symm) := by
      refine (isScSmoothRetractMap_iff_exists ⟨Rp, hRp⟩).2 ⟨fun z hz => ?_, Rp, hRp, ?_⟩
      · rw [hFeq z hz.2]
        exact hRO (hseg hz.2.1 hz.2.2 _).2
      · have hU := Rp.isScDomain
        have hz2 : ∀ z ∈ Rp.U, R z.2 ∈ φ.model.O ∩ Metric.ball u₀ ε' := fun z hz =>
          ⟨hRO hz.2.1, hz.2.2⟩
        have hid := isScSmooth_id hU
        have h1 : IsScSmooth (F := φ.model.E) Rp.U fun z => R z.2 :=
          IsScSmooth.comp hU R.isScDomain R.isScSmooth (hid.snd hU) fun z hz => hz.2.1
        have hρ1 : IsScSmooth (E := rnSc 1) (F := ScBanach.const ℝ) univ
            fun t : Fin 1 → ℝ => ρ (t 0) :=
          IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) (isScDomain_univ _)
            ((Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).contDiffOn)
        have h2 : IsScSmooth (F := ScBanach.const ℝ) Rp.U fun z => ρ (z.1 0) :=
          IsScSmooth.comp hU (isScDomain_univ _) hρ1 (hid.fst hU) (mapsTo_univ _ _)
        have h3 : IsScSmooth (F := φ.model.E) Rp.U fun _ => u₀ :=
          isScSmooth_const_of_mem_smooth hU hu₀sm
        have h4 : IsScSmooth (F := φ.model.E) Rp.U fun z => u₀ + ρ (z.1 0) • (R z.2 - u₀) :=
          h3.add hU (h2.smul hU (h1.sub hU h3))
        have h5 : IsScSmooth (F := φ.model.E) Rp.U fun z => F (Rp z) :=
          IsScSmooth.comp hU R.isScDomain R.isScSmooth h4 fun z hz =>
            (hseg (hz2 z hz).1 (hz2 z hz).2 _).2
        refine h5.congr hU fun z hz => ?_
        exact (hFeq (Rp z) (hz2 z hz)).symm
    refine hbig.mono_source ⟨Rp, hRp⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, φ.mapsTo_model _ hq.2.1, hq.2.2⟩
  · change φ.symm (R (u₀ + ρ t • (φ y - u₀))) = x
    rw [hρdef, Real.smoothTransition.zero_of_nonpos ht, zero_smul, add_zero, hRu₀,
      φ.symm_apply_apply hxφ]
  · change φ.symm (R (u₀ + ρ t • (φ y - u₀))) = y
    rw [hρdef, Real.smoothTransition.one_of_one_le ht, one_smul, add_sub_cancel,
      R.apply_eq_self_of_mem_retract (hOR (hφU' hy)), φ.symm_apply_apply hy.1]
  · change φ.symm (R (u₀ + ρ (t 0) • (φ x - u₀))) = x
    rw [← hu₀def, sub_self, smul_zero, add_zero, hRu₀, φ.symm_apply_apply hxφ]

/-- **Proposition 6.6.3 (1), parameter in `[0, 1]`** (2021 p. 263): every smooth `x` has, inside
any neighbourhood `N`, an open neighbourhood `U′` that is sc-smoothly contractible in `N` to `x`
(`exists_isScContractionRn` composed with the sc-smooth inclusion `[0, 1] → ℝ`). -/
theorem exists_isScContraction [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (unitInterval × X)] {x : X} (hx : x ∈ PX.smoothSet) {N : Set X}
    (hN : N ∈ 𝓝 x) :
    ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ N ∧ ∃ H, IsScContraction PX U' N x H := by
  obtain ⟨U', hU'o, hxU', hU'N, H, hH⟩ := exists_isScContractionRn hx hN
  set j : unitInterval × X → (Fin 1 → ℝ) × X := fun p => (fun _ => (p.1 : ℝ), p.2) with hjdef
  have hVo : IsOpen (univ ×ˢ U' : Set (unitInterval × X)) := isOpen_univ.prod hU'o
  have hj : (unitIntervalPolyfold.prod PX).IsScSmoothOn ((rnPolyfold 1).prod PX) j
      (univ ×ˢ U') :=
    IsScSmoothOn.prodMk
      ((isScSmoothMap_unitInterval_val.comp
        (isScSmoothMap_fst unitIntervalPolyfold PX)).mono hVo (subset_univ _))
      ((isScSmoothMap_snd unitIntervalPolyfold PX).mono hVo (subset_univ _))
  refine ⟨U', hU'o, hxU', hU'N, H ∘ j,
    ⟨hH.isScSmoothOn.comp hj fun p hp => ⟨mem_univ _, hp.2⟩, fun t y hy => hH.mapsTo _ y hy,
      fun y hy => ?_, fun y hy => ?_, fun t => hH.fix _⟩⟩
  · exact hH.zero ((0 : unitInterval) : ℝ) (le_of_eq Set.Icc.coe_zero) y hy
  · exact hH.one ((1 : unitInterval) : ℝ) (ge_of_eq Set.Icc.coe_one) y hy

end Contraction

/-! ### Proposition 6.6.3 as printed in 2021 -/

section Proposition

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Proposition 6.6.3, 2021 p. 263, with (1)**: every smooth point `x` has open
neighbourhoods `U′ ⊆ U ⊆ W` with (1) `U′` is sc-smoothly contractible in `U` to `x`
(parameter `[0, 1]`), (1′) any two sc-smooth paths in `U` with the same end points are
sc-smoothly homotopic in `W` with end points fixed, (2) `{y ∈ cl(U) | f(y) = 0}` is compact,
(3) and (4) as in `proposition_6_6_3` (sections along families in `W`, sc⁺-sections through
smooth fibre points), all in the domain of one chart `c` of the atlas. -/
theorem proposition_6_6_3_one [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (unitInterval × X)] (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSection f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (U' U W : Set X) (c : StrongBundleChart PX P) (H : unitInterval × X → X),
      IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ IsScContraction PX U' U x H ∧
      IsOpen U ∧ IsOpen W ∧ x ∈ U ∧ U ⊆ W ∧
      c ∈ B.atlas.charts ∧ W ⊆ c.φ.source ∧
      (∀ γ₀ γ₁ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ₀ →
        (rnPolyfold 1).IsScSmoothMap PX γ₁ → (∀ t ∈ Icc (0 : ℝ) 1, γ₀ (pt1 t) ∈ U) →
        (∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U) → γ₀ (pt1 0) = γ₁ (pt1 0) →
        γ₀ (pt1 1) = γ₁ (pt1 1) →
        ∃ Φ, IsScHomotopyRel PX γ₀ γ₁ Φ ∧ ∀ τ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (pt2 τ t) ∈ W) ∧
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
            ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2) ∧
      ∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))],
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).HasScPlusSectionsThrough := by
  obtain ⟨U, W, c, hUo, hWo, hxU, hUW, hc, hWc, h1', h2, h3, h4⟩ :=
    proposition_6_6_3 hbump hf hx
  obtain ⟨U', hU'o, hxU', hU'U, H, hH⟩ := exists_isScContraction hx (hUo.mem_nhds hxU)
  exact ⟨U', U, W, c, H, hU'o, hxU', hU'U, hH, hUo, hWo, hxU, hUW, hc, hWc, h1', h2, h3, h4⟩

end Proposition

end Polyfold
