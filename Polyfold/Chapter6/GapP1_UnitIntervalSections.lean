import Polyfold.Chapter3.UnitIntervalPolyfold
import Polyfold.Chapter6.OrientableNbhd

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6,
**Proposition 6.6.3 (3) and (4)** (p. 263; preprint Proposition 6.28) **on `[0, 1]`**.
Gap G.65, row V6.32.

# sc⁺-sections over `[0, 1] × X` along a path

## The text, paraphrased

Given an sc-smooth path `φ : [0, 1] → U` in the domain of strong bundle coordinates, the map
`s(y, t) = R(y, f(φ(t)))` is an sc⁺-section of the pull-back of `Y → X` to `U × [0, 1]`, and
`s(φ(t), t) = f(φ(t))`.

## What is formalized

The project reads the families of §6.6 on `ℝⁿ` (decision D2), with sections over `ℝⁿ × X`
(`exists_isScPlusSection_pullback_of_mapsTo_of_bump`).  Here the parameter space is the
M-polyfold with boundary `[0, 1]` itself (`unitIntervalPolyfold`):

* `PullbackChartData.ofProdChart`: for a chart `χ` of any M-polyfold `Q` and a strong bundle
  chart `c` of `P`, the product chart `χ × φ_c` of `Q × X` with the retraction `r_Q × r_c`, as
  pull-back chart data of `pr₂*P` (the generic form of `PullbackChartData.ofProd`).
* `exists_isScPlusSection_prodChart`: in such a product chart, for an sc-smooth
  `ê : O_χ → F¹` and a cut-off `β` supported in the chart, the section
  `(t, y) ↦ β(t, y)·(−R(φ_c(y), ê(χ(t))))` is an sc⁺-section of `pr₂*P` over `Q × X`.
* `exists_levelOne_lift_unitInterval`: for an sc-smooth path `φ : [0, 1] → dom φ_c` and each of
  the two charts `t`, `1 − t` of `[0, 1]`, the principal part `v ↦ f̂(φ(χ⁻¹(v)))` lifts to an
  sc-smooth map into `F¹` (the parameter space is finite-dimensional).
* **`proposition_6_6_3_three_interval`** (Proposition 6.6.3 (3) on `[0, 1]`): there is an
  sc⁺-section `S` of `pr₂*P` over `[0, 1] × X` whose fibre part over `y ∈ dom φ_c` is the
  text's `−β(y)·R(y, f(φ(t)))` (`β` an sc-smooth cut-off, `= 1` near `φ([0, 1])`), and
  `(f + S)(t, φ(t)) = 0` for **every** `t ∈ [0, 1]`.  The sign is that of `sectionAdd` (the
  text's `F = f − s`); the cut-off extends the text's section on `U × [0, 1]` to `X × [0, 1]`.
  The two charts of `[0, 1]` are glued with a partition of unity `a_L + a_R = 1` in `t`.
* `admitsBumpFunctions_prod_unitInterval` and **`proposition_6_6_3_four_interval`**
  (Proposition 6.6.3 (4) on `[0, 1]`): `[0, 1] × X` admits sc-smooth bump functions when `X`
  does, so the pull-back of `P` to `[0, 1] × X` has sc⁺-sections through every smooth point of a
  fibre over a smooth point.

The paracompactness instances on `[0, 1] × X` and on the pull-back are those of the `ℝⁿ` forms
(`MPolyfold.paracompactSpace_prod`, `paracompactSpace_pullbackSpace`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v w

open StrongRetr StrongBundle

/-! ### Fibres of sections of `pr₂*P` over `T × X` -/

section Fibres

variable {T : Type w} {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

omit [∀ x, AddCommGroup (P ⁻¹' {x})] in
lemma mem_fiber_of_isSection_pullback_snd
    {S : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (z : T × X) : (S z).1.2 ∈ P ⁻¹' {z.2} := by
  have h1 : P (S z).1.2 = (S z).1.1.2 := (S z).2
  have h2 : (S z).1.1 = z := hS z
  change P (S z).1.2 = z.2
  rw [h1, h2]

/-- A section of `pr₂*P` vanishes at `z` iff its value in `Y` is the zero of `P⁻¹(z₂)`. -/
lemma isZeroAt_pullback_snd_iff {G : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G) (z : T × X) :
    IsZeroAt (pullbackProj P Prod.snd) G z ↔ (G z).1.2 = fiberZero P z.2 := by
  have h0 : fiberZero (pullbackProj P Prod.snd) z = ⟨(z, fiberZero P z.2), (0 : P ⁻¹' {z.2}).2⟩ :=
    rfl
  have h1 : (G z).1.1 = z := hG z
  unfold IsZeroAt
  rw [h0]
  constructor
  · intro h
    exact congrArg (fun q : pullbackSpace P (Prod.snd : T × X → X) => q.1.2) h
  · intro h
    exact Subtype.ext (Prod.ext h1 h)

/-- The value in `Y` of a sum of sections of `pr₂*P` is the sum in the fibre `P⁻¹(z₂)`. -/
lemma sectionAdd_pullback_snd_apply {S₁ S₂ : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (h₂ : IsSection (pullbackProj P Prod.snd) S₂)
    (z : T × X) :
    (sectionAdd (pullbackProj P Prod.snd) S₁ S₂ z).1.2 =
      (((⟨(S₁ z).1.2, mem_fiber_of_isSection_pullback_snd h₁ z⟩ : P ⁻¹' {z.2}) +
        ⟨(S₂ z).1.2, mem_fiber_of_isSection_pullback_snd h₂ z⟩ : P ⁻¹' {z.2}) : Y) := by
  set e := pullbackFiberEquiv P (Prod.snd : T × X → X) z with he
  have e1 : e ⟨S₁ z, h₁ z⟩ = ⟨(S₁ z).1.2, mem_fiber_of_isSection_pullback_snd h₁ z⟩ :=
    Subtype.ext rfl
  have e2 : e ⟨S₂ z, h₂ z⟩ = ⟨(S₂ z).1.2, mem_fiber_of_isSection_pullback_snd h₂ z⟩ :=
    Subtype.ext rfl
  have e3 := pullbackFiberEquiv_add P (Prod.snd : T × X → X) z ⟨S₁ z, h₁ z⟩ ⟨S₂ z, h₂ z⟩
  rw [e1, e2] at e3
  rw [sectionAdd_apply h₁ h₂]
  exact congrArg Subtype.val e3

end Fibres

/-! ### Product charts of `Q × X` and sc⁺-sections in them -/

section ProdChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {T : Type w} [TopologicalSpace T] [T2Space T] [ParacompactSpace T] {Q : MPolyfold T}
  [ParacompactSpace (T × X)]

/-- **The product chart `χ × φ_c`** of `Q × X` pulled back from a strong bundle chart `c` of `P`
(the generic form of `PullbackChartData.ofProd`, where `Q = ℝⁿ`): the chart `χ × φ` with the
retraction `r_Q × r` onto `O_χ × O`; here `g = φ ∘ pr₂ ∘ (χ × φ)⁻¹` is `(v, u) ↦ u`. -/
def PullbackChartData.ofProdChart {χ : MChart T} (hχ : Q.IsChart χ)
    (RQ : ScRetraction χ.model.E χ.model.C) (hRQ : RQ.retract = χ.model.O)
    (c : StrongBundleChart PX P) : PullbackChartData PX P (Q.prod PX) Prod.snd where
  c := c
  ψ := χ.prod c.φ
  isChart := MPolyfold.IsChart.prod hχ c.isChart
  mapsTo := fun _ hz => hz.2
  RZ := RQ.prod (c.isRetraction.baseRetraction c.relOpen)
  RZ_retract := by
    have h := ScRetraction.prod_retract RQ (c.isRetraction.baseRetraction c.relOpen)
    rw [c.base_retract, hRQ] at h
    exact h
  smooth := by
    refine ((ScBanach.prodSndOp χ.model.E c.φ.model.E).isScSmoothRetractMap
      (χ.prod c.φ).model.isScRetract (fun w hw => hw.2)).congr fun w hw => ?_
    change w.2 = c.φ (c.φ.symm w.2)
    rw [c.φ.apply_symm_apply hw.2]

variable [ParacompactSpace (pullbackSpace P (Prod.snd : T × X → X))]

/-- **A cut-off sc⁺-section of `pr₂*P` over `Q × X` in a product chart**: for a chart `χ` of `Q`,
a strong bundle chart `c` of the atlas, an sc-smooth `ê : O_χ → F¹` and an sc-smooth cut-off `β`
supported in `dom χ × dom φ_c`, there is an sc⁺-section `S` of `pr₂*P` whose fibre part over
`y ∈ dom φ_c` is `β(t, y)·(−R(φ_c(y), ê(χ(t))))` (the text's `R(y, ·)`, with the sign of
`sectionAdd`).  It is `cutoffSection` in the product chart `χ × φ_c`, with
`τ(v, u) = −R[1](u, ê(v))₂`.  (`q₀` is the junk value of the inverse of the chart.) -/
theorem exists_isScPlusSection_prodChart {χ : MChart T} (hχ : Q.IsChart χ)
    (RQ : ScRetraction χ.model.E χ.model.C) (hRQ : RQ.retract = χ.model.O)
    {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) {ê : χ.model.E 0 → c.F 1}
    (hê : IsScSmoothRetractMap χ.model.E χ.model.C χ.model.O c.F.shift univ univ ê)
    {β : T × X → ℝ} (hβ : (Q.prod PX).IsScSmoothMap realPolyfold β)
    (hβs : tsupport β ⊆ χ.source ×ˢ c.φ.source) (q₀ : pullbackSpace P (Prod.snd : T × X → X)) :
    ∃ S : T × X → pullbackSpace P (Prod.snd : T × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd Q PX)).IsScPlusSection S ∧
      ∀ t y, y ∈ c.φ.source → (c (S (t, y)).1.2).2 =
        β (t, y) • -(c.R (c.φ y, c.F.toBase 1 (ê (χ t)))).2 := by
  classical
  set d := PullbackChartData.ofProdChart hχ RQ hRQ c with hd
  set pc := d.toChart q₀ with hpc
  have hpcmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd Q PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  -- the local section `τ(v, u) = −R[1](u, ê(v))₂`
  set τ : (χ.model.E.prod c.φ.model.E) 0 → c.F 1 :=
    fun z => -(shiftFiber c.R (z.2, ê z.1)).2 with hτdef
  have hRfib : ∀ u ∈ c.U, ∀ e : c.F 1, (c.R (u, c.F.toBase 1 e)).2 ∈ range (c.F.toBase 1) :=
    fun u hu e => (c.isRetraction.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩ _
      ⟨e, rfl⟩).2
  have hτbase : ∀ z : (χ.model.E.prod c.φ.model.E) 0, z.2 ∈ c.U →
      c.F.toBase 1 (τ z) = -(c.R (z.2, c.F.toBase 1 (ê z.1))).2 := fun z hz => by
    simp only [hτdef, map_neg, shiftFiber]
    rw [Function.invFun_eq (hRfib z.2 hz _)]
  -- `(z, τ(z)) ∈ K[1]` for `z ∈ O_χ × O`
  have hτK : ∀ z : (χ.model.E.prod c.φ.model.E) 0, z ∈ χ.model.O ×ˢ c.φ.model.O →
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
    set h := c.F.toBase 1 (ê z.1) with hh
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
      set R' : pc.φ.model.E 0 → (χ.model.E.prod c.φ.model.E) 0 := fun w => R w with hR'def
      have hRO : ∀ w ∈ R.U, R' w ∈ χ.model.O ×ˢ c.φ.model.O := fun w hw => by
        change R w ∈ pc.φ.model.O
        rw [← hR]; exact R.apply_mem_retract hw
      have hRsm : IsScSmooth (E := pc.φ.model.E) (F := χ.model.E.prod c.φ.model.E) R.U R' :=
        R.isScSmooth
      have hfst : IsScSmoothRetractMap pc.φ.model.E pc.φ.model.C pc.φ.model.O χ.model.E
          χ.model.C χ.model.O (ScBanach.prodFstOp χ.model.E c.φ.model.E 0) :=
        (ScBanach.prodFstOp χ.model.E c.φ.model.E).isScSmoothRetractMap
          pc.φ.model.isScRetract fun w hw => hw.1
      have hêR : IsScSmooth (E := pc.φ.model.E) (F := c.F.shift) R.U
          (fun w => ê (R' w).1) :=
        ((hê.comp hfst χ.model.isScRetract).comp_isScSmooth R hR).congr hU fun _ _ => rfl
      have hpair : IsScSmooth (E := pc.φ.model.E) (F := c.φ.model.E.prod c.F.shift) R.U
          (fun w => ((R' w).2, ê (R' w).1)) :=
        IsScSmooth.scPair hU (hRsm.snd hU) hêR
      have hmaps : MapsTo (fun w => ((R' w).2, ê (R' w).1)) R.U (c.U ×ˢ univ) :=
        fun w hw => ⟨StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ (hRO w hw).2),
          mem_univ _⟩
      have hsf := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
        c.isRetraction.isScSmooth_one hpair hmaps
      have hτR : IsScSmooth (E := pc.φ.model.E) (F := c.F.shift) R.U (τ ∘ R) :=
        ((hsf.snd hU).neg hU).congr hU fun _ _ => rfl
      exact (R.isScSmooth.scPair hU hτR).congr hU fun _ _ => rfl
  set S := StrongBundle.cutoffSection pc β τ with hSdef
  have hS : (B.pullback (MPolyfold.isScSmoothMap_snd Q PX)).IsScPlusSection S :=
    StrongBundle.isScPlusSection_cutoffSection hpcmem hβ hβs hτ
  refine ⟨S, hS, fun t y hy => ?_⟩
  by_cases hty : (t, y) ∈ pc.φ.source
  · have h2 : (c (S (t, y)).1.2).2 = c.F.toBase 1 (β (t, y) • τ (pc.φ (t, y))) :=
      congrArg Prod.snd (StrongBundle.apply_cutoffSection hτ.mapsTo hty)
    rw [h2, map_smul]
    have hpcφ : pc.φ (t, y) = (χ t, c.φ y) := rfl
    rw [hpcφ, hτbase _ (StrongRetr.mem_U_of_mem_O c.isRetraction
      (c.r_image ▸ c.φ.mapsTo_model _ hy))]
  · have hβ0 : β (t, y) = 0 := image_eq_zero_of_notMem_tsupport fun h => hty (hβs h)
    have h0 : S (t, y) = fiberZero (pullbackProj P Prod.snd) (t, y) := by
      simp only [hSdef, StrongBundle.cutoffSection, if_neg hty]
    rw [h0, hβ0, zero_smul]
    exact c.snd_fiberZero hy

end ProdChart

/-! ### `[0, 1]`: level-one lifts along the two charts -/

section UnitIntervalSections

open UnitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The principal part along a path on `[0, 1]` lifts to `F¹`**: for an sc-smooth section `f`,
an sc-smooth path `φ : [0, 1] → dom φ_c` and a chart `χ` of `[0, 1]` on the model `[0, 1)` (the
charts `t` and `1 − t`), the map `v ↦ Φ(f(φ(χ⁻¹(v))))₂` lifts to an sc-smooth `ê : O_χ → F¹`:
the parameter space is finite-dimensional with the constant sc-structure, so the shift of the
sc-smooth representative (Proposition 1.2.2, preprint 1.17) has the same domain. -/
theorem exists_levelOne_lift_unitInterval (hf : B.IsScSmoothSection f) {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hφc : ∀ t, φ t ∈ c.φ.source) {χ : MChart unitInterval}
    (hχ : unitIntervalPolyfold.IsChart χ) (hm : χ.model = UnitInterval.model) :
    ∃ ê : χ.model.E 0 → c.F 1,
      IsScSmoothRetractMap χ.model.E χ.model.C χ.model.O c.F.shift univ univ ê ∧
      ∀ t ∈ χ.source, c.F.toBase 1 (ê (χ t)) = (c (f (φ t))).2 := by
  have hfs : IsSection P f := hf.1
  have hfφ : unitIntervalPolyfold.IsScSmoothMap B.toMPolyfold0 (f ∘ φ) := hf.2.comp hφ
  have h1 := hfφ.smooth χ (c.toMChart B.continuous) hχ (B.isChart_toMChart hc) χ.source
    χ.isOpen_source (fun _ ht => ⟨mem_univ _, ht⟩)
    (fun t _ => c.mem_source_of_proj (by rw [Function.comp_apply, hfs]; exact hφc t))
  rw [χ.image_source] at h1
  rcases χ with ⟨m, e, h₁, h₂, h₃, h₄⟩
  subst hm
  set g : (Fin 1 → ℝ) → (c.φ.model.E.prod c.F) 0 := fun v => c (f (φ (e.symm v))) with hgdef
  have hU : IsScDomain (rnSc 1) modelO := isRelOpen_modelO.isScDomain
  have hg : IsScSmooth (E := rnSc 1) (F := c.φ.model.E.prod c.F) modelO g :=
    h1.comp_isScSmooth (ScRetraction.id isRelOpen_modelO) (image_id _)
  have hg1 := hg.shift hU
  have hlv : (rnSc 1).lvlSet modelO 1 = modelO := by
    ext v
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]
  rw [hlv] at hg1
  have hg1' : IsScSmooth (E := rnSc 1) (F := c.φ.model.E.shift.prod c.F.shift) modelO
      (fun v => levelMap (E := rnSc 1) (F := c.φ.model.E.prod c.F) g 1 v) := hg1
  set ê : (Fin 1 → ℝ) → c.F 1 :=
    fun v => (levelMap (E := rnSc 1) (F := c.φ.model.E.prod c.F) g 1 v).2 with hêdef
  have hê : IsScSmooth (E := rnSc 1) (F := c.F.shift) modelO ê := hg1'.snd hU
  have hêbase : ∀ v ∈ modelO, c.F.toBase 1 (ê v) = (g v).2 := fun v hv => by
    have h := IsSc0.toBase_levelMap (hg 0) (m := 1) (x := v)
      (by rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]; exact hv)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase] at h
    exact congrArg Prod.snd h
  refine ⟨ê, ⟨mapsTo_univ _ _, fun R hR => ?_⟩, fun t ht => ?_⟩
  · refine IsScSmooth.comp R.isScDomain hU hê R.isScSmooth fun w hw => ?_
    have := R.apply_mem_retract hw
    rw [hR] at this
    exact this
  · have hv : e t ∈ modelO := by
      have := e.map_source ht
      rw [h₂] at this
      exact this
    change c.F.toBase 1 (ê (e t)) = _
    rw [hêbase _ hv]
    change (c (f (φ (e.symm (e t))))).2 = _
    rw [e.left_inv ht]

/-! ### The partition of unity `a_L + a_R = 1` on `[0, 1]` -/

/-- `a_R(t) = σ(3t − 1)` (`σ` the smooth transition): `0` on `[0, 1/3]`, `1` on `[2/3, 1]`. -/
def intervalCutR (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

/-- `a_L = 1 − a_R`: `1` on `[0, 1/3]`, `0` on `[2/3, 1]`. -/
def intervalCutL (t : ℝ) : ℝ := 1 - intervalCutR t

lemma contDiff_intervalCutR : ContDiff ℝ ∞ intervalCutR :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma intervalCutR_eq_zero {t : ℝ} (ht : t ≤ 1 / 3) : intervalCutR t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma intervalCutL_eq_zero {t : ℝ} (ht : 2 / 3 ≤ t) : intervalCutL t = 0 := by
  rw [intervalCutL, intervalCutR, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

lemma isScSmoothMap_intervalCutR :
    unitIntervalPolyfold.IsScSmoothMap realPolyfold fun t => intervalCutR t :=
  (isScSmoothMap_rn_real_of_contDiff (g := fun v : Fin 1 → ℝ => intervalCutR (v 0))
    (contDiff_intervalCutR.comp (contDiff_apply ℝ ℝ (0 : Fin 1)))).comp
    isScSmoothMap_unitInterval_val

lemma isScSmoothMap_intervalCutL :
    unitIntervalPolyfold.IsScSmoothMap realPolyfold fun t => intervalCutL t :=
  isScSmoothMap_intervalCutR.comp_contDiff (σ := fun r => 1 - r) (contDiff_const.sub contDiff_id)

/-! ### Proposition 6.6.3 (3) on `[0, 1]` -/

variable [ParacompactSpace (unitInterval × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : unitInterval × X → X))]

omit [T2Space X] [ParacompactSpace X] [ParacompactSpace (unitInterval × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : unitInterval × X → X))] in
/-- The support of `(t, y) ↦ a(t)β(y)` lies in `s × V` if `a ≠ 0` only on a closed `K ⊆ s` and
`supp β ⊆ V`. -/
lemma tsupport_cut_mul_subset {a : ℝ → ℝ} {s : Set unitInterval} {β₂ : X → ℝ}
    {K : Set unitInterval} {V : Set X} (hK : IsClosed K) (hKs : K ⊆ s)
    (ha : ∀ t : unitInterval, a t ≠ 0 → t ∈ K) (hβ₂s : tsupport β₂ ⊆ V) :
    tsupport (fun p : unitInterval × X => a p.1 * β₂ p.2) ⊆ s ×ˢ V := by
  refine (closure_minimal (fun p hp => ?_)
    ((hK.preimage continuous_fst).inter (isClosed_tsupport β₂ |>.preimage continuous_snd))).trans
    fun p hp => ⟨hKs hp.1, hβ₂s hp.2⟩
  have hp' : a p.1 * β₂ p.2 ≠ 0 := hp
  exact ⟨ha p.1 (left_ne_zero_of_mul hp'), subset_tsupport _ (right_ne_zero_of_mul hp')⟩

/-- **2021 Proposition 6.6.3 (3), p. 263, on `[0, 1]`** (preprint Proposition 6.28 (3)): with
sc-smooth bump functions, for an sc-smooth section `f`, a strong bundle chart `c` of the atlas
and an sc-smooth path `φ : [0, 1] → dom φ_c`, there are an sc-smooth cut-off `β` with
`supp β ⊆ dom φ_c` and `β = 1` on `φ([0, 1])`, and an sc⁺-section `S` of `pr₂*P` over the
M-polyfold `[0, 1] × X` with
* fibre part `−β(y)·R(φ_c(y), f̂(φ(t)))` over `y ∈ dom φ_c` (the text's `s(y, t) = R(y, f(φ(t)))`
  with the sign of `sectionAdd` and the cut-off), and
* `(f + S)(t, φ(t)) = 0` for every `t ∈ [0, 1]` (the text's `s(φ(t), t) = f(φ(t))`).
The two charts `t`, `1 − t` of `[0, 1]` are glued with the partition `a_L + a_R = 1`
(`exists_isScPlusSection_prodChart`, `exists_levelOne_lift_unitInterval`). -/
theorem proposition_6_6_3_three_interval (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScSmoothSection f) {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ)
    (hφc : ∀ t, φ t ∈ c.φ.source) :
    ∃ (β₂ : X → ℝ) (S : unitInterval × X → pullbackSpace P (Prod.snd : unitInterval × X → X)),
      PX.IsScSmoothMap realPolyfold β₂ ∧ tsupport β₂ ⊆ c.φ.source ∧ (∀ t, β₂ (φ t) = 1) ∧
      (B.pullback (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX)).IsScPlusSection S ∧
      (∀ t y, y ∈ c.φ.source →
        (c (S (t, y)).1.2).2 = -(β₂ y • (c.R (c.φ y, (c (f (φ t))).2)).2)) ∧
      ∀ t, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd)
          (pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf.1 z.2) S) (t, φ t) := by
  have hfs : IsSection P f := hf.1
  have hφcont : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  obtain ⟨β₂, hβ₂, hβ₂s, hβ₂1⟩ := exists_isScSmoothMap_eq_one_nhdsSet hbump
    (isCompact_range hφcont) c.φ.isOpen_source (range_subset_iff.2 hφc)
  have hβ₂φ : ∀ t, β₂ (φ t) = 1 := fun t => hβ₂1.self_of_nhdsSet (φ t) ⟨t, rfl⟩
  obtain ⟨êL, hêL, hêLb⟩ := exists_levelOne_lift_unitInterval hf hφ hc hφc isChart_leftChart rfl
  obtain ⟨êR, hêR, hêRb⟩ := exists_levelOne_lift_unitInterval hf hφ hc hφc isChart_rightChart rfl
  -- the cut-offs `a_L(t)β(y)` and `a_R(t)β(y)`
  have hβsnd := hβ₂.comp (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX)
  have hβL : (unitIntervalPolyfold.prod PX).IsScSmoothMap realPolyfold
      (fun p : unitInterval × X => intervalCutL p.1 * β₂ p.2) :=
    (isScSmoothMap_intervalCutL.comp
      (MPolyfold.isScSmoothMap_fst unitIntervalPolyfold PX)).mul hβsnd
  have hβR : (unitIntervalPolyfold.prod PX).IsScSmoothMap realPolyfold
      (fun p : unitInterval × X => intervalCutR p.1 * β₂ p.2) :=
    (isScSmoothMap_intervalCutR.comp
      (MPolyfold.isScSmoothMap_fst unitIntervalPolyfold PX)).mul hβsnd
  have hβLs := tsupport_cut_mul_subset (a := intervalCutL) (s := leftChart.source)
    (K := {t : unitInterval | (t : ℝ) ≤ 2 / 3})
    (isClosed_le continuous_subtype_val continuous_const)
    (fun t (ht : (t : ℝ) ≤ 2 / 3) => show (t : ℝ) < 1 by linarith)
    (fun t ht => by
      by_contra h
      exact ht (intervalCutL_eq_zero (le_of_lt (not_le.1 h))))
    hβ₂s
  have hβRs := tsupport_cut_mul_subset (a := intervalCutR) (s := rightChart.source)
    (K := {t : unitInterval | 1 / 3 ≤ (t : ℝ)})
    (isClosed_le continuous_const continuous_subtype_val)
    (fun t (ht : 1 / 3 ≤ (t : ℝ)) => show (0 : ℝ) < t by linarith)
    (fun t ht => by
      by_contra h
      exact ht (intervalCutR_eq_zero (le_of_lt (not_le.1 h))))
    hβ₂s
  set q₀ : pullbackSpace P (Prod.snd : unitInterval × X → X) :=
    ⟨((0, φ 0), fiberZero P (φ 0)), proj_fiberZero P (φ 0)⟩ with hq₀
  obtain ⟨SL, hSL, hvL⟩ := exists_isScPlusSection_prodChart (B := B) isChart_leftChart
    (ScRetraction.id isRelOpen_modelO) (image_id _) hc hêL hβL hβLs q₀
  obtain ⟨SR, hSR, hvR⟩ := exists_isScPlusSection_prodChart (B := B) isChart_rightChart
    (ScRetraction.id isRelOpen_modelO) (image_id _) hc hêR hβR hβRs q₀
  set S := sectionAdd (pullbackProj P Prod.snd) SL SR with hSdef
  have hS : (B.pullback (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX)).IsScPlusSection S :=
    hSL.add hSR
  -- the fibre part of `S`
  have hval : ∀ t y, y ∈ c.φ.source →
      (c (S (t, y)).1.2).2 = -(β₂ y • (c.R (c.φ y, (c (f (φ t))).2)).2) := by
    intro t y hy
    have hL : (intervalCutL t * β₂ y) • -(c.R (c.φ y, c.F.toBase 1 (êL (leftChart t)))).2 =
        (intervalCutL t * β₂ y) • -(c.R (c.φ y, (c (f (φ t))).2)).2 := by
      by_cases ht : (t : ℝ) < 1
      · rw [hêLb t ht]
      · rw [intervalCutL_eq_zero (by linarith [not_lt.1 ht]), zero_mul, zero_smul, zero_smul]
    have hR : (intervalCutR t * β₂ y) • -(c.R (c.φ y, c.F.toBase 1 (êR (rightChart t)))).2 =
        (intervalCutR t * β₂ y) • -(c.R (c.φ y, (c (f (φ t))).2)).2 := by
      by_cases ht : (0 : ℝ) < t
      · rw [hêRb t ht]
      · rw [intervalCutR_eq_zero (by linarith [not_lt.1 ht]), zero_mul, zero_smul, zero_smul]
    rw [hSdef, sectionAdd_pullback_snd_apply hSL.1 hSR.1 (t, y), c.snd_add hy]
    change (c (SL (t, y)).1.2).2 + (c (SR (t, y)).1.2).2 = _
    rw [hvL t y hy, hvR t y hy, hL, hR, ← add_smul,
      show intervalCutL t * β₂ y + intervalCutR t * β₂ y = β₂ y by
        unfold intervalCutL; ring, smul_neg]
  refine ⟨β₂, S, hβ₂, hβ₂s, hβ₂φ, hS, hval, fun t => ?_⟩
  -- `(f + S)(t, φ(t)) = 0`
  have hL : IsSection (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : unitInterval × X => hfs z.2) :=
    isSection_pullbackLift _
  have hG : IsSection (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : unitInterval × X => hfs z.2) S) :=
    hL.sectionAdd hS.1
  rw [isZeroAt_pullback_snd_iff hG]
  set σ : X → Y := fun x => (sectionAdd (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z : unitInterval × X => hfs z.2) S (t, x)).1.2
    with hσdef
  have hσ : IsSection P σ := fun x => mem_fiber_of_isSection_pullback_snd hG (t, x)
  have hxt : φ t ∈ c.φ.source := hφc t
  change IsZeroAt P σ (φ t)
  refine (c.isZeroAt_iff hσ hxt).2 ?_
  change (c (σ (c.φ.symm (c.φ (φ t))))).2 = 0
  rw [c.φ.symm_apply_apply hxt, hσdef]
  simp only
  rw [sectionAdd_pullback_snd_apply hL hS.1 (t, φ t), c.snd_add hxt]
  change (c (f (φ t))).2 + (c (S (t, φ t)).1.2).2 = 0
  rw [hval t (φ t) hxt, hβ₂φ t, one_smul]
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

/-! ### Proposition 6.6.3 (4) on `[0, 1]` -/

/-- **`[0, 1] × X` admits sc-smooth bump functions when `X` does** (Definition 5.3.1, preprint
5.9): around `(t, x)`, the product `b(t')β(x')` of a `C^∞` bump `b` of `ℝ` restricted to `[0, 1]`
and a bump `β` of `X` (as `admitsBumpFunctions_prod_rn` for `ℝⁿ × X`). -/
theorem admitsBumpFunctions_prod_unitInterval (hbump : PX.AdmitsBumpFunctions) :
    (unitIntervalPolyfold.prod PX).AdmitsBumpFunctions := by
  rintro ⟨r, x⟩ U hU hxU
  obtain ⟨U₁, U₂, hU₁, hU₂, hr, hx, hsub⟩ := isOpen_prod_iff.1 hU r x hxU
  obtain ⟨β₂, hβ₂, hβ₂x, hβ₂s⟩ := hbump x U₂ hU₂ hx
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU₁
  have hrW : (r : ℝ) ∈ W := by
    rw [← hWU] at hr
    exact hr
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW r hrW
  let b : ContDiffBump (r : ℝ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun p => b p.1 * β₂ p.2, ?_, ?_, ?_⟩
  · have hb : unitIntervalPolyfold.IsScSmoothMap realPolyfold fun t : unitInterval => b t :=
      (isScSmoothMap_rn_real_of_contDiff (g := fun v : Fin 1 → ℝ => b (v 0))
        (b.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1)))).comp isScSmoothMap_unitInterval_val
    exact (hb.comp (MPolyfold.isScSmoothMap_fst unitIntervalPolyfold PX)).mul
      (hβ₂.comp (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX))
  · change b r * β₂ x ≠ 0
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
    exact hβ₂x
  · refine (tsupport_prod_mul_subset (fun t : unitInterval => b t) β₂).trans
      ((prod_mono ?_ hβ₂s).trans hsub)
    have hcl : IsClosed (Subtype.val ⁻¹' Metric.closedBall (r : ℝ) (ε / 2) : Set unitInterval) :=
      Metric.isClosed_closedBall.preimage continuous_subtype_val
    refine (closure_minimal (fun t ht => ?_) hcl).trans fun t ht => ?_
    · have h : (t : ℝ) ∈ Function.support b := ht
      rw [b.support_eq] at h
      exact Metric.ball_subset_closedBall h
    · rw [← hWU]
      exact hball (Metric.closedBall_subset_ball (by linarith) ht)

/-- **2021 Proposition 6.6.3 (4), p. 263, on `[0, 1]`** (preprint Proposition 6.28 (4)): with
sc-smooth bump functions, the pull-back of `P` to `[0, 1] × X` has sc⁺-sections through every
smooth point of a fibre over a smooth point (`HasScPlusSectionsThrough`, Lemma 5.3.3, preprint
5.11, for `[0, 1] × X`). -/
theorem proposition_6_6_3_four_interval (hbump : PX.AdmitsBumpFunctions) :
    (B.pullback (MPolyfold.isScSmoothMap_snd unitIntervalPolyfold PX)).HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough
    (admitsBumpFunctions_prod_unitInterval hbump)

end UnitIntervalSections

end Polyfold
