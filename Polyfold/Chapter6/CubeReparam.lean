import Polyfold.Chapter6.CubeBoundarySlice
import Polyfold.Chapter6.ProperHomotopy2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 263–266
(preprint §6.5): families on `[0, 1]ⁿ` read through families on `ℝⁿ`.

# Smooth maps into `[0, 1]ⁿ` and reparametrized sections

* `UnitCube.isScSmoothMap_toCube`: a map `g : ℝᵐ → [0, 1]ⁿ` whose coordinates are `C^∞` is an
  sc-smooth map into the M-polyfold `[0, 1]ⁿ` (in the corner chart `b` its representative is
  `r ↦ (fl (bᵢ) (gᵢ(r)))ᵢ`).
* `UnitCube.sinSqCube`: `v ↦ (sin²(π vᵢ / 2))ᵢ`, an sc-smooth map `ℝⁿ → [0, 1]ⁿ` with the
  continuous right inverse `UnitCube.arcCube : [0, 1]ⁿ → [0, 1]ⁿ ⊆ ℝⁿ`,
  `q ↦ ((2/π) arcsin √qᵢ)ᵢ` (`sinSqCube_arcCube`).
* `cubeReparamSection g S`: `(v, y) ↦ S(g(v), y)` for a section `S` of `pr₂*P → [0, 1]ⁿ × X`;
  its slices are those of `S` (`pullbackSlice_cubeReparamSection`), and it is an sc⁺-section of
  `pr₂*P → ℝᵐ × X` when `S` is one and `g` has `C^∞` coordinates
  (**`StrongBundle.IsScPlusSection.cubeReparam`**; in the product charts its representative is
  that of `S` composed with `(a, u) ↦ (χ_b(g(a)), u)`, on the part of `ℝᵐ` that `g` maps into the
  corner chart `χ_b`).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open UnitCube

namespace UnitCube

variable {m n : ℕ}

/-- **A map into `[0, 1]ⁿ` with `C^∞` coordinates is sc-smooth**: around `r₀` take the corner chart
`b = corner (g r₀)`; on `g⁻¹(dom χ_b)` the representative is `r ↦ (fl (bᵢ) (gᵢ(r)))ᵢ`. -/
theorem isScSmoothMap_toCube {g : (Fin m → ℝ) → (Fin n → unitInterval)}
    (hg : ContDiff ℝ ∞ fun r i => (g r i : ℝ)) :
    (rnPolyfold m).IsScSmoothMap (cubePolyfold n) g := by
  have hgc : Continuous g := continuous_pi fun i =>
    (((continuous_apply i).comp hg.continuous).subtype_mk fun r => (g r i).2)
  have hg' : ContDiff ℝ ∞ fun r : Fin m → ℝ => fun i => (g (r + 0) i : ℝ) :=
    hg.comp (contDiff_id.add contDiff_const)
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hgc.continuousOn fun x _ => ?_
  set b := corner (g x)
  have hV : IsOpen (g ⁻¹' (chart b).source) := (chart b).isOpen_source.preimage hgc
  refine ⟨rnChart m 0, chart b, g ⁻¹' (chart b).source, isChart_rnChart 0, isChart_chart b, hV,
    mem_chart_corner (g x), fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ hr => hr, ?_⟩
  refine isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin m → ℝ) (V' := Fin n → ℝ)
    (g := fun r i => fl (b i) (g (r + 0) i)) ((rnChart m 0).isScRetract_image (subset_univ _) hV)
    (contDiff_pi.2 fun i => (contDiff_fl (b i)).comp
      ((contDiff_apply ℝ ℝ i).comp hg')) ?_
  rintro _ ⟨r, hr, rfl⟩
  change (fun i => fl (b i) (g (r - 0 + 0) i)) ∈ modelO n
  rw [sub_add_cancel]
  exact mem_modelO.2 fun i => ⟨(fl_mem_Icc (b i) (g r i).2).1, hr i⟩

/-- `v ↦ (sin²(π vᵢ / 2))ᵢ : ℝⁿ → [0, 1]ⁿ`. -/
def sinSqCube (v : Fin n → ℝ) : Fin n → unitInterval := fun i =>
  ⟨Real.sin (Real.pi / 2 * v i) ^ 2, sq_nonneg _, Real.sin_sq_le_one _⟩

theorem contDiff_sinSqCube : ContDiff ℝ ∞ fun v i => (sinSqCube (n := n) v i : ℝ) :=
  contDiff_pi.2 fun i =>
    (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ i))).pow 2

/-- `sinSqCube` is an sc-smooth map `ℝⁿ → [0, 1]ⁿ`. -/
theorem isScSmoothMap_sinSqCube : (rnPolyfold n).IsScSmoothMap (cubePolyfold n) sinSqCube :=
  isScSmoothMap_toCube contDiff_sinSqCube

lemma arc_mem_Icc (t : unitInterval) :
    2 / Real.pi * Real.arcsin (Real.sqrt (t : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ Real.arcsin (Real.sqrt (t : ℝ)) :=
    Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have h1 : Real.arcsin (Real.sqrt (t : ℝ)) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  refine ⟨by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_le_one hpi]
  linarith

/-- **The continuous right inverse of `sinSqCube`**: `q ↦ ((2/π) arcsin √qᵢ)ᵢ ∈ [0, 1]ⁿ`. -/
def arcCube (q : Fin n → unitInterval) : Icc (0 : Fin n → ℝ) 1 :=
  ⟨fun i => 2 / Real.pi * Real.arcsin (Real.sqrt (q i : ℝ)),
    fun i => (arc_mem_Icc (q i)).1, fun i => (arc_mem_Icc (q i)).2⟩

theorem continuous_arcCube : Continuous (arcCube (n := n)) :=
  (continuous_pi fun i => continuous_const.mul (Real.continuous_arcsin.comp
    (Real.continuous_sqrt.comp (continuous_subtype_val.comp (continuous_apply i))))).subtype_mk _

theorem sinSqCube_arcCube (q : Fin n → unitInterval) : sinSqCube (arcCube q : Fin n → ℝ) = q := by
  funext i
  refine Subtype.ext ?_
  have hpi := Real.pi_pos
  have h1 : Real.sqrt (q i : ℝ) ≤ 1 := Real.sqrt_le_one.mpr (q i).2.2
  have h0 : -1 ≤ Real.sqrt (q i : ℝ) := by linarith [Real.sqrt_nonneg (q i : ℝ)]
  change Real.sin (Real.pi / 2 * (2 / Real.pi * Real.arcsin (Real.sqrt (q i : ℝ)))) ^ 2 = q i
  have e : Real.pi / 2 * (2 / Real.pi * Real.arcsin (Real.sqrt (q i : ℝ))) =
      Real.arcsin (Real.sqrt (q i : ℝ)) := by
    field_simp
  rw [e, Real.sin_arcsin h0 h1, Real.sq_sqrt (q i).2.1]

end UnitCube

/-! ### Sections over `[0, 1]ⁿ × X` reparametrized along maps `ℝᵐ → [0, 1]ⁿ` -/

section Reparam

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Reparametrizing a section of `pr₂*P → [0, 1]ⁿ × X`** along `g : ℝᵐ → [0, 1]ⁿ`:
`(v, y) ↦ S(g(v), y)`, a section of `pr₂*P → ℝᵐ × X`. -/
def cubeReparamSection {m n : ℕ} (g : (Fin m → ℝ) → (Fin n → unitInterval))
    (S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X) :=
  pullbackLift Prod.snd (fun z => prodSlice S (g z.1) z.2)
    (fun z => IsSection.prodSlice hS (g z.1) z.2)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slices of the reparametrized section are those of `S`. -/
theorem pullbackSlice_cubeReparamSection {m n : ℕ} (g : (Fin m → ℝ) → (Fin n → unitInterval))
    (S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) (v : Fin m → ℝ) :
    pullbackSlice (cubeReparamSection g S hS) v = prodSlice S (g v) :=
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
theorem isSection_cubeReparamSection {m n : ℕ} (g : (Fin m → ℝ) → (Fin n → unitInterval))
    (S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    IsSection (pullbackProj P Prod.snd) (cubeReparamSection g S hS) :=
  isSection_pullbackLift _

/-- **An sc⁺-section over `[0, 1]ⁿ × X` reparametrized along a map with `C^∞` coordinates is
sc⁺**: for an sc⁺-section `S` of `pr₂*P → [0, 1]ⁿ × X` and `g : ℝᵐ → [0, 1]ⁿ` with `C^∞`
coordinates, `(v, y) ↦ S(g(v), y)` is an sc⁺-section of `pr₂*P → ℝᵐ × X`.  Around `(v, x)`:
the product chart `χ × φ_c` with `χ` the chart `ℝᵐ` restricted to `g⁻¹(dom χ_b)`,
`b = corner (g(v))`, and the product chart `χ_b × φ_c` of `[0, 1]ⁿ × X`; the representative is
that of `S` composed with `(a, u) ↦ (χ_b(g(a)), u)`. -/
theorem StrongBundle.IsScPlusSection.cubeReparam {m n : ℕ}
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {g : (Fin m → ℝ) → (Fin n → unitInterval)} (hg : ContDiff ℝ ∞ fun r i => (g r i : ℝ)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScPlusSection
      (cubeReparamSection g S hS.1) := by
  set S' := cubeReparamSection g S hS.1 with hS'
  have hsec : IsSection (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X)) S' :=
    isSection_pullbackLift _
  have hgc : Continuous g := continuous_pi fun i =>
    (((continuous_apply i).comp hg.continuous).subtype_mk fun r => (g r i).2)
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2
  set b := corner (g z.1) with hb
  set W := g ⁻¹' (chart b).source with hWdef
  have hW : IsOpen W := (chart b).isOpen_source.preimage hgc
  set χ := (rnChart m 0).restrict (subset_univ W) hW with hχdef
  have hχ : (rnPolyfold m).IsChart χ :=
    MPolyfold.IsChart.restrict _ (isChart_rnChart 0) (subset_univ W) hW
  obtain ⟨RQ, hRQ⟩ := χ.model.isScRetract
  -- the product charts at `z = (v, x)` and at `(g(v), x)`
  set c' := (PullbackChartData.ofProdChart hχ RQ hRQ c).toChart (S' z) with hc'
  obtain ⟨Rb, hRb⟩ := (chart b).model.isScRetract
  set pc := (PullbackChartData.ofProdChart (isChart_chart b) Rb hRb c).toChart
    (S (g z.1, z.2)) with hpc
  have hmem' : c' ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  have hmem : pc ∈
      (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ w ∈ c'.φ.source, ((g w.1, w.2) : (Fin n → unitInterval) × X) ∈ pc.φ.source :=
    fun w hw => ⟨hw.1, hw.2⟩
  refine ⟨c', hmem', ⟨mem_chart_corner (g z.1), hxc⟩, fun w hw => hrange _ (hsrc w hw), ?_⟩
  have hO : IsScRetract c'.φ.model.E c'.φ.model.C c'.φ.model.O := c'.φ.model.isScRetract
  -- the map `(a, u) ↦ (χ_b(g(a)), u)` of retracts `χ(W) × O → [0, 1)ⁿ × O`
  set h : (Fin m → ℝ) → (Fin n → ℝ) := fun a i => fl (b i) (g (a + 0) i) with hh
  have hhs : ContDiff ℝ ∞ h := contDiff_pi.2 fun i => (contDiff_fl (b i)).comp
    ((contDiff_apply ℝ ℝ i).comp (hg.comp (contDiff_id.add contDiff_const)))
  have hWr : IsScRetract (rnSc m) univ ((rnChart m 0) '' W) :=
    (rnChart m 0).isScRetract_image (subset_univ _) hW
  have h1 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O (rnSc m) univ
      ((rnChart m 0) '' W) (ScBanach.prodFstOp (rnSc m) c.φ.model.E 0) :=
    (ScBanach.prodFstOp _ _).isScSmoothRetractMap hO fun p hp => hp.1
  have h2 : IsScSmoothRetractMap (rnSc m) univ ((rnChart m 0) '' W) (rnSc n) (halfC n)
      (modelO n) h := by
    refine isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin m → ℝ) (V' := Fin n → ℝ)
      hWr hhs ?_
    rintro _ ⟨r, hr, rfl⟩
    change (fun i => fl (b i) (g (r - 0 + 0) i)) ∈ modelO n
    rw [sub_add_cancel]
    exact mem_modelO.2 fun i => ⟨(fl_mem_Icc (b i) (g r i).2).1, hr i⟩
  have h3 := h2.comp h1 hWr
  have h4 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O c.φ.model.E
      c.φ.model.C c.φ.model.O (ScBanach.prodSndOp (rnSc m) c.φ.model.E 0) :=
    (ScBanach.prodSndOp _ _).isScSmoothRetractMap hO fun p hp => hp.2
  have hT : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O pc.φ.model.E
      pc.φ.model.C pc.φ.model.O
      (scPair (h ∘ ScBanach.prodFstOp (rnSc m) c.φ.model.E 0)
        (ScBanach.prodSndOp (rnSc m) c.φ.model.E 0)) :=
    h3.scPair h4 fun p hp => show ((h p.1, p.2) : (Fin n → ℝ) × c.φ.model.E 0) ∈
      modelO n ×ˢ c.φ.model.O from ⟨h2.1 hp.1, hp.2⟩
  have hcomp := hsm.comp hT pc.φ.model.isScRetract
  refine ⟨fun w hw => ?_, fun R hR => ?_⟩
  · have hws := c'.φ.symm_mapsTo hw
    exact c'.liftOne_mem (c'.mem_source_of_proj (by rw [hsec]; exact hws))
      (hrange _ (hsrc _ hws))
  · have hU := R.isScDomain
    have h1 := (hcomp.comp_isScSmooth R hR).snd hU
    have h2 := R.isScSmooth.scPair hU h1
    refine h2.congr hU fun w hw => ?_
    have hRw : R w ∈ c'.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hw
    change (R w, (StrongBundle.localRepOne pc S ((h (R w).1, (R w).2))).2) =
      StrongBundle.localRepOne c' S' (R w)
    generalize R w = p at hRw ⊢
    obtain ⟨a, u⟩ := p
    obtain ⟨⟨r, hr, rfl⟩, hu⟩ := hRw
    have hu' : u ∈ c.φ.model.O := hu
    have hbr : (chart b).symm (h (r - 0)) = g r := by
      have e : h (r - 0) = chart b (g r) := by
        funext i
        change fl (b i) (g (r - 0 + 0) i) = fl (b i) (g r i)
        rw [sub_add_cancel]
      rw [e, (chart b).symm_apply_apply hr]
    change ((r - 0, u), Function.invFun (c.F.toBase 1)
        (c (S ((chart b).symm (h (r - 0)), c.φ.symm u)).1.2).2) =
      ((r - 0 + 0 - 0, c.φ (c.φ.symm u)),
        Function.invFun (c.F.toBase 1) (c (S (g (r - 0 + 0), c.φ.symm u)).1.2).2)
    rw [hbr, c.φ.apply_symm_apply hu', sub_add_cancel]

end Reparam

end Polyfold
