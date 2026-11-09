import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter3.GermCalculusParam
import Polyfold.Chapter3.TameGermsAddG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Theorem 3.1.21 (preprint 3.18)** (parametrized perturbations; book 2017: Theorem 3.3) **in the text's germ
reading** of Definition 3.1.11 (preprint 3.11) (phase 2 of the germ-versus-chart work; Findings, Chapter 3, items
300–309), with its tame form (Definition 3.6.4 (preprint 3.51)) and the linearization of the parametrized section
used after Theorem 3.1.22 (preprint 3.19).

# Parametrized perturbations, germ reading

## The text, paraphrased

(Before Theorem 3.1.21 (preprint 3.18)) For an sc-Fredholm section `f` of `P : Y → X`, the section
`f̃(r, x) = ((r, x), f(x))` of the pull-back `π*(P)` along `π : ℝⁿ × X → X` "is a sc-Fredholm
section as is readily verified"; for sc⁺-sections `s₁, …, sₙ`, `s̃(r, x) = ((r, x), Σ rᵢ sᵢ(x))` is
an sc⁺-section, and by Theorem 3.1.18 (preprint 3.15) `f̃ + s̃` is sc-Fredholm.  (Theorem 3.1.21 (preprint 3.18))
`(r, x) ↦ f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of `π*(P)`.  The germ data of Definition
3.11 are germs (Definitions 3.1.1–3.1.2 (preprint 3.1–3.2): sc-germs of neighbourhoods whose levels may shrink with the
level).

## What is formalized

* `Polyfold.StrongBundle.IsScFredholmGerm.param`: **`(f̃, (r₀, x))` is an sc-Fredholm germ in the
  germ reading** when `(f, x)` is: in the product chart `(r ↦ r − r₀) × φ` the filling germ
  `(a, u) ↦ g(u)` on `ℝⁿ × G_g` (`PullbackChartData.ofProd_isFillingGerm`), the sc⁺-germ
  `(a, u) ↦ t₀(u)` on `ℝⁿ × G_{t₀}` (`ScNbhdGerm.univProd`, `IsScSmoothGerm.univProd`), and the
  conjugation to the `ℝⁿ`-extension of the basic germ (`IsConjugateToBasicGerm.paramExtend`,
  unchanged: it is about `g − t₀` on `U`).
* `Polyfold.StrongBundle.regularizing_paramLift`,
  `Polyfold.StrongBundle.IsScFredholmSection.param` (`f̃` is an sc-Fredholm section of `π*P` in the
  germ reading), **`Polyfold.theorem_3_1_21_preprint`** (`F = f̃ + s̃` is one, by `theorem_3_1_18_preprint`) and
  `Polyfold.theorem_3_1_21'` (no paracompactness instance arguments).
* Tame germ data: `StrongBundle.IsScFredholmGermTame.param` (the product chart of a tame chart is
  tame, `PullbackChartData.ofProd_isTame`), `StrongBundle.IsScFredholmSectionTame.param` and
  **`Polyfold.theorem_3_1_21_tame`** (by `theorem_3_1_18_tame`).
* The linearization of `F` in the product chart, which only uses that `f` is an sc-smooth section:
  `scDeriv_paramSection_of_isScSmoothSection` (the proof of `scDeriv_paramSection_wholeChart` with that
  hypothesis), and the germ-reading forms `scDeriv_paramSection`, `linAt_paramSection`,
  `linAt_paramSection_zero` (hypothesis `IsScFredholmSection`).

## What the text leaves implicit, and the choices made

* The product germ `ℝⁿ × G` is unbounded in the `ℝⁿ`-direction on every level, which Definition
  3.1 allows (as for the old whole-chart data `ℝⁿ × U`); the `ℝⁿ`-factor needs no shrinking.
* `scDeriv_paramSection_wholeChart` and its `linAt` forms took an sc-Fredholm section only to know that `f` is
  sc-smooth (the derivative is that of the whole-chart map `F̂ ∘ (1 × r)`, no germ data enter);
  the germ-reading forms are instances of the version for sc-smooth sections.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

section ParamGerm

universe u v

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

namespace StrongBundle

variable {B : StrongBundle PX P} {f : X → Y}

/-- **The germ property of `f̃ = f ∘ π` at `(r₀, x)`, germ reading** (phase 2; the germ form of
`IsScFredholmGermWholeChart.param`, Theorem 3.1.21 (preprint 3.18)'s "readily verified"): if `(f, x)` is an sc-Fredholm germ in
the germ reading (`IsScFredholmGerm`, filling germ `g` on `G_g`, sc⁺-germ `t₀` on `G_{t₀}`), then
so is `(f̃, (r₀, x))`, in the product chart `(r ↦ r − r₀) × φ`: the filling germ `(a, u) ↦ g(u)`
(`PullbackChartData.ofProd_isFillingGerm`, on `ℝⁿ × G_g`), the sc⁺-germ `(a, u) ↦ t₀(u)` on
`ℝⁿ × G_{t₀}`, and `(a, u) ↦ (g − t₀)(u)` conjugated to the `ℝⁿ`-extension of the basic germ of
`g − t₀` (`IsConjugateToBasicGerm.paramExtend`). -/
theorem IsScFredholmGerm.param (hfs : IsSection P f) {x : X} (hg : B.IsScFredholmGerm f x)
    (r₀ : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmGerm
      (paramLift (n := n) f hfs) (r₀, x) := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ⟨Gt, hGtU, ht⟩, ht₀0, hconj⟩ := hg
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set q₀ := paramLift (n := n) f hfs (r₀, x) with hq₀
  have hQ := c.isQuadrantLike
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x hxV
  refine ⟨prod_rn_mem_smoothSet_iff.2 hxs, d.toChart q₀, d.isChart_toChart B _ hc q₀,
    show (r₀, x) ∈ d.ψ.source from ⟨mem_univ _, hxV⟩, ?_, ⟨mem_univ _, h0U⟩,
    fun w => g w.2, fun w => t₀ w.2, ?_,
    ⟨Gt.univProd (Fin n → ℝ), fun w hw => ⟨mem_univ _, hGtU hw.2⟩, ht.univProd hQ⟩, ht₀0, ?_⟩
  · change ((r₀ - r₀, c.φ x) : (Fin n → ℝ) × c.φ.model.E 0) = 0
    rw [sub_self, h0]
    rfl
  · exact PullbackChartData.ofProd_isFillingGerm c r₀ q₀ h0U h0O hfill
  · exact IsConjugateToBasicGerm.paramExtend (Fin n → ℝ) c.relOpen hconj

/-- `f̃` is regularizing when `f` is an sc-Fredholm section in the germ reading (phase 2; the proof
of `regularizing_paramLift_wholeChart`, which uses only that `f` is an sc-smooth regularizing section). -/
theorem regularizing_paramLift (hf : B.IsScFredholmSection f) :
    ∀ m, ∀ z ∈ ((rnPolyfold n).prod PX).levelSet m,
      paramLift (n := n) f hf.isScSmooth.1 z ∈
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).doubleLevel m (m + 1) →
      z ∈ ((rnPolyfold n).prod PX).levelSet (m + 1) := by
  intro m z hz hdl
  rw [prod_rn_mem_levelSet_iff] at hz ⊢
  have hfsec := hf.isScSmooth.1
  refine hf.regularizing m z.2 hz fun c hc hmem => ?_
  have hxV : z.2 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, hfsec z.2] at hmem; exact hmem
  obtain ⟨d, rfl, hzd⟩ := exists_pullbackChartData (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)
    c (z := z) hxV
  have h1 := hdl (d.toChart (paramLift (n := n) f hfsec z)) ⟨d, _, hc, rfl⟩
    (show z ∈ d.ψ.source from hzd)
  refine ⟨?_, h1.2⟩
  rw [d.c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
  exact (PX.mem_levelSet_iff d.c.isChart hxV).1 hz

/-- **`f̃(r, x) = ((r, x), f(x))` is an sc-Fredholm section of `π*P` in the germ reading** (phase 2;
the germ form of `IsScFredholmSectionWholeChart.param`). -/
theorem IsScFredholmSection.param (hf : B.IsScFredholmSection f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSection
      (paramLift (n := n) f hf.isScSmooth.1) where
  isScSmooth := hf.isScSmooth.pullback _
  regularizing := regularizing_paramLift hf
  germ z hz :=
    (hf.germ z.2 (prod_rn_mem_smoothSet_iff.1 hz)).param hf.isScSmooth.1 z.1

end StrongBundle

/-- **Theorem 3.1.21 (preprint 3.18) (parametrized perturbations), germ reading** (phase 2; the germ form of
`theorem_3_1_21_wholeChart`): if `f` is an sc-Fredholm section of `P : Y → X` in the text's germ reading of
Definition 3.1.11 (preprint 3.11) (`IsScFredholmSection`) and `s₁, …, sₙ` are sc⁺-sections of `P`, then
`F(r, x) = f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of `π*P : π*Y → ℝⁿ × X` in the germ
reading: `F = f̃ + s̃` (`paramSection_eq_sectionAdd`), `f̃` is one
(`IsScFredholmSection.param`), `s̃` is sc⁺ (`isScPlusSection_paramComb`), and Theorem 3.1.18 (preprint 3.15) in the
germ reading (`theorem_3_1_18_preprint`) applies. -/
theorem theorem_3_1_21_preprint {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSection f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSection
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  rw [paramSection_eq_sectionAdd]
  exact theorem_3_1_18_preprint hf.param (StrongBundle.isScPlusSection_paramComb hs)

omit [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **Theorem 3.1.21 (preprint 3.18), germ reading, with no instance argument** (phase 2; the germ form of
`theorem_3_1_21'_wholeChart`): the paracompactness of `ℝⁿ × X` and of `π*Y` is supplied by Theorem 2.3.10 (preprint 2.16). -/
theorem theorem_3_1_21' {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSection f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    haveI := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
    haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
      ((rnPolyfold n).prod PX) B
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSection
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  have := MPolyfold.paracompactSpace_prod (rnPolyfold n) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) B
  exact theorem_3_1_21_preprint hf hs

/-! ### Theorem 3.1.21 (preprint 3.18) for tame germ data, germ reading -/

namespace StrongBundle

variable {B : StrongBundle PX P} {f : X → Y}

/-- **The germ property of `f̃` at `(r₀, x)` in a tame chart, germ reading** (phase 2; the germ form
of `IsScFredholmGermTameWholeChart.param`): the data of `IsScFredholmGerm.param` in the product chart of a
tame chart, which is tame (`PullbackChartData.ofProd_isTame`). -/
theorem IsScFredholmGermTame.param (hfs : IsSection P f) {x : X}
    (hg : B.IsScFredholmGermTame f x) (r₀ : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmGermTame
      (paramLift (n := n) f hfs) (r₀, x) := by
  obtain ⟨hxs, c, hct, hxV, h0, h0U, g, t₀, hfill, ⟨Gt, hGtU, ht⟩, ht₀0, hconj⟩ := hg
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set q₀ := paramLift (n := n) f hfs (r₀, x) with hq₀
  have hQ := c.isQuadrantLike
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x hxV
  refine ⟨prod_rn_mem_smoothSet_iff.2 hxs, d.toChart q₀,
    ⟨d.isChart_toChart B _ hct.1 q₀, PullbackChartData.ofProd_isTame c r₀ q₀ hct.2⟩,
    show (r₀, x) ∈ d.ψ.source from ⟨mem_univ _, hxV⟩, ?_, ⟨mem_univ _, h0U⟩,
    fun w => g w.2, fun w => t₀ w.2, ?_,
    ⟨Gt.univProd (Fin n → ℝ), fun w hw => ⟨mem_univ _, hGtU hw.2⟩, ht.univProd hQ⟩, ht₀0, ?_⟩
  · change ((r₀ - r₀, c.φ x) : (Fin n → ℝ) × c.φ.model.E 0) = 0
    rw [sub_self, h0]
    rfl
  · exact PullbackChartData.ofProd_isFillingGerm c r₀ q₀ h0U h0O hfill
  · exact IsConjugateToBasicGerm.paramExtend (Fin n → ℝ) c.relOpen hconj

/-- **`f̃` is an sc-Fredholm section of `π*P` with tame germ data, germ reading** (phase 2; the germ
form of `IsScFredholmSectionTameWholeChart.param`). -/
theorem IsScFredholmSectionTame.param (hf : B.IsScFredholmSectionTame f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTame
      (paramLift (n := n) f hf.isScSmooth.1) where
  toIsScFredholmSection := hf.toIsScFredholmSection.param
  germTame z hz :=
    (hf.germTame z.2 (prod_rn_mem_smoothSet_iff.1 hz)).param hf.isScSmooth.1 z.1

end StrongBundle

/-- **Theorem 3.1.21 (preprint 3.18) for a tame strong bundle, germ reading** (phase 2; the germ form of
`theorem_3_1_21_tame_wholeChart`, Definition 3.6.4 (preprint 3.51)): if `f` is an sc-Fredholm section with tame germ data in the
germ reading (`IsScFredholmSectionTame`) and `s₁, …, sₙ` are sc⁺-sections, then
`F(r, x) = f(x) + Σ rᵢ sᵢ(x)` is one of `π*P` (`IsScFredholmSectionTame.param` and
`theorem_3_1_18_tame`). -/
theorem theorem_3_1_21_tame {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTame
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) := by
  rw [paramSection_eq_sectionAdd]
  exact theorem_3_1_18_tame hf.param (StrongBundle.isScPlusSection_paramComb hs)

/-! ### The linearization of `F` in the product chart, for sc-smooth `f` -/

/-- **The linearization of `F` at the centre of the product chart, for an sc-smooth section `f`**
(phase 2; `scDeriv_paramSection_wholeChart` with the hypothesis it uses: `f` is an sc-smooth section, no germ
data of `f` enter): in the product chart `(r ↦ r − r₀) × Φ` pulled back from a strong bundle chart
`c` with `0 ∈ O`, `D(F̂ ∘ (1 × r))(0)(δa, δu) = D(Ĝ ∘ r)(0) δu + Σ δaᵢ ŝᵢ(0)`,
`Ĝ = f̂ + Σ r₀ᵢ ŝᵢ`. -/
theorem scDeriv_paramSection_of_isScSmoothSection {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScSmoothSection f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (v : (Fin n → ℝ) × c.φ.model.E 0) :
    scDeriv (univ ×ˢ c.U) (((PullbackChartData.ofProd c r₀).toChart q₀).principal
        (paramSection f hf.1 s fun i => (hs i).1) ∘
          StrongRetr.r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
        (0 : (rnSc n |>.prod c.φ.model.E) 1) v =
      scDeriv c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
        StrongRetr.r c.R) (0 : c.φ.model.E 1) v.2 + ∑ i, v.1 i • c.principal (s i) 0 := by
  set d := PullbackChartData.ofProd (n := n) c r₀ with hd
  set c' := d.toChart q₀ with hc'
  set Fs := paramSection f hf.1 s fun i => (hs i).1 with hFs
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hr0 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
  -- the pieces on `U`
  have hfr : IsScSmooth c.U (c.principal f ∘ StrongRetr.r c.R) :=
    (((hf.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU).congr hU fun _ _ => rfl
  have hsr : ∀ i, IsScSmooth c.U (c.principal (s i) ∘ StrongRetr.r c.R) := fun i => by
    have hlift : IsScSmooth (F := c.F.shift) c.U
        fun u => c.principalLift (s i) (StrongRetr.r c.R u) :=
      (((hs i).isScSmoothRetractMap_one hc).comp_isScSmooth
        (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU |>.congr hU
        fun _ _ => rfl
    exact (hlift.toBase_shift hU).congr hU fun u hu => (hs i).toBase_principalLift hc (c.r_mem_O hu)
  have hGr : IsScSmooth c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
      StrongRetr.r c.R) := by
    have hconst : ∀ i, IsScSmooth (F := ScBanach.const ℝ) c.U fun _ => r₀ i := fun i =>
      IsScSmooth.of_contDiffOn_finiteDimensional hU contDiffOn_const
    exact (hfr.add hU (IsScSmooth.finsetSum hU _ fun i _ => (hconst i).smul hU (hsr i))).congr hU
      fun _ _ => rfl
  -- the map `Φ = F̂ ∘ (1 × r)` is sc¹ on `ℝⁿ × U`, and equal there to
  -- `Ψ(a, u) = Ĝ(r(u)) + Σ aᵢ ŝᵢ(r(u))`
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart c' :=
    d.isChart_toChart B _ hc q₀
  have hFsm :
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection Fs := by
    rw [hFs, paramSection_eq_sectionAdd]
    exact (hf.pullback _).sectionAdd (StrongBundle.isScPlusSection_paramComb hs)
  have hΦ : IsScSmooth (univ ×ˢ c.U) (c'.principal Fs ∘ StrongRetr.r c'.R) :=
    (((hFsm.isScSmoothRetractMap hc'B).comp_isScSmooth
      (c'.isRetraction.baseRetraction c'.relOpen) c'.base_retract).snd hU'.isScDomain).congr
      hU'.isScDomain fun _ _ => rfl
  have hΦΨ : ∀ w ∈ (univ ×ˢ c.U : Set ((Fin n → ℝ) × c.φ.model.E 0)),
      (c'.principal Fs ∘ StrongRetr.r c'.R) w =
        ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘ StrongRetr.r c.R) w.2 +
          ∑ i, w.1 i • (c.principal (s i) ∘ StrongRetr.r c.R) w.2 := by
    intro w hw
    have hrw : StrongRetr.r c.R w.2 ∈ c.φ.model.O := c.r_mem_O hw.2
    have := PullbackChartData.ofProd_principal_paramSection c r₀ q₀ hf.1
      (fun i => (hs i).1) (w := (w.1, StrongRetr.r c.R w.2)) hrw
    refine this.trans ?_
    simp only [Function.comp_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  -- the derivative on level `1`
  have h01 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ univ ×ˢ c.U
    rw [map_zero]
    exact ⟨mem_univ _, h0U⟩
  set D := scDeriv c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
    StrongRetr.r c.R) (0 : c.φ.model.E 1) with hD
  set L : (Fin n → ℝ) × c.φ.model.E 0 →L[ℝ] c.F 0 :=
    D.comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)) +
      ∑ i, ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c.φ.model.E 0))).smulRight
          (c.principal (s i) 0) with hL
  have hmaps : MapsTo (Prod.snd : (Fin n → ℝ) × c.φ.model.E 1 → c.φ.model.E 1)
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (c.φ.model.E.lvlSet c.U 1) := by
    intro w hw
    have := hw
    rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase] at this
    exact this.2
  have hb : ∀ w : (rnSc n |>.prod c.φ.model.E) 1,
      (rnSc n |>.prod c.φ.model.E).toBase 1 w = (w.1, c.φ.model.E.toBase 1 w.2) := fun w => by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  have hderG := (hGr.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).comp
    (0 : (rnSc n |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
  have hderS : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivWithinAt
      (fun w : (rnSc n |>.prod c.φ.model.E) 1 =>
        w.1 i • ((c.principal (s i) ∘ StrongRetr.r c.R) ∘ c.φ.model.E.toBase 1) w.2)
      ((0 : (rnSc n |>.prod c.φ.model.E) 1).1 i •
          ((scDeriv c.U (c.principal (s i) ∘ StrongRetr.r c.R) 0).comp (c.φ.model.E.toBase 1)).comp
            (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 1)) +
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
          (c.φ.model.E 1))).smulRight
          (((c.principal (s i) ∘ StrongRetr.r c.R) ∘ c.φ.model.E.toBase 1)
            (0 : (rnSc n |>.prod c.φ.model.E) 1).2))
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 := by
    intro i _
    have h1 : HasFDerivWithinAt (fun w : (rnSc n |>.prod c.φ.model.E) 1 => w.1 i)
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
          (c.φ.model.E 1))) ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 :=
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
        (c.φ.model.E 1))).hasFDerivWithinAt
    have h2 := ((hsr i).isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).comp
      (0 : (rnSc n |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
    exact h1.fun_smul h2
  have hderΨ := hderG.add (HasFDerivWithinAt.fun_sum hderS)
  have hderΦ : HasFDerivWithinAt ((c'.principal Fs ∘ StrongRetr.r c'.R) ∘
      (rnSc n |>.prod c.φ.model.E).toBase 1) (L.comp ((rnSc n |>.prod c.φ.model.E).toBase 1))
      ((rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) 0 := by
    refine (hderΨ.congr (fun w hw => ?_) ?_).congr_fderiv ?_
    · have := hΦΨ _ hw
      rw [hb] at this
      exact this
    · have := hΦΨ _ h0'
      rw [hb] at this
      exact this
    · refine ContinuousLinearMap.ext fun w => ?_
      simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
        Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_smul, zero_add, map_zero, hr0, hL, hb]
      rfl
  have hderΦ' := hΦ.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h0'
  have heq := ContinuousLinearMap.ext_of_comp_toBase_one (E := rnSc n |>.prod c.φ.model.E)
    ((hU'.isScDomain.uniqueDiffWithinAt 1 0 h0').eq hderΦ' hderΦ)
  have hv := congrArg (fun T : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ] c.F 0 => T v) heq
  refine hv.trans ?_
  simp only [hL, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]

/-- **The linearization of `F` at the centre of the product chart, germ reading** (phase 2; the
germ form of `scDeriv_paramSection_wholeChart`, used for transversality after Theorem 3.1.22 (preprint 3.19)):
`D(F̂ ∘ (1 × r))(0)(δa, δu) = D(Ĝ ∘ r)(0) δu + Σ δaᵢ ŝᵢ(0)`, `Ĝ = f̂ + Σ r₀ᵢ ŝᵢ`, for `f` an
sc-Fredholm section in the germ reading (only its sc-smoothness is used). -/
theorem scDeriv_paramSection {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScFredholmSection f) {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    (r₀ : Fin n → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (v : (Fin n → ℝ) × c.φ.model.E 0) :
    scDeriv (univ ×ˢ c.U) (((PullbackChartData.ofProd c r₀).toChart q₀).principal
        (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) ∘
          StrongRetr.r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
        (0 : (rnSc n |>.prod c.φ.model.E) 1) v =
      scDeriv c.U ((fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) ∘
        StrongRetr.r c.R) (0 : c.φ.model.E 1) v.2 + ∑ i, v.1 i • c.principal (s i) 0 :=
  scDeriv_paramSection_of_isScSmoothSection hf.isScSmooth hs hc h0O r₀ q₀ v

/-- **The linearization of `F` at the centre `(r₀, x)` of the product chart, in the chart form
`linAt`, germ reading** (phase 2; the germ form of `linAt_paramSection_wholeChart`): on `T₀(ℝⁿ × O)`,
`Lin_F(0)(δa, δu) = Lin_G(0) δu + Σ δaᵢ ŝᵢ(0)` with `G = f + Σ r₀ᵢ sᵢ`. -/
theorem linAt_paramSection {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScFredholmSection f)
    {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i)) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (r₀ : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {w : (Fin n → ℝ) × c.φ.model.E 0}
    (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c r₀).toChart q₀).U
      (StrongRetr.r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
      (0 : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 1))) :
    linAt ((PullbackChartData.ofProd c r₀).toChart q₀).U
        ((PullbackChartData.ofProd c r₀).toChart q₀).R
        (((PullbackChartData.ofProd c r₀).toChart q₀).principal
          (paramSection f hf.isScSmooth.1 s fun i => (hs i).1)) 0 ⟨w, hw⟩ =
      linAt c.U c.R (fun u => c.principal f u + ∑ i, r₀ i • c.principal (s i) u) 0
          ⟨w.2, PullbackChartData.ofProd_mem_tangent c r₀ q₀
            (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)) hw⟩ +
        ∑ i, w.1 i • c.principal (s i) 0 :=
  scDeriv_paramSection hf hs hc h0O r₀ q₀ w

/-- **The text's form, germ reading** (phase 2; the germ form of `linAt_paramSection_zero_wholeChart`, after
Theorem 3.1.22 (preprint 3.19)): at `r₀ = 0` the linearization of `F` at `(0, x)` is
`(δr, ξ) ↦ f'(x)ξ + Σ δrᵢ sᵢ(x)`, in the chart form
`Lin_F(0)(δa, δu) = Lin_f(0) δu + Σ δaᵢ ŝᵢ(0)`. -/
theorem linAt_paramSection_zero {B : StrongBundle PX P} {f : X → Y}
    (hf : B.IsScFredholmSection f) {s : Fin n → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {w : (Fin n → ℝ) × c.φ.model.E 0}
    (hw : w ∈ rangeS (scDeriv ((PullbackChartData.ofProd c 0).toChart q₀).U
      (StrongRetr.r ((PullbackChartData.ofProd c 0).toChart q₀).R)
      (0 : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E 1))) :
    linAt ((PullbackChartData.ofProd c 0).toChart q₀).U
        ((PullbackChartData.ofProd c 0).toChart q₀).R
        (((PullbackChartData.ofProd c 0).toChart q₀).principal
          (paramSection f hf.isScSmooth.1 s fun i => (hs i).1)) 0 ⟨w, hw⟩ =
      linAt c.U c.R (c.principal f) 0
          ⟨w.2, PullbackChartData.ofProd_mem_tangent c 0 q₀
            (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)) hw⟩ +
        ∑ i, w.1 i • c.principal (s i) 0 := by
  rw [linAt_paramSection hf hs hc h0O 0 q₀ hw]
  have : (fun u => c.principal f u + ∑ i, (0 : Fin n → ℝ) i • c.principal (s i) u) =
      c.principal f := funext fun u => by simp
  simp only [this]
  rfl

end ParamGerm

end Polyfold
