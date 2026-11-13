import Polyfold.Chapter6.GapP1_CubeGerms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.1, Theorem 3.1.21
(p. 89; preprint Theorem 3.18) and §6.6 (p. 264): **the pull-back of an sc-Fredholm section to
`[0, 1]ⁿ × X` is a tame sc-Fredholm section**, the input of Lemmas 6.6.4–6.6.5 for families on
`[0, 1]ⁿ` (gap G.65 (a), steps 3–4).

# `f̃(q, x) = ((q, x), f(x))` over `[0, 1]ⁿ × X`

## The text, paraphrased

(p. 264) For an sc-Fredholm section `f` and `s(y, t)` an sc⁺-section over `X × [0, 1]`, the
section `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` over `[0, 1] × X × ℝᵏ` is sc-Fredholm.
This rests on Theorem 3.1.21's "readily verified" statement for the pull-back `f̃` of `f`, here
with the parameter space `[0, 1]ⁿ`, which has boundary and corners.

## What is formalized

* `cubeProdData q₁ c`: the product chart `χ_{q₁} × φ_c` of `[0, 1]ⁿ × X` with `χ_{q₁}` the chart
  centred at `q₁` (`UnitCube.cChart`) and the retraction `id × r_c`
  (`PullbackChartData.ofProdChart`).
* `cubeProd_isFillingGerm`: a filling germ `g` of `f̂` in `c` gives the filling germ
  `(a, u) ↦ g(u)` on `O_χ × G` (quadrant `C_χ × C`) in the product chart;
  `cubeProd_isTame`: the product chart of a tame chart is tame.
* `IsScFredholmGermTame.paramCube`, `regularizing_cubeLift` and
  **`IsScFredholmSectionTame.paramCube`**: `f̃(q, x) = ((q, x), f(x))` is an sc-Fredholm section
  of `pr₂*P` over `[0, 1]ⁿ × X` with tame germ data; the conjugation to a basic germ is
  `IsConjugateToBasicGerm.quadExtend` (parameter quadrant `C̃ × C_χ`).
* **`theorem_3_1_21_tame_cube`**: `F(λ, (q, x)) = G(q, x) + Σ λᵢ sᵢ(q, x)` for `G = f̃ + S`, `S`
  and `sᵢ` sc⁺-sections over `[0, 1]ⁿ × X`, is an sc-Fredholm section with tame germ data
  (Theorems 3.1.18 and 3.1.21).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube

section CubeFredholm

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The pulled-back section `f̃(q, x) = ((q, x), f(x))` of `pr₂*P` over `[0, 1]ⁿ × X`. -/
abbrev cubeLift (f : X → Y) (hf : IsSection P f) :
    (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X) :=
  pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf z.2

/-- **The product chart centred at `(q₁, ·)`**: `χ_{q₁} × φ_c` with the retraction `id × r_c`. -/
abbrev cubeProdData (q₁ : Fin n → unitInterval) (c : StrongBundleChart PX P) :
    PullbackChartData PX P ((cubePolyfold n).prod PX) Prod.snd :=
  PullbackChartData.ofProdChart (isChart_cChart q₁) (cRetr q₁) (cRetr_retract q₁) c

omit [T2Space Y] [ParacompactSpace Y] in
/-- **The filling germ in the product chart over `[0, 1]ⁿ`** (the `[0, 1]ⁿ` form of
`PullbackChartData.ofProd_isFillingGerm`): if `g` fills `f̂` in `c`, then `(a, u) ↦ g(u)`, an
sc-smooth germ on `O_χ × G` (quadrant `C_χ × C`), fills `(a, u) ↦ f̂(u)` in the product chart:
`ker D(id × r)(0) = 0 × ker Dr(0)` and `ρ'(0) = ρ(0)`. -/
theorem cubeProd_isFillingGerm (q₁ : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    {fb g : c.φ.model.E 0 → c.F 0} (hfill : IsFillingGerm c.relOpen c.isRetraction h0U fb g) :
    IsFillingGerm ((cubeProdData q₁ c).toChart q₀).relOpen
      ((cubeProdData q₁ c).toChart q₀).isRetraction
      (show (0 : (cubeProdData q₁ c).ψ.model.E 0) ∈ ((cubeProdData q₁ c).toChart q₀).U from
        ⟨zero_mem_cChart_O q₁, h0U⟩)
      (fun w => fb w.2) (fun w => g w.2) := by
  have hO0 := zero_mem_cChart_O q₁
  have h0U' : (0 : ((cubeProdData q₁ c).toChart q₀).φ.model.E 0) ∈
      ((cubeProdData q₁ c).toChart q₀).U := ⟨hO0, h0U⟩
  set c' := (cubeProdData q₁ c).toChart q₀ with hc'
  have hrelχ := cChart_relOpen q₁
  have hQ := c.relOpen.isPartialQuadrant.isQuadrantLike
  have hQΛ := hrelχ.isPartialQuadrant.isQuadrantLike
  have ht : Tendsto (fun w : (rnSc n |>.prod c.φ.model.E) 0 => w.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' _ _ rfl
  have hrr : ∀ u ∈ c.U, StrongRetr.r c.R (StrongRetr.r c.R u) = StrongRetr.r c.R u :=
    fun u hu => StrongRetr.r_r c.isRetraction hu
  let g' : c'.φ.model.E 0 → c'.F 0 := fun w => g w.2
  -- the fill defect in the product chart is the pull-back of the fill defect along `pr₂`
  have heq : EqOn (fillDefect c.R g ∘ (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0))
      (fillDefect c'.R g') ((cChart q₁).model.O ×ˢ c.U) := by
    intro y hy
    change g y.2 - (c.R (StrongRetr.r c.R y.2, g y.2)).2 =
      g y.2 - (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
    rw [hrr y.2 hy.2, c.φ.apply_symm_apply (c.r_mem_O hy.2)]
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet ((cChart q₁).model.O ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ (cChart q₁).model.O ×ˢ c.U
    rw [map_zero]
    exact ⟨hO0, h0U⟩
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ht.eventually hfill.eq_on] with w hw hwO
    obtain ⟨v, hv, rfl⟩ := hwO
    exact hw ⟨v.2, hv.2, rfl⟩
  · filter_upwards [ht.eventually hfill.mem_of_fixed] with y hy hyU hfix
    change g y.2 = (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
      at hfix
    rw [hrr y.2 hyU.2, c.φ.apply_symm_apply (c.r_mem_O hyU.2)] at hfix
    obtain ⟨u, hu, hru⟩ := hy hyU.2 hfix
    exact ⟨(y.1, u), ⟨hyU.1, hu⟩, Prod.ext rfl hru⟩
  · obtain ⟨G, hGU, hg, Dk, hDk, hΦex⟩ := hfill.germ
    refine ⟨G.quadProd hrelχ hO0, fun w hw => ⟨hw.1, hGU hw.2⟩, hg.quadProd hrelχ hO0 hQΛ hQ,
      fun x => (Dk x.2).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)), ?_, ?_⟩
    · exact (hDk.quadProd hrelχ hO0 hQ).congr fun w hw => heq ⟨hw.1, hGU hw.2⟩
    set D := scDeriv c.U (StrongRetr.r c.R) (0 : c.φ.model.E 1) with hDdef
    -- `D(id × r)(0) = id × Dr(0)`
    let D' : (Fin n → ℝ) × c.φ.model.E 0 →L[ℝ] (Fin n → ℝ) × c.φ.model.E 0 :=
      scDeriv c'.U (StrongRetr.r c'.R) (0 : c'.φ.model.E 1)
    have hDv : ∀ v : (Fin n → ℝ) × c.φ.model.E 0, D' v = (v.1, D v.2) := by
      intro v
      have h1 := scDeriv_prodMap (F := rnSc n) (F' := c.φ.model.E) hrelχ c.relOpen
        (isScSmooth_id hrelχ.isScDomain)
        (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
      have e := congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ]
        (rnSc n |>.prod c.φ.model.E) 0 => L v) h1
      have h2 : scDeriv (E := rnSc n) (F := rnSc n) (cChart q₁).model.O id (0 : (rnSc n) 1) =
          ContinuousLinearMap.id ℝ (Fin n → ℝ) :=
        IsSc1.scDeriv_eqOn (isSc1With_id _) (hrelχ.isScDomain.uniqueDiffWithinAt 1)
          (by
            change (ScBanach.const (Fin n → ℝ)).toBase 1 (0 : Fin n → ℝ) ∈
              ((cChart q₁).model.O : Set (Fin n → ℝ))
            rw [ScBanach.const_toBase]; exact hO0)
      refine e.trans (Prod.ext ?_ rfl)
      exact congrArg (fun L : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => L v.1) h2
    -- `ρ'(0) = ρ(0)`
    have hr0 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
    let ρ' : c.F 0 →L[ℝ] c.F 0 := StrongRetr.ρCLM c'.isRetraction h0U'
    have hρ0 : ∀ h : c.F 0, ρ' h = StrongRetr.ρCLM c.isRetraction h0U h := by
      intro h
      change (c.R (c.φ (c.φ.symm (StrongRetr.r c.R 0)), h)).2 = (c.R (0, h)).2
      rw [hr0, c.φ.apply_symm_apply h0O]
    let e₁ : LinearMap.ker (D' : (Fin n → ℝ) × c.φ.model.E 0 →ₗ[ℝ] (Fin n → ℝ) × c.φ.model.E 0)
        ≃L[ℝ] LinearMap.ker (D : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) :=
      { toFun := fun v => ⟨(v : (Fin n → ℝ) × c.φ.model.E 0).2, by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact LinearMap.mem_ker.2 (congrArg Prod.snd h)⟩
        invFun := fun u => ⟨((0 : Fin n → ℝ), (u : c.φ.model.E 0)), by
          refine LinearMap.mem_ker.2 ?_
          change D' ((0 : Fin n → ℝ), (u : c.φ.model.E 0)) = 0
          rw [hDv]
          exact Prod.ext rfl (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact Subtype.ext (Prod.ext (congrArg Prod.fst h).symm rfl)
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 (continuous_snd.comp continuous_subtype_val)
        continuous_invFun :=
          continuous_induced_rng.2 (continuous_const.prodMk continuous_subtype_val) }
    let e₂ : LinearMap.ker ((StrongRetr.ρCLM c.isRetraction h0U : c.F 0 →L[ℝ] c.F 0) :
          c.F 0 →ₗ[ℝ] c.F 0) ≃L[ℝ] LinearMap.ker (ρ' : c.F 0 →ₗ[ℝ] c.F 0) :=
      { toFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).trans (LinearMap.mem_ker.1 u.2)⟩
        invFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).symm.trans (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
        continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }
    obtain ⟨Φ, hΦ⟩ := hΦex
    refine ⟨e₁.trans (Φ.trans e₂), fun v => ?_⟩
    exact (hΦ (e₁ v)).trans rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- **The product chart of a tame chart is tame** over `[0, 1]ⁿ`: the base retraction `id × r`,
with the identity of the relatively open model of `χ_{q₁}` tame (`cRetr_isTame`) and
`ScRetraction.IsTameWith.prod`. -/
theorem cubeProd_isTame (q₁ : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (hc : (c.isRetraction.baseRetraction c.relOpen).IsTame) :
    (((cubeProdData q₁ c).toChart q₀).isRetraction.baseRetraction
      ((cubeProdData q₁ c).toChart q₀).relOpen).IsTame := by
  obtain ⟨n₁, W₁, T₁, hT₁⟩ := (cChart_relOpen q₁).isPartialQuadrant
  obtain ⟨n₂, W₂, T₂, hT₂⟩ := c.relOpen.isPartialQuadrant
  have h := ScRetraction.IsTameWith.prod hT₁ hT₂ (cRetr_isTame q₁ n₁ W₁ T₁ hT₁) (hc n₂ W₂ T₂ hT₂)
  exact h.isTame (prod_eq_prodPresentation T₁ T₂ hT₁ hT₂)

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
  {B : StrongBundle PX P} {f : X → Y}

namespace StrongBundle

/-- **The germ property of `f̃` at `(q₁, x)` over `[0, 1]ⁿ`, in a tame chart** (the `[0, 1]ⁿ`
form of `IsScFredholmGermTame.param`): in the product chart `χ_{q₁} × φ_c` of a tame chart `c`
at `x`, the filling germ `(a, u) ↦ g(u)` on `O_χ × G`, the sc⁺-germ `(a, u) ↦ t₀(u)` on
`O_χ × G_{t₀}`, and the conjugation of `(a, u) ↦ (g − t₀)(u)` to the `(ℝⁿ, C_χ)`-extension of
the basic germ (`IsConjugateToBasicGerm.quadExtend`). -/
theorem IsScFredholmGermTame.paramCube (hfs : IsSection P f) {x : X}
    (hg : B.IsScFredholmGermTame f x) (q₁ : Fin n → unitInterval) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScFredholmGermTame
      (cubeLift f hfs) (q₁, x) := by
  obtain ⟨hxs, c, hct, hxV, h0, h0U, g, t₀, hfill, ⟨Gt, hGtU, ht⟩, ht₀0, hconj⟩ := hg
  set d := cubeProdData q₁ c with hd
  set q₀ := cubeLift f hfs (q₁, x) with hq₀
  have hQ := c.isQuadrantLike
  have hrelχ := cChart_relOpen q₁
  have hQΛ := hrelχ.isPartialQuadrant.isQuadrantLike
  have hO0 := zero_mem_cChart_O q₁
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x hxV
  refine ⟨prod_cube_mem_smoothSet_iff.2 hxs, d.toChart q₀,
    ⟨d.isChart_toChart B _ hct.1 q₀, cubeProd_isTame q₁ c q₀ hct.2⟩,
    show (q₁, x) ∈ d.ψ.source from ⟨mem_cChart q₁, hxV⟩, ?_, ⟨hO0, h0U⟩,
    fun w => g w.2, fun w => t₀ w.2, ?_,
    ⟨Gt.quadProd hrelχ hO0, fun w hw => ⟨hw.1, hGtU hw.2⟩, ht.quadProd hrelχ hO0 hQΛ hQ⟩,
    ht₀0, ?_⟩
  · change ((cChart q₁ q₁, c.φ x) : (Fin n → ℝ) × c.φ.model.E 0) = 0
    rw [cChart_self, h0]
    rfl
  · exact cubeProd_isFillingGerm q₁ c q₀ h0U h0O hfill
  · exact IsConjugateToBasicGerm.quadExtend hrelχ hO0 c.relOpen hconj

/-- `f̃` is regularizing over `[0, 1]ⁿ × X` when `f` is (the proof of `regularizing_paramLift`
with `prod_cube_mem_levelSet_iff`). -/
theorem regularizing_cubeLift (hf : B.IsScFredholmSection f) :
    ∀ m, ∀ z ∈ ((cubePolyfold n).prod PX).levelSet m,
      cubeLift f hf.isScSmooth.1 z ∈
        (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).doubleLevel m (m + 1) →
      z ∈ ((cubePolyfold n).prod PX).levelSet (m + 1) := by
  intro m z hz hdl
  rw [prod_cube_mem_levelSet_iff] at hz ⊢
  have hfsec := hf.isScSmooth.1
  refine hf.regularizing m z.2 hz fun c hc hmem => ?_
  have hxV : z.2 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, hfsec z.2] at hmem; exact hmem
  obtain ⟨d, rfl, hzd⟩ := exists_pullbackChartData
    (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX) c (z := z) hxV
  have h1 := hdl (d.toChart (cubeLift f hfsec z)) ⟨d, _, hc, rfl⟩
    (show z ∈ d.ψ.source from hzd)
  refine ⟨?_, h1.2⟩
  rw [d.c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
  exact (PX.mem_levelSet_iff d.c.isChart hxV).1 hz

/-- **`f̃(q, x) = ((q, x), f(x))` is an sc-Fredholm section of `pr₂*P` over `[0, 1]ⁿ × X` with
tame germ data** (Theorem 3.1.21's "readily verified" step for the parameter space `[0, 1]ⁿ`). -/
theorem IsScFredholmSectionTame.paramCube (hf : B.IsScFredholmSectionTame f) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScFredholmSectionTame
      (cubeLift f hf.isScSmooth.1) where
  isScSmooth := hf.isScSmooth.pullback _
  regularizing := regularizing_cubeLift hf.toIsScFredholmSection
  germ z hz := ((hf.germTame z.2 (prod_cube_mem_smoothSet_iff.1 hz)).paramCube
    hf.isScSmooth.1 z.1).isScFredholmGerm
  germTame z hz :=
    (hf.germTame z.2 (prod_cube_mem_smoothSet_iff.1 hz)).paramCube hf.isScSmooth.1 z.1

end StrongBundle

end CubeFredholm

end Polyfold
