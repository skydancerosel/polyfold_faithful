import Polyfold.Chapter6.GapP1_CubeBoundaryP

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30): **`π : S → [0, 1]` is a submersion, at boundary points of the
parameter space**.  Gap G.65; row V6.34.

# `π : S → [0, 1]ⁿ` as a submersion in the corner sense

## The text, paraphrased

The solution set `S` of `F = 0` near the points `(t, φ(t), 0)` is a manifold with boundary with
corners; "it follows from property (P)" that `π : S → [0, 1]`, `(t, y, λ) ↦ t`, is a submersion,
and the fibres `S_t = π⁻¹(t)` are manifolds with boundary with corners.  At `t ∈ {0, 1}` the
fibre `S_t` is part of the boundary of `S`.

## What is formalized

The parameter space is `[0, 1]ⁿ` (`cubePolyfold n`), the points are `(0, (q, Φ(q)))` for
**every** `q ∈ [0, 1]ⁿ`, and the chart is `χ = (λ ↦ λ) × (χ_q × φ_c)` for a strong bundle chart `c`
centred at `Φ(q)`.

* `exists_stabCubeCurveDeriv`: the derivative of the curve of zeros `q' ↦ (0, (q', Φ(q')))` in
  `χ` is a linear `D : ℝⁿ → ℝᵏ × ℝⁿ × E₀` with `D σ ∈ ker F'`, `dπ(D σ) = σ`, and `D σ` in the
  reduced tangent space of `ℝᵏ × [0, 1]ⁿ × X` when `σ` is in that of `[0, 1]ⁿ`.
* `submersion_cube_of_isGeneralPositionGerm` (any tame `F` vanishing along the curve) and
  **`lemma_6_6_5_submersion_cube`** (`F` of the text): if `F` is in general position at
  `(0, (q, Φ(q)))` (by `lemma_6_6_4_propertyP_cube`, equivalently (P) at `q`, through
  `isGeneralPositionGerm_cubeSlice_iff`), there is an open `V ∋ (0, (q, Φ(q)))`
  such that in `χ` the tangent space of `S ∩ V` at the point is `ker F'` (Theorem 3.6.8), and
  `dπ = sliceProj : (λ, (σ, v)) ↦ σ`
  - maps `T S = ker F'` onto `ℝⁿ` (`π` is a submersion), and
  - maps `T S ∩ T^R` **onto** the reduced tangent space `E_0(q)` of `[0, 1]ⁿ` at `q` (and
    `T^R` into it): `π` is a submersion of the faces, the corner sense of a submersion.  The
    directions leaving the boundary of `[0, 1]ⁿ` are tangent to `S` but not to its face through
    the point, as in the text's picture of `S_0`, `S_1` as boundary parts of `S`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube

section CubeSubmersion

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P} {f : X → Y} {k : ℕ}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]

/-- The chart `(λ ↦ λ) × (χ_q × φ_c)` of the pull-back bundle over `ℝᵏ × ([0, 1]ⁿ × X)`. -/
abbrev stabCubePC (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)) :
    StrongBundleChart ((rnPolyfold k).prod ((cubePolyfold n).prod PX))
      (pullbackProj (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
        (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)) :=
  (PullbackChartData.ofProd (cubePC q c q₀) 0).toChart q₁

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))] in
/-- The reduced tangent space of `ℝᵏ × C_{χ_q} × C` at `0` is `ℝᵏ × E_0(q) × E_0`. -/
lemma mem_minimalSubspaceWith_stabCubeProd {E W Wχ : ScBanach} {nχ m : ℕ}
    (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (T : ScIso E ((ScBanach.const (Fin m → ℝ)).prod W))
    (w : (Fin k → ℝ) × ((Fin n → ℝ) × E 0)) :
    w ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
        (0 : (Fin k → ℝ) × ((Fin n → ℝ) × E 0)) ↔
      w.2.1 ∈ minimalSubspaceWith Tχ 0 ∧ w.2.2 ∈ minimalSubspaceWith T 0 := by
  rw [minimalSubspaceWith_prodPresentation, Submodule.mem_prod]
  change w.1 ∈ minimalSubspaceWith (rnPres k) (0 : Fin k → ℝ) ∧
    w.2 ∈ minimalSubspaceWith (prodPresentation Tχ T) (0 : (Fin n → ℝ) × E 0) ↔ _
  rw [minimalSubspaceWith_rnPres, mem_minimalSubspaceWith_cubeProd Tχ T w.2]
  simp only [Submodule.mem_top, true_and]

/-- **The curve of zeros `q' ↦ (0, (q', Φ(q')))` in the chart `(λ ↦ λ) × (χ_q × φ_c)`**: its
derivative `D` at `0` (within a relatively open subset of the partial quadrant of `χ_q`) has
`D σ ∈ ker Lin_F(0)` and `dπ(D σ) = σ` for every `σ ∈ ℝⁿ`, and `D σ` lies in the reduced tangent
space `ℝᵏ × E_0(q) × E_0(Φ(q))` for `σ ∈ E_0(q)`. -/
theorem exists_stabCubeCurveDeriv
    {F : (Fin k → ℝ) × ((Fin n → unitInterval) × X) →
      pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
        (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)}
    (hF : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((cubePolyfold n).prod PX))).IsScSmoothSection F)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ) {q : Fin n → unitInterval}
    (hyV : Φ q ∈ c.φ.source) (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ q', IsZeroAt (pullbackProj (pullbackProj P
      (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd) F ((0 : Fin k → ℝ), (q', Φ q')))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hTχ : (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0)
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0) :
    ∃ D : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0),
      (∀ σ, D σ ∈ (stabCubePC q c q₀ q₁).linKer F 0) ∧
      (∀ σ, sliceProj k n (c.φ.model.E 0) (D σ) = σ) ∧
      ∀ σ ∈ minimalSubspaceWith Tχ 0,
        D σ ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
          (0 : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) := by
  have hΓ : (cubePolyfold n).IsScSmoothMap ((rnPolyfold k).prod ((cubePolyfold n).prod PX))
      (fun q' => ((0 : Fin k → ℝ), (q', Φ q'))) :=
    MPolyfold.IsScSmoothOn.prodMk
      ((isScSmoothMap_rn_rn_of_contDiff (m := n) (n := k) contDiff_const).comp isScSmoothMap_val)
      (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ)
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsChart
      (cubePC q c q₀) := (cubeProdData q c).isChart_toChart B _ hc q₀
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((cubePolyfold n).prod PX))).IsChart
      (stabCubePC q c q₀ q₁) :=
    (PullbackChartData.ofProd (cubePC q c q₀) 0).isChart_toChart _ _ hpcc q₁
  have hsrc : ((0 : Fin k → ℝ), (q, Φ q)) ∈ (stabCubePC q c q₀ q₁).φ.source :=
    ⟨mem_univ _, mem_cChart q, hyV⟩
  have hz : (stabCubePC q c q₀ q₁).φ.model.E.toBase 1 (0 : (stabCubePC q c q₀ q₁).φ.model.E 1) =
      (stabCubePC q c q₀ q₁).φ ((0 : Fin k → ℝ), (q, Φ q)) := by
    rw [map_zero]
    exact (Prod.ext (sub_self _) (cubePC_apply_eq_zero q c q₀ hφ0)).symm
  obtain ⟨V₀, hrel, h0V, hVO, hVsrc, D, hD, hker⟩ :=
    exists_hasFDerivWithinAt_cubeCurve hF hχc hΓ q hsrc h0 0 hz
  have hu := uniqueDiffWithinAt_rnRel hrel h0V
  have hπ : (sliceProj k n (c.φ.model.E 0)).comp D = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    have d1 := (sliceProj k n (c.φ.model.E 0)).hasFDerivAt.comp_hasFDerivWithinAt
      (0 : Fin n → ℝ) hD
    have d2 : HasFDerivWithinAt
        ((sliceProj k n (c.φ.model.E 0)) ∘
          fun v => (stabCubePC q c q₀ q₁).φ
            ((0 : Fin k → ℝ), ((cChart q).symm v, Φ ((cChart q).symm v))))
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) V₀ 0 := by
      refine (hasFDerivWithinAt_id (0 : Fin n → ℝ) V₀).congr (fun v hv => ?_) ?_
      · change (cChart q) ((cChart q).symm v) = v
        exact (cChart q).apply_symm_apply (hVO hv)
      · change (cChart q) ((cChart q).symm 0) = 0
        exact (cChart q).apply_symm_apply (hVO h0V)
    exact hu.eq d1 d2
  have hπσ : ∀ σ, sliceProj k n (c.φ.model.E 0) (D σ) = σ := fun σ =>
    congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) hπ
  refine ⟨D, hker, hπσ, fun σ hσ => ?_⟩
  refine (mem_minimalSubspaceWith_stabCubeProd Tχ T (D σ)).2 ⟨?_, ?_⟩
  · have : (D σ).2.1 = σ := hπσ σ
    rw [this]; exact hσ
  · set L : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0) →L[ℝ] c.φ.model.E 0 :=
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)).comp
        (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin n → ℝ) × c.φ.model.E 0)) with hL
    have hDX : HasFDerivWithinAt (fun v => c.φ (Φ ((cChart q).symm v))) (L.comp D) V₀ 0 :=
      L.hasFDerivAt.comp_hasFDerivWithinAt (0 : Fin n → ℝ) hD
    have h00 : c.φ (Φ ((cChart q).symm 0)) = 0 := by rw [cChart_symm_zero]; exact hφ0
    exact mem_minimalSubspaceWith_of_hasFDerivWithinAt hrel h0V Tχ hTχ T hT
      (fun v hv => c.φ.apply_mem_C (hVsrc v hv).2.2) h00 hDX hσ

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))] in
/-- In the chart `(λ ↦ λ) × (χ_q × φ_c)` with `c` centred at `Φ(q)`, the point `(0, (q, Φ(q)))`
is read as `0`. -/
lemma stabCubePC_toBase_zero (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    {Φ : (Fin n → unitInterval) → X} (hφ0 : c.φ (Φ q) = 0)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)) :
    (stabCubePC q c q₀ q₁).φ.model.E.toBase 1 (0 : (stabCubePC q c q₀ q₁).φ.model.E 1) =
      (stabCubePC q c q₀ q₁).φ ((0 : Fin k → ℝ), (q, Φ q)) := by
  rw [map_zero]
  exact (Prod.ext (sub_self _) (cubePC_apply_eq_zero q c q₀ hφ0)).symm

/-- **`π` is a submersion in the corner sense at `(0, (q, Φ(q)))`, `q ∈ [0, 1]ⁿ`, for a section
`F` over `ℝᵏ × ([0, 1]ⁿ × X)`** which is tame sc-Fredholm, vanishes along `q' ↦ (0, (q', Φ(q')))`
and is in general position (Definition 5.3.9) at `(0, (q, Φ(q)))`.  There is an open
`V ∋ (0, (q, Φ(q)))` such that for every chart `c` centred at `Φ(q)` and the chart
`χ = (λ ↦ λ) × (χ_q × φ_c)`:
* the tangent space at `0` of `χ(G ∩ S ∩ V)` (`G` open, on which it is a retract) is `ker F'(0)`;
* `dπ = sliceProj` maps `ker F'(0)` onto `ℝⁿ`;
* for presentations `Tχ` of `C_{χ_q}` and `T` of `C_c`, `dπ` maps `ker F'(0) ∩ T^R` onto the
  reduced tangent space `E_0(q)` of `[0, 1]ⁿ` at `q`, and maps `T^R` into `E_0(q)`. -/
theorem submersion_cube_of_isGeneralPositionGerm
    {F : (Fin k → ℝ) × ((Fin n → unitInterval) × X) →
      pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
        (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X)}
    (hFt : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((cubePolyfold n).prod PX))).IsScFredholmSectionTame F)
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    (h0 : ∀ q', IsZeroAt (pullbackProj (pullbackProj P
      (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd) F ((0 : Fin k → ℝ), (q', Φ q')))
    (q : Fin n → unitInterval)
    (hgp : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((cubePolyfold n).prod PX))).IsGeneralPositionGerm F (0, (q, Φ q))) :
    ∃ V : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X)), IsOpen V ∧
      ((0 : Fin k → ℝ), (q, Φ q)) ∈ V ∧
      ∀ (c : StrongBundleChart PX P), B.IsChart c → Φ q ∈ c.φ.source → c.φ (Φ q) = 0 →
      ∀ (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
        (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))
        (G : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X))), IsOpen G →
        G ⊆ (stabCubePC q c q₀ q₁).φ.source → ((0 : Fin k → ℝ), (q, Φ q)) ∈ G →
        IsScRetract (stabCubePC q c q₀ q₁).φ.model.E (stabCubePC q c q₀ q₁).φ.model.C
          ((stabCubePC q c q₀ q₁).φ '' (G ∩ (solutionSet (pullbackProj (pullbackProj P
            (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd) F ∩ V))) →
        tangentSpace (stabCubePC q c q₀ q₁).φ.model.E (stabCubePC q c q₀ q₁).φ.model.C
            ((stabCubePC q c q₀ q₁).φ '' (G ∩ (solutionSet (pullbackProj (pullbackProj P
              (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd) F ∩ V)))
            (0 : (stabCubePC q c q₀ q₁).φ.model.E 1) =
          (stabCubePC q c q₀ q₁).linKer F 0 ∧
        (∀ σ : Fin n → ℝ, ∃ w ∈ (stabCubePC q c q₀ q₁).linKer F 0,
          sliceProj k n (c.φ.model.E 0) w = σ) ∧
        ∀ {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ)),
          (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0 →
        ∀ {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq)),
          c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0 →
          (∀ σ ∈ minimalSubspaceWith Tχ 0, ∃ w ∈ (stabCubePC q c q₀ q₁).linKer F 0,
            w ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
              (0 : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) ∧
            sliceProj k n (c.φ.model.E 0) w = σ) ∧
          ∀ w ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
              (0 : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)),
            sliceProj k n (c.φ.model.E 0) w ∈ minimalSubspaceWith Tχ 0 := by
  have hq0 := h0 q
  obtain ⟨V, hVo, hqV, -, hT⟩ := exists_tangentSpace_eq_linKer hFt
    (hgp.isGoodPositionGermTame hFt hq0) hq0
  refine ⟨V, hVo, hqV, fun c hc hyc hφ0 q₀ q₁ G hGo hGc hqG hR => ⟨?_, fun σ => ?_,
    fun {_ _} Tχ hTχ {_ _} T hTc => ⟨fun σ hσ => ?_, fun w hw => ?_⟩⟩⟩
  · have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsChart
        (cubePC q c q₀) := (cubeProdData q c).isChart_toChart B _ hc q₀
    have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((cubePolyfold n).prod PX))).IsChart
        (stabCubePC q c q₀ q₁) :=
      (PullbackChartData.ofProd (cubePC q c q₀) 0).isChart_toChart _ _ hpcc q₁
    exact hT _ hqV hq0 _ hχc ⟨mem_univ _, mem_cChart q, hyc⟩ G hGo hGc hqG hR _
      (stabCubePC_toBase_zero q c hφ0 q₀ q₁)
  · obtain ⟨m, Wq, T, hT'⟩ := c.φ.model.isPartialQuadrant
    obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cChart_relOpen q).isPartialQuadrant
    obtain ⟨D, hD, hπ, -⟩ :=
      exists_stabCubeCurveDeriv hFt.isScSmooth hc hΦ hyc hφ0 h0 q₀ q₁ Tχ hTχ T hT'
    exact ⟨D σ, hD σ, hπ σ⟩
  · obtain ⟨D, hD, hπ, hR'⟩ :=
      exists_stabCubeCurveDeriv hFt.isScSmooth hc hΦ hyc hφ0 h0 q₀ q₁ Tχ hTχ T hTc
    exact ⟨D σ, hD σ, hR' σ hσ, hπ σ⟩
  · exact ((mem_minimalSubspaceWith_stabCubeProd Tχ T w).1 hw).1

/-- **2021 Lemma 6.6.5 (p. 265): `π : S → [0, 1]ⁿ` is a submersion at every point
`(0, (q, Φ(q)))`, `q ∈ [0, 1]ⁿ`, boundary points included** (preprint Lemma 6.30), in the corner
sense of `submersion_cube_of_isGeneralPositionGerm`: for `F = paramSection` of `f̃ + S` and
`s₁, …, s_k` vanishing along `q ↦ (q, Φ(q))` and in general position at `(0, (q, Φ(q)))` (which
`lemma_6_6_4_propertyP_cube` provides at every `q`), in the chart `(λ ↦ λ) × (χ_q × φ_c)` the
tangent space of `S` at the point is `ker F'`, `dπ` maps it onto `ℝⁿ`, and it maps
`ker F' ∩ T^R` onto the reduced tangent space of `[0, 1]ⁿ` at `q`. -/
theorem lemma_6_6_5_submersion_cube (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i))
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    (hz : ∀ q', IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q', Φ q'))
    (q : Fin n → unitInterval)
    (hgp : ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∃ V : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X)), IsOpen V ∧
      ((0 : Fin k → ℝ), (q, Φ q)) ∈ V ∧
      ∀ (c : StrongBundleChart PX P), B.IsChart c → Φ q ∈ c.φ.source → c.φ (Φ q) = 0 →
      ∀ (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
        (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))
        (G : Set ((Fin k → ℝ) × ((Fin n → unitInterval) × X))), IsOpen G →
        G ⊆ (stabCubePC q c q₀ q₁).φ.source → ((0 : Fin k → ℝ), (q, Φ q)) ∈ G →
        IsScRetract (stabCubePC q c q₀ q₁).φ.model.E (stabCubePC q c q₀ q₁).φ.model.C
          ((stabCubePC q c q₀ q₁).φ '' (G ∩ (solutionSet (pullbackProj (pullbackProj P
            (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
            (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V))) →
        tangentSpace (stabCubePC q c q₀ q₁).φ.model.E (stabCubePC q c q₀ q₁).φ.model.C
            ((stabCubePC q c q₀ q₁).φ '' (G ∩ (solutionSet (pullbackProj (pullbackProj P
              (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd)
            (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) ∩ V)))
            (0 : (stabCubePC q c q₀ q₁).φ.model.E 1) =
          (stabCubePC q c q₀ q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) 0 ∧
        (∀ σ : Fin n → ℝ, ∃ w ∈ (stabCubePC q c q₀ q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) 0,
          sliceProj k n (c.φ.model.E 0) w = σ) ∧
        ∀ {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ)),
          (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0 →
        ∀ {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq)),
          c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0 →
          (∀ σ ∈ minimalSubspaceWith Tχ 0, ∃ w ∈ (stabCubePC q c q₀ q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd)
              (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) 0,
            w ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
              (0 : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) ∧
            sliceProj k n (c.φ.model.E 0) w = σ) ∧
          ∀ w ∈ minimalSubspaceWith (prodPresentation (rnPres k) (prodPresentation Tχ T))
              (0 : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)),
            sliceProj k n (c.φ.model.E 0) w ∈ minimalSubspaceWith Tχ 0 :=
  submersion_cube_of_isGeneralPositionGerm (theorem_3_1_21_tame_cube hf hS hs) hΦ
    (fun q' => isZeroAt_stab_cube _ (fun i => (hs i).1) (hz q')) q hgp

end CubeSubmersion

end Polyfold
