import Polyfold.Chapter6.Propagation
import Polyfold.Chapter6.ParamKernel
import Polyfold.Chapter6.StabilizationContinuity
import Polyfold.Chapter6.Lemma629

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–223: **Lemma 6.30** in the form used for the push-forward: with property (P), the
stabilized kernels `L_t` along the family form a continuous family *(book 2017: Lemma 6.13; see
`BookConcordance.md`)*.

# The stabilized kernels exist

## What is formalized

* `exists_isStabKernels`: for an sc-smooth `Φ : ℝⁿ → X` with `Φ([0, 1]ⁿ)` in the domain of a chart
  `c`, an sc⁺-section `S` of `π*P` with `f̃ + S = 0` along `Φ` near `[0, 1]ⁿ`, and sc⁺-sections
  `s₁, …, s_k` with property (P) near `[0, 1]ⁿ`, the stabilized kernels form a continuous family
  over `[0, 1]ⁿ` (`IsStabKernels`), for the slices `S(q, ·)`, `sᵢ(q, ·)`.

## Reading

The proof: Lemma 6.30's family of tangent spaces of the solution set
(`exists_subspaceFamily_linKer`, from the implicit function theorem), cut by `{dt = 0}`
(`exists_inf_ker`, onto by `fderiv_mem_linKer` along the curve of zeros), identified with
`ker(T_q ⊕ φ_q)` in the product chart (`exists_sliceKernel`), and moved to `E₀ × ℝᵏ`
(`SubspaceFamily.exists_map`).
-/

open Topology Set

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- A constant map `ℝᵐ → ℝⁿ` is an sc-smooth map of the M-polyfolds `ℝᵐ → ℝⁿ`. -/
private theorem isScSmoothMap_rn_const' {m m' : ℕ} (b : Fin m' → ℝ) :
    (rnPolyfold m).IsScSmoothMap (rnPolyfold m') fun _ => b := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart m 0, rnChart m' 0, univ,
    isChart_rnChart 0, isChart_rnChart 0, isOpen_univ, mem_univ x, subset_univ _,
    mapsTo_univ _ _, ?_⟩
  have himg : rnChart m 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc m) univ univ (rnSc m') univ univ (fun _ => b - 0)
  exact isScSmoothRetractMap_const_of_contDiff (V := Fin m → ℝ) (V' := Fin m' → ℝ) contDiff_const

/-- **A continuous level-`1` lift of an sc-smooth map read in a chart**: for an sc-smooth
`Φ : ℝⁿ → X` and a chart `φ`, `q ↦ φ(Φ(q))` lifts continuously to level `1` on `Φ⁻¹(dom φ)`. -/
theorem exists_continuousOn_lift_chart {n : ℕ} {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {φ : MChart X} (hφ : PX.IsChart φ) :
    ∃ z : (Fin n → ℝ) → φ.model.E 1, ContinuousOn z (Φ ⁻¹' φ.source) ∧
      ∀ q ∈ Φ ⁻¹' φ.source, φ.model.E.toBase 1 (z q) = φ (Φ q) := by
  have hΦc : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  set V₀ := Φ ⁻¹' φ.source
  have hV₀o : IsOpen V₀ := φ.isOpen_source.preimage hΦc
  have hrel : IsRelOpenInQuadrant (rnSc n) univ V₀ :=
    ⟨isPartialQuadrant_univ _, V₀, hV₀o, (inter_univ _).symm⟩
  set H : (Fin n → ℝ) → φ.model.E 0 := fun q => φ (Φ q)
  have h1 := hΦ.smooth (rnChart n 0) φ (isChart_rnChart 0) hφ V₀ hV₀o
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun _ hq => hq)
  have himg : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) '' V₀ = V₀ := by
    have : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) = id :=
      funext fun q => by rw [rnChart_apply, sub_zero]; rfl
    rw [this]; exact image_id V₀
  have hH : IsScSmooth (E := rnSc n) (F := φ.model.E) V₀ H := by
    have := h1.comp_isScSmooth (ScRetraction.id hrel) (by rw [himg]; exact image_id _)
    refine this.congr hrel.isScDomain fun q _ => ?_
    change φ (Φ ((rnChart n 0).symm q)) = φ (Φ q)
    rw [rnChart_symm_apply, add_zero]
  have h0 : IsSc0 (rnSc n) φ.model.E V₀ H := hH.isSc1.isSc0
  refine ⟨fun q => levelMap (E := rnSc n) H 1 q, ?_, fun q hq => ?_⟩
  · have := h0.continuousOn 1
    rw [ScBanach.lvlSet_const] at this
    exact this
  · have hq1 : (q : (rnSc n) 1) ∈ (rnSc n).lvlSet V₀ 1 := by
      rw [ScBanach.lvlSet_const]; exact hq
    rw [h0.toBase_levelMap hq1, ScBanach.const_toBase]

/-- **The stabilized kernels along `Φ` form a continuous family** (Lemma 6.30). -/
theorem exists_isStabKernels (hf : B.IsScFredholmSectionTame f) {n : ℕ}
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hΦc : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ c.φ.source)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    {k : ℕ} {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    ∃ Λ : SubspaceFamily (Icc (0 : Fin n → ℝ) 1) (c.φ.model.E 0 × (Fin k → ℝ)),
      IsStabKernels f c hc (fun q : Icc (0 : Fin n → ℝ) 1 => Φ q) (fun q => hΦc q q.2)
        (fun q => pullbackSlice S q) (fun i q => pullbackSlice (s i) q) Λ := by
  have hfs := hf.isScSmooth
  have hΦcont : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  -- the sections `G = f̃ + S` and `F = G + Σ λᵢ sᵢ`
  have hGt : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTame
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) :=
    theorem_3_15_tame hf.param hS
  have hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) := hGt.isScSmooth
  have hgt : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((rnPolyfold n).prod PX))).IsScFredholmSectionTame
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S)
          hG.1 s fun i => (hs i).1) :=
    theorem_3_18_tame hGt hs
  have hslice : ∀ q : Fin n → ℝ,
      pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) q =
        sectionAdd P f (pullbackSlice S q) := fun q =>
    pullbackSlice_sectionAdd_paramLift hfs.1 hS.1 q
  -- the zeros along `Φ`
  have hz0 : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) (q', Φ q') := fun q hq =>
    hz.filter_mono (nhds_le_nhdsSet hq)
  have hF0 : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ᶠ q' in 𝓝 q, IsZeroAt
      (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S)
          hG.1 s fun i => (hs i).1) ((0 : Fin k → ℝ), (q', Φ q')) := fun q hq =>
    (hz0 q hq).mono fun q' h => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice _ hG.1 s (fun i => (hs i).1) 0) (q', Φ q')
      rw [paramSlice_zero]
      exact h
  -- the product chart `χ = (λ ↦ λ) × ((q ↦ q) × φ)`
  obtain ⟨q₀⟩ : Nonempty (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) := ⟨S (0, Φ 0)⟩
  obtain ⟨q₁⟩ : Nonempty (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :=
    ⟨paramSection _ hG.1 s (fun i => (hs i).1) (0, (0, Φ 0))⟩
  set cZ := (PullbackChartData.ofProd c 0).toChart q₀
  set χ := (PullbackChartData.ofProd cZ 0).toChart q₁
  have hcZc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart cZ :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart χ :=
    (PullbackChartData.ofProd cZ 0).isChart_toChart _ _ hcZc q₁
  -- the continuous level-`1` lift
  obtain ⟨z, hzc, hzy⟩ := exists_continuousOn_lift_chart hΦ c.isChart
  -- the parameter space
  have : Nonempty (Icc (0 : Fin n → ℝ) 1) := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  have : PreconnectedSpace (Icc (0 : Fin n → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hzQ : Continuous fun q : Icc (0 : Fin n → ℝ) 1 => z q :=
    hzc.comp_continuous continuous_subtype_val fun q => hΦc q q.2
  have hsrc : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ((0 : Fin k → ℝ), (q, Φ q)) ∈ χ.φ.source :=
    fun q hq => ⟨mem_univ _, mem_univ _, hΦc q hq⟩
  have hz' : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, χ.φ.model.E.toBase 1 ((0, (q, z q)) : χ.φ.model.E 1) =
      χ.φ ((0 : Fin k → ℝ), (q, Φ q)) := by
    intro q hq
    change ((rnSc k).prod ((rnSc n).prod c.φ.model.E)).toBase 1 (0, (q, z q)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      hzy q (hΦc q hq), sub_zero, sub_zero]
  have hzz : Continuous fun q : Icc (0 : Fin n → ℝ) 1 =>
      ((0, ((q : Fin n → ℝ), z q)) : χ.φ.model.E 1) :=
    continuous_const.prodMk (continuous_subtype_val.prodMk hzQ)
  have hy : Continuous fun q : Icc (0 : Fin n → ℝ) 1 =>
      ((0 : Fin k → ℝ), ((q : Fin n → ℝ), Φ q)) :=
    continuous_const.prodMk (continuous_subtype_val.prodMk (hΦcont.comp continuous_subtype_val))
  -- Lemma 6.30: the kernels `ker Lin_F(0, (q, z_q))`
  obtain ⟨Λ₀, hΛ₀⟩ := exists_subspaceFamily_linKer hgt hχc _ hy (fun q => hsrc q q.2)
    (fun q => (hF0 q q.2).self_of_nhds)
    (fun q => (hP.self_of_nhdsSet q q.2).isGoodPositionGermTame hgt (hF0 q q.2).self_of_nhds)
    _ hzz (fun q => hz' q q.2)
  -- the `ℝⁿ`-directions: `ℓ(λ, (σ, v)) = σ` maps `ker Lin_F` onto `ℝⁿ`
  have hΓ : (rnPolyfold n).IsScSmoothMap ((rnPolyfold k).prod ((rnPolyfold n).prod PX))
      (fun q' => ((0 : Fin k → ℝ), (q', Φ q'))) :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_const' 0)
      (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ)
  have hℓ : ∀ q, (Λ₀.L q).map (sliceProj k n (c.φ.model.E 0)).toLinearMap = ⊤ := by
    intro q
    refine eq_top_iff.2 fun σ _ => ?_
    obtain ⟨hd, hmem⟩ := fderiv_mem_linKer hgt.isScSmooth hχc hΓ (hsrc q q.2) (hF0 q q.2) _
      (hz' q q.2) σ
    refine ⟨fderiv ℝ (fun q' => χ.φ ((0 : Fin k → ℝ), (q', Φ q'))) (q : Fin n → ℝ) σ,
      (hΛ₀ q).symm ▸ hmem, ?_⟩
    have hd' : HasFDerivAt (fun q' : Fin n → ℝ => (((0 : Fin k → ℝ) - 0, (q' - 0, c.φ (Φ q'))) :
        (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)))
        (fderiv ℝ (fun q' => χ.φ ((0 : Fin k → ℝ), (q', Φ q'))) (q : Fin n → ℝ) :
          (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) (q : Fin n → ℝ) :=
      hd.hasFDerivAt
    have := hd'.snd.fst.unique ((hasFDerivAt_id (q : Fin n → ℝ)).sub_const 0)
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) this
  obtain ⟨Λ₁, hΛ₁⟩ := Λ₀.exists_inf_ker (sliceProj k n (c.φ.model.E 0)) hℓ
  -- moving to `E₀ × ℝᵏ` by `(λ, (σ, v)) ↦ (v, λ)`
  set M : χ.φ.model.E 0 →L[ℝ] c.φ.model.E 0 × (Fin k → ℝ) :=
    (((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)).comp
      (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin n → ℝ) × c.φ.model.E 0))).prod
      (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ((Fin n → ℝ) × c.φ.model.E 0)) :
        (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0) →L[ℝ] c.φ.model.E 0 × (Fin k → ℝ))
  have hinj : ∀ q, InjOn M (Λ₁.L q) := by
    intro q w hw w' hw' h
    rw [hΛ₁] at hw hw'
    have h1 : w.2.1 = 0 := LinearMap.mem_ker.1 hw.2
    have h2 : w'.2.1 = 0 := LinearMap.mem_ker.1 hw'.2
    have h3 : w.2.2 = w'.2.2 := congrArg Prod.fst h
    have h4 : w.1 = w'.1 := congrArg Prod.snd h
    exact Prod.ext h4 (Prod.ext (h1.trans h2.symm) h3)
  obtain ⟨Λ, hΛ⟩ := Λ₁.exists_map (fun _ => M) (M.continuous.comp continuous_snd) hinj
  refine ⟨Λ, fun q => hS.pullbackSlice q, fun q => ?_, fun i q => (hs i).1.pullbackSlice q,
    fun q => ⟨z q, hzy q (hΦc q q.2)⟩, ?_⟩
  · -- `(f + S(q, ·))(Φ(q)) = 0`
    have h := (isZeroAt_pullback_iff_pullbackSlice hG.1 q (Φ q)).1 (hz0 q q.2).self_of_nhds
    rw [hslice] at h
    exact h
  · -- the stabilized kernels, read at an arbitrary lift
    intro q x hx hxc z₁ hz₁ T hT φ hφ
    subst hx
    obtain rfl : z₁ = z q :=
      c.φ.model.E.toBase_injective 1 (hz₁.trans (hzy q (hΦc q q.2)).symm)
    have hT' : ∀ v, (T v : c.F 0) = linAt c.U c.R (c.principal (pullbackSlice
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) q)) (z q) v := fun v => by
      rw [hslice]; exact hT v
    have hsurj := surjective_coprod_of_isLinSurjAt hG hs (chartPt c hc hxc (z q) hz₁) q hΦ rfl
      (hz0 q q.2) (hP.self_of_nhdsSet q q.2).isLinSurjAt T hT' φ hφ
    have hker : χ.linKer (paramSection (sectionAdd (pullbackProj P Prod.snd)
          (paramLift f hfs.1) S) hG.1 s fun i => (hs i).1)
          ((0, ((q : Fin n → ℝ), z q)) : χ.φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k n (c.φ.model.E 0)).toLinearMap =
        (LinearMap.ker (T.coprod φ).toLinearMap).map
          (sliceIncl k n (chartPt c hc hxc (z q) hz₁).T).toLinearMap :=
      linKer_inf_ker_sliceProj_eq_map hG hs (chartPt c hc hxc (z q) hz₁) q₀ q₁ q T hT' φ hφ
    refine ⟨hsurj, ?_⟩
    rw [hΛ q, hΛ₁ q, hΛ₀ q, hker]
    ext w
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩

end Polyfold
