import Polyfold.Chapter6.SolutionManifoldFamily2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.4**
(p. 264; preprint Lemma 6.29, p. 222): **property (P)** for the slices `F_t`.  Gap G.63, row V6.33.

# Property (P) of Lemma 6.6.4 for the slices

## The text, paraphrased

For sc⁺-sections `s₁, …, s_k`, `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` and its slices
`F_t(y, λ) = F(t, y, λ)`.  (P): for every `t ∈ [0, 1]` the slice `F_t` is in general position to
the boundary of `X × ℝᵏ` at `(φ(t), 0)`.  Lemma 6.6.4 asserts that finitely many `sᵢ` with (P)
exist; the paragraph after it derives the general position of `F` at the points `(t, φ(t), 0)`.

## What is formalized

The setting is that of `lemma_6_6_4`: `t ∈ [0, 1]` is `q ∈ ℝⁿ` near `[0, 1]ⁿ` (decision D2),
`G = f̃ + S` is the text's `f − s` (a section of `π*P → ℝⁿ × X`), and
`F(λ, (q, y)) = G(q, y) + Σ λᵢ sᵢ(q, y)` is `paramSection`.  The slice `F_q` is the section
`(λ, y) ↦ G(q, y) + Σ λᵢ sᵢ(q, y)` of the pull-back of `P` to `ℝᵏ × X`, i.e. `paramSection` of
the slices `G(q, ·) = f + S(q, ·)` and `sᵢ(q, ·)` (`pullbackSlice`).

* `isParamGP_slice_of_isParamGP` (**the chart computation**): in a tame chart `c` centred at
  `Φ(q)` and the product chart `(r ↦ r − q) × c`, properties (i)–(ii) of the proof of Theorem
  5.3.10 for `G` and the `sᵢ` at `(q, Φ(q))` give (i)–(ii) for the slice `G(q, ·)` and the
  `sᵢ(q, ·)` at `Φ(q)`.  The `ℝⁿ`-directions are absorbed by the derivative of the curve of zeros
  `q' ↦ (q', Φ(q'))`, which lies in `ker G'` (`fderiv_mem_linKer`), and its `X`-component lies in
  the reduced tangent space: every corner coordinate of `φ ∘ Φ` is `≥ 0` near `q` and vanishes at
  `q`, so its derivative vanishes (`fderiv_mem_minimalSubspaceWith_of_centre`; `ℝⁿ` has no
  boundary).
* `isGeneralPositionGerm_slice` (**(P) at one point**): if `F` is in general position at
  `(0, (q, Φ(q)))` and `G(q', Φ(q')) = 0` near `q`, the slice `F_q` is in general position
  (Definition 5.3.9) at `(0, Φ(q))`.
* **`lemma_6_6_4_propertyP`** (**Lemma 6.6.4 as printed**, under the hypotheses of
  `lemma_6_6_4`): there are finitely many sc⁺-sections `s₁, …, s_k` such that for all `q` near
  `[0, 1]ⁿ` the slice `F_q` is in general position at `(0, Φ(q))` (property (P)) and `F` is in
  general position at `(0, (q, Φ(q)))` (the paragraph after the lemma).
* `isZeroAt_paramSection_iff_slice`: `F(λ, (q, y)) = 0` iff `F_q(λ, y) = 0`, so the zero set of
  `F_q` is the fibre `S_q` of the solution set of `F` over `q`.
* `isScFredholmSectionTame_slice` and **`lemma_6_6_5_fibre_isManifold`** (Lemma 6.6.5, the fibres
  `S_t`): given (P), for `q` near `[0, 1]ⁿ` the fibre `S_q` near `(0, Φ(q))` is a Mathlib manifold
  with boundary and corners (`theorem_3_1_26_isManifold` for `F_q`).
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle

section SliceP

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The corner coordinates of a family through the centre of a chart have zero derivative**
(`ℝⁿ` has no boundary): for a chart `c` centred at `Φ(q)` and a presentation `T` of its partial
quadrant, `q' ↦ (T(φ(Φ(q'))))ᵢ` is `≥ 0` near `q` and vanishes at `q`, so its derivative at `q`
vanishes; hence the derivative of `φ ∘ Φ` at `q` lies in the minimal subspace `E_0`. -/
theorem fderiv_mem_minimalSubspaceWith_of_centre (c : StrongBundleChart PX P)
    {Φ : (Fin n → ℝ) → X} (hΦc : Continuous Φ) {q : Fin n → ℝ} (hq : Φ q ∈ c.φ.source)
    (hφ0 : c.φ (Φ q) = 0) {m : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0)
    {D : (Fin n → ℝ) →L[ℝ] c.φ.model.E 0} (hD : HasFDerivAt (fun q' => c.φ (Φ q')) D q)
    (σ : Fin n → ℝ) : D σ ∈ minimalSubspaceWith T 0 := by
  rw [mem_minimalSubspaceWith]
  intro i _
  set L : c.φ.model.E 0 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Wq 0)).comp
      (T 0 : c.φ.model.E 0 →L[ℝ] (Fin m → ℝ) × Wq 0)) with hL
  have hLD : HasFDerivAt (fun q' => L (c.φ (Φ q'))) (L.comp D) q := L.hasFDerivAt.comp q hD
  have hmin : IsLocalMin (fun q' => L (c.φ (Φ q'))) q := by
    have hsrc : ∀ᶠ q' in 𝓝 q, Φ q' ∈ c.φ.source :=
      hΦc.continuousAt.preimage_mem_nhds (c.φ.isOpen_source.mem_nhds hq)
    filter_upwards [hsrc] with q' hq'
    have hC : c.φ (Φ q') ∈ c.φ.model.C := c.φ.apply_mem_C hq'
    rw [hT] at hC
    have h0 : L (c.φ (Φ q)) = 0 := by rw [hφ0, map_zero]
    rw [h0]
    exact hC i
  have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A σ) (hmin.hasFDerivAt_eq_zero hLD)
  exact this

/-- The product chart `(r ↦ r − q) × c` of the pull-back `π*P → ℝⁿ × X` at the parameter `q`. -/
abbrev slicePC (c : StrongBundleChart PX P) (q : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :
    StrongBundleChart ((rnPolyfold n).prod PX) (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) :=
  (PullbackChartData.ofProd c q).toChart q₀

/-- **The curve of zeros `q' ↦ (q', Φ(q'))` in the product chart centred at `(q, Φ(q))`**: with
`D` the derivative at `q` of its reading `q' ↦ (q' − q, φ(Φ(q')))`, every `D σ` lies in
`ker Lin_G(0)`, has `ℝⁿ`-component `σ`, and `snd ∘ D` is the derivative of `φ ∘ Φ`. -/
theorem curve_slicePC {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} (hyV : Φ q ∈ c.φ.source)
    (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :
    HasFDerivAt (fun q' => c.φ (Φ q'))
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)).comp
        (fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q)) q ∧
      ∀ σ : Fin n → ℝ,
        fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q σ ∈
          (slicePC c q q₀).linKer G 0 ∧
        (fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q σ :
          (Fin n → ℝ) × c.φ.model.E 0).1 = σ := by
  set pc := slicePC c q q₀ with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart pc :=
    (PullbackChartData.ofProd c q).isChart_toChart B _ hc q₀
  have hΓ : (rnPolyfold n).IsScSmoothMap ((rnPolyfold n).prod PX) (fun q' => (q', Φ q')) :=
    MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ
  have hsrc : (q, Φ q) ∈ pc.φ.source := ⟨mem_univ _, hyV⟩
  have hz' : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) = pc.φ (q, Φ q) := by
    rw [map_zero, ofProd_apply_eq_zero c q q₀ hφ0]
  have hker := fun σ => fderiv_mem_linKer hG hpcc hΓ hsrc h0 0 hz' σ
  have hd : HasFDerivAt (fun q' : Fin n → ℝ => ((q' - q, c.φ (Φ q')) :
      (Fin n → ℝ) × c.φ.model.E 0))
      (fderiv ℝ (fun q' => pc.φ (q', Φ q')) q :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × c.φ.model.E 0) q :=
    (hker 0).1.hasFDerivAt
  refine ⟨hd.snd, fun σ => ⟨(hker σ).2, ?_⟩⟩
  have := hd.fst.unique ((hasFDerivAt_id q).sub_const q)
  exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) this

/-- **The linearization of `G` in the product chart, through the slice**: at the centre of the
product chart `(r ↦ r − q) × c` (`c` centred at `Φ(q)`), every tangent vector `u = (σ, v)` has
`Lin_G(0) u = Lin_{G(q, ·)}(0)(v − δσ)`, where `δσ` is the `X`-component of the derivative of the
curve of zeros (`curve_slicePC`): subtract that derivative, which lies in `ker Lin_G(0)` and has
`ℝⁿ`-component `σ`, and apply `linAt_ofProd_slice`. -/
theorem linAt_slicePC_eq
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} (hyV : Φ q ∈ c.φ.source)
    (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (u : ↥(rangeS (scDeriv (slicePC c q q₀).U (r (slicePC c q q₀).R)
      (0 : (slicePC c q q₀).φ.model.E 1)))) :
    ∃ hv : (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 -
        (fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q
          (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1 : (Fin n → ℝ) × c.φ.model.E 0).2 ∈
        rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)),
      linAt (slicePC c q q₀).U (slicePC c q q₀).R ((slicePC c q q₀).principal G) 0 u =
        linAt c.U c.R (c.principal (pullbackSlice G q)) 0 ⟨_, hv⟩ := by
  obtain ⟨-, hcur⟩ := curve_slicePC hG hc hΦ hyV hφ0 h0 q₀
  set D := fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q with hD
  obtain ⟨hwk, hw1⟩ := hcur (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1
  obtain ⟨hwr, hw0⟩ := ((slicePC c q q₀).mem_linKer_iff G 0 _).1 hwk
  set w : ↥(rangeS (scDeriv (slicePC c q q₀).U (r (slicePC c q q₀).R)
      (0 : (slicePC c q q₀).φ.model.E 1))) := ⟨_, hwr⟩ with hw
  set d := u - w with hd
  have hd1 : (d.1 : (Fin n → ℝ) × c.φ.model.E 0).1 = 0 := by
    exact sub_eq_zero.2 hw1.symm
  have key := StrongBundle.linAt_ofProd_slice hG hc q q₀ h0U d hd1
  have hu : u = d + w := (sub_add_cancel u w).symm
  refine ⟨by exact PullbackChartData.ofProd_mem_tangent c q q₀ h0U d.2, ?_⟩
  have e1 : linAt (slicePC c q q₀).U (slicePC c q q₀).R ((slicePC c q q₀).principal G) 0 u =
      linAt (slicePC c q q₀).U (slicePC c q q₀).R ((slicePC c q q₀).principal G) 0 d := by
    conv_lhs => rw [hu]
    rw [map_add, hw0, add_zero]
  rw [e1, key]
  rfl

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- The principal part of a section of `π*P` at the centre of the product chart `(r ↦ r − q) × c`
is that of its slice at `q` in `c`. -/
lemma principal_slicePC_zero (c : StrongBundleChart PX P) (q : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (S' : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :
    (slicePC c q q₀).principal S' 0 = c.principal (pullbackSlice S' q) 0 := by
  change (c (S' ((0 : Fin n → ℝ) + q, c.φ.symm 0)).1.2).2 = (c (S' (q, c.φ.symm 0)).1.2).2
  rw [zero_add]

/-- **Properties (i)–(ii) pass to the slice** (the chart computation behind property (P)): let
`c` be a chart centred at `Φ(q)` with presentation `T`, `G` an sc-smooth section of `π*P` vanishing
along `q' ↦ (q', Φ(q'))` near `q`, and `s₁, …, s_k` sections of `π*P`.  If (i)–(ii) of the proof
of Theorem 5.3.10 hold for `G` and the `sᵢ` in the product chart `(r ↦ r − q) × c` (presentation
`ℝⁿ × T`), they hold for the slice `G(q, ·)` and the `sᵢ(q, ·)` in `c`.  A tangent vector
`(σ, v)` is replaced by `v − δσ` (`linAt_slicePC_eq`); `δσ` lies in `E_0`
(`fderiv_mem_minimalSubspaceWith_of_centre`), so the transversality (ii) survives. -/
theorem isParamGP_slice_of_isParamGP {k : ℕ}
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} (hyV : Φ q ∈ c.φ.source)
    (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {m : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0)
    (h : (slicePC c q q₀).IsParamGP G s (prodPresentation (rnPres n) T)) :
    c.IsParamGP (pullbackSlice G q) (fun i => pullbackSlice (s i) q) T := by
  have hΦc : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  obtain ⟨hδ, -⟩ := curve_slicePC hG hc hΦ hyV hφ0 h0 q₀
  have hpr : ∀ i, (slicePC c q q₀).principal (s i) 0 = c.principal (pullbackSlice (s i) q) 0 :=
    fun i => principal_slicePC_zero c q q₀ (s i)
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · -- (i)
    have hk : ((0 : (slicePC c q q₀).φ.model.E 0), k') ∈ (slicePC c q q₀).K :=
      (mem_K_ofProd_zero_iff c q q₀ h0O k').2 hk'
    obtain ⟨u, a, hua⟩ := h.1 k' hk
    obtain ⟨hv, hl⟩ := linAt_slicePC_eq hG hc hΦ hyV hφ0 h0 q₀ h0U u
    refine ⟨⟨_, hv⟩, a, ?_⟩
    rw [← hl]
    refine Eq.trans ?_ hua
    simp only [hpr]
    rfl
  · -- (ii)
    have hu0 : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0U
    have hlift : (((0 : Fin n → ℝ), (w : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (slicePC c q q₀).U (r (slicePC c q q₀).R)
          (0 : (slicePC c q q₀).φ.model.E 1)) :=
      (PullbackChartData.ofProd_mem_tangent_iff c q q₀ 0 hu0 _).2 w.2
    obtain ⟨u, a, hua, hmin⟩ := h.2 ⟨_, hlift⟩
    obtain ⟨hv, hl⟩ := linAt_slicePC_eq hG hc hΦ hyV hφ0 h0 q₀ h0U u
    refine ⟨⟨_, hv⟩, a, ?_, ?_⟩
    · rw [← hl]
      refine Eq.trans ?_ hua
      simp only [hpr]
      rfl
    · change ((((0 : Fin n → ℝ), (w : c.φ.model.E 0)) : ((rnSc n).prod c.φ.model.E) 0) -
          (show ((rnSc n).prod c.φ.model.E) 0 from u.1)) ∈
          minimalSubspaceWith (prodPresentation (rnPres n) T)
            (0 : ((rnSc n).prod c.φ.model.E) 0) at hmin
      rw [minimalSubspaceWith_prodPresentation] at hmin
      have hm2 := (Submodule.mem_prod.1 hmin).2
      have hc2 := fderiv_mem_minimalSubspaceWith_of_centre c hΦc hyV hφ0 T hT hδ
        (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1
      have hm2' : (w : c.φ.model.E 0) - (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 ∈
          minimalSubspaceWith T 0 := hm2
      have := add_mem hm2' hc2
      convert this using 1
      change (w : c.φ.model.E 0) - ((u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 - _) =
        ((w : c.φ.model.E 0) - (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2) + _
      abel

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- The slice at `q` of `G + Σ λᵢ sᵢ` is `G(q, ·) + Σ λᵢ sᵢ(q, ·)`. -/
lemma pullbackSlice_paramSlice {k : ℕ}
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, IsSection (pullbackProj P Prod.snd) (s i)) (lam : Fin k → ℝ) (q : Fin n → ℝ) :
    pullbackSlice (paramSlice G hG s hs lam) q =
      paramSlice (pullbackSlice G q) (hG.pullbackSlice q) (fun i => pullbackSlice (s i) q)
        (fun i => (hs i).pullbackSlice q) lam := by
  funext x
  set e := pullbackFiberEquiv P (Prod.snd : (Fin n → ℝ) × X → X) (q, x) with he
  let eA : (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X) ⁻¹' {(q, x)}) →+ (P ⁻¹' {x}) :=
    AddMonoidHom.mk' e (pullbackFiberEquiv_add P _ (q, x))
  have h1 : e ⟨G (q, x), hG (q, x)⟩ = ⟨pullbackSlice G q x, hG.pullbackSlice q x⟩ :=
    Subtype.ext rfl
  have h2 : ∀ i, e ⟨s i (q, x), hs i (q, x)⟩ =
      ⟨pullbackSlice (s i) q x, (hs i).pullbackSlice q x⟩ := fun i => Subtype.ext rfl
  have hsum : e (fiberComb s hs (lam, (q, x))) =
      fiberComb (fun i => pullbackSlice (s i) q) (fun i => (hs i).pullbackSlice q) (lam, x) := by
    change eA (∑ i, lam i • (⟨s i (q, x), hs i (q, x)⟩ :
      pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X) ⁻¹' {(q, x)})) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change e (lam i • _) = _
    rw [pullbackFiberEquiv_smul, h2]
  have h3 := pullbackFiberEquiv_add P (Prod.snd : (Fin n → ℝ) × X → X) (q, x)
    ⟨G (q, x), hG (q, x)⟩ (fiberComb s hs (lam, (q, x)))
  rw [h1, hsum] at h3
  exact congrArg Subtype.val h3

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The fibre of `S` over `q` is the solution set of the slice** (the text's `S_t`):
`F(λ, (q, y)) = 0` iff `F_q(λ, y) = 0`. -/
lemma isZeroAt_paramSection_iff_slice {k : ℕ}
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, IsSection (pullbackProj P Prod.snd) (s i)) (lam : Fin k → ℝ) (q : Fin n → ℝ)
    (y : X) :
    IsZeroAt (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
        (paramSection G hG s hs) (lam, (q, y)) ↔
      IsZeroAt (pullbackProj P Prod.snd)
        (paramSection (pullbackSlice G q) (hG.pullbackSlice q) (fun i => pullbackSlice (s i) q)
          (fun i => (hs i).pullbackSlice q)) (lam, y) := by
  rw [isZeroAt_paramSection_iff, isZeroAt_paramSection_iff]
  change IsZeroAt _ (paramSlice G hG s hs lam) (q, y) ↔ _
  rw [isZeroAt_pullback_iff_pullbackSlice (isSection_paramSlice lam) q y,
    pullbackSlice_paramSlice hG hs lam q]

end SliceP

section PropertyP

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Property (P) at one point** (2021 Lemma 6.6.4, p. 264; preprint Lemma 6.29): let `f` be an
sc-Fredholm section with tame germ data, `S` and `s₁, …, s_k` sc⁺-sections of `π*P → ℝⁿ × X`,
`Φ : ℝⁿ → X` sc-smooth with `(f̃ + S)(q', Φ(q')) = 0` for `q'` near `q`.  If
`F(λ, (q', y)) = (f̃ + S)(q', y) + Σ λᵢ sᵢ(q', y)` is in general position (Definition 5.3.9) at
`(0, (q, Φ(q)))`, then the slice `F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)`, a section of the
pull-back of `P` to `ℝᵏ × X`, is in general position at `(0, Φ(q))`.  *Proof*: in a tame chart
`c` centred at `Φ(q)` (from the tame germ data of `f + S(q, ·)`), (i)–(ii) hold for `f̃ + S` in
the product chart (`isParamGP_of_isGeneralPositionGerm`), pass to the slice
(`isParamGP_slice_of_isParamGP`), and give general position of `F_q`
(`isGeneralPositionGerm_paramSection_of_isParamGP`). -/
theorem isGeneralPositionGerm_slice {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ}
    (hz : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q'))
    (hgp : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q))) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
      (paramSection
        (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
        (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q) := by
  set G := sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S with hGdef
  have hGt : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSectionTame
      G := theorem_3_1_18_tame hf.param hS
  have hy0' : IsZeroAt (pullbackProj P Prod.snd) G (q, Φ q) := hz.self_of_nhds
  have hgq : pullbackSlice G q = sectionAdd P f (pullbackSlice S q) :=
    pullbackSlice_sectionAdd_paramLift hf.isScSmooth.1 hS.1 q
  have hgqt : B.IsScFredholmSectionTame (pullbackSlice G q) :=
    hgq ▸ theorem_3_1_18_tame hf (hS.pullbackSlice q)
  have hy0 : IsZeroAt P (pullbackSlice G q) (Φ q) :=
    (isZeroAt_pullback_iff_pullbackSlice hGt.isScSmooth.1 q (Φ q)).1 hy0'
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hgqt.germTame (Φ q) (hgqt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨m, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  set q₀ := G (q, Φ q) with hq₀
  have hpcT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsTameChart
      (slicePC c q q₀) :=
    ⟨(PullbackChartData.ofProd c q).isChart_toChart B _ hc.1 q₀,
      PullbackChartData.ofProd_isTame c q q₀ hc.2⟩
  have hT' : (slicePC c q q₀).φ.model.C =
      (prodPresentation (rnPres n) T) 0 ⁻¹'
        quadrant (0 + m) ((ScBanach.const (Fin n → ℝ)).prod Wq) 0 :=
    prod_eq_prodPresentation (rnPres n) T (rnPres_eq (m := n)) hT
  have hpar := isParamGP_of_isGeneralPositionGerm hGt hs hy0' hpcT ⟨mem_univ _, hyc⟩
    (ofProd_apply_eq_zero c q q₀ hφ0) (prodPresentation (rnPres n) T) hT' hgp
  have hsl := isParamGP_slice_of_isParamGP hGt.isScSmooth hc.1 hΦ hyc hφ0 hz q₀ T hT hpar
  exact isGeneralPositionGerm_paramSection_of_isParamGP hgqt (fun i => (hs i).pullbackSlice q)
    hy0 hc hyc hφ0 T hT hsl

/-- **2021 Lemma 6.6.4 (p. 264) as printed: property (P)** (preprint Lemma 6.29), with the
paragraph after it: let `X` be tame with sc-smooth bump functions, `f` an sc-Fredholm section with
tame germ data, `Φ : ℝⁿ → X` sc-smooth and `S` an sc⁺-section of `π*P → ℝⁿ × X` with
`(f̃ + S)(q, Φ(q)) = 0` for `q` near `[0, 1]ⁿ` (Proposition 6.6.3 (3)).  Then there are finitely
many sc⁺-sections `s₁, …, s_k` of `π*P` such that, for all `q` near `[0, 1]ⁿ`,
* (P) the slice `F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)`, a section of the pull-back of `P`
  to `ℝᵏ × X`, is in general position (Definition 5.3.9) at `(0, Φ(q))`, and
* `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position at `(0, (q, Φ(q)))`.
The paracompactness instances are binders of the conclusion, `k` being existential.  *Proof*:
`lemma_6_6_4` gives the second item; the first follows pointwise (`isGeneralPositionGerm_slice`). -/
theorem lemma_6_6_4_propertyP (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
        [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))],
        ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
            (paramSection
              (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
                q)
              (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
              (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q) ∧
          ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) := by
  obtain ⟨k, s, hs, hP⟩ := lemma_6_6_4 hX hbump hf hΦ hS hz
  refine ⟨k, s, hs, fun {_ _ _ _} => ?_⟩
  filter_upwards [hz.eventually_nhdsSet, hP] with q hq hgp
  exact ⟨isGeneralPositionGerm_slice hf hS hs hΦ hq hgp, hgp⟩

/-- **The slice `F_q` is a tame sc-Fredholm section vanishing at `(0, Φ(q))`**: `F_q` is
`paramSection` of `G(q, ·) = f + S(q, ·)` (Theorem 3.1.18, `pullbackSlice_sectionAdd_paramLift`)
and of the sc⁺-sections `sᵢ(q, ·)` (`IsScPlusSection.pullbackSlice`, Theorem 3.1.21). -/
theorem isScFredholmSectionTame_slice {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    (q : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsScFredholmSectionTame
      (paramSection
        (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
        (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) ∧
    ∀ y : X, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, y) →
      IsZeroAt (pullbackProj P Prod.snd)
        (paramSection
          (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
          (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, y) := by
  have hgq : pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
      q = sectionAdd P f (pullbackSlice S q) :=
    pullbackSlice_sectionAdd_paramLift hf.isScSmooth.1 hS.1 q
  have hgqt : B.IsScFredholmSectionTame
      (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q) :=
    hgq ▸ theorem_3_1_18_tame hf (hS.pullbackSlice q)
  refine ⟨theorem_3_1_21_tame hgqt fun i => (hs i).pullbackSlice q, fun y hy => ?_⟩
  exact isZeroAt_paramSection_zero _ _
    ((isZeroAt_pullback_iff_pullbackSlice ((isSection_pullbackLift _).sectionAdd hS.1) q y).1 hy)

/-- **2021 Lemma 6.6.5 (p. 265): the fibres `S_t` are manifolds with boundary with corners**
(preprint Lemma 6.30), in Mathlib's language: given property (P) for the slices
(`lemma_6_6_4_propertyP`), for every `q` near `[0, 1]ⁿ` the point `(0, Φ(q))` is a zero of the
slice `F_q`, and near it the solution set `S_q = {F_q = 0}` (the fibre of `S` over `q`,
`isZeroAt_paramSection_iff_slice`) is a smooth manifold with boundary and corners
(`IsManifold (modelWithCornersEuclideanQuadrant d) ∞`), by `theorem_3_1_26_isManifold` applied to
`F_q`. -/
theorem lemma_6_6_5_fibre_isManifold {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {Φ : (Fin n → ℝ) → X}
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    (hPs : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
        (paramSection
          (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
          (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q)) :
    ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      IsZeroAt (pullbackProj P Prod.snd)
        (paramSection
          (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
          (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q) ∧
      ∃ U : Set ((Fin k → ℝ) × X), IsOpen U ∧ ((0 : Fin k → ℝ), Φ q) ∈ U ∧
        ∃ (d : ℕ) (hsub : ((rnPolyfold k).prod PX).IsSubMPolyfold
            {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
              (pullbackSlice (sectionAdd (pullbackProj P Prod.snd)
                (paramLift f hf.isScSmooth.1) S) q)
              (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
              (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) y}),
          letI := ((rnPolyfold k).prod PX).paracompactSpace_subtype
            {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
              (pullbackSlice (sectionAdd (pullbackProj P Prod.snd)
                (paramLift f hf.isScSmooth.1) S) q)
              (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
              (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) y}
          ∃ h : (MPolyfold.subPolyfold hsub).HasCornerStructureOfDim d,
            letI := (MPolyfold.subPolyfold hsub).cornerChartedSpace h
            IsManifold (modelWithCornersEuclideanQuadrant d) ∞
              {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
                (pullbackSlice (sectionAdd (pullbackProj P Prod.snd)
                  (paramLift f hf.isScSmooth.1) S) q)
                (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
                (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) y} := by
  filter_upwards [hz, hPs] with q hq hgp
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_slice hf hS hs q
  have h0 := hzero (Φ q) hq
  exact ⟨h0, theorem_3_1_26_isManifold (isScFredholmSectionTame2021_iff.2 hFt) h0
    (isGoodPositionGermTame2021_iff.2 (hgp.isGoodPositionGermTame hFt h0))⟩

end PropertyP

end Polyfold
