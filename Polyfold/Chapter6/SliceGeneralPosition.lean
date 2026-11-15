import Polyfold.Chapter6.SlicePropertyP

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.4**
(p. 264; preprint Lemma 6.29) and the paragraph after it: **(P) implies the general position of
`F`**, for families on `ℝⁿ`.

# From property (P) to the general position of `F` on `ℝⁿ`

`isGeneralPositionGerm_slice` (`SlicePropertyP.lean`) passes from the general position of
`F(λ, (q, y)) = (f̃ + S)(q, y) + Σ λᵢ sᵢ(q, y)` at `(0, (q, Φ(q)))` to that of the slice `F_q`.
Here the converse, the text's "(P) automatically implies that `F` is in general position":

* `isParamGP_of_isParamGP_slice`: properties (i)–(ii) of the proof of Theorem 5.3.10 for the slice
  `G(q, ·)` and the `sᵢ(q, ·)` in a chart `c` centred at `Φ(q)` give them for `G` and the `sᵢ` in
  the product chart `(r ↦ r − q) × c` (presentation `ℝⁿ × T`).  A tangent vector `(σ, v)` is
  `(σ, u + δσ) + (0, e)`, with `δσ` the `X`-component of the derivative of the curve of zeros
  (`curve_slicePC`) and `v − δσ = u + e` from (ii) for the slice.
* **`isGeneralPositionGerm_of_slice`**: if `(f̃ + S)(q', Φ(q')) = 0` near `q` and the slice `F_q`
  is in general position at `(0, Φ(q))`, then `F` is in general position at `(0, (q, Φ(q)))`.
  With `isGeneralPositionGerm_slice` the two are equivalent (`isGeneralPositionGerm_slice_iff`).
  This is the `ℝⁿ` form of `isGeneralPositionGerm_cubeSlice_iff`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle

section SliceGP

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Properties (i)–(ii) for the slice give them for `G`** in the product chart
`(r ↦ r − q) × c` (the converse of `isParamGP_slice_of_isParamGP`). -/
theorem isParamGP_of_isParamGP_slice {k : ℕ}
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} (hyV : Φ q ∈ c.φ.source)
    (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) {m : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (h : c.IsParamGP (pullbackSlice G q) (fun i => pullbackSlice (s i) q) T) :
    (slicePC c q q₀).IsParamGP G s (prodPresentation (rnPres n) T) := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hu0 : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0U
  obtain ⟨-, hcur⟩ := curve_slicePC hG hc hΦ hyV hφ0 h0 q₀
  set D := fderiv ℝ (fun q' => (slicePC c q q₀).φ (q', Φ q')) q with hD
  have hpr : ∀ i, (slicePC c q q₀).principal (s i) 0 = c.principal (pullbackSlice (s i) q) 0 :=
    fun i => principal_slicePC_zero c q q₀ (s i)
  have hsum : ∀ a : Fin k → ℝ, ∑ i, a i • (slicePC c q q₀).principal (s i) 0 =
      ∑ i, a i • c.principal (pullbackSlice (s i) q) 0 := fun a =>
    Finset.sum_congr rfl fun i _ => by rw [hpr]; rfl
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · -- (i)
    have hk : ((0 : c.φ.model.E 0), k') ∈ c.K := (mem_K_ofProd_zero_iff c q q₀ h0O k').1 hk'
    obtain ⟨u, a, hua⟩ := h.1 k' hk
    have hlift : (((0 : Fin n → ℝ), (u : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (slicePC c q q₀).U (r (slicePC c q q₀).R)
          (0 : (slicePC c q q₀).φ.model.E 1)) :=
      (PullbackChartData.ofProd_mem_tangent_iff c q q₀ 0 hu0 _).2 u.2
    refine ⟨⟨_, hlift⟩, a, ?_⟩
    rw [StrongBundle.linAt_ofProd_slice hG hc q q₀ h0U ⟨_, hlift⟩ rfl, hsum]
    exact hua
  · -- (ii)
    have hw2 := (PullbackChartData.ofProd_mem_tangent_iff c q q₀ 0 hu0 _).1 w.2
    set τ := (w.1 : (Fin n → ℝ) × c.φ.model.E 0).1 with hτ
    obtain ⟨hDk, hD1⟩ := hcur τ
    obtain ⟨hDr, -⟩ := ((slicePC c q q₀).mem_linKer_iff G 0 _).1 hDk
    have hDr2 : (D τ : (Fin n → ℝ) × c.φ.model.E 0).2 ∈
        rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)) :=
      (PullbackChartData.ofProd_mem_tangent_iff c q q₀ 0 hu0 _).1 hDr
    obtain ⟨u, a, hua, hm⟩ := h.2 ⟨_, sub_mem hw2 hDr2⟩
    have hlift : ((τ, (u : c.φ.model.E 0) + (D τ : (Fin n → ℝ) × c.φ.model.E 0).2) :
        (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (slicePC c q q₀).U (r (slicePC c q q₀).R)
          (0 : (slicePC c q q₀).φ.model.E 1)) :=
      (PullbackChartData.ofProd_mem_tangent_iff c q q₀ 0 hu0 _).2 (add_mem u.2 hDr2)
    refine ⟨⟨_, hlift⟩, a, ?_, ?_⟩
    · obtain ⟨hv, hl⟩ := linAt_slicePC_eq hG hc hΦ hyV hφ0 h0 q₀ h0U ⟨_, hlift⟩
      rw [hl, hsum]
      have e : (⟨_, hv⟩ : ↥(rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)))) = u :=
        Subtype.ext (add_sub_cancel_right _ _)
      rw [e]
      exact hua
    · change ((show ((rnSc n).prod c.φ.model.E) 0 from w.1) -
          (show ((rnSc n).prod c.φ.model.E) 0 from
            (τ, (u : c.φ.model.E 0) + (D τ : (Fin n → ℝ) × c.φ.model.E 0).2))) ∈
          minimalSubspaceWith (prodPresentation (rnPres n) T)
            (0 : ((rnSc n).prod c.φ.model.E) 0)
      rw [minimalSubspaceWith_prodPresentation]
      refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [minimalSubspaceWith_rnPres]; exact Submodule.mem_top
      · change (w.1 : (Fin n → ℝ) × c.φ.model.E 0).2 -
          ((u : c.φ.model.E 0) + (D τ : (Fin n → ℝ) × c.φ.model.E 0).2) ∈
          minimalSubspaceWith T 0
        convert hm using 1
        change _ = ((w.1 : (Fin n → ℝ) × c.φ.model.E 0).2 -
          (D τ : (Fin n → ℝ) × c.φ.model.E 0).2) - (u : c.φ.model.E 0)
        abel

variable {f : X → Y}

/-- **(P) implies the general position of `F`** (2021 Lemma 6.6.4, p. 264, the paragraph after
it; preprint Lemma 6.29), for families on `ℝⁿ`: let `f` be an sc-Fredholm section with tame germ
data, `S` and `s₁, …, s_k` sc⁺-sections of `π*P → ℝⁿ × X`, `Φ : ℝⁿ → X` sc-smooth with
`(f̃ + S)(q', Φ(q')) = 0` for `q'` near `q`.  If the slice
`F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position at `(0, Φ(q))`, then
`F(λ, (q', y)) = (f̃ + S)(q', y) + Σ λᵢ sᵢ(q', y)` is in general position at `(0, (q, Φ(q)))`.
*Proof*: in a tame chart `c` centred at `Φ(q)` (tame germ data of `f + S(q, ·)`) the slice has
(i)–(ii) (`isParamGP_of_isGeneralPositionGerm`), so `G = f̃ + S` has them in the product chart
(`isParamGP_of_isParamGP_slice`), which gives the general position of `F`
(`isGeneralPositionGerm_paramSection_of_isParamGP`). -/
theorem isGeneralPositionGerm_of_slice {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
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
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
      (paramSection
        (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
        (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q)) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) := by
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
  have hsl := isParamGP_of_isGeneralPositionGerm hgqt (fun i => (hs i).pullbackSlice q) hy0 hc
    hyc hφ0 T hT hgp
  have hpar := isParamGP_of_isParamGP_slice hGt.isScSmooth hc.1 hΦ hyc hφ0 hz q₀ T hsl
  exact isGeneralPositionGerm_paramSection_of_isParamGP hGt hs hy0' hpcT ⟨mem_univ _, hyc⟩
    (ofProd_apply_eq_zero c q q₀ hφ0) (prodPresentation (rnPres n) T) hT' hpar

/-- **Property (P) at `q` is equivalent to the general position of `F` at `(0, (q, Φ(q)))`**, for
families on `ℝⁿ` (`isGeneralPositionGerm_slice` and `isGeneralPositionGerm_of_slice`). -/
theorem isGeneralPositionGerm_slice_iff {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
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
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q')) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) ↔
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
        (paramSection
          (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).pullbackSlice q)
          (fun i => pullbackSlice (s i) q) fun i => (hs i).1.pullbackSlice q) (0, Φ q) :=
  ⟨isGeneralPositionGerm_slice hf hS hs hΦ hz, isGeneralPositionGerm_of_slice hf hS hs hΦ hz⟩

end SliceGP

end Polyfold
