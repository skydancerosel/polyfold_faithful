import Polyfold.Chapter6.CubeBoundarySlice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.4**
(p. 265; preprint Lemma 6.29): **property (P) at every point of `[0, 1]ⁿ`**, boundary and corners
included, and the paragraph after it.  Gap G.65; row V6.33.

# Property (P) on `[0, 1]ⁿ`

## The text, paraphrased

For `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` over `[0, 1] × X × ℝᵏ`, (P): for **every**
`t ∈ [0, 1]` the slice `F_t` is in general position at `(φ(t), 0)` to the boundary of `X × ℝᵏ`.
Lemma 6.6.4 asserts that finitely many `sᵢ` with (P) exist; the text then says that (P)
"automatically implies" that `F` is in general position to the boundary of `[0, 1] × X × ℝᵏ` at
all points `(t, φ(t), 0)`.  At `t ∈ {0, 1}` the parameter `t` is a corner coordinate of
`[0, 1] × X × ℝᵏ`.

## What is formalized

The parameter space is the M-polyfold `[0, 1]ⁿ` itself (`cubePolyfold n`; `t ∈ [0, 1]` is
`n = 1`).  General position is Definition 5.3.9: `F'` onto, and `ker F'` has an sc-complement in
the reduced tangent space.  At a boundary point `q` the reduced tangent space of `[0, 1]ⁿ` is
`E_0 = {τ | τᵢ = 0 for qᵢ ∈ {0, 1}}`.

* `exists_cubeCurveDeriv`: in the product chart `χ_q × φ_c` centred at `(q, Φ(q))`, the curve of
  zeros `q' ↦ (q', Φ(q'))` has a derivative `τ ↦ (τ, Dτ)` with `(τ, Dτ) ∈ ker Lin_G(0)` for every
  `τ ∈ ℝⁿ`, and `Dτ ∈ E_0(Φ(q))` for `τ ∈ E_0(q)`.
* `linAt_cubePC_eq`: `Lin_G(0)(τ, v) = Lin_{G(q, ·)}(0)(v − Dτ)`.
* `isParamGP_cubeSlice_of_isParamGP` and `isParamGP_of_isParamGP_cubeSlice`: properties (i)–(ii)
  of the proof of Theorem 5.3.10 hold for `G = f̃ + S` and the `sᵢ` at `(q, Φ(q))` (product chart,
  reduced tangent space `E_0(q) × E_0(Φ(q))`) **iff** they hold for the slices at `Φ(q)`.  The
  forward direction uses only `τ ∈ E_0(q)`, because the reduced tangent space of `[0, 1]ⁿ` at `q`
  contains no direction leaving the boundary; property (i) is first reduced to such `τ` with (ii).
* **`isGeneralPositionGerm_cubeSlice_iff`**: for every `q ∈ [0, 1]ⁿ`, boundary and corners
  included, `F` is in general position at `(0, (q, Φ(q)))` iff the slice `F_q` is in general
  position at `(0, Φ(q))`.  The direction "⇐" is the text's "(P) automatically implies that `F`
  is in general position"; it holds at the boundary of `[0, 1]ⁿ` as printed.
* **`lemma_6_6_4_propertyP_cube`** (**Lemma 6.6.4 as printed, on `[0, 1]ⁿ`**): there are
  finitely many sc⁺-sections `sᵢ` over `[0, 1]ⁿ × X` such that, for **every** `q ∈ [0, 1]ⁿ`, (P)
  holds and `F` is in general position at `(0, (q, Φ(q)))`.
* `lemma_6_6_5_fibre_isManifold_cube`: the fibres `S_q`, `q ∈ [0, 1]ⁿ`, are manifolds with
  boundary and corners near `(0, Φ(q))`.

## On the hand example of the O-cube note

For `X = [0, ∞)²`, `f(y) = y₁ + y₂`, `s(y, t) = 2t`, `φ(t) = (t, t)`, `k = 0`, the kernel of
`F'(0, (0, 0))` is two-dimensional and the reduced tangent space of `[0, 1] × X` at `(0, (0, 0))`
is `0`, so `F` is **not** in general position there (Definition 5.3.9); the kernel is only in
good position (Definition 3.1.24).  The example therefore does not separate (P) from general
position of `F`, in agreement with `isGeneralPositionGerm_cubeSlice_iff`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube

section CubeParamGP

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- Points of relatively open subsets of partial quadrants of `ℝⁿ` are points of unique
differentiability. -/
lemma uniqueDiffWithinAt_rnRel {C V₀ : Set (Fin n → ℝ)} (hrel : IsRelOpenInQuadrant (rnSc n) C V₀)
    {v : Fin n → ℝ} (hv : v ∈ V₀) : UniqueDiffWithinAt ℝ V₀ v := by
  have h := hrel.isScDomain.uniqueDiffWithinAt 1 (v : (rnSc n) 1)
    (by rw [ScBanach.lvlSet_const]; exact hv)
  rwa [ScBanach.lvlSet_const] at h

omit [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The reduced tangent space of `C_{χ_q} × C` at `0` is `E_0(q) × E_0`. -/
lemma mem_minimalSubspaceWith_cubeProd {E W Wχ : ScBanach} {nχ m : ℕ}
    (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (T : ScIso E ((ScBanach.const (Fin m → ℝ)).prod W)) (e : (Fin n → ℝ) × E 0) :
    e ∈ minimalSubspaceWith (prodPresentation Tχ T) (0 : (Fin n → ℝ) × E 0) ↔
      e.1 ∈ minimalSubspaceWith Tχ 0 ∧ e.2 ∈ minimalSubspaceWith T 0 := by
  rw [minimalSubspaceWith_prodPresentation]
  exact Submodule.mem_prod

/-- **The curve of zeros `q' ↦ (q', Φ(q'))` in the product chart `χ_q × φ_c`** (the `[0, 1]ⁿ` form
of `curve_slicePC`): there is a continuous linear `D : ℝⁿ → E₀` with `(τ, Dτ) ∈ ker Lin_G(0)` for
every `τ ∈ ℝⁿ` (`exists_hasFDerivWithinAt_cubeCurve`; its `ℝⁿ`-component is `τ` since
`χ_q ∘ χ_q⁻¹ = id`), and `Dτ ∈ E_0(Φ(q))` for `τ` in the reduced tangent space `E_0(q)` of
`[0, 1]ⁿ` (`mem_minimalSubspaceWith_of_hasFDerivWithinAt`). -/
theorem exists_cubeCurveDeriv
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ) {q : Fin n → unitInterval}
    (hyV : Φ q ∈ c.φ.source) (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ q', IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hTχ : (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0)
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0) :
    ∃ D : (Fin n → ℝ) →L[ℝ] c.φ.model.E 0,
      (∀ τ : Fin n → ℝ, ((τ, D τ) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        (cubePC q c q₀).linKer G 0) ∧
      ∀ τ ∈ minimalSubspaceWith Tχ 0, D τ ∈ minimalSubspaceWith T 0 := by
  have hΓ : (cubePolyfold n).IsScSmoothMap ((cubePolyfold n).prod PX) (fun q' => (q', Φ q')) :=
    MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsChart
      (cubePC q c q₀) := (cubeProdData q c).isChart_toChart B _ hc q₀
  have hz : (cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1) =
      (cubePC q c q₀).φ (q, Φ q) := by
    rw [map_zero, cubePC_apply_eq_zero q c q₀ hφ0]
  obtain ⟨V₀, hrel, h0V, hVO, hVsrc, D', hD', hker⟩ :=
    exists_hasFDerivWithinAt_cubeCurve hG hpcc hΓ q ⟨mem_cChart q, hyV⟩ h0 0 hz
  have hu := uniqueDiffWithinAt_rnRel hrel h0V
  -- the `ℝⁿ`-component of the derivative is the identity
  have hfst : (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c.φ.model.E 0)).comp D' =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    have d1 :=
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c.φ.model.E 0)).hasFDerivAt.comp_hasFDerivWithinAt
        (0 : Fin n → ℝ) hD'
    have d2 : HasFDerivWithinAt
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c.φ.model.E 0)) ∘
          fun v => (cubePC q c q₀).φ ((cChart q).symm v, Φ ((cChart q).symm v)))
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) V₀ 0 := by
      refine (hasFDerivWithinAt_id (0 : Fin n → ℝ) V₀).congr (fun v hv => ?_) ?_
      · change (cChart q) ((cChart q).symm v) = v
        exact (cChart q).apply_symm_apply (hVO hv)
      · change (cChart q) ((cChart q).symm 0) = 0
        exact (cChart q).apply_symm_apply (hVO h0V)
    exact hu.eq d1 d2
  set D : (Fin n → ℝ) →L[ℝ] c.φ.model.E 0 :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)).comp D' with hDdef
  have hD'τ : ∀ τ : Fin n → ℝ, D' τ = ((τ, D τ) : (Fin n → ℝ) × c.φ.model.E 0) := fun τ =>
    Prod.ext (congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L τ) hfst) rfl
  refine ⟨D, fun τ => hD'τ τ ▸ hker τ, fun τ hτ => ?_⟩
  have hD : HasFDerivWithinAt (fun v => c.φ (Φ ((cChart q).symm v))) D V₀ 0 :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)).hasFDerivAt.comp_hasFDerivWithinAt
      (0 : Fin n → ℝ) hD'
  have h00 : c.φ (Φ ((cChart q).symm 0)) = 0 := by rw [cChart_symm_zero]; exact hφ0
  exact mem_minimalSubspaceWith_of_hasFDerivWithinAt hrel h0V Tχ hTχ T hT
    (fun v hv => c.φ.apply_mem_C (hVsrc v hv).2) h00 hD hτ

/-- **The linearization of `G` in the product chart, through the slice** (the `[0, 1]ⁿ` form of
`linAt_slicePC_eq`): for `D` as in `exists_cubeCurveDeriv` and every tangent vector
`u = (τ, v)` of `χ_q × φ_c` at `0`, `Lin_G(0) u = Lin_{G(q, ·)}(0)(v − Dτ)`: subtract
`(τ, Dτ) ∈ ker Lin_G(0)` and apply `linAt_cubePC_slice`. -/
theorem linAt_cubePC_eq
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (q : Fin n → unitInterval)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) {D : (Fin n → ℝ) →L[ℝ] c.φ.model.E 0}
    (hD : ∀ τ : Fin n → ℝ, ((τ, D τ) : (Fin n → ℝ) × c.φ.model.E 0) ∈
      (cubePC q c q₀).linKer G 0)
    (u : ↥(rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
      (0 : (cubePC q c q₀).φ.model.E 1)))) :
    ∃ hv : (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 - D (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1 ∈
        rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)),
      linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u =
        linAt c.U c.R (c.principal (prodSlice G q)) 0 ⟨_, hv⟩ := by
  obtain ⟨hwr, hw0⟩ := ((cubePC q c q₀).mem_linKer_iff G 0 _).1
    (hD (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1)
  set w : ↥(rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
      (0 : (cubePC q c q₀).φ.model.E 1))) := ⟨_, hwr⟩ with hw
  set d := u - w with hd
  have hd1 : (d.1 : (Fin n → ℝ) × c.φ.model.E 0).1 = 0 := sub_self _
  have key := linAt_cubePC_slice hG hc q q₀ h0U d hd1
  have hu : u = d + w := (sub_add_cancel u w).symm
  refine ⟨(cubePC_mem_tangent_iff q c q₀ h0U _).1 d.2, ?_⟩
  have e1 : linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u =
      linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 d := by
    conv_lhs => rw [hu]
    rw [map_add, hw0, add_zero]
  rw [e1, key]
  rfl

/-- **Properties (i)–(ii) pass to the slice at every `q ∈ [0, 1]ⁿ`** (the `[0, 1]ⁿ` form of
`isParamGP_slice_of_isParamGP`): if (i)–(ii) of the proof of Theorem 5.3.10 hold for `G` and the
`sᵢ` in `χ_q × φ_c` (presentation `Tχ × T`), they hold for `G(q, ·)` and the `sᵢ(q, ·)` in `c`.
In (ii) the transversality of `ker` to `ℝᵏ ⊕ (E_0(q) × E_0(Φ(q)))` only produces cube
directions `τ ∈ E_0(q)`, whose `Dτ` lies in `E_0(Φ(q))`; (i) is reduced to such directions by
first applying (ii) to the tangent vector it provides. -/
theorem isParamGP_cubeSlice_of_isParamGP {k : ℕ}
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ) {q : Fin n → unitInterval}
    (hyV : Φ q ∈ c.φ.source) (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ q', IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hTχ : (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0)
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0)
    (h : (cubePC q c q₀).IsParamGP G s (prodPresentation Tχ T)) :
    c.IsParamGP (prodSlice G q) (fun i => prodSlice (s i) q) T := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  obtain ⟨D, hD, hDmin⟩ := exists_cubeCurveDeriv hG hc hΦ hyV hφ0 h0 q₀ Tχ hTχ T hT
  have hpr : ∀ i, (cubePC q c q₀).principal (s i) 0 = c.principal (prodSlice (s i) q) 0 :=
    fun i => cubePC_principal_zero q c q₀ (s i)
  have hmin : ∀ e : (Fin n → ℝ) × c.φ.model.E 0,
      e ∈ minimalSubspaceWith (prodPresentation Tχ T) (0 : (Fin n → ℝ) × c.φ.model.E 0) →
      e.1 ∈ minimalSubspaceWith Tχ 0 ∧ e.2 ∈ minimalSubspaceWith T 0 := fun e he =>
    (mem_minimalSubspaceWith_cubeProd Tχ T e).1 he
  have hsum : ∀ a : Fin k → ℝ, ∑ i, a i • (cubePC q c q₀).principal (s i) 0 =
      ∑ i, a i • c.principal (prodSlice (s i) q) 0 := fun a =>
    Finset.sum_congr rfl fun i _ => by rw [hpr]; rfl
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · -- (i): reduce to a cube direction in `E_0(q)` with (ii)
    have hk : ((0 : (cubePC q c q₀).φ.model.E 0), k') ∈ (cubePC q c q₀).K :=
      (mem_K_cubePC_zero_iff q c q₀ h0O k').2 hk'
    obtain ⟨u, a, hua⟩ := h.1 k' hk
    obtain ⟨u', a', hua', hm⟩ := h.2 u
    set e := u - u' with he
    have hem := hmin _ hm
    obtain ⟨hv, hl⟩ := linAt_cubePC_eq hG hc q q₀ h0U hD e
    have hτ := hDmin _ hem.1
    refine ⟨⟨_, hv⟩, a - a', ?_⟩
    rw [← hl]
    have hLe : linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 e =
        linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u +
          ∑ i, a' i • (cubePC q c q₀).principal (s i) 0 := by
      rw [he, map_sub, eq_sub_of_add_eq hua']
      abel
    rw [hLe, ← hsum, ← hua]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    abel
  · -- (ii)
    have hlift : (((0 : Fin n → ℝ), (w : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
          (0 : (cubePC q c q₀).φ.model.E 1)) :=
      (cubePC_mem_tangent_iff q c q₀ h0U _).2 w.2
    obtain ⟨u, a, hua, hm⟩ := h.2 ⟨_, hlift⟩
    have hem := hmin _ hm
    obtain ⟨hv, hl⟩ := linAt_cubePC_eq hG hc q q₀ h0U hD u
    refine ⟨⟨_, hv⟩, a, ?_, ?_⟩
    · rw [← hl, ← hsum]; exact hua
    · have h1 : (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1 ∈ minimalSubspaceWith Tχ 0 := by
        have e : (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1 =
            -((((0 : Fin n → ℝ), (w : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) -
              (show (Fin n → ℝ) × c.φ.model.E 0 from u.1)).1 := by
          change _ = -((0 : Fin n → ℝ) - (show (Fin n → ℝ) × c.φ.model.E 0 from u.1).1)
          rw [zero_sub, neg_neg]
        rw [e]
        exact neg_mem hem.1
      have h2 := hDmin _ h1
      have h3 : (w : c.φ.model.E 0) - (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 ∈
          minimalSubspaceWith T 0 := hem.2
      convert add_mem h3 h2 using 1
      change (w : c.φ.model.E 0) - ((u.1 : (Fin n → ℝ) × c.φ.model.E 0).2 - _) =
        ((w : c.φ.model.E 0) - (u.1 : (Fin n → ℝ) × c.φ.model.E 0).2) + _
      abel

/-- **Properties (i)–(ii) for the slice give them for `G` in the product chart** (the
`[0, 1]ⁿ`-form of the text's "(P) automatically implies that `F` is in general position"): if
(i)–(ii) hold for `G(q, ·)` and the `sᵢ(q, ·)` in `c`, they hold for `G` and the `sᵢ` in
`χ_q × φ_c`, at every `q ∈ [0, 1]ⁿ`.  A tangent vector `(τ, v)` is `(τ, u + Dτ) + (0, e)` with
`v − Dτ = u + e` from (ii) for the slice; the summand `(0, e)` lies in `E_0(q) × E_0(Φ(q))`. -/
theorem isParamGP_of_isParamGP_cubeSlice {k : ℕ}
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ) {q : Fin n → unitInterval}
    (hyV : Φ q ∈ c.φ.source) (hφ0 : c.φ (Φ q) = 0)
    (h0 : ∀ q', IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hTχ : (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0)
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant m Wq 0)
    (h : c.IsParamGP (prodSlice G q) (fun i => prodSlice (s i) q) T) :
    (cubePC q c q₀).IsParamGP G s (prodPresentation Tχ T) := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  obtain ⟨D, hD, -⟩ := exists_cubeCurveDeriv hG hc hΦ hyV hφ0 h0 q₀ Tχ hTχ T hT
  have hpr : ∀ i, (cubePC q c q₀).principal (s i) 0 = c.principal (prodSlice (s i) q) 0 :=
    fun i => cubePC_principal_zero q c q₀ (s i)
  have hsum : ∀ a : Fin k → ℝ, ∑ i, a i • (cubePC q c q₀).principal (s i) 0 =
      ∑ i, a i • c.principal (prodSlice (s i) q) 0 := fun a =>
    Finset.sum_congr rfl fun i _ => by rw [hpr]; rfl
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · -- (i)
    have hk : ((0 : c.φ.model.E 0), k') ∈ c.K := (mem_K_cubePC_zero_iff q c q₀ h0O k').1 hk'
    obtain ⟨u, a, hua⟩ := h.1 k' hk
    have hlift : (((0 : Fin n → ℝ), (u : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
          (0 : (cubePC q c q₀).φ.model.E 1)) :=
      (cubePC_mem_tangent_iff q c q₀ h0U _).2 u.2
    refine ⟨⟨_, hlift⟩, a, ?_⟩
    rw [linAt_cubePC_slice hG hc q q₀ h0U ⟨_, hlift⟩ rfl, hsum]
    exact hua
  · -- (ii)
    have hw2 := (cubePC_mem_tangent_iff q c q₀ h0U _).1 w.2
    obtain ⟨hDr, -⟩ := ((cubePC q c q₀).mem_linKer_iff G 0 _).1
      (hD (w.1 : (Fin n → ℝ) × c.φ.model.E 0).1)
    have hDr2 : D (w.1 : (Fin n → ℝ) × c.φ.model.E 0).1 ∈
        rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)) :=
      (cubePC_mem_tangent_iff q c q₀ h0U _).1 hDr
    obtain ⟨u, a, hua, hm⟩ := h.2 ⟨_, sub_mem hw2 hDr2⟩
    set τ := (w.1 : (Fin n → ℝ) × c.φ.model.E 0).1 with hτ
    have hlift : ((τ, (u : c.φ.model.E 0) + D τ) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
          (0 : (cubePC q c q₀).φ.model.E 1)) :=
      (cubePC_mem_tangent_iff q c q₀ h0U _).2 (add_mem u.2 hDr2)
    refine ⟨⟨_, hlift⟩, a, ?_, ?_⟩
    · obtain ⟨hv, hl⟩ := linAt_cubePC_eq hG hc q q₀ h0U hD ⟨_, hlift⟩
      rw [hl, hsum]
      have e : (⟨_, hv⟩ : ↥(rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)))) = u :=
        Subtype.ext (by simp)
      rw [e]
      exact hua
    · refine (mem_minimalSubspaceWith_cubeProd Tχ T _).2 ⟨?_, ?_⟩
      · change τ - τ ∈ minimalSubspaceWith Tχ 0
        rw [sub_self]; exact zero_mem _
      · change (w.1 : (Fin n → ℝ) × c.φ.model.E 0).2 - ((u : c.φ.model.E 0) + D τ) ∈
          minimalSubspaceWith T 0
        convert hm using 1
        change _ = ((w.1 : (Fin n → ℝ) × c.φ.model.E 0).2 - D τ) - (u : c.φ.model.E 0)
        abel

end CubeParamGP

/-! ### Property (P) at every `q ∈ [0, 1]ⁿ` -/

section PropertyPCube

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P} {f : X → Y}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The slice of `f̃ + S` at `q ∈ [0, 1]ⁿ` is `f + S(q, ·)`. -/
lemma prodSlice_sectionAdd_cubeLift (hf : IsSection P f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (q : Fin n → unitInterval) :
    prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf) S) q =
      sectionAdd P f (prodSlice S q) :=
  prodSlice_sectionAdd_pullbackLift hf hS q

/-- The slice `G(q, ·) = f + S(q, ·)` at `q ∈ [0, 1]ⁿ` is a tame sc-Fredholm section
(Theorem 3.1.18 with `IsScPlusSection.cubeSlice`). -/
theorem isScFredholmSectionTame_cubeSliceG (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (q : Fin n → unitInterval) :
    B.IsScFredholmSectionTame
      (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q) := by
  rw [prodSlice_sectionAdd_cubeLift hf.isScSmooth.1 hS.1 q]
  exact theorem_3_1_18_tame hf (hS.cubeSlice q)

variable {k : ℕ} [ParacompactSpace ((Fin k → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]

omit [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))] in
/-- **The slice `F_q` at `q ∈ [0, 1]ⁿ` is a tame sc-Fredholm section**, vanishing at `(0, y)` when
`G(q, y) = 0`: `F_q = paramSection` of `G(q, ·)` and the `sᵢ(q, ·)` (Theorem 3.1.21). -/
theorem isScFredholmSectionTame_cubeSlice (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i)) (q : Fin n → unitInterval) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsScFredholmSectionTame
      (paramSection
        (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
        (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) ∧
    ∀ y : X, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y) →
      IsZeroAt (pullbackProj P Prod.snd)
        (paramSection
          (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
          (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, y) := by
  refine ⟨theorem_3_1_21_tame (isScFredholmSectionTame_cubeSliceG hf hS q)
    fun i => (hs i).cubeSlice q, fun y hy => ?_⟩
  exact isZeroAt_paramSection_zero _ _
    ((isZeroAt_iff_prodSlice ((isSection_pullbackLift _).sectionAdd hS.1) q y).1 hy)

/-- **Property (P) is equivalent to the general position of `F`, at every `q ∈ [0, 1]ⁿ`** (2021
Lemma 6.6.4, p. 265, and the paragraph after it; preprint Lemma 6.29): let `f` be an sc-Fredholm
section with tame germ data, `S` and `s₁, …, s_k` sc⁺-sections of `pr₂*P` over `[0, 1]ⁿ × X` and
`Φ : [0, 1]ⁿ → X` sc-smooth with `(f̃ + S)(q', Φ(q')) = 0` for all `q'`.  For every
`q ∈ [0, 1]ⁿ`, boundary and corners included, `F(λ, (q', y)) = (f̃ + S)(q', y) + Σ λᵢ sᵢ(q', y)`
is in general position (Definition 5.3.9) at `(0, (q, Φ(q)))` iff the slice
`F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position at `(0, Φ(q))`.  The
direction "⇐" is the text's "(P) automatically implies that `F` is in general position to the
boundary of `[0, 1] × X × ℝᵏ` at all points `(t, φ(t), 0)`".  *Proof*: in a tame chart `c`
centred at `Φ(q)` and the tame product chart `χ_q × φ_c`, general position is (i)–(ii) of the
proof of Theorem 5.3.10 (`isParamGP_of_isGeneralPositionGerm`,
`isGeneralPositionGerm_paramSection_of_isParamGP`), and (i)–(ii) for `F` and for `F_q` are
equivalent (`isParamGP_cubeSlice_of_isParamGP`, `isParamGP_of_isParamGP_cubeSlice`). -/
theorem isGeneralPositionGerm_cubeSlice_iff (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i))
    {Φ : (Fin n → unitInterval) → X} (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    (hz : ∀ q', IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q', Φ q'))
    (q : Fin n → unitInterval) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) ↔
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
        (paramSection
          (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
          (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
          (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, Φ q) := by
  set G := sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S with hGdef
  have hGt : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScFredholmSectionTame
      G := theorem_3_1_18_tame hf.paramCube hS
  have hy0' : IsZeroAt (pullbackProj P Prod.snd) G (q, Φ q) := hz q
  have hgqt : B.IsScFredholmSectionTame (prodSlice G q) :=
    isScFredholmSectionTame_cubeSliceG hf hS q
  have hy0 : IsZeroAt P (prodSlice G q) (Φ q) :=
    (isZeroAt_iff_prodSlice hGt.isScSmooth.1 q (Φ q)).1 hy0'
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hgqt.germTame (Φ q) (hgqt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨m, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cChart_relOpen q).isPartialQuadrant
  set q₀ := G (q, Φ q) with hq₀
  have hpcT : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsTameChart
      (cubePC q c q₀) :=
    ⟨(cubeProdData q c).isChart_toChart B _ hc.1 q₀, cubeProd_isTame q c q₀ hc.2⟩
  have hT' : (cubePC q c q₀).φ.model.C =
      (prodPresentation Tχ T) 0 ⁻¹' quadrant (nχ + m) (Wχ.prod Wq) 0 :=
    prod_eq_prodPresentation Tχ T hTχ hT
  have hsrc : (q, Φ q) ∈ (cubePC q c q₀).φ.source := ⟨mem_cChart q, hyc⟩
  constructor
  · intro hgp
    have hpar := isParamGP_of_isGeneralPositionGerm hGt hs hy0' hpcT hsrc
      (cubePC_apply_eq_zero q c q₀ hφ0) (prodPresentation Tχ T) hT' hgp
    have hsl := isParamGP_cubeSlice_of_isParamGP hGt.isScSmooth hc.1 hΦ hyc hφ0 hz q₀ Tχ hTχ T hT
      hpar
    exact isGeneralPositionGerm_paramSection_of_isParamGP hgqt (fun i => (hs i).cubeSlice q)
      hy0 hc hyc hφ0 T hT hsl
  · intro hgp
    have hsl := isParamGP_of_isGeneralPositionGerm hgqt (fun i => (hs i).cubeSlice q) hy0 hc hyc
      hφ0 T hT hgp
    have hpar := isParamGP_of_isParamGP_cubeSlice hGt.isScSmooth hc.1 hΦ hyc hφ0 hz q₀ Tχ hTχ T hT
      hsl
    exact isGeneralPositionGerm_paramSection_of_isParamGP hGt hs hy0' hpcT hsrc
      (cubePC_apply_eq_zero q c q₀ hφ0) (prodPresentation Tχ T) hT' hpar

/-- **2021 Lemma 6.6.4, p. 265, as printed, on `[0, 1]ⁿ`: property (P)** (preprint Lemma 6.29),
with the paragraph after it: let `X` be tame with sc-smooth bump functions, `f` an sc-Fredholm
section with tame germ data, `Φ : [0, 1]ⁿ → X` sc-smooth and `S` an sc⁺-section of `pr₂*P` over
`[0, 1]ⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for all `q`.  Then there are finitely many
sc⁺-sections `s₁, …, s_k` over `[0, 1]ⁿ × X` such that for **every** `q ∈ [0, 1]ⁿ` (boundary
and corners included)
* (P) the slice `F_q(λ, y) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position
  (Definition 5.3.9) at `(0, Φ(q))`, and
* `F` is in general position at `(0, (q, Φ(q)))` in `ℝᵏ × ([0, 1]ⁿ × X)`.
*Proof*: `lemma_6_6_4_cube` gives the second item, and `isGeneralPositionGerm_cubeSlice_iff`
the first.  The paracompactness instances are binders of the conclusion, `k` being
existential. -/
theorem lemma_6_6_4_propertyP_cube (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → unitInterval) → X}
    (hΦ : (cubePolyfold n).IsScSmoothMap PX Φ)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
        [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P
          (Prod.snd : (Fin n → unitInterval) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))],
        ∀ q : Fin n → unitInterval,
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
            (paramSection
              (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
              (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
              (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, Φ q) ∧
          ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((cubePolyfold n).prod PX))).IsGeneralPositionGerm
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) := by
  obtain ⟨k, s, hs, hP⟩ := lemma_6_6_4_cube hX hbump hf hΦ hS hz
  refine ⟨k, s, hs, fun {_ _ _ _} q => ?_⟩
  have hgp := hP q
  exact ⟨(isGeneralPositionGerm_cubeSlice_iff hf hS hs hΦ hz q).1 hgp, hgp⟩

omit [ParacompactSpace ((Fin k → ℝ) × ((Fin n → unitInterval) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))] in
/-- **2021 Lemma 6.6.5 (p. 265): the fibres `S_t` are manifolds with boundary with corners, on
`[0, 1]ⁿ`** (preprint Lemma 6.30), in Mathlib's language: given (P) at `q ∈ [0, 1]ⁿ`
(`lemma_6_6_4_propertyP_cube`; boundary points included), `(0, Φ(q))` is a zero of the slice
`F_q`, and near it the solution set `S_q = {F_q = 0}` is a smooth manifold with boundary and
corners (`theorem_3_1_26_isManifold` for `F_q`). -/
theorem lemma_6_6_5_fibre_isManifold_cube (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (s i))
    {Φ : (Fin n → unitInterval) → X} {q : Fin n → unitInterval}
    (hz : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, Φ q))
    (hPs : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
      (paramSection
        (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
        (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, Φ q)) :
    IsZeroAt (pullbackProj P Prod.snd)
      (paramSection
        (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
        (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
        (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) (0, Φ q) ∧
    ∃ U : Set ((Fin k → ℝ) × X), IsOpen U ∧ ((0 : Fin k → ℝ), Φ q) ∈ U ∧
      ∃ (d : ℕ) (hsub : ((rnPolyfold k).prod PX).IsSubMPolyfold
          {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
            (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
            (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
            (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) y}),
        letI := ((rnPolyfold k).prod PX).paracompactSpace_subtype
          {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
            (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
            (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
            (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) y}
        ∃ h : (MPolyfold.subPolyfold hsub).HasCornerStructureOfDim d,
          letI := (MPolyfold.subPolyfold hsub).cornerChartedSpace h
          IsManifold (modelWithCornersEuclideanQuadrant d) ∞
            {y ∈ U | IsZeroAt (pullbackProj P Prod.snd) (paramSection
              (prodSlice (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) q)
              (((isSection_pullbackLift _).sectionAdd hS.1).prodSlice q)
              (fun i => prodSlice (s i) q) fun i => (hs i).1.prodSlice q) y} := by
  obtain ⟨hFt, hzero⟩ := isScFredholmSectionTame_cubeSlice hf hS hs q
  have h0 := hzero (Φ q) hz
  exact ⟨h0, theorem_3_1_26_isManifold (isScFredholmSectionTame2021_iff.2 hFt) h0
    (isGoodPositionGermTame2021_iff.2 (hPs.isGoodPositionGermTame hFt h0))⟩

end PropertyPCube

end Polyfold
