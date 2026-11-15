import Polyfold.Chapter6.IntervalEndIdentity
import Polyfold.Chapter6.CubePropertyP
import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, p. 220
(**Definition 5.3.9**; preprint Definition 5.17), §6.6, p. 265 (the paragraph after
**Lemma 6.6.4**; preprint Lemma 6.29) and the proof of **Theorem 6.7.1**, p. 278: general
position of a section `G` over `[0, 1]ⁿ × X` at one zero `(q, y)` and general position of its
slice `G(q, ·)` at `y`.

# General position at a point of `{0, 1} × X` and on the slice

## What is formalized

* `UnitCube.minimalSubspaceWith_cChart_vertex`: at a vertex `q` of `[0, 1]ⁿ` the centred chart
  has no reduced direction, `E_0(q) = 0`.
* `isGeneralPositionGerm_of_isParamGP_elim0`: properties (i)–(ii) of the proof of Theorem 5.3.10
  with no added sections, in a tame chart centred at the zero, give general position
  (Definition 5.3.9).
* `isParamGP_elim0_of_cubeSlice`: (i)–(ii) for the slice `G(q, ·)` at `y` give (i)–(ii) for `G` at
  `(q, y)` in the product chart, for every `q ∈ [0, 1]ⁿ` and one zero `(q, y)` (no curve of
  zeros is needed).
* `isParamGP_elim0_cubeSlice_of_vertex`: the converse at a vertex `q`.
* **`isGeneralPositionGerm_of_cubeSlice`**: if the slice `G(q, ·)` is in general position at
  `y`, then `G` is in general position at `(q, y)`.
* **`isGeneralPositionGerm_cubeSlice_of_vertex`**: at a vertex `q` (for `n = 1`: `q ∈ {0, 1}`),
  if `G` is in general position at `(q, y)`, then `G(q, ·)` is in general position at `y`; in
  particular its linearization at `y` is onto (`isLinSurjAt_cubeSlice_of_vertex`).
* `isGeneralPositionGerm_cubeSlice_vertex_iff`: the two together.
* `isGeneralPositionGerm_cubeLift_add_of_slice`, `isGeneralPositionGerm_slice_of_end`,
  `isLinSurjAt_slice_of_end`: the same for `F = f̃ + S` over `[0, 1] × X` and
  `F_i = f + S(i, ·)`, `i ∈ {0, 1}`.
* **`pullOr_tangentOr_ivFirst_iff_slice_of_end`**: the end identity
  `pullOr_tangentOr_ivFirst_iff_slice` at `t ∈ {0, 1}` with general position of `F` at `(t, x)`
  as the only hypothesis on the linearizations.

At an interior point `0 < t < 1` general position of `F` at `(t, x)` does not make `F_t'(x)`
onto (the kernel of `F'(t, x)` may be transversal to `{0} × T_xX` only together with the
`t`-direction); at `t ∈ {0, 1}` the reduced tangent space of `[0, 1] × X` is `{0} × T^R_xX`, and
the complement of `ker F'(t, x)` inside it is a complement of `ker F_t'(x)` in `T_xX`.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

/-! ### The reduced directions of `[0, 1]ⁿ` at a vertex -/

/-- **At a vertex `q` of `[0, 1]ⁿ` the centred chart has no reduced direction**: `E_0 = 0` for
every presentation of its partial quadrant (the degeneracy index of `q` is `n`). -/
theorem UnitCube.minimalSubspaceWith_cChart_vertex {n : ℕ} {q : Fin n → unitInterval}
    (hq : ∀ i, (q i : ℝ) = 0 ∨ (q i : ℝ) = 1) {nχ : ℕ} {Wχ : ScBanach}
    (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hTχ : (cChart q).model.C = Tχ 0 ⁻¹' quadrant nχ Wχ 0) :
    minimalSubspaceWith Tχ (0 : (rnSc n) 0) = ⊥ := by
  classical
  have : FiniteDimensional ℝ ((rnSc n) 0) := inferInstanceAs (FiniteDimensional ℝ (Fin n → ℝ))
  have hfin : finrank ℝ ((rnSc n) 0) = n := (Module.finrank_fin_fun ℝ : finrank ℝ (Fin n → ℝ) = n)
  have hdeg : (cubePolyfold n).degIndex q = n := by
    rw [cubePolyfold_degIndex, Finset.filter_true_of_mem fun i _ => hq i, Finset.card_univ,
      Fintype.card_fin]
  have hch := (cubePolyfold n).degIndex_eq_chartDegIndex_of_isTameRetract (isChart_cChart q)
    ⟨cRetr q, cRetr_retract q, cRetr_isTame q⟩ (mem_cChart q)
  have h0C : (0 : (rnSc n) 0) ∈ (cChart q).model.C := by
    have h := (cChart q).apply_mem_C (mem_cChart q)
    rwa [cChart_self q] at h
  have hw : degIndexWith Tχ (0 : (rnSc n) 0) = n := by
    rw [← degIndex_eq Tχ hTχ h0C]
    have h2 : Polyfold.degIndex (cChart q).model.E (cChart q).model.C (cChart q q) = n :=
      hch.symm.trans hdeg
    rw [cChart_self q] at h2
    exact h2
  have hcard : finrank ℝ ({i : Fin nχ // (Tχ 0 (0 : (rnSc n) 0)).1 i = 0} → ℝ) =
      degIndexWith Tχ (0 : (rnSc n) 0) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hinj : Function.Injective (coordMapL Tχ (0 : (rnSc n) 0)).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hfin.trans (hw.symm.trans hcard.symm))).2 (coordMapL_surjective Tχ 0)
  unfold minimalSubspaceWith
  exact LinearMap.ker_eq_bot.2 hinj

/-! ### Properties (i)–(ii) with no sections and general position -/

section ElimZero

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Properties (i)–(ii) with no added sections give general position** (2021 Definition
5.3.9, p. 220, and the proof of Theorem 5.3.10, p. 216): if in a tame chart `c` centred at the
zero `y` of the tame sc-Fredholm section `g` the linearization `Lin_g(0)` is onto and every
tangent vector is `u + e` with `u ∈ ker Lin_g(0)` and `e ∈ E_0`, then `(g, y)` is in general
position.  The converse is `isParamGP_elim0_of_isGeneralPositionGerm`. -/
theorem isGeneralPositionGerm_of_isParamGP_elim0 {g : X → Y}
    (hg : B.IsScFredholmSectionTame g) {y : X} (hy0 : IsZeroAt P g y)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hyV : y ∈ c.φ.source)
    (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (h : c.IsParamGP g (Fin.elim0 : Fin 0 → X → Y) T) : B.IsGeneralPositionGerm g y := by
  refine isGeneralPositionGerm_of_sup_eq hg hy0 hc hyV hφ0 T hT (fun k hk => ?_) ?_
  · rw [hφ0] at hk
    obtain ⟨u, a, hua⟩ := h.1 k hk
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hua
    exact ⟨u, (add_zero _).symm.trans hua⟩
  · refine le_antisymm (sup_le (c.linKer_le _ 0) inf_le_left) fun v hv => ?_
    obtain ⟨u, a, hua, hwu⟩ := h.2 ⟨v, hv⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hua
    have hk : (u : c.φ.model.E 0) ∈ c.linKer g 0 :=
      (c.mem_linKer_iff _ 0 _).2 ⟨u.2, (add_zero _).symm.trans hua⟩
    have hrest : v - (u : c.φ.model.E 0) ∈
        reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T 0 := by
      refine ⟨Submodule.sub_mem _ hv u.2, ?_⟩
      have hb0 : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = 0 := map_zero _
      rw [hb0]
      exact hwu
    have e : v = (u : c.φ.model.E 0) + (v - (u : c.φ.model.E 0)) := by abel
    rw [e]
    exact Submodule.add_mem_sup hk hrest

end ElimZero

/-! ### The slice at one zero -/

section PointwiseSlice

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- **Properties (i)–(ii) for the slice give them for `G`, at one zero**: if (i)–(ii) of the
proof of Theorem 5.3.10 hold with no added sections for `G(q, ·)` in the chart `c` centred at
`y`, they hold for `G` in `χ_q × φ_c`, for every `q ∈ [0, 1]ⁿ`.  A tangent vector `w = (τ, v)`
is `(w − (0, u)) + (0, u' ) + (0, e)` with `Lin_{G(q, ·)}(0) u = Lin_G(0) w`, `u = u' + e`,
`u' ∈ ker`, `e ∈ E_0(y)`. -/
theorem isParamGP_elim0_of_cubeSlice
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (q : Fin n → unitInterval) {y : X}
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (h0 : IsZeroAt (pullbackProj P Prod.snd) G (q, y))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (h : c.IsParamGP (prodSlice G q) (Fin.elim0 : Fin 0 → X → Y) T) :
    (cubePC q c q₀).IsParamGP G
      (Fin.elim0 : Fin 0 → (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (prodPresentation Tχ T) := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsChart
      (cubePC q c q₀) := (cubeProdData q c).isChart_toChart B _ hc q₀
  have hlift : ∀ u : ↥(rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1))),
      (((0 : Fin n → ℝ), (u : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
          (0 : (cubePC q c q₀).φ.model.E 1)) := fun u =>
    (cubePC_mem_tangent_iff q c q₀ h0U _).2 u.2
  have hsl : ∀ u : ↥(rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1))),
      linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0
        ⟨_, hlift u⟩ = linAt c.U c.R (c.principal (prodSlice G q)) 0 u := fun u =>
    linAt_cubePC_slice hG hc q q₀ h0U ⟨_, hlift u⟩ rfl
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · obtain ⟨u, a, hua⟩ := h.1 k' ((mem_K_cubePC_zero_iff q c q₀ h0O k').1 hk')
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hua
    refine ⟨⟨_, hlift u⟩, 0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, hsl u]
    exact hua
  · -- the value `Lin_G(0) w` lies in the fibre over `0`
    have hz : (cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1) =
        (cubePC q c q₀).φ (q, y) := by
      rw [map_zero, cubePC_apply_eq_zero q c q₀ hφ0]
    let p : ChartPoint (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)) (q, y) :=
      ⟨cubePC q c q₀, hpcc, ⟨mem_cChart q, hyV⟩, 0, hz⟩
    obtain ⟨k, hk⟩ := p.scDeriv_mem_K hG h0 (w : (cubePC q c q₀).φ.model.E 0)
    have hO : (cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1) ∈
        (cubePC q c q₀).φ.model.O := by
      rw [hz]; exact (cubePC q c q₀).φ.mapsTo_model _ ⟨mem_cChart q, hyV⟩
    have h1 := (cubePC q c q₀).mem_K_ρ hO k
    have hb0 : (cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1) = 0 :=
      map_zero _
    have h2 : ((0 : (cubePC q c q₀).φ.model.E 0),
        linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 w) ∈
        (cubePC q c q₀).K := by
      have e : (((cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1),
          ρ (cubePC q c q₀).R
            ((cubePC q c q₀).φ.model.E.toBase 1 (0 : (cubePC q c q₀).φ.model.E 1)) k) :
          (cubePC q c q₀).φ.model.E 0 × (cubePC q c q₀).F 0) =
          (0, linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 w) :=
        Prod.ext hb0 hk
      rw [← e]
      exact h1
    obtain ⟨u, a, hua⟩ := h.1 _ ((mem_K_cubePC_zero_iff q c q₀ h0O _).1 h2)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hua
    have hua' : linAt c.U c.R (c.principal (prodSlice G q)) 0 u =
        linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 w :=
      (add_zero _).symm.trans hua
    obtain ⟨u', a', hu', hm⟩ := h.2 u
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hu'
    have hu'0 : linAt c.U c.R (c.principal (prodSlice G q)) 0 u' = 0 :=
      (add_zero _).symm.trans hu'
    set nn : ↥(rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
      (0 : (cubePC q c q₀).φ.model.E 1))) := w - ⟨_, hlift u⟩ + ⟨_, hlift u'⟩ with hnn
    have hd : (w.1 : (Fin n → ℝ) × c.φ.model.E 0) - nn.1 =
        ((0 : Fin n → ℝ), (u : c.φ.model.E 0) - u') := by
      refine Prod.ext ?_ ?_
      · change (show (Fin n → ℝ) × c.φ.model.E 0 from w.1).1 -
          ((show (Fin n → ℝ) × c.φ.model.E 0 from w.1).1 - (0 : Fin n → ℝ) + (0 : Fin n → ℝ)) =
            (0 : Fin n → ℝ)
        rw [sub_zero, add_zero, sub_self]
      · change (show (Fin n → ℝ) × c.φ.model.E 0 from w.1).2 -
          ((show (Fin n → ℝ) × c.φ.model.E 0 from w.1).2 - (u : c.φ.model.E 0) + u') =
            (u : c.φ.model.E 0) - u'
        rw [sub_add_eq_sub_sub, sub_sub_cancel]
    have hmem : (((0 : Fin n → ℝ), (u : c.φ.model.E 0) - u') : (Fin n → ℝ) × c.φ.model.E 0) ∈
        minimalSubspaceWith (prodPresentation Tχ T) (0 : (Fin n → ℝ) × c.φ.model.E 0) :=
      (mem_minimalSubspaceWith_cubeProd Tχ T _).2 ⟨Submodule.zero_mem _, hm⟩
    refine ⟨nn, 0, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty, hnn, map_add, map_sub, hsl u, hsl u', hua',
        hu'0, sub_self]
      exact (add_zero _).trans (add_zero _)
    · rw [← hd] at hmem
      exact hmem

/-- **Properties (i)–(ii) pass to the slice at a point with no reduced cube direction**: if
`E_0(q) = 0` (a vertex of `[0, 1]ⁿ`) and (i)–(ii) hold with no added sections for `G` in
`χ_q × φ_c`, they hold for `G(q, ·)` in `c`.  In (ii) the kernel vector `u` with
`(0, w) − u ∈ E_0(q) × E_0(y) = 0 × E_0(y)` has no cube component, so it is a kernel vector of
the slice. -/
theorem isParamGP_elim0_cubeSlice_of_vertex
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (q : Fin n → unitInterval) {y : X}
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    {nχ : ℕ} {Wχ : ScBanach} (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin nχ → ℝ)).prod Wχ))
    (hmin : minimalSubspaceWith Tχ (0 : (rnSc n) 0) = ⊥)
    {m : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod Wq))
    (h : (cubePC q c q₀).IsParamGP G
      (Fin.elim0 : Fin 0 → (Fin n → unitInterval) × X →
        pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
      (prodPresentation Tχ T)) :
    c.IsParamGP (prodSlice G q) (Fin.elim0 : Fin 0 → X → Y) T := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hmin' : ∀ e : (Fin n → ℝ) × c.φ.model.E 0,
      e ∈ minimalSubspaceWith (prodPresentation Tχ T) (0 : (Fin n → ℝ) × c.φ.model.E 0) →
      e.1 = 0 ∧ e.2 ∈ minimalSubspaceWith T 0 := fun e he => by
    obtain ⟨h1, h2⟩ := (mem_minimalSubspaceWith_cubeProd Tχ T e).1 he
    rw [hmin] at h1
    exact ⟨(Submodule.mem_bot ℝ).1 h1, h2⟩
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · obtain ⟨u, a, hua⟩ := h.1 k' ((mem_K_cubePC_zero_iff q c q₀ h0O k').2 hk')
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hua
    have hua' : linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u =
        k' := (add_zero _).symm.trans hua
    obtain ⟨u', a', hu', hm⟩ := h.2 u
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hu'
    have hu'0 : linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u' =
        0 := (add_zero _).symm.trans hu'
    obtain ⟨he1, -⟩ := hmin' _ hm
    have key := linAt_cubePC_slice hG hc q q₀ h0U (u - u') he1
    refine ⟨⟨_, (cubePC_mem_tangent_iff q c q₀ h0U _).1 (u - u').2⟩, 0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← key, map_sub, hua', hu'0]
    exact (add_zero _).trans (sub_zero _)
  · have hlift : (((0 : Fin n → ℝ), (w : c.φ.model.E 0)) : (Fin n → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
          (0 : (cubePC q c q₀).φ.model.E 1)) :=
      (cubePC_mem_tangent_iff q c q₀ h0U _).2 w.2
    obtain ⟨u, a, hu, hm⟩ := h.2 ⟨_, hlift⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hu
    have hu0 : linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 u =
        0 := (add_zero _).symm.trans hu
    obtain ⟨he1, he2⟩ := hmin' _ hm
    have hu1 : (u.1 : (Fin n → ℝ) × c.φ.model.E 0).1 = 0 := by
      have e : (0 : Fin n → ℝ) - (show (Fin n → ℝ) × c.φ.model.E 0 from u.1).1 =
          (0 : Fin n → ℝ) := he1
      rw [zero_sub, neg_eq_zero] at e
      exact e
    have key := linAt_cubePC_slice hG hc q q₀ h0U u hu1
    refine ⟨⟨_, (cubePC_mem_tangent_iff q c q₀ h0U _).1 u.2⟩, 0, ?_, he2⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← key, hu0]
    exact add_zero _

variable {f : X → Y}

/-- **General position of the slice gives general position of `F`, at one zero** (2021
Definition 5.3.9, p. 220, and the paragraph after Lemma 6.6.4, p. 265): let `f` be an
sc-Fredholm section with tame germ data, `S` an sc⁺-section of `pr₂*P` over `[0, 1]ⁿ × X`,
`F = f̃ + S` and `(q, y)` a zero of `F`.  If `F_q = f + S(q, ·)` is in general position at `y`,
then `F` is in general position at `(q, y)`, for every `q ∈ [0, 1]ⁿ` (boundary and corners
included). -/
theorem isGeneralPositionGerm_of_cubeSlice (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {q : Fin n → unitInterval} {y : X}
    (hy0 : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y))
    (hgp : B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S q)) y) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsGeneralPositionGerm
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y) := by
  set G := sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S with hGdef
  have hGt : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScFredholmSectionTame
      G := theorem_3_1_18_tame hf.paramCube hS
  have hsl : prodSlice G q = sectionAdd P f (prodSlice S q) :=
    prodSlice_sectionAdd_cubeLift hf.isScSmooth.1 hS.1 q
  have hgqt : B.IsScFredholmSectionTame (prodSlice G q) :=
    isScFredholmSectionTame_cubeSliceG hf hS q
  have hy0s : IsZeroAt P (prodSlice G q) y :=
    (isZeroAt_iff_prodSlice hGt.isScSmooth.1 q y).1 hy0
  rw [← hsl] at hgp
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hgqt.germTame y (hgqt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0s)
  obtain ⟨m, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cChart_relOpen q).isPartialQuadrant
  set q₀ := G (q, y) with hq₀
  have hpcT : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsTameChart
      (cubePC q c q₀) :=
    ⟨(cubeProdData q c).isChart_toChart B _ hc.1 q₀, cubeProd_isTame q c q₀ hc.2⟩
  have hT' : (cubePC q c q₀).φ.model.C =
      (prodPresentation Tχ T) 0 ⁻¹' quadrant (nχ + m) (Wχ.prod Wq) 0 :=
    prod_eq_prodPresentation Tχ T hTχ hT
  have hsrc : (q, y) ∈ (cubePC q c q₀).φ.source := ⟨mem_cChart q, hyc⟩
  have h1 := isParamGP_elim0_of_isGeneralPositionGerm hgqt hy0s hc hyc hφ0 T hT hgp
  have h2 := isParamGP_elim0_of_cubeSlice hGt.isScSmooth hc.1 q hyc hφ0 hy0 q₀ Tχ T h1
  exact isGeneralPositionGerm_of_isParamGP_elim0 hGt hy0 hpcT hsrc
    (cubePC_apply_eq_zero q c q₀ hφ0) (prodPresentation Tχ T) hT' h2

/-- **General position of `F` at a vertex gives general position of the slice** (the proof of
2021 Theorem 6.7.1, p. 278): let `q` be a vertex of `[0, 1]ⁿ` (for `n = 1`: `q ∈ {0, 1}`) and
`(q, y)` a zero of `F = f̃ + S`.  If `F` is in general position at `(q, y)`, then
`F_q = f + S(q, ·)` is in general position at `y`.  The reduced tangent space of `[0, 1]ⁿ × X`
at `(q, y)` is `0 × T^R_yX`, so a complement of `ker F'(q, y)` inside it is a complement of
`ker F_q'(y)` in `T_yX` inside `T^R_yX`. -/
theorem isGeneralPositionGerm_cubeSlice_of_vertex (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {q : Fin n → unitInterval} (hq : ∀ i, (q i : ℝ) = 0 ∨ (q i : ℝ) = 1) {y : X}
    (hy0 : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y))
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsGeneralPositionGerm
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y)) :
    B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S q)) y := by
  set G := sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S with hGdef
  have hGt : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScFredholmSectionTame
      G := theorem_3_1_18_tame hf.paramCube hS
  have hsl : prodSlice G q = sectionAdd P f (prodSlice S q) :=
    prodSlice_sectionAdd_cubeLift hf.isScSmooth.1 hS.1 q
  have hgqt : B.IsScFredholmSectionTame (prodSlice G q) :=
    isScFredholmSectionTame_cubeSliceG hf hS q
  have hy0s : IsZeroAt P (prodSlice G q) y :=
    (isZeroAt_iff_prodSlice hGt.isScSmooth.1 q y).1 hy0
  rw [← hsl]
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hgqt.germTame y (hgqt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0s)
  obtain ⟨m, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cChart_relOpen q).isPartialQuadrant
  set q₀ := G (q, y) with hq₀
  have hpcT : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsTameChart
      (cubePC q c q₀) :=
    ⟨(cubeProdData q c).isChart_toChart B _ hc.1 q₀, cubeProd_isTame q c q₀ hc.2⟩
  have hT' : (cubePC q c q₀).φ.model.C =
      (prodPresentation Tχ T) 0 ⁻¹' quadrant (nχ + m) (Wχ.prod Wq) 0 :=
    prod_eq_prodPresentation Tχ T hTχ hT
  have hsrc : (q, y) ∈ (cubePC q c q₀).φ.source := ⟨mem_cChart q, hyc⟩
  have h1 := isParamGP_elim0_of_isGeneralPositionGerm hGt hy0 hpcT hsrc
    (cubePC_apply_eq_zero q c q₀ hφ0) (prodPresentation Tχ T) hT' hgp
  have h2 := isParamGP_elim0_cubeSlice_of_vertex hGt.isScSmooth hc.1 q hyc hφ0 q₀ Tχ
    (minimalSubspaceWith_cChart_vertex hq Tχ hTχ) T h1
  exact isGeneralPositionGerm_of_isParamGP_elim0 hgqt hy0s hc hyc hφ0 T hT h2

/-- **At a vertex, `F` is in general position at `(q, y)` iff the slice `F_q` is at `y`.** -/
theorem isGeneralPositionGerm_cubeSlice_vertex_iff (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {q : Fin n → unitInterval} (hq : ∀ i, (q i : ℝ) = 0 ∨ (q i : ℝ) = 1) {y : X}
    (hy0 : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y) ↔
      B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S q)) y :=
  ⟨isGeneralPositionGerm_cubeSlice_of_vertex hf hS hq hy0,
    isGeneralPositionGerm_of_cubeSlice hf hS hy0⟩

/-- **At a vertex, general position of `F` at `(q, y)` makes `F_q'(y)` onto.** -/
theorem isLinSurjAt_cubeSlice_of_vertex (hf : B.IsScFredholmSectionTame f)
    {S : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    {q : Fin n → unitInterval} (hq : ∀ i, (q i : ℝ) = 0 ∨ (q i : ℝ) = 1) {y : X}
    (hy0 : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y))
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsGeneralPositionGerm
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift f hf.isScSmooth.1) S) (q, y)) :
    B.IsLinSurjAt (sectionAdd P f (prodSlice S q)) y :=
  (isGeneralPositionGerm_cubeSlice_of_vertex hf hS hq hy0 hgp).isLinSurjAt

end PointwiseSlice

/-! ### The ends of `[0, 1] × X` -/

section IvEnds

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- A point `t` of `[0, 1]` with `t = 0` or `t = 1` is a vertex of `[0, 1]¹`. -/
theorem UnitCube.isVertex_of_end {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) : ∀ i, (t i : ℝ) = 0 ∨ (t i : ℝ) = 1 := fun i => by
  rw [Subsingleton.elim i 0]; exact ht

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **The slice of a zero of `F = f̃ + S`** is a zero of `F_t = f + S(t, ·)`. -/
theorem isZeroAt_slice_of_isZeroAt (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x)) :
    IsZeroAt P (sectionAdd P f (prodSlice S t)) x := by
  rw [← prodSlice_sectionAdd_cubeLift hf.isScSmooth.1 hS.1 t]
  exact (isZeroAt_iff_prodSlice ((isSection_pullbackLift _).sectionAdd hS.1) t x).1 hz0

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **General position of `F_t` gives general position of `F` at `(t, x)`**, for every
`t ∈ [0, 1]`: `isGeneralPositionGerm_of_cubeSlice` over `[0, 1] × X`. -/
theorem isGeneralPositionGerm_cubeLift_add_of_slice (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hgp : B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S t)) x) :
    (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x) :=
  isGeneralPositionGerm_of_cubeSlice hf hS hz0 hgp

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **General position of `F` at a point of `{0, 1} × X` gives general position of `F_i`**
(the proof of 2021 Theorem 6.7.1, p. 278: the ends `S_{F_0}`, `S_{F_1}` of the cobordism are
solution sets of sections in general position): for `t ∈ {0, 1}` and a zero `(t, x)` of
`F = f̃ + S` at which `F` is in general position, `F_t = f + S(t, ·)` is in general position at
`x`. -/
theorem isGeneralPositionGerm_slice_of_end (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) {x : X}
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hgp : (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x)) :
    B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S t)) x :=
  isGeneralPositionGerm_cubeSlice_of_vertex hf hS (isVertex_of_end ht) hz0 hgp

omit [ParacompactSpace ((Fin 1 → unitInterval) × X)] in
/-- **At the ends, general position of `F` makes `F_i'(x)` onto.** -/
theorem isLinSurjAt_slice_of_end (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) {x : X}
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hgp : (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x)) :
    B.IsLinSurjAt (sectionAdd P f (prodSlice S t)) x :=
  (isGeneralPositionGerm_slice_of_end hf hS ht hz0 hgp).isLinSurjAt

/-- **The end identity at `t ∈ {0, 1}` from general position of `F` alone** (2021 Remark
6.6.19, p. 276, and the proof of Theorem 6.7.1, p. 278): `pullOr_tangentOr_ivFirst_iff_slice`
at a zero `(t, x)` of `F = f̃ + S` with `t ∈ {0, 1}`, where the surjectivity of `F'(t, x)` and
of `F_t'(x)` both come from the general position of `F` at `(t, x)`
(`isLinSurjAt_slice_of_end`).  In coordinates `ι` of `ker F_t'(x)` and `ι̂` of `ker F'(t, x)`
with `ι̂(0, w) = (0, ι w)` and `ι̂(1, 0)` in the direction of increasing `t`, the tangent
orientation of `S_F` given by `e ∧ o` is the standard one iff the tangent orientation of
`S_{F_t}` given by `o` is. -/
theorem pullOr_tangentOr_ivFirst_iff_slice_of_end (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) {x : X}
    (hxs : x ∈ PX.smoothSet) (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hgp : (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ]
      c.linKer (sectionAdd P f (prodSlice S t)) (chartPtOf c hc hxc hxs).z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).z)
    (hι₀ : ∀ w, ((ι' (consE 0 w)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (0, (ι w : c.φ.model.E 0)))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k)))).1 :
      (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) :
    pullOr finrank_euclideanSpace_fin ι'
        ((chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).tangentOr
          (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) hz0
          hgp.isLinSurjAt
          (toChartOr (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS)
            (prod_cube_mem_smoothSet_iff.2 hxs) (ivChart b c q₀) (isChart_ivChart b hc q₀)
            (mem_ivChart_source q₀ hxc hb)
            ((SectionOrientation.ivFirst hX hbump hf o hS).1 (t, x)
              (prod_cube_mem_smoothSet_iff.2 hxs)))) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        ((chartPtOf c hc hxc hxs).tangentOr
          (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t))
          (isZeroAt_slice_of_isZeroAt hf hS hz0) (isLinSurjAt_slice_of_end hf hS ht hz0 hgp)
          (toChartOr (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hxs c
            hc hxc ((o.sectionAdd (hS.cubeSlice t)).1 x hxs))) = stdOrientation k :=
  pullOr_tangentOr_ivFirst_iff_slice hX hbump hf o hS hxs b hb hc hxc q₀ hz0 hgp.isLinSurjAt
    (isZeroAt_slice_of_isZeroAt hf hS hz0) (isLinSurjAt_slice_of_end hf hS ht hz0 hgp) ι ι'
    hι₀ hι₁

end IvEnds

end Polyfold
