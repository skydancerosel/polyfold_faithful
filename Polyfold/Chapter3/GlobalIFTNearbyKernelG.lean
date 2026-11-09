import Polyfold.Chapter3.GlobalIFTNearbyKernel
import Polyfold.Chapter3.GlobalIFTNearbyGraphG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54 (1), the kernel of the linearization at the nearby zeros, in the chart at `x₀`, **in the
text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# Theorem 3.6.8 (preprint 3.54) (1), the kernel at the nearby zeros, germ reading

## What is formalized

`Polyfold.theorem_3_6_8_chart_kernel`: the germ form of `theorem_3_6_8_chart_kernel_wholeChart`.  In the
data of `theorem_3_6_8_chart_graph` (the data `𝒮` of Theorem 3.4.2 (preprint 3.38) on a germ whose points
`ψ'` sends into the germ `G_g` of the filling `g`, with derivative family `Dg`), there is an open
neighbourhood `N₃ ⊆ N₂` of `0` such that for every zero `z₀ ∈ O ∩ N₃` of `g` there are `v ∈ V'`
with `ψ(z₀) = v + σ(v)`, the level-`1` point `z₀₁ ∈ U₁` over `z₀` **with `z₀₁ ∈ (G_g)₁`**, and
`x₁ = ψ₁(z₀₁) ∈ 𝒮.G₁` over `v + σ(v)`, with (i) `D(h + t)(x₁)` surjective Fredholm of index
`n − N`; (a) `N_v = ker D(h + t)(x₁)`; (b) `D(Ψ_*g)(x₁) = D(h + t)(x₁)` for the family
`pushforwardDeriv`, and `ker Dg(z₀₁) = Dψ'(x₁)(ker D(h + t)(x₁))`; (c) `ker Dg(z₀₁) ⊆ T_{z₀}O`;
(d) `ker Dg(z₀₁)` is in good position to `C_{z₀}` inside `T_{z₀}O`; and `Dg(z₀₁)` is onto.

## What the text leaves implicit, and the choices made (the findings)

* **This is the site where the germ reading matters most**: the text differentiates `g` at the
  nearby zero `z₀` ("`ker f'(y)` is in good position"), which requires `g` to be sc¹ at `z₀₁`.
  With `g` a germ on `G_g` only, this is the G″ property `ψ'₁(x₁) ∈ (G_g)₁` of the hypothesis
  `hGψ'`, satisfied by the data of `theorem_3_6_8_chart_graph` built on `G″`
  (`BasicGermShrink.lean`, `BasicGermShrinkIFT.lean`); the derivative `Dg(z₀₁)` is the value of
  the derivative family `Dg` of the germ.
* The two uses of the whole-chart `g` in the old proof — `D(Ψ_*g)(x₁) = D(h + t)(x₁)` and the
  chain rule `D(Ψ_*g)(x₁) = Γ(z₀₁) Dg(z₀₁) Dψ'(x₁)` — become the uniqueness of the derivative
  within `𝒮.G₁` (`pushforward_isSc1GermWith` restricted to `𝒮.G ⊆ ψ'⁻¹(G_g)`) and the identity
  `IsStrongBundleIso.pushforwardDeriv_at` of the explicit family.  Nothing else of `g` is used.
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

section ChartKernel

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1) at the nearby zeros, the kernel, in the chart at `x₀`, germ reading**
(phase 2; the germ form of `theorem_3_6_8_chart_kernel_wholeChart`).  In the data of
`theorem_3_6_8_chart_graph`, with `ψ'` mapping `𝒮.G` into the germ `G_g` of the filling `g`
(derivative family `Dg`), there is an open neighbourhood `N₃ ⊆ N₂` of `0` such that for every
zero `z₀ ∈ O ∩ N₃` of `g` there are `v ∈ V'` with `ψ(z₀) = v + σ(v)`, the level-`1` point
`z₀₁ ∈ U₁ ∩ (G_g)₁` over `z₀` and `x₁ = ψ₁(z₀₁) ∈ 𝒮.G₁` over `v + σ(v)`, with:
(i) `D(h + t)(x₁)` surjective Fredholm of index `n − N`;
(a) `N_v = ker D(h + t)(x₁)`;
(b) `D(Ψ_*g)(x₁) = D(h + t)(x₁)` and `ker Dg(z₀₁) = Dψ'(x₁)(ker D(h + t)(x₁))`;
(c) `ker Dg(z₀₁) ⊆ T_{z₀}O = Dr(z₀₁)E`;
(d) `ker Dg(z₀₁)` is in good position to `C_{z₀}` inside `T_{z₀}O`. -/
theorem theorem_3_6_8_chart_kernel (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0U : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0U fb g) (hfb0 : fb 0 = 0)
    {Gg : ScNbhdGerm E C} (hGg : Gg.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0}
    (hDg : IsSc1GermWith Gg g Dg)
    {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {W : ScBanach} {Ct : Set Pn} {U' : Set ((ScBanach.paramProd Pn W) 0)}
    {Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0}
    {Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0}
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0)
    {n : ℕ} {Wc : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wc))
    (hT : C = T 0 ⁻¹' quadrant n Wc 0)
    (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0) {Bc : Pn × W 0 → W 0}
    (Yc : Submodule ℝ (Pn × W 0))
    (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
    (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0)
    (Wo : Set ((ScBanach.paramProd Pn W) 0)) (N₂ : Set (E 0))
    (hG : 𝒮.G.U 0 ⊆ U') (hh'𝒮 : IsBasicGerm Ct 𝒮.G h' Bc) (hsurj : Surjective (𝒮.Dfs h'))
    (hpos : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
    (hGψ' : ∀ m, ∀ x ∈ 𝒮.G.U m, levelMap (IsStrongBundleMap.base Ψ') m x ∈ Gg.U m)
    (hWo : IsOpen Wo) (hagree : ∀ u' ∈ U' ∩ Wo, 𝒮.fsum h' u' = pushforward Ψ Ψ' g u')
    (hYc : IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc)
    (hYcc : IsClosed (Yc : Set (Pn × W 0)))
    (hV'rel : ∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) (h0V' : 0 ∈ V')
    (hσY : ∀ y, σ y ∈ Yc) (hσC : ContDiffOn ℝ 1 σ V') (hσ0 : σ 0 = 0)
    (hDσ : fderivWithin ℝ σ V' 0 = 0)
    (hsol : ∀ y ∈ V', (y : Pn × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum h' ((y : Pn × W 0) + σ y) = 0)
    (hlift : ∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
      (∃ O : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
        IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
      (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V' ∧
      ∃ σk : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) k,
        ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd Pn W).toBase k (σk y) = σ y)
    (hN₂o : IsOpen N₂) (h0N₂ : (0 : E 0) ∈ N₂)
    (hN₂ψ : ∀ u ∈ U ∩ N₂, IsStrongBundleMap.base Ψ u ∈ 𝒮.G.U 0 ∧
      IsStrongBundleMap.base Ψ u ∈ U' ∩ Wo)
    (himage : IsStrongBundleMap.base Ψ '' {u ∈ r R '' U ∩ N₂ | g u = 0} =
      (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V') :
    ∃ N₃ : Set (E 0), IsOpen N₃ ∧ (0 : E 0) ∈ N₃ ∧ N₃ ⊆ N₂ ∧
      ∀ z₀ ∈ r R '' U ∩ N₃, g z₀ = 0 →
        ∃ (v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) (_ : v ∈ V') (z₀₁ : E 1)
          (x₁ : (ScBanach.paramProd Pn W) 1),
          E.toBase 1 z₀₁ = z₀ ∧ z₀₁ ∈ E.lvlSet U 1 ∧ z₀₁ ∈ Gg.U 1 ∧
          (ScBanach.paramProd Pn W).toBase 1 x₁ = (v : Pn × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
          levelMap (IsStrongBundleMap.base Ψ) 1 z₀₁ = x₁ ∧
          IsStrongBundleMap.base Ψ z₀ = (v : Pn × W 0) + σ v ∧
          IsFredholm (𝒮.Dfs' h' x₁) ∧
          fredholmIndex (𝒮.Dfs' h' x₁) = finrank ℝ Pn - finrank ℝ Q ∧
          Surjective (𝒮.Dfs' h' x₁) ∧
          graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) (fderivWithin ℝ σ V' v) =
            LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0) ∧
          pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg x₁ = 𝒮.Dfs' h' x₁ ∧
          LinearMap.ker (Dg z₀₁ : E 0 →ₗ[ℝ] F 0) =
            (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)).map
              (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ : Pn × W 0 →ₗ[ℝ] E 0) ∧
          Surjective (Dg z₀₁) ∧
          LinearMap.ker (Dg z₀₁ : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z₀₁) ∧
          IsInGoodPositionIn E (rangeS (scDeriv U (r R) z₀₁)) (partialQuadrantAtWith T z₀)
            (LinearMap.ker (Dg z₀₁ : E 0 →ₗ[ℝ] F 0)) := by
  classical
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hOU : r R '' U ⊆ U := fun z hz => mem_U_of_mem_O hR hz
  have hC'q : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hψsc : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψcont : ContinuousOn ψ U := hψsc.isSc1.isSc0.continuousOn_base
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh'𝒮).1.finite_ker
  have hKs : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) ≤ (ScBanach.paramProd Pn W).smooth :=
    𝒮.ker_Dfs_le_smooth hCt hh'𝒮
  obtain ⟨n', Wq, T', hT'⟩ := hCt.prod_univ W
  -- the push-forward is an sc¹-germ on `𝒮.G ⊆ ψ'⁻¹(G_g)` with the family `pushforwardDeriv`
  have hGsub : ∀ m, 𝒮.G.U m ⊆ (ScBanach.paramProd Pn W).lvlSet U' m := fun m z hz =>
    hG (𝒮.G.toBase_mem hz)
  have hGpull : ∀ m, 𝒮.G.U m ⊆ (hΨ.pullGerm hU hU' h0U hψ0 Gg).U m := fun m z hz =>
    ⟨hGsub m hz, hGψ' m z hz⟩
  have hpushG : IsSc1GermWith 𝒮.G (pushforward Ψ Ψ' g) (pushforwardDeriv U U' Ψ ψ' g Dg) :=
    (hΨ.pushforward_isSc1GermWith h0U hψ0 hU hU' hGg hDg).mono hGpull
  -- the `C¹`-lift of `σ`
  obtain ⟨V₁, ⟨O₁, hO₁, hV₁⟩, h0V₁, hV₁V', σ₁, hσ₁, hσ₁eq⟩ := hlift 1 le_rfl
  have hV₁V'' : V₁ = V' ∩ O₁ := relOpen_cone_inter hV'rel hV₁ hV₁V'
  -- Corollary 3.5.3 (preprint 3.41) and Lemma 3.6.9 (preprint 3.55) at the graph points
  obtain ⟨ρ₁, hρ₁, hA⟩ := 𝒮.exists_surjective_Dfs'_graph hCt hh'𝒮 hsurj h0V' hσC.continuousOn hσ0
    hsol
  obtain ⟨ρ₂, hρ₂, hB⟩ := lemma_3_6_9_relOpen T' hT' hpos hYc hYcc hV'rel h0V' σ hσY hσC hσ0 hDσ
  obtain ⟨ρ₃, hρ₃, hρ₃O⟩ := Metric.isOpen_iff.1 hO₁ 0 (hV₁ ▸ h0V₁ : (0 : _) ∈ O₁ ∩ _).1
  -- the projection onto `K` along `Yc`
  have hTC : Submodule.IsTopCompl (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hYc.isCompl.symm hYcc).symm
  set π : Pn × W 0 →L[ℝ] LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) :=
    (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).projectionOntoL Yc hTC with hπdef
  have hπ : ∀ v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), ∀ y ∈ Yc,
      π ((v : Pn × W 0) + y) = v := fun v y hy => by
    rw [map_add, Submodule.projectionOntoL_apply_left hTC v,
      (Submodule.projectionOntoL_apply_eq_zero_iff hTC).2 hy, add_zero]
  set ρ := min (min ρ₁ ρ₂) ρ₃ with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) hρ₃
  set ρ' := ρ / (‖π‖ + 1) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  -- the neighbourhood `N₃ = N₂ ∩ O₃`, `O₃ ∩ U = ψ⁻¹(ball 0 ρ') ∩ U`
  obtain ⟨O₃, hO₃, hO₃eq⟩ := (_root_.continuousOn_iff'.1 hψcont) (ball 0 ρ') isOpen_ball
  have h0O₃ : (0 : E 0) ∈ O₃ := by
    have : (0 : E 0) ∈ ψ ⁻¹' ball 0 ρ' ∩ U :=
      ⟨by rw [mem_preimage, hψ0]; exact mem_ball_self hρ', h0U⟩
    rw [hO₃eq] at this; exact this.1
  refine ⟨N₂ ∩ O₃, hN₂o.inter hO₃, ⟨h0N₂, h0O₃⟩, inter_subset_left, ?_⟩
  rintro z₀ ⟨hz₀O, hz₀N₂, hz₀O₃⟩ hgz₀
  have hz₀U : z₀ ∈ U := hOU hz₀O
  have hball : ψ z₀ ∈ ball 0 ρ' := by
    have : z₀ ∈ O₃ ∩ U := ⟨hz₀O₃, hz₀U⟩
    rw [← hO₃eq] at this; exact this.1
  have hz : ψ z₀ ∈ (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) =>
      (v : Pn × W 0) + σ v) '' V' := by
    rw [← himage]; exact ⟨z₀, ⟨⟨hz₀O, hz₀N₂⟩, hgz₀⟩, rfl⟩
  obtain ⟨v, hv, hveq⟩ := hz
  change (v : Pn × W 0) + σ v = ψ z₀ at hveq
  have hvnorm : ‖v‖ < ρ := by
    have h1 : π (ψ z₀) = v := by rw [← hveq]; exact hπ v _ (hσY v)
    have h2 : ‖ψ z₀‖ < ρ' := by rwa [mem_ball_zero_iff] at hball
    calc ‖v‖ = ‖π (ψ z₀)‖ := by rw [h1]
      _ ≤ ‖π‖ * ‖ψ z₀‖ := π.le_opNorm _
      _ ≤ ‖π‖ * ρ' := by gcongr
      _ < (‖π‖ + 1) * ρ' := by gcongr; linarith
      _ = ρ := by rw [hρ'def]; field_simp
  have hvρ₁ : ‖v‖ < ρ₁ := hvnorm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hvρ₂ : ‖v‖ < ρ₂ := hvnorm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hvρ₃ : ‖v‖ < ρ₃ := hvnorm.trans_le (min_le_right _ _)
  have hvV₁ : v ∈ V₁ := by
    rw [hV₁]
    refine ⟨hρ₃O (mem_ball_zero_iff.2 hvρ₃), ?_⟩
    obtain ⟨O, -, hV'⟩ := hV'rel
    exact (hV' ▸ hv : v ∈ O ∩ _).2
  obtain ⟨x₁, hx₁, hx₁G, hF, hind, hsurj'⟩ := hA v hv hvρ₁
  obtain ⟨hzC, hgc, hgp'⟩ := hB v hv hvρ₂
  -- the level-`1` points
  have hψz₀ : ψ z₀ ∈ U' ∩ Wo := (hN₂ψ z₀ ⟨hz₀U, hz₀N₂⟩).2
  have hx₁U' : x₁ ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, hx₁, hveq]; exact hψz₀.1
  set z₀₁ := levelMap ψ' 1 x₁ with hz₀₁def
  have hz₀₁ : E.toBase 1 z₀₁ = z₀ := by
    rw [hz₀₁def, hψ'sc.isSc1.isSc0.toBase_levelMap hx₁U', hx₁, hveq, hψψ' z₀ hz₀U]
  have hz₀₁U : z₀₁ ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, hz₀₁]; exact hz₀U
  -- the G″ property: `z₀₁ = ψ'₁(x₁)` lies in `(G_g)₁`
  have hz₀₁G : z₀₁ ∈ Gg.U 1 := hGψ' 1 x₁ hx₁G
  have hlev : levelMap ψ 1 z₀₁ = x₁ := levelMap_comp_eq_self hψ'sc.isSc1.isSc0 hx₁U' hψ'ψ
  have hgz₀₁ : g (E.toBase 1 z₀₁) = 0 := by rw [hz₀₁]; exact hgz₀
  -- (a) `N_v = ker D(h + t)(x₁)`
  have hker := 𝒮.graphSpace_eq_ker_Dfs' hCt hh'𝒮 hsurj hpos hYc hYcc hV'rel hσY hσC hsol hO₁ hV₁
    hV₁V' hσ₁ hσ₁eq hvV₁ hx₁ hx₁G hF hind hsurj'
  -- `D(Ψ_*g)(x₁) = D(h + t)(x₁)`: uniqueness of the derivative within `𝒮.G₁`
  have hDeq : pushforwardDeriv U U' Ψ ψ' g Dg x₁ = 𝒮.Dfs' h' x₁ := by
    obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
    obtain ⟨Og₁, hOg₁, hGeq₁⟩ := 𝒮.G.relOpen 1
    have h₁ := (𝒮.isSc1GermWith_Dfs' hCt.isQuadrantLike hh'𝒮.isScSmooth).hasFDerivWithinAt x₁ hx₁G
    have h₂ := hpushG.hasFDerivWithinAt x₁ hx₁G
    have hx₁C : x₁ ∈ (ScBanach.paramProd Pn W).lvlSet (Ct ×ˢ univ) 1 :=
      (ScBanach.paramProd Pn W).lvlSet_mono (fun y hy => (hU'eq ▸ hy : y ∈ Uo ∩ _).2) 1 hx₁U'
    refine scDeriv_eq_of_eqOn_nhds_at hC'q h₂ h₁
      (W₁ := (ScBanach.paramProd Pn W).lvlSet (Wo ∩ Uo) 1 ∩ Og₁)
      (((ScBanach.paramProd Pn W).isOpen_lvlSet (hWo.inter hUo) 1).inter hOg₁)
      ⟨by rw [ScBanach.mem_lvlSet, hx₁, hveq]; exact ⟨hψz₀.2, (hU'eq ▸ hψz₀.1 : ψ z₀ ∈ Uo ∩ _).1⟩,
        (hGeq₁ ▸ hx₁G : x₁ ∈ Og₁ ∩ _).1⟩ ?_ ?_ hx₁C ?_
    · rintro y ⟨⟨-, hyOg⟩, hyC⟩
      rw [hGeq₁]; exact ⟨hyOg, hyC⟩
    · rintro y ⟨⟨-, hyOg⟩, hyC⟩
      rw [hGeq₁]; exact ⟨hyOg, hyC⟩
    · rintro y ⟨⟨hyW, -⟩, hyC⟩
      have hyU' : (ScBanach.paramProd Pn W).toBase 1 y ∈ U' := by
        rw [hU'eq]; exact ⟨(hyW : _ ∈ Wo ∩ Uo).2, hyC⟩
      exact (hagree _ ⟨hyU', (hyW : _ ∈ Wo ∩ Uo).1⟩).symm
  -- (b) `ker Dg(z₀₁) = Dψ'(x₁)(ker D(h + t)(x₁))`
  have hkerb := hΨ.ker_deriv_eq_map_germ hU hU' Dg hz₀₁U hgz₀₁
  rw [hlev, hDeq] at hkerb
  -- `Dg(z₀₁)` is surjective: `D(Ψ_*g)(x₁) = Γ(z₀) Dg(z₀₁) Dψ'(x₁)` with `Γ(z₀)` injective
  have hgsurj : Surjective (Dg z₀₁) := by
    intro k
    obtain ⟨w, hw⟩ := hsurj' (hΨ.toFun.fiberCLM hz₀₁U k)
    refine ⟨scDeriv U' ψ' x₁ w, hΨ.fiberCLM_injective hz₀₁U ?_⟩
    have := hΨ.pushforwardDeriv_at hU Dg hz₀₁U hgz₀₁ w
    rw [hlev, hDeq, hw] at this
    exact this.symm
  -- (c): the transported retraction `r' = ψ ∘ r ∘ ψ'` fixes the graph points
  have hdiff : IsScDiffeoQuadrant hU hU' ψ ψ' := ⟨hψsc, hψ'sc, hψU', hψ'U, hψψ', hψ'ψ⟩
  set rT := hR.baseRetraction hU with hrTdef
  have hrTU : rT.U = U := rfl
  set r' := hdiff.transport rT hrTU with hr'def
  have hr'sc : IsSc1 U' ⇑r' := r'.isScSmooth.isSc1
  set lift := (ScBanach.paramProd Pn W).finLift hKs 1 with hliftdef
  have hliftb : ∀ w, (ScBanach.paramProd Pn W).toBase 1 (lift w) = w := fun w =>
    (ScBanach.paramProd Pn W).toBase_finLift hKs 1 w
  set Γ₁ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) 1 :=
    fun w => lift w + σ₁ w with hΓ₁def
  have hΓ₁ : ∀ w ∈ V₁, (ScBanach.paramProd Pn W).toBase 1 (Γ₁ w) = (w : Pn × W 0) + σ w :=
    fun w hw => by simp only [hΓ₁def, map_add, hliftb, hσ₁eq w hw]
  have hΓ₁v : Γ₁ v = x₁ := (ScBanach.paramProd Pn W).toBase_injective 1 (by rw [hΓ₁ v hvV₁, hx₁])
  have huniq : UniqueDiffWithinAt ℝ V₁ v :=
    uniqueDiffWithinAt_relOpen_cone hCt hpos ⟨O₁, hO₁, hV₁⟩ hvV₁
  have hσ₁d : DifferentiableWithinAt ℝ σ₁ V₁ v := hσ₁.differentiableOn one_ne_zero v hvV₁
  have hΓ₁d : HasFDerivWithinAt Γ₁ (lift + fderivWithin ℝ σ₁ V₁ v) V₁ v :=
    lift.hasFDerivWithinAt.add hσ₁d.hasFDerivWithinAt
  have hDσv : fderivWithin ℝ σ V' v =
      ((ScBanach.paramProd Pn W).toBase 1).comp (fderivWithin ℝ σ₁ V₁ v) :=
    fderivWithin_eq_toBase_comp hO₁ hV₁V'' hvV₁ huniq hσ₁d hσ₁eq
  have hΓ₁U : MapsTo Γ₁ V₁ ((ScBanach.paramProd Pn W).lvlSet U' 1) := fun w hw => by
    rw [ScBanach.mem_lvlSet, hΓ₁ w hw]; exact hG (hsol w (hV₁V' hw)).1
  have hgraphO : ∀ w ∈ V', ψ' ((w : Pn × W 0) + σ w) ∈ r R '' U ∧
      ψ (ψ' ((w : Pn × W 0) + σ w)) = (w : Pn × W 0) + σ w := by
    intro w hw
    have hmem : (w : Pn × W 0) + σ w ∈ ψ '' {u ∈ r R '' U ∩ N₂ | g u = 0} := by
      rw [himage]; exact ⟨w, hw, rfl⟩
    obtain ⟨u, ⟨⟨huO, -⟩, -⟩, hu⟩ := hmem
    have huU := hOU huO
    refine ⟨?_, ?_⟩
    · rw [← hu, hψψ' u huU]; exact huO
    · rw [← hu, hψψ' u huU]
  have hfix : ∀ w ∈ V₁, r' ((ScBanach.paramProd Pn W).toBase 1 (Γ₁ w)) =
      (ScBanach.paramProd Pn W).toBase 1 (Γ₁ w) := by
    intro w hw
    rw [hΓ₁ w hw, hdiff.transport_apply]
    obtain ⟨huO, hψψ⟩ := hgraphO w (hV₁V' hw)
    show ψ (r R (ψ' _)) = _
    rw [r_eq_self hR huO, hψψ]
  have hfixed := fun m => scDeriv_apply_toBase_deriv_eq_of_fixed hr'sc hΓ₁d huniq hvV₁ hΓ₁U hfix m
  set L : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) →L[ℝ] Pn × W 0 :=
    fderivWithin ℝ σ V' v with hLdef
  have hc : ∀ m' ∈ graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) L,
      scDeriv U (r R) z₀₁ (scDeriv U' ψ' x₁ m') = scDeriv U' ψ' x₁ m' := by
    rintro _ ⟨m, rfl⟩
    have h1 := hfixed m
    rw [hΓ₁v] at h1
    have e : (ScBanach.paramProd Pn W).toBase 1 ((lift + fderivWithin ℝ σ₁ V₁ v) m) =
        ((LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).subtype +
          (L : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) →ₗ[ℝ] Pn × W 0)) m := by
      simp only [add_apply, map_add, hliftb, hDσv, LinearMap.add_apply,
        Submodule.subtype_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    rw [e] at h1
    have hyO : ψ' ((ScBanach.paramProd Pn W).toBase 1 x₁) ∈ rT.retract := by
      rw [hx₁]; exact (hgraphO v hv).1
    have h2 := hdiff.scDeriv_transport rT hrTU hx₁U' hyO
      (((LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).subtype +
        (L : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) →ₗ[ℝ] Pn × W 0)) m)
    rw [h1] at h2
    have h3 := congrArg (scDeriv U' ψ' (levelMap ψ 1 z₀₁)) h2
    rw [hΨ.scDeriv_base_inv_base hU hU' hz₀₁U, hlev] at h3
    exact h3.symm
  have hcle : LinearMap.ker (Dg z₀₁ : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z₀₁) := by
    rw [hkerb, ← hker]
    rintro _ ⟨m', hm', rfl⟩
    exact ⟨scDeriv U' ψ' x₁ m', hc m' hm'⟩
  -- (d): good position inside `T_{z₀}O`
  have hS : ∀ x, x ∈ partialQuadrantAtWith T' ((v : Pn × W 0) + σ v) ↔
      scDeriv U' ψ' x₁ x ∈ partialQuadrantAtWith T z₀ := by
    intro x
    have := scDeriv_mem_partialQuadrantAtWith_iff T hT T' hT' hU hU' hψsc hψ'sc hψU' hψ'U hψ'ψ
      hx₁U' x
    rwa [hx₁, hveq, hψψ' z₀ hz₀U, ← hveq] at this
  set S := hΨ.derivInvEquiv hU hU' hz₀₁U with hSdef
  have hSapply : ∀ x, S x = scDeriv U' ψ' x₁ x := fun x => by
    rw [hSdef, hΨ.derivInvEquiv_apply, hlev]
  have hS' : ∀ x, x ∈ partialQuadrantAtWith T' ((v : Pn × W 0) + σ v) ↔
      S x ∈ partialQuadrantAtWith T z₀ := fun x => by rw [hSapply]; exact hS x
  have hgpE := hgp'.map S hS'
  have hSlin : (S : (ScBanach.paramProd Pn W) 0 →ₗ[ℝ] E 0) =
      ((scDeriv U' ψ' x₁ : (ScBanach.paramProd Pn W) 0 →L[ℝ] E 0) :
        (ScBanach.paramProd Pn W) 0 →ₗ[ℝ] E 0) := LinearMap.ext fun x => hSapply x
  have hmapeq : (graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
      (fderivWithin ℝ σ V' v)).map (S : (ScBanach.paramProd Pn W) 0 →ₗ[ℝ] E 0) =
      LinearMap.ker (Dg z₀₁ : E 0 →ₗ[ℝ] F 0) := by
    rw [hkerb, ← hker, hSlin]
  rw [hmapeq] at hgpE
  exact ⟨v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, hz₀₁G, hx₁, hx₁G, hlev, hveq.symm, hF, hind, hsurj', hker,
    hDeq, hkerb, hgsurj, hcle, hgpE.isInGoodPositionIn_of_le hcle⟩

end ChartKernel

end Polyfold
