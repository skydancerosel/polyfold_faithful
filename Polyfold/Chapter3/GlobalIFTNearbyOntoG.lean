import Polyfold.Chapter3.GlobalIFTNearbyOnto
import Polyfold.Chapter3.GlobalIFTNearbySurjG
import Polyfold.Chapter3.GlobalIFTTheoremsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54 (1) with the text's hypotheses — the surjectivity of the linearization at the nearby zeros
by the perturbation argument — and the main theorems 3.54, 3.23, 3.19 without the added
hypothesis, **in the text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# Theorem 3.6.8 (preprint 3.54) (1) with the text's hypotheses, germ reading

## What is formalized

* `Polyfold.theorem_3_6_8_chart_onto`: the germ form of `theorem_3_6_8_chart_onto_wholeChart` (Theorem A
  of the perturbation argument): in the data of `theorem_3_6_8_chart_graph`, for every zero
  `z₀ ∈ O ∩ N₄` of the filling germ `g`, the level-`1` point `z₀₁` over `z₀` and every smooth
  `k ∈ F_∞` there is `x ∈ T_{z₀}O` with `Dg(z₀₁) x = ρ(z₀) k`, for the derivative family `Dg`.
* `Polyfold.theorem_3_6_8_one'`: **Theorem 3.6.8 (preprint 3.54) (1) with the text's hypotheses**, germ
  reading: every zero near `x₀` is in good position in a tame chart (`IsGoodPositionGermTame`).
* `Polyfold.theorem_3_6_8'`, `Polyfold.theorem_3_1_26'`, `Polyfold.theorem_3_1_22'`:
  Theorems 3.6.8 (preprint 3.54) (1)–(2), 3.23 and 3.19 with the text's hypotheses, germ reading.

## What the text leaves implicit, and the choices made (the findings)

* **The curve of zeros lies in the germ of the filling.**  The perturbation argument differentiates
  `g` along the curve `u(μ) = ψ'₁(ι glue(u'(μ)))` of zeros of `g + μ ρ(r(·)) k` through `z₀`,
  where `u'(μ)` lies on level `2` of the germ `𝒮.G` of Theorem 3.5.1 (preprint 3.40).  With `g` a germ on `G_g`
  only, `g ∘ u` is differentiable at `μ = 0` because `u(μ) ∈ (G_g)₁`: `ι glue(u'(μ)) ∈ 𝒮.G₁`
  (`ScNbhdGerm.inclK_mem`) and `ψ'₁` maps `𝒮.G₁ ⊆ G″₁` into `(G_g)₁` (the G″ property).  The
  derivative of `g` at `z₀₁` is the value `Dg(z₀₁)` of the family, and the chain rule along the
  curve is `HasFDerivWithinAt.comp_hasDerivWithinAt` within `(G_g)₁`.  Nothing else of the old
  proof changes: the normal form, its contraction regions, the inward direction and the perturbed
  curve are constructed on the `E'`-side (`GlobalIFTNearbyOnto*.lean`, unchanged), and the
  filler condition (2) on `U ∩ N₂` is level `0`.
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

section ChartOnto

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

set_option maxHeartbeats 3200000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1), the surjectivity of the linearization at the nearby zeros, in the chart at
`x₀`, germ reading** (phase 2; the germ form of `theorem_3_6_8_chart_onto_wholeChart`).  In the data of
`theorem_3_6_8_chart_graph`, with `ψ'` mapping `𝒮.G` into the germ `G_g` of the filling `g`
(derivative family `Dg`), together with condition (2) of Definition 3.1.4 (preprint 3.4) on `N₂` and
`ker D(h + t)(0) ≠ 0`, there is an open neighbourhood `N₄ ⊆ N₂` of `0` such that for every zero
`z₀ ∈ O ∩ N₄` of `g`, every level-`1` point `z₀₁` over `z₀` and every smooth `k ∈ F_∞` there is
`x ∈ T_{z₀}O = Dr(z₀)E` with `Dg(z₀₁) x = ρ(z₀) k`. -/
theorem theorem_3_6_8_chart_onto (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0U : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0U fb g) (hfb0 : fb 0 = 0)
    {Gg : ScNbhdGerm E C} (hGg : Gg.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0}
    (hgD : IsSc1GermWith Gg g Dg)
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
      (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V')
    (hfix : ∀ u ∈ U ∩ N₂, g u = ρ R (r R u) (g u) → u ∈ r R '' U)
    (hK0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) ≠ ⊥) :
    ∃ N₄ : Set (E 0), IsOpen N₄ ∧ (0 : E 0) ∈ N₄ ∧ N₄ ⊆ N₂ ∧
      ∀ z₀ ∈ r R '' U ∩ N₄, g z₀ = 0 → ∀ z₀₁ : E 1, E.toBase 1 z₀₁ = z₀ → ∀ k ∈ F.smooth,
        ∃ x ∈ rangeS (scDeriv U (r R) z₀₁), Dg z₀₁ x = ρ R z₀ k := by
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
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc.isSc1.isSc0.continuousOn_base
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  have hrsc : IsScSmooth U (r R) := hR.toIsStrongBundleMap.base_isScSmooth hU
  have hCq := hCt.isQuadrantLike
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh'𝒮).1.finite_ker
  obtain ⟨n', Wq, T', hT'⟩ := hCt.prod_univ W
  -- Lemma 3.6.9 (preprint 3.55) at the graph points, with its radius
  obtain ⟨ρ₂, hρ₂, hB⟩ := lemma_3_6_9_relOpen T' hT' hpos hYc hYcc hV'rel h0V' σ hσY hσC hσ0 hDσ
  -- the kernel at the nearby zeros
  obtain ⟨N₃, hN₃o, h0N₃, hN₃N₂, hker⟩ := theorem_3_6_8_chart_kernel hU hR h0U h0O hfill
    hfb0 hGg hgD hCt hU' hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂ hG hh'𝒮 hsurj hpos hGψ' hWo hagree hYc hYcc
    hV'rel h0V' hσY hσC
    hσ0 hDσ hsol hlift hN₂o h0N₂ hN₂ψ himage
  -- the normal form, its contraction regions and the bounds of the perturbation
  set 𝒟 := 𝒮.toShiftedBasicData hCq hh'𝒮 with h𝒟
  obtain ⟨δ, hδ, hbounds⟩ := exists_xi_radii_bounds (𝒮 := 𝒮) hU hR hCt hU' hΨ hψ0 h0U hG
  obtain ⟨Rd, hRd⟩ := 𝒟.exists_radii δ hδ
  obtain ⟨r₄₂, hr₄₂, h₄₂⟩ := 𝒮.lemma_3_5_5 hCt hh'𝒮 (Rd.ρ 0) (Rd.ρ_pos 0)
  -- the projection onto `K` along `Yc`
  have hTC : Submodule.IsTopCompl (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hYc.isCompl.symm hYcc).symm
  set π : Pn × W 0 →L[ℝ] LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) :=
    (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).projectionOntoL Yc hTC with hπdef
  have hπ : ∀ v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), ∀ y ∈ Yc,
      π ((v : Pn × W 0) + y) = v := fun v y hy => by
    rw [map_add, Submodule.projectionOntoL_apply_left hTC v,
      (Submodule.projectionOntoL_apply_eq_zero_iff hTC).2 hy, add_zero]
  -- the radius `r'` of the ball in `E'` around `0`
  set cs : ℝ := ‖𝒮.split₀ 0‖ + 1 with hcs
  have hcspos : 0 < cs := by positivity
  set r' : ℝ := min (ρ₂ / (‖π‖ + 1)) (min (r₄₂ / cs) (Rd.ν 3 / cs)) with hr'def
  have hr' : 0 < r' := lt_min (by positivity) (lt_min (by positivity) (by have := Rd.ν_pos 3; positivity))
  obtain ⟨O₄, hO₄, hO₄eq⟩ := (_root_.continuousOn_iff'.1 hψcont) (ball 0 r') isOpen_ball
  have h0O₄ : (0 : E 0) ∈ O₄ := by
    have : (0 : E 0) ∈ ψ ⁻¹' ball 0 r' ∩ U :=
      ⟨by rw [mem_preimage, hψ0]; exact mem_ball_self hr', h0U⟩
    rw [hO₄eq] at this; exact this.1
  refine ⟨N₃ ∩ O₄, hN₃o.inter hO₄, ⟨h0N₃, h0O₄⟩, inter_subset_left.trans hN₃N₂, ?_⟩
  rintro z₀ ⟨hz₀O, hz₀N₃, hz₀O₄⟩ hgz₀ z₀₁ hz₀₁ k hk
  have hz₀U : z₀ ∈ U := hOU hz₀O
  have hz₀N₂ : z₀ ∈ N₂ := hN₃N₂ hz₀N₃
  have hball : ‖ψ z₀‖ < r' := by
    have : z₀ ∈ O₄ ∩ U := ⟨hz₀O₄, hz₀U⟩
    rw [← hO₄eq] at this
    exact mem_ball_zero_iff.1 this.1
  -- the data of the kernel theorem at `z₀`
  obtain ⟨v, hv, z₀₁', x₁, hz₀₁', hz₀₁U', hz₀₁G', hx₁, hx₁G, hlev, hveq, hF, hind, hsurj', hker',
    hDeq, hkerb, hgsurj, hcle, hgpIn⟩ := hker z₀ ⟨hz₀O, hz₀N₃⟩ hgz₀
  have hz₀₁eq : z₀₁ = z₀₁' := E.toBase_injective 1 (by rw [hz₀₁, hz₀₁'])
  subst hz₀₁eq
  rw [← hψdef] at hveq hlev
  have hψz₀ : ψ z₀ ∈ U' ∩ Wo := (hN₂ψ z₀ ⟨hz₀U, hz₀N₂⟩).2
  have hψz₀G : ψ z₀ ∈ 𝒮.G.U 0 := (hN₂ψ z₀ ⟨hz₀U, hz₀N₂⟩).1
  -- `‖v‖ < ρ₂`
  have hvnorm : ‖v‖ < ρ₂ := by
    have h1 : π (ψ z₀) = v := by rw [hveq]; exact hπ v _ (hσY v)
    calc ‖v‖ = ‖π (ψ z₀)‖ := by rw [h1]
      _ ≤ ‖π‖ * ‖ψ z₀‖ := π.le_opNorm _
      _ ≤ ‖π‖ * r' := by gcongr
      _ < (‖π‖ + 1) * r' := by gcongr; linarith
      _ ≤ (‖π‖ + 1) * (ρ₂ / (‖π‖ + 1)) := by gcongr; exact min_le_left _ _
      _ = ρ₂ := by field_simp
  obtain ⟨hzC, -, hgp'⟩ := hB v hv hvnorm
  rw [hker'] at hgp'
  -- the zero `z = split₀(x₁)` of the normal form
  set z : 𝒮.E₀' 1 := 𝒮.split₀ 1 x₁ with hzdef
  have hz : z ∈ 𝒟.G₀.U 1 := by
    change 𝒮.glue₀ 1 (𝒮.split₀ 1 x₁) ∈ 𝒮.G.U 1
    rw [𝒮.glue₀_split₀]; exact hx₁G
  have hglz : 𝒮.glue₀ 1 z = x₁ := 𝒮.glue₀_split₀ 1 x₁
  have hzbase : 𝒮.E₀'.toBase 1 z = 𝒮.split₀ 0 (ψ z₀) := by
    rw [hzdef, 𝒮.split₀.toBase_comm, hx₁, hveq]
  have hx₁1 : x₁.1 = ((v : Pn × W 0) + σ v).1 := by
    have := congrArg Prod.fst hx₁
    rwa [ScBanach.paramProd_toBase] at this
  have hz1 : z.1 = (x₁.1, 𝒮.toC 1 x₁.2) := rfl
  have hzC' : z.1 ∈ Ct ×ˢ (univ : Set 𝒮.Cs) := ⟨by rw [hz1, hx₁1]; exact hzC.1, mem_univ _⟩
  have hzbase1 : (𝒮.E₀'.toBase 1 z).1 = z.1 := by rw [ScBanach.paramProd_toBase]
  have hsplitnorm : ‖𝒮.split₀ 0 (ψ z₀)‖ < cs * r' := by
    calc ‖𝒮.split₀ 0 (ψ z₀)‖ ≤ ‖𝒮.split₀ 0‖ * ‖ψ z₀‖ := (𝒮.split₀ 0).le_opNorm _
      _ ≤ ‖𝒮.split₀ 0‖ * r' := by gcongr
      _ < cs * r' := by rw [hcs]; nlinarith [norm_nonneg (𝒮.split₀ 0)]
  have hzν : ‖z.1‖ < Rd.ν 3 := by
    calc ‖z.1‖ = ‖(𝒮.E₀'.toBase 1 z).1‖ := by rw [hzbase1]
      _ ≤ ‖𝒮.E₀'.toBase 1 z‖ := norm_fst_le _
      _ < cs * r' := by rw [hzbase]; exact hsplitnorm
      _ ≤ cs * (Rd.ν 3 / cs) := by
          gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
      _ = Rd.ν 3 := by field_simp
  -- the zero of the normal form at level `0`
  have hψz₀0 : 𝒮.fsum h' (ψ z₀) = 0 := by rw [hveq]; exact (hsol v hv).2
  have hsplitmem : 𝒮.split₀ 0 (ψ z₀) ∈ 𝒮.pushGerm₀.U 0 := by
    rw [StabilityData.mem_pushGerm₀_U, 𝒮.glue₀_split₀]; exact hψz₀G
  have hsplitzero : 𝒮.pushMap₀ h' (𝒮.split₀ 0 (ψ z₀)) = 0 := by
    unfold StabilityData.pushMap₀
    rw [Function.comp_apply, Function.comp_apply, 𝒮.glue₀_split₀, hψz₀0, map_zero]
  have hzρ : ‖z.2‖ < Rd.ρ 0 := by
    obtain ⟨w₁, hw₁, hw₁n⟩ := h₄₂ _ hsplitmem hsplitzero (hsplitnorm.trans_le (by
      calc cs * r' ≤ cs * (r₄₂ / cs) := by
            gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
        _ = r₄₂ := by field_simp))
    have h1 : 𝒮.XB.toBase 1 z.2 = (𝒮.split₀ 0 (ψ z₀)).2 := by
      have := congrArg Prod.snd hzbase
      rwa [ScBanach.paramProd_toBase] at this
    have h2 : w₁ = z.2 := 𝒮.XB.toBase_injective 1 (by rw [hw₁, h1])
    rw [← h2]; exact hw₁n
  have hz0 : 𝒟.g (𝒮.E₀'.toBase 1 z) = 0 := by rw [hzbase]; exact hsplitzero
  -- the derivative of the normal form at `z` and its kernel
  have hDg : 𝒟.Dg' z = (𝒮.fiber₀ 0).comp ((𝒮.Dfs' h' x₁).comp (𝒮.glue₀ 0)) := by
    have := 𝒮.scDerivGerm_pushMap₀_at hCq hh'𝒮.isScSmooth hz
    rw [hglz] at this
    exact this
  have hkerz : LinearMap.ker (𝒟.Dg' z : (Pn × 𝒮.Cs) × 𝒮.XB 0 →ₗ[ℝ] (Q × 𝒮.Zs) × 𝒮.XB 0) =
      (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)).map
        (𝒮.split₀ 0 : Pn × W 0 →ₗ[ℝ] 𝒮.E₀' 0) := by
    rw [hDg]; exact 𝒮.ker_fiber₀_comp_glue₀ _
  have hFfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    hF.finite_ker
  have hequiv := Submodule.equivMapOfInjective (𝒮.split₀ 0 : Pn × W 0 →ₗ[ℝ] 𝒮.E₀' 0)
    (𝒮.split₀_injective 0) (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0))
  have hfin : FiniteDimensional ℝ
      (LinearMap.ker (𝒟.Dg' z : (Pn × 𝒮.Cs) × 𝒮.XB 0 →ₗ[ℝ] (Q × 𝒮.Zs) × 𝒮.XB 0)) := by
    rw [hkerz]; exact hequiv.finiteDimensional
  have hdimx : (finrank ℝ (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)) : ℤ) =
      finrank ℝ Pn - finrank ℝ Q := by
    rw [finrank_ker_eq_fredholmIndex_of_surjective hF hsurj', hind]
  have hdim : (finrank ℝ
      (LinearMap.ker (𝒟.Dg' z : (Pn × 𝒮.Cs) × 𝒮.XB 0 →ₗ[ℝ] (Q × 𝒮.Zs) × 𝒮.XB 0)) : ℤ) =
      finrank ℝ (Pn × 𝒮.Cs) - finrank ℝ (Q × 𝒮.Zs) := by
    have h1 : finrank ℝ (LinearMap.ker (𝒟.Dg' z : (Pn × 𝒮.Cs) × 𝒮.XB 0 →ₗ[ℝ] (Q × 𝒮.Zs) × 𝒮.XB 0)) =
        finrank ℝ (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)) := by
      rw [hkerz]; exact hequiv.finrank_eq.symm
    rw [h1, hdimx, Module.finrank_prod, Module.finrank_prod, 𝒮.finrank_Cs_eq_finrank_Zs]
    push_cast; ring
  -- the inward direction
  have hK0' : LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0) ≠ ⊥ := by
    intro hbot
    apply hK0
    have hd0 : finrank ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) = 0 := by
      have h1 := finrank_ker_eq_fredholmIndex_of_surjective (𝒮.isFredholm_Dfs hCt hh'𝒮).1 hsurj
      rw [(𝒮.isFredholm_Dfs hCt hh'𝒮).2] at h1
      have h2 : finrank ℝ (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)) = 0 := by
        rw [hbot]; exact finrank_bot ℝ _
      have h3 := hdimx
      rw [h2] at h3
      have : (finrank ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) : ℤ) = 0 := by
        rw [h1]; push_cast at h3 ⊢; linarith
      exact_mod_cast this
    exact Submodule.finrank_eq_zero.1 hd0
  obtain ⟨vv, hvv, η, hη, t₀, ht₀, hin⟩ :=
    exists_inward_of_isInGoodPosition T' hT' hzC hK0' hgp'
  have hvv' : 𝒮.split₀ 0 vv ∈
      LinearMap.ker (𝒟.Dg' z : (Pn × 𝒮.Cs) × 𝒮.XB 0 →ₗ[ℝ] (Q × 𝒮.Zs) × 𝒮.XB 0) := by
    rw [hkerz]; exact Submodule.mem_map_of_mem hvv
  set η' : ℝ := η / (‖𝒮.glue₀ 0‖ + 1) with hη'def
  have hη' : 0 < η' := by positivity
  have hin' : ∀ β : Pn × 𝒮.Cs, ‖β‖ < η' → ∀ t ∈ Icc (0 : ℝ) t₀,
      z.1 + t • ((𝒮.split₀ 0 vv).1 + β) ∈ Ct ×ˢ (univ : Set 𝒮.Cs) := by
    intro β hβ t ht
    set ζ : Pn × W 0 := 𝒮.glue₀ 0 ((β, 0) : 𝒮.E₀' 0) with hζ
    have hζn : ‖ζ‖ < η := by
      have h1 : ‖((β, (0 : 𝒮.XB 0)) : 𝒮.E₀' 0)‖ = ‖β‖ := by
        rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg β)]
      calc ‖ζ‖ ≤ ‖𝒮.glue₀ 0‖ * ‖((β, (0 : 𝒮.XB 0)) : 𝒮.E₀' 0)‖ := (𝒮.glue₀ 0).le_opNorm _
        _ = ‖𝒮.glue₀ 0‖ * ‖β‖ := by rw [h1]
        _ ≤ ‖𝒮.glue₀ 0‖ * η' := by gcongr
        _ < (‖𝒮.glue₀ 0‖ + 1) * η' := by gcongr; linarith
        _ = η := by rw [hη'def]; field_simp
    have h1 := (hin ζ hζn t ht).1
    refine ⟨?_, mem_univ _⟩
    change x₁.1 + t • (vv.1 + β.1) ∈ Ct
    rw [hx₁1]
    simp only [Prod.fst_add, Prod.smul_fst] at h1 ⊢
    exact h1
  -- the perturbation `ê_k`
  obtain ⟨k₁, hk₁⟩ := F.mem_smooth_iff.1 hk 1
  have hk₁' : F.toBase 1 k₁ ∈ F.smooth := by rw [hk₁]; exact hk
  have hê := ehat_isScSmoothGerm (𝒮 := 𝒮) hU hR hCt hU' hΨ hψ0 h0U hG hk₁'
  obtain ⟨c, hc, hce⟩ := hbounds h' Bc hh'𝒮 Rd hRd k₁ hk₁'
  -- the curve of zeros of `G + μ ê_k` through `z`
  obtain ⟨μ₀, hμ₀, cv, ξ, hcv0, hcvd, hcv⟩ := 𝒟.exists_perturbed_curve hCq.prod_univ_const Rd hê
    c hc hce hz hzC' hzν hzρ hz0 hfin hdim hvv' hη' ht₀ hin'
  -- transport to the chart: `u(μ) = ψ⁻¹(glue(u'(μ)))` on level `1`
  set Φ : (ScBanach.paramProd Pn W) 2 → E 1 :=
    levelMap ψ' 1 ∘ (ScBanach.paramProd Pn W).inclK 1 1 with hΦdef
  have hΦ : ContDiffOn ℝ 1 Φ ((ScBanach.paramProd Pn W).lvlSet U' 2) :=
    hψ'sc.contDiffOn_levels hU'.isScDomain 1 1
  have hcvG : ∀ μ ∈ Ico (0 : ℝ) μ₀, cv μ ∈ 𝒮.pushGerm₀.U 2 := fun μ hμ => (hcv μ hμ).1
  have hcvU' : ∀ μ ∈ Ico (0 : ℝ) μ₀,
      𝒮.glue₀ 2 (cv μ) ∈ (ScBanach.paramProd Pn W).lvlSet U' 2 := fun μ hμ => by
    have h1 : 𝒮.glue₀ 2 (cv μ) ∈ 𝒮.G.U 2 := hcvG μ hμ
    rw [ScBanach.mem_lvlSet]
    exact hG (𝒮.G.toBase_mem h1)
  have hbaseΦ : ∀ y ∈ (ScBanach.paramProd Pn W).lvlSet U' 2,
      E.toBase 1 (Φ y) = ψ' ((ScBanach.paramProd Pn W).toBase 2 y) := fun y hy => by
    have h1 : (ScBanach.paramProd Pn W).inclK 1 1 y ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
      rw [ScBanach.mem_lvlSet, (ScBanach.paramProd Pn W).toBase_inclK]
      exact hy
    simp only [hΦdef, Function.comp_apply]
    rw [hψ'sc.isSc1.isSc0.toBase_levelMap h1, (ScBanach.paramProd Pn W).toBase_inclK]
  set u : ℝ → E 1 := fun μ => Φ (𝒮.glue₀ 2 (cv μ)) with hudef
  have h0μ : (0 : ℝ) ∈ Ico (0 : ℝ) μ₀ := ⟨le_rfl, hμ₀⟩
  have hglue0 : (ScBanach.paramProd Pn W).toBase 2 (𝒮.glue₀ 2 (cv 0)) = ψ z₀ := by
    rw [𝒮.glue₀.toBase_comm, hcv0, hzbase, 𝒮.glue₀_split₀]
  have hu0 : u 0 = z₀₁ := by
    apply E.toBase_injective 1
    rw [hz₀₁]
    change E.toBase 1 (Φ (𝒮.glue₀ 2 (cv 0))) = z₀
    rw [hbaseΦ _ (hcvU' 0 h0μ), hglue0, hψψ' z₀ hz₀U]
  -- the base points `u_μ = ψ⁻¹(glue(ι u'(μ)))` and their properties
  set ub : ℝ → E 0 := fun μ => ψ' (𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ))) with hubdef
  have hub : ∀ μ ∈ Ico (0 : ℝ) μ₀, E.toBase 1 (u μ) = ub μ := fun μ hμ => by
    change E.toBase 1 (Φ (𝒮.glue₀ 2 (cv μ))) = ψ' (𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ)))
    rw [hbaseΦ _ (hcvU' μ hμ), 𝒮.glue₀.toBase_comm]
  have hyU' : ∀ μ ∈ Ico (0 : ℝ) μ₀, 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ)) ∈ U' := fun μ hμ => by
    have h1 := hcvU' μ hμ
    rw [ScBanach.mem_lvlSet, 𝒮.glue₀.toBase_comm] at h1
    exact h1
  have hubU : ∀ μ ∈ Ico (0 : ℝ) μ₀, ub μ ∈ U := fun μ hμ => hψ'U (hyU' μ hμ)
  have hub0 : ub 0 = z₀ := by
    change ψ' (𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv 0))) = z₀
    rw [← 𝒮.glue₀.toBase_comm, hglue0, hψψ' z₀ hz₀U]
  -- the derivative of `u` at `0`
  have hcvd' : HasDerivWithinAt (fun μ => 𝒮.glue₀ 2 (cv μ)) (𝒮.glue₀ 2 ξ) (Ico 0 μ₀) 0 :=
    ((𝒮.glue₀ 2).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hcvd).mono Ico_subset_Ici_self
  set ξ₁ : E 1 := fderivWithin ℝ Φ ((ScBanach.paramProd Pn W).lvlSet U' 2)
    (𝒮.glue₀ 2 (cv 0)) (𝒮.glue₀ 2 ξ) with hξ₁
  have hud : HasDerivWithinAt u ξ₁ (Ici 0) 0 := by
    have h1 := (hΦ.differentiableOn one_ne_zero _ (hcvU' 0 h0μ)).hasFDerivWithinAt
    have h2 := h1.comp_hasDerivWithinAt (0 : ℝ) hcvd' (fun μ hμ => hcvU' μ hμ)
    exact h2.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hμ₀)
  set ξ₀ : E 0 := E.toBase 1 ξ₁ with hξ₀
  -- the perturbed equation along the curve, where `glue(ι u'(μ)) ∈ Wo` and `u_μ ∈ N₂`
  have hcvc : ContinuousWithinAt (fun μ => 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ))) (Ici 0) 0 :=
    ((𝒮.glue₀ 0).continuous.comp ((𝒮.E₀').toBase 2).continuous).continuousWithinAt.comp
      hcvd.continuousWithinAt (mapsTo_univ _ _)
  have hcv0' : 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv 0)) = ψ z₀ := by
    rw [← 𝒮.glue₀.toBase_comm, hglue0]
  have hevWo : ∀ᶠ μ in 𝓝[Ici (0 : ℝ)] (0 : ℝ), 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ)) ∈ Wo := by
    refine hcvc.preimage_mem_nhdsWithin ?_
    rw [hcv0']; exact hWo.mem_nhds hψz₀.2
  have hubc : ContinuousWithinAt ub (Ico 0 μ₀) 0 := by
    change ContinuousWithinAt (ψ' ∘ fun μ => 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ))) (Ico 0 μ₀) 0
    exact ContinuousWithinAt.comp (g := ψ') (f := fun μ => 𝒮.glue₀ 0 ((𝒮.E₀').toBase 2 (cv μ)))
      (hψ'cont.continuousWithinAt (hyU' 0 h0μ)) (hcvc.mono Ico_subset_Ici_self)
      fun μ hμ => hyU' μ hμ
  have hevN₂ : ∀ᶠ μ in 𝓝[Ici (0 : ℝ)] (0 : ℝ), ub μ ∈ N₂ := by
    have h1 : ∀ᶠ μ in 𝓝[Ico (0 : ℝ) μ₀] (0 : ℝ), ub μ ∈ N₂ := by
      refine hubc.preimage_mem_nhdsWithin ?_
      rw [hub0]; exact hN₂o.mem_nhds hz₀N₂
    exact h1.filter_mono (nhdsWithin_le_of_mem (Ico_mem_nhdsGE hμ₀))
  obtain ⟨μ₁, hμ₁, hμ₁'⟩ := exists_Ico_of_eventually_nhdsWithin_Ici (hevWo.and hevN₂)
  set μ₂ : ℝ := min μ₀ μ₁ with hμ₂def
  have hμ₂ : 0 < μ₂ := lt_min hμ₀ hμ₁
  have hμ₂₀ : Ico (0 : ℝ) μ₂ ⊆ Ico 0 μ₀ := Ico_subset_Ico_right (min_le_left _ _)
  have hμ₂₁ : Ico (0 : ℝ) μ₂ ⊆ Ico 0 μ₁ := Ico_subset_Ico_right (min_le_right _ _)
  have hzero : ∀ μ ∈ Ico (0 : ℝ) μ₂, g (ub μ) + μ • ρ R (r R (ub μ)) k = 0 := by
    intro μ hμ
    have hμ' := hμ₂₀ hμ
    set y := (𝒮.E₀').toBase 2 (cv μ) with hydef
    set x' := 𝒮.glue₀ 0 y with hx'def
    have hx'U' : x' ∈ U' := hyU' μ hμ'
    have hx'Wo : x' ∈ Wo := (hμ₁' μ (hμ₂₁ hμ)).1
    have hubU' : ub μ ∈ U := hubU μ hμ'
    have hrub : r R (ub μ) ∈ U := r_mem hR hubU'
    have h1 := (hcv μ hμ').2.2
    -- `ι ê_k(y) = Ψ(u_μ, ρ(r(u_μ)) k)` (transported by `fiber₀`)
    have hê1 : (𝒮.F₀' Q).toBase 1 (ehat 𝒮 Ψ Ψ' R k₁ y) =
        𝒮.fiber₀ 0 (Ψ (ub μ, ρ R (r R (ub μ)) k)).2 := by
      change (𝒮.F₀' Q).toBase 1 (𝒮.fiber₀ 1 (shiftFiber Ψ (ψ' x',
        (shiftFiber R (r R (ψ' x'), k₁)).2)).2) = 𝒮.fiber₀ 0 (Ψ (ub μ, ρ R (r R (ub μ)) k)).2
      rw [𝒮.fiber₀.toBase_comm]
      congr 1
      rw [hΨ.toFun.toBase_shiftFiber_snd (p := (ψ' x', _)) hubU',
        hR.toBase_shiftFiber_snd (p := (r R (ψ' x'), k₁)) hrub, hk₁]
      rfl
    have h2 : 𝒮.fiber₀ 0 (𝒮.fsum h' x' + μ • (Ψ (ub μ, ρ R (r R (ub μ)) k)).2) = 0 := by
      rw [map_add, map_smul, ← hê1]
      exact h1
    rw [𝒮.fiber₀_eq_zero_iff] at h2
    rw [hagree x' ⟨hx'U', hx'Wo⟩] at h2
    have h3 : (Ψ (ub μ, g (ub μ) + μ • ρ R (r R (ub μ)) k)).2 = 0 := by
      rw [(hΨ.toFun.fiber_linear _ hubU').map_add, (hΨ.toFun.fiber_linear _ hubU').map_smul]
      exact h2
    exact (hΨ.snd_eq_zero_iff hubU').1 h3
  -- the curve lies in `O` (condition (2) of the filler)
  have hubO : ∀ μ ∈ Ico (0 : ℝ) μ₂, ub μ ∈ r R '' U := fun μ hμ =>
    mem_O_of_perturbed_zero hR (hubU μ (hμ₂₀ hμ)) (hfix _ ⟨hubU μ (hμ₂₀ hμ), (hμ₁' μ (hμ₂₁ hμ)).2⟩)
      (hzero μ hμ)
  -- differentiating `r(u(μ)) = u(μ)` and `g(u(μ)) = −μ ρ(r(u(μ))) k`
  have hz₀₁U : z₀₁ ∈ E.lvlSet U 1 := hz₀₁U'
  have hgd := hgD.hasFDerivWithinAt z₀₁ hz₀₁G'
  have hrd := hrsc.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z₀₁ hz₀₁U
  have humaps : MapsTo u (Ico 0 μ₂) (E.lvlSet U 1) := fun μ hμ => by
    rw [ScBanach.mem_lvlSet, hub μ (hμ₂₀ hμ)]; exact hubU μ (hμ₂₀ hμ)
  -- the curve lies in the germ `G_g` of the filling (the G″ property on level `1`)
  have humapsG : MapsTo u (Ico 0 μ₂) (Gg.U 1) := fun μ hμ => by
    have h1 : 𝒮.glue₀ 2 (cv μ) ∈ 𝒮.G.U (1 + 1) := hcvG μ (hμ₂₀ hμ)
    show levelMap ψ' 1 ((ScBanach.paramProd Pn W).inclK 1 1 (𝒮.glue₀ 2 (cv μ))) ∈ Gg.U 1
    exact hGψ' 1 _ (𝒮.G.inclK_mem h1)
  have hud' : HasDerivWithinAt u ξ₁ (Ico 0 μ₂) 0 := hud.mono Ico_subset_Ici_self
  have hu0' : u 0 = z₀₁ := hu0
  have hgu : HasDerivWithinAt (fun μ => g (E.toBase 1 (u μ))) (Dg z₀₁ ξ₀) (Ici 0) 0 := by
    have h1 : HasFDerivWithinAt (g ∘ E.toBase 1) ((Dg z₀₁).comp (E.toBase 1))
        (Gg.U 1) (u 0) := by rw [hu0']; exact hgd
    exact (h1.comp_hasDerivWithinAt (0 : ℝ) hud' humapsG).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE hμ₂)
  have hru : HasDerivWithinAt (fun μ => r R (E.toBase 1 (u μ))) (scDeriv U (r R) z₀₁ ξ₀)
      (Ici 0) 0 := by
    have h1 : HasFDerivWithinAt (r R ∘ E.toBase 1) ((scDeriv U (r R) z₀₁).comp (E.toBase 1))
        (E.lvlSet U 1) (u 0) := by rw [hu0']; exact hrd
    exact (h1.comp_hasDerivWithinAt (0 : ℝ) hud' humaps).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE hμ₂)
  have hid : HasDerivWithinAt (fun μ => E.toBase 1 (u μ)) ξ₀ (Ici 0) 0 :=
    (E.toBase 1).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hud
  have hevIco : ∀ᶠ μ in 𝓝[Ici (0 : ℝ)] (0 : ℝ), μ ∈ Ico (0 : ℝ) μ₂ := Ico_mem_nhdsGE hμ₂
  have hru' : HasDerivWithinAt (fun μ => E.toBase 1 (u μ)) (scDeriv U (r R) z₀₁ ξ₀) (Ici 0) 0 := by
    refine hru.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hevIco] with μ hμ
      rw [hub μ (hμ₂₀ hμ)]
      exact (r_eq_self hR (hubO μ hμ)).symm
    · rw [hu0', hz₀₁]
      exact (r_eq_self hR hz₀O).symm
  have hξr : scDeriv U (r R) z₀₁ ξ₀ = ξ₀ := eq_of_hasDerivWithinAt_Ici hru' hid
  -- the right derivative of `μ ↦ g(u(μ)) = −μ ρ(r(u(μ))) k`
  set kk : ℝ → F 0 := fun μ => ρ R (r R (E.toBase 1 (u μ))) k with hkkdef
  have hkk : ContinuousWithinAt kk (Ici 0) 0 := by
    have hRc : ContinuousOn R (U ×ˢ univ) := hR.isScSmooth_zero.isSc1.isSc0.continuousOn_base
    have h1 : ContinuousWithinAt (fun μ => ((r R (E.toBase 1 (u μ)), k) : E 0 × F 0))
        (Ico 0 μ₂) 0 :=
      (hru.continuousWithinAt.mono Ico_subset_Ici_self).prodMk continuousWithinAt_const
    have h2 : MapsTo (fun μ => ((r R (E.toBase 1 (u μ)), k) : E 0 × F 0)) (Ico 0 μ₂)
        (U ×ˢ univ) := fun μ hμ => by
      change ((r R (E.toBase 1 (u μ)), k) : E 0 × F 0) ∈ U ×ˢ univ
      rw [hub μ (hμ₂₀ hμ)]; exact ⟨r_mem hR (hubU μ (hμ₂₀ hμ)), mem_univ _⟩
    have h3 : (r R (E.toBase 1 (u 0)), k) ∈ U ×ˢ (univ : Set (F 0)) := by
      rw [hu0', hz₀₁]; exact ⟨r_mem hR hz₀U, mem_univ _⟩
    have h4 := ContinuousWithinAt.comp (g := R)
      (f := fun μ => ((r R (E.toBase 1 (u μ)), k) : E 0 × F 0)) (hRc.continuousWithinAt h3) h1 h2
    have h5 : ContinuousWithinAt kk (Ico 0 μ₂) 0 :=
      ContinuousWithinAt.comp (g := Prod.snd)
        (f := R ∘ fun μ => ((r R (E.toBase 1 (u μ)), k) : E 0 × F 0))
        continuous_snd.continuousWithinAt h4 (mapsTo_univ _ _)
    exact h5.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hμ₂)
  have hsm := hasDerivWithinAt_smul_right_of_continuousWithinAt hkk
  have hgu' : HasDerivWithinAt (fun μ => g (E.toBase 1 (u μ))) (-(kk 0)) (Ici 0) 0 := by
    refine hsm.neg.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hevIco] with μ hμ
      have := hzero μ hμ
      rw [← hub μ (hμ₂₀ hμ)] at this
      change g (E.toBase 1 (u μ)) = -(μ • kk μ)
      exact eq_neg_of_add_eq_zero_left this
    · show g (E.toBase 1 (u 0)) = -((0 : ℝ) • kk 0)
      rw [hu0', hz₀₁, hgz₀, zero_smul, neg_zero]
  have hξg : Dg z₀₁ ξ₀ = -(kk 0) := eq_of_hasDerivWithinAt_Ici hgu hgu'
  have hkk0 : kk 0 = ρ R z₀ k := by
    change ρ R (r R (E.toBase 1 (u 0))) k = ρ R z₀ k
    rw [hu0', hz₀₁, r_eq_self hR hz₀O]
  refine ⟨-ξ₀, ⟨-ξ₀, by show scDeriv U (r R) z₀₁ (-ξ₀) = -ξ₀; rw [map_neg, hξr]⟩, ?_⟩
  rw [map_neg, hξg, hkk0, neg_neg]

end ChartOnto

/-! ### Theorem 3.6.8 (preprint 3.54) (1) with the text's hypotheses, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

set_option maxHeartbeats 3200000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1) with the text's hypotheses, germ reading** (phase 2; the germ form of
`theorem_3_6_8_one'_wholeChart`): let `f` be an sc-Fredholm section with tame germ data in the germ reading
(`IsScFredholmSectionTame`), `f(x₀) = 0`, and `(f, x₀)` in good position in a tame chart
(`IsGoodPositionGermTame`).  Then there is an open neighbourhood `Vx` of `x₀` such that `(f, y)`
is in good position in a tame chart in the germ reading at every zero `y ∈ Vx`.  Proof: in the
chart `c` at `x₀` with the data of Theorem 3.4.2 (preprint 3.38) on `G″`, `theorem_3_6_8_chart_kernel` gives the
kernel conditions and `z₀₁ ∈ (G_g)₁`, `theorem_3_6_8_chart_onto` the surjectivity
`ρ(z₀)F_∞ ⊆ Dg(z₀₁)(T_{z₀}O)` (for `d = 0` the only zero near `x₀` is `x₀`), and the chart
independence `isGoodPositionGermTame_of_chart_dense` transports both to the tame chart of the
germ data at `y`.  No hypothesis beyond the text's is added. -/
theorem theorem_3_6_8_one' (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame f y := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, hsP, ht₀0, hconj, G₀, Dg₀, -, hDg₀, hgp₀⟩ := id hg
  obtain ⟨Gs, -, ht₀⟩ := id hsP
  -- the germ of the filling and its derivative family
  obtain ⟨Gg, hGg, hgsm, -⟩ := hfill.germ
  set Dg := scDerivGerm Gg g with hDgdef
  have hDg : IsSc1GermWith Gg g Dg := (hgsm 1).1.isSc1GermWith_scDerivGerm
  have hgp : IsGoodPositionAtGerm c.relOpen c.isRetraction h0U (Dg 0) :=
    hgp₀.of_isSc1GermWith c.isQuadrantLike hDg₀ hDg
  -- the conjugation data, shrunk to `G″`
  obtain ⟨d⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  set d' := d.shrink c.relOpen h0U (Gg.inter Gs) with hd'def
  have hGψ' : ∀ m, ∀ x ∈ d'.G.U m,
      levelMap (IsStrongBundleMap.base d'.Ψ') m x ∈ Gg.U m ∩ Gs.U m := fun m x hx =>
    d.levelMap_mem_inter_of_mem_shrink c.relOpen h0U hx
  set ψ' := IsStrongBundleMap.base d'.Ψ' with hψ'def
  have hΨ := d'.iso
  have hψ0 := d'.base_zero
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  obtain ⟨h0O', hfb0, hfK⟩ := c.zero_data hfs hxV h0 hx₀
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK := hc.range_id_sub_scDeriv_le hxV h0 T hT
  obtain ⟨𝒮, h', Yc, V', σ, Wo, N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, -, hWo, h0Wo, hagree, hYc, hYcc,
    -, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hN₁o, h0N₁, hN₁, hψ'N₁, hN₂o, h0N₂,
    hN₂N₁, hN₂ψ, hgO, hzero, himage⟩ :=
    theorem_3_6_8_chart_graph hU c.isRetraction h0U h0O' hfill hfb0 hfK hGg hgsm hDg ht₀ ht₀0
      d'.quadrant d'.relOpen hΨ hψ0 d'.germ_subset d'.basic hGψ' d'.conj T hT hK hgp
  have hGψ'g : ∀ m, ∀ x ∈ 𝒮.G.U m, levelMap ψ' m x ∈ Gg.U m := fun m x hx => by
    rw [h𝒮G] at hx; exact (hGψ' m x hx).1
  obtain ⟨N₃, hN₃o, h0N₃, hN₃N₂, hker⟩ := theorem_3_6_8_chart_kernel hU c.isRetraction h0U
    h0O' hfill hfb0 hGg hDg d'.quadrant d'.relOpen hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂
    (h𝒮G ▸ d'.germ_subset) hh'𝒮 hsurj hpos hGψ'g hWo hagree hYc hYcc hV'rel h0V' hσY hσC hσ0 hDσ
    hsol hlift hN₂o h0N₂ hN₂ψ himage
  have hφ : ContinuousOn c.φ c.φ.source := c.φ.continuousOn_toFun
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    exact mem_U_of_mem_O c.isRetraction hz
  -- the zeros `y` near `x₀` with `φ y ∈ N`: `f̂(φ y) = g(φ y) = 0`
  have hzeroN : ∀ y ∈ c.φ.source, c.φ y ∈ N₂ → IsZeroAt P f y → g (c.φ y) = 0 := by
    intro y hyV hyN hy0
    have hyO : c.φ y ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model y hyV
    have hfbg : fb (c.φ y) = g (c.φ y) := (hN₁ _ (hN₂N₁ hyN)).1 hyO
    have hfy : fb (c.φ y) = 0 := (c.isZeroAt_iff hfs hyV).1 hy0
    rw [← hfbg]; exact hfy
  by_cases hK0 : LinearMap.ker (𝒮.Dfs h' : d'.Pn × d'.W 0 →ₗ[ℝ] d'.Q × d'.W 0) = ⊥
  · -- the case `d = 0`: the only zero of `f` in `Vx` is `x₀`
    refine ⟨c.φ.source ∩ c.φ ⁻¹' N₂, hφ.isOpen_inter_preimage c.φ.isOpen_source hN₂o,
      ⟨hxV, by rw [mem_preimage, h0]; exact h0N₂⟩, ?_⟩
    rintro y ⟨hyV, hyN⟩ hy0
    rw [mem_preimage] at hyN
    have hyO : c.φ y ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model y hyV
    have hgy : g (c.φ y) = 0 := hzeroN y hyV hyN hy0
    have hmem : IsStrongBundleMap.base d'.Ψ (c.φ y) ∈
        (fun v : LinearMap.ker (𝒮.Dfs h' : d'.Pn × d'.W 0 →ₗ[ℝ] d'.Q × d'.W 0) =>
          (v : d'.Pn × d'.W 0) + σ v) '' V' := by
      rw [← himage]; exact ⟨c.φ y, ⟨⟨hyO, hyN⟩, hgy⟩, rfl⟩
    obtain ⟨v, -, hveq⟩ := hmem
    change (v : d'.Pn × d'.W 0) + σ v = IsStrongBundleMap.base d'.Ψ (c.φ y) at hveq
    have hbot : ∀ x ∈ LinearMap.ker (𝒮.Dfs h' : d'.Pn × d'.W 0 →ₗ[ℝ] d'.Q × d'.W 0), x = 0 :=
      fun x hx => by
      rw [hK0] at hx; exact (Submodule.mem_bot ℝ).1 hx
    have hv0 : v = 0 := Subtype.ext (hbot v v.2)
    rw [hv0, Submodule.coe_zero, hσ0, add_zero] at hveq
    have hyeq : c.φ y = 0 := by
      have h1 := hΨ.base_base (hOU (c.φ.mapsTo_model y hyV))
      rw [← hveq, hΨ.base_zero' h0U hψ0] at h1
      exact h1.symm
    have hyx : y = x₀ := c.φ.toPartialEquiv.injOn hyV hxV (by rw [hyeq, h0])
    rw [hyx]; exact hg
  · -- the case `d ≥ 1`: the perturbation argument
    have hfix : ∀ u ∈ c.U ∩ N₂, g u = ρ c.R (r c.R u) (g u) → u ∈ r c.R '' c.U :=
      fun u hu => (hN₁ u (hN₂N₁ hu.2)).2.1 hu.1
    obtain ⟨N₄, hN₄o, h0N₄, hN₄N₂, honto⟩ := theorem_3_6_8_chart_onto hU c.isRetraction h0U h0O'
      hfill hfb0 hGg hDg d'.quadrant d'.relOpen hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂
      (h𝒮G ▸ d'.germ_subset) hh'𝒮 hsurj hpos hGψ'g hWo hagree hYc hYcc hV'rel h0V' hσY hσC hσ0 hDσ
      hsol hlift hN₂o h0N₂ hN₂ψ himage hfix hK0
    refine ⟨c.φ.source ∩ c.φ ⁻¹' (N₃ ∩ N₄),
      hφ.isOpen_inter_preimage c.φ.isOpen_source (hN₃o.inter hN₄o),
      ⟨hxV, by rw [mem_preimage, h0]; exact ⟨h0N₃, h0N₄⟩⟩, ?_⟩
    rintro y ⟨hyV, hyN⟩ hy0
    rw [mem_preimage] at hyN
    have hyO : c.φ y ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model y hyV
    have hyN₁ : c.φ y ∈ N₁ := hN₂N₁ (hN₃N₂ hyN.1)
    have hgy : g (c.φ y) = 0 := hzeroN y hyV (hN₃N₂ hyN.1) hy0
    obtain ⟨v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, hz₀₁G, hx₁, hx₁G, hlev, hveq, hF, hind, hsurj', hker',
      hDeq, hkerb, hgsurj, hcle, hgpIn⟩ := hker (c.φ y) ⟨hyO, hyN.1⟩ hgy
    have hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x := by
      filter_upwards [hN₁o.mem_nhds hyN₁] with x hx hxO
      exact (hN₁ x hx).1 (c.r_image ▸ hxO)
    have hysm : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
    refine StrongBundle.isGoodPositionGermTame_of_chart_dense hf.isScSmooth
      (hf.germTame y hysm) hy0 hc.1 hyV hz₀₁ h0U h0O' hDg hz₀₁G hfg T hT (fun k hk => ?_) ?_
    · exact honto (c.φ y) ⟨hyO, hyN.2⟩ hgy z₀₁ hz₀₁ k hk
    · rwa [inf_eq_left.2 hcle]

/-- **Theorem 3.6.8 (preprint 3.54) (1) and (2) with the text's hypotheses, germ reading** (phase 2; the germ form
of `theorem_3_6_8'_wholeChart`): for an sc-Fredholm section with tame germ data in the germ reading,
`f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, (1) every zero `y ∈ Vx` is in good
position in a tame chart (`theorem_3_6_8_one'`); (2) the solution set has the regular tangent
germ data of Definition 3.2.1 (preprint 3.25) (2) at `x₀` on a chart in `Vx`, with locally constant dimension
(`theorem_3_6_8_two`). -/
theorem theorem_3_6_8' (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall⟩ := theorem_3_6_8_one' hf hg hx₀
  exact ⟨Vx, hVxo, hx₀Vx, hall, theorem_3_6_8_two hf.isScSmooth.1 hg hx₀ hVxo hx₀Vx hall⟩

/-- **Theorem 3.1.26 (preprint 3.23) (implicit function theorem, boundary case) with the text's hypotheses, germ
reading** (phase 2; the germ form of `theorem_3_1_26'_wholeChart`): an sc-Fredholm section with tame germ data
in the germ reading, `f(x) = 0`, `(f, x)` in good position in a tame chart; then there is an open
`U ∋ x` such that every zero in `U` is in good position in a tame chart, `S(f, U)` consists of
smooth points, is a sub-M-polyfold, and its induced structure is tame and that of a
`d`-dimensional manifold with boundary with corners. -/
theorem theorem_3_1_26' (hf : B.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermTame f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_6_8_one' hf hg hx
  obtain ⟨U, hUo, hxU, hUV, hsm, d, hsub, h1, h2⟩ :=
    theorem_3_1_26_of_nearby hf.toIsScFredholmSection hx hg hVxo hxVx hall
  exact ⟨U, hUo, hxU, fun y hy hy0 => hall y (hUV hy) hy0, hsm, d, hsub, h1, h2⟩

/-- **Theorem 3.1.22 (preprint 3.19) (implicit function theorem, interior case) with the text's hypotheses, germ
reading** (phase 2; the germ form of `theorem_3_1_22'_wholeChart`): for an M-polyfold without boundary, an
sc-Fredholm section with tame germ data in the germ reading, `f(x₀) = 0` and `(f, x₀)` in good
position in a tame chart; then there is an open `U ∋ x₀` such that every zero in `U` is in good
position in a tame chart, `S(f, U)` consists of smooth points and is a sub-M-polyfold whose
induced structure is that of a `d`-dimensional manifold without boundary. -/
theorem theorem_3_1_22' (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTame f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermTame f x₀) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, hUo, hxU, hgood, hsm, d, hsub, -, h2⟩ := theorem_3_1_26' hf hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, hUo, hxU, hgood, hsm, d, hsub, h2, fun y => ?_⟩
  have := lemma_2_4_6 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

end Bundle

end Polyfold
