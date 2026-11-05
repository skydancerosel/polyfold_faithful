import Polyfold.Chapter3.GlobalIFTNearbyGraph
import Polyfold.Chapter3.GoodPositionGermG
import Polyfold.Chapter3.FredholmGermLinearizationG
import Polyfold.Chapter3.BasicGermShrinkIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54, the graph description of the solution set in the chart at `x₀`, **in the text's germ
reading of Definition 3.11** (phase 2): the filling `g` and the sc⁺-section `t₀` are sc-smooth
germs on germs of neighbourhoods `G_g`, `G_s` whose levels may shrink, and the basic germ lives
on a germ `G` that the inverse base map `ψ'` sends into `G_g ∩ G_s` level by level (the germ
`G″` of `BasicGermShrink.lean`).

# Theorem 3.54 (3) in the chart, germ reading

## What is formalized

* `Polyfold.IsStrongBundleMap.fiberCompDeriv_at`, `Polyfold.IsStrongBundleIso.pushforwardDeriv_at`:
  the chain rule for the push-forward `Ψ_*(g)` of a germ at a level-`1` zero `u₁` of `g`:
  `D(Ψ_*g)(ψ(u₁)) = Γ(u₁) ∘ Dg(u₁) ∘ Dψ'(ψ(u₁))` for the explicit derivative family
  `pushforwardDeriv` (the germ form of `IsStrongBundleIso.scDeriv_pushforward_at`).
* `Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ`:
  `ker Dg(u₁) = Dψ'(ψ u₁)(ker D(Ψ_*g)(ψ u₁))` (the germ form of `ker_scDeriv_eq_map`).
* `Polyfold.theorem_3_54_chart_graph`: **Theorem 3.54 (3) in the chart at `x₀`, germ
  reading** — the germ form of `theorem_3_54_chart_graph_wholeChart`, with the good complement of
  `theorem_3_47_proj` (closed, and with `ProjectsInto`), and `D(h + t)(0) = D(Ψ_*g)(0)` for the
  derivative family `pushforwardDeriv` exposed.

## What the text leaves implicit, and the choices made (the findings)

* **The germ `G` of the basic germ is assumed inside `G″`**: the hypothesis `hGψ'` asks that
  `ψ'_m` map `G_m` into `(G_g)_m ∩ (G_s)_m` for every `m`.  The conjugation of Definition 3.11 can
  always be shrunk to such a germ (`ConjugationData.shrink`, `BasicGermShrink.lean`), with the
  same `Ψ`, `h`, `B`; the section-level statements (`GlobalIFTG.lean`) do this.  On such a `G`
  the push-forward `t = Ψ[1]_*(t₀)` of the sc⁺-germ is an sc-smooth germ (`t₀ ∘ ψ'` is a germ on
  `ψ'⁻¹(G_s) ⊇ G`, then the whole-chart `Ψ[1]` is composed on the outside), the data `𝒮` of
  Theorem 3.38 are built on `G` itself (`𝒮.G = G`), and every nearby zero that Theorem 3.47
  produces lies in `𝒮.G₀ = G₀`.
* **`D(h + t)(0) = D(Ψ_*g)(0)`** is the uniqueness of the derivative at `0` within `G₁` for the two
  maps that agree on `U' ∩ W'`; `D(Ψ_*g)(0)` is the value at `0` of the family `pushforwardDeriv`
  of `Ψ_*(g)` on `ψ'⁻¹(G_g) ⊇ G` (`IsStrongBundleIso.pushforward_isSc1GermWith`), whose
  surjectivity and the good position of whose kernel are `theorem_3_54_pushforward`; the
  Fredholm property of `Dg(0)` that this needs is Proposition 3.52 for germs
  (`proposition_3_52_local`).
* Nothing of `g` or `t₀` away from the germs `G_g`, `G_s` is used: level `0` of `g` enters only
  through the conditions (1)–(2) of the filling (`eq_on`, `mem_of_fixed`, eventual statements at
  `0`) and the conjugation identity on `U ∩ N₁`; the sc¹-structure of `g` enters only at `0`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}

/-! ### The chain rule for the push-forward of a germ at a level-`1` zero -/

section DerivAt

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}

/-- At a level-`1` zero `u₁` of `k`, the level-`1` point of `(1, k)` over `ι u₁` is `(u₁, 0)`. -/
lemma levelMap_pairMap_id_at {k : E 0 → F 0} {u₁ : E 1} (hk0 : k (E.toBase 1 u₁) = 0) :
    levelMap (pairMap id k) 1 u₁ = ((u₁, 0) : (E.prod F) 1) := by
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.prod_toBase, map_zero]
  change ((E.toBase 1 u₁, (0 : F 0)) : (E.prod F) 0) = (E.toBase 1 u₁, k (E.toBase 1 u₁))
  rw [hk0]

/-- **The derivative family of `u ↦ (Ψ(u, k(u)))₂` at a level-`1` zero `u₁` of `k`** is
`Γ(u₁) ∘ Dk(u₁)` (germ reading, phase 2; `fiberCompDeriv_zero_eq` at a general zero, from
`IsStrongBundleMap.scDeriv_fiber_at`). -/
theorem IsStrongBundleMap.fiberCompDeriv_at (hU : IsRelOpenInQuadrant E C U)
    (hΨ : IsStrongBundleMap U U' Ψ) {k : E 0 → F 0} (Dk : E 1 → E 0 →L[ℝ] F 0) {u₁ : E 1}
    (hu₁ : u₁ ∈ E.lvlSet U 1) (hk0 : k (E.toBase 1 u₁) = 0) :
    fiberCompDeriv U Ψ k Dk u₁ = (hΨ.fiberCLM hu₁).comp (Dk u₁) := by
  unfold fiberCompDeriv
  rw [levelMap_pairMap_id_at hk0]
  ext h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  exact hΨ.scDeriv_fiber_at hU hu₁ h (Dk u₁ h)

namespace IsStrongBundleIso

variable (hΨ : IsStrongBundleIso U U' Ψ Ψ')
include hΨ

/-- **The chain rule for the push-forward of a germ at a level-`1` zero `u₁` of `g`** (germ
reading, phase 2; the germ form of `IsStrongBundleIso.scDeriv_pushforward_at`): for the explicit
derivative family `pushforwardDeriv` of `Ψ_*(g)`,
`D(Ψ_*g)(ψ(u₁)) = Γ(u₁) ∘ Dg(u₁) ∘ Dψ'(ψ(u₁))`.  (An identity of the explicit family: it holds
for every `Dg`; that `pushforwardDeriv` is a derivative family of `Ψ_*(g)` is
`pushforward_isSc1GermWith`.) -/
theorem pushforwardDeriv_at (hU : IsRelOpenInQuadrant E C U) {g : E 0 → F 0}
    (Dg : E 1 → E 0 →L[ℝ] F 0) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1)
    (hg0 : g (E.toBase 1 u₁) = 0) (x : E' 0) :
    pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg
        (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) x =
      hΨ.toFun.fiberCLM hu₁ (Dg u₁ (scDeriv U' (IsStrongBundleMap.base Ψ')
        (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) x)) := by
  unfold pushforwardDeriv
  rw [hΨ.levelMap_base_base hU hu₁, hΨ.toFun.fiberCompDeriv_at hU Dg hu₁ hg0]
  rfl

/-- **`ker Dg(u₁) = Dψ'(ψ u₁)(ker D(Ψ_*g)(ψ u₁))`** at a level-`1` zero `u₁` of `g`, for the
derivative family `pushforwardDeriv` (germ reading, phase 2; the germ form of
`ker_scDeriv_eq_map`). -/
theorem ker_deriv_eq_map_germ (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {g : E 0 → F 0} (Dg : E 1 → E 0 →L[ℝ] F 0) {u₁ : E 1}
    (hu₁ : u₁ ∈ E.lvlSet U 1) (hg0 : g (E.toBase 1 u₁) = 0) :
    LinearMap.ker (Dg u₁ : E 0 →ₗ[ℝ] F 0) =
      (LinearMap.ker (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg
        (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) : E' 0 →ₗ[ℝ] F' 0)).map
        (scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) :
          E' 0 →ₗ[ℝ] E 0) := by
  ext v
  rw [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hv
    refine ⟨scDeriv U (IsStrongBundleMap.base Ψ) u₁ v, ?_, hΨ.scDeriv_base_inv_base hU hU' hu₁ v⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΨ.pushforwardDeriv_at hU Dg hu₁ hg0,
      hΨ.scDeriv_base_inv_base hU hU' hu₁, hv, map_zero]
  · rintro ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΨ.pushforwardDeriv_at hU Dg hu₁ hg0] at hw
    exact (map_eq_zero_iff _ (hΨ.fiberCLM_injective hu₁)).1 hw

end IsStrongBundleIso

end DerivAt

/-! ### Theorem 3.54 (3) in the chart at `x₀`, germ reading -/

section ChartGraph

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.54 (3) in the chart at `x₀`, germ reading** (phase 2; the germ form of
`theorem_3_54_chart_graph_wholeChart`).  Let `g` be a filling germ of `f̂` at the zero `0`, sc-smooth on the
germ `G_g ⊆ U` with a derivative family `Dg`, the germ in good position at `Dg(0)`
(`IsGoodPositionAtGerm`), `t₀` an sc⁺-germ on `G_s ⊆ U` with `t₀(0) = g(0)`, `g − t₀` conjugated
by `Ψ` (base map `ψ`, inverse `ψ'`) to the basic germ `h` on a germ `G` that `ψ'` maps into
`G_g ∩ G_s` level by level (`G ⊆ G″`), the retraction tame (`(1 − Dr(0))E ⊆ E₀`).  Then there are
the data `𝒮` of Theorem 3.38 **on the germ `G` itself** and the basic germ `h' = h + (t_{ℝᴺ}, 0)`
with `𝒮.fsum h' = Ψ_*(g)` on `U' ∩ W'`, `W'` an open neighbourhood of `0`;
`D(𝒮.fsum h')(0) = D(Ψ_*g)(0)` (the family `pushforwardDeriv` at `0`), surjective with kernel `K`
in good position; the data `Yc`, `V'`, `σ` of Theorem 3.47 (`Yc` closed, with `ProjectsInto`,
`σ` with `C^k`-lifts); an open neighbourhood `N₁` of `0` on which the identities of the filling
and of the conjugation hold and `ψ'(U' ∩ W') ⊆ N₁`; and an open neighbourhood `N₂ ⊆ N₁` of `0`
such that `ψ(U ∩ N₂) ⊆ G₀ ∩ W'`, every zero of `g` in `U ∩ N₂` lies in `O`,
`g(u) = 0 ↔ 𝒮.fsum h'(ψ u) = 0` on `O ∩ N₂`, and `ψ({u ∈ O ∩ N₂ | g(u) = 0}) = {v + σ(v) | v ∈ V'}`. -/
theorem theorem_3_54_chart_graph (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0U : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0U fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {Gg : ScNbhdGerm E C} (hGg : Gg.U 0 ⊆ U) (hg : IsScSmoothGerm Gg g)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hDg : IsSc1GermWith Gg g Dg)
    {Gs : ScNbhdGerm E C} {t₀ : E 0 → F 1} (ht₀ : IsScSmoothGerm (F := F.shift) Gs t₀)
    (ht₀0 : F.toBase 1 (t₀ 0) = g 0)
    {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {W : ScBanach} {Ct : Set Pn} {U' : Set ((ScBanach.paramProd Pn W) 0)}
    {Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0}
    {Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0}
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
    {Bc : Pn × W 0 → W 0} (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (hG : G.U 0 ⊆ U')
    (hh : IsBasicGerm Ct G h Bc)
    (hGψ' : ∀ m, ∀ x ∈ G.U m, levelMap (IsStrongBundleMap.base Ψ') m x ∈ Gg.U m ∩ Gs.U m)
    (hev : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U →
      (Ψ (u, g u - F.toBase 1 (t₀ u))).2 = h (IsStrongBundleMap.base Ψ u))
    {n : ℕ} {Wc : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wc))
    (hT : C = T 0 ⁻¹' quadrant n Wc 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAtGerm hU hR h0U (Dg 0)) :
    ∃ (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0) (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0)
      (W' : Set ((ScBanach.paramProd Pn W) 0)) (N₁ N₂ : Set (E 0)),
      𝒮.G = G ∧ IsBasicGerm Ct 𝒮.G h' Bc ∧ Surjective (𝒮.Dfs h') ∧
      IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∧
      𝒮.Dfs h' = pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 ∧
      IsOpen W' ∧ (0 : (ScBanach.paramProd Pn W) 0) ∈ W' ∧
      (∀ u' ∈ U' ∩ W', 𝒮.fsum h' u' = pushforward Ψ Ψ' g u') ∧
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      ProjectsInto (Ct ×ˢ univ) (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V' ∧
      (∀ y, σ y ∈ Yc) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (∀ y ∈ V', (y : Pn × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum h' ((y : Pn × W 0) + σ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
        (∃ O : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
          IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V' ∧
        ∃ σk : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) k,
          ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd Pn W).toBase k (σk y) = σ y) ∧
      IsOpen N₁ ∧ (0 : E 0) ∈ N₁ ∧
      (∀ u ∈ N₁, (u ∈ r R '' U → fb u = g u) ∧
        (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
        (u ∈ U → (Ψ (u, g u - F.toBase 1 (t₀ u))).2 = h (IsStrongBundleMap.base Ψ u))) ∧
      (∀ u' ∈ U' ∩ W', IsStrongBundleMap.base Ψ' u' ∈ N₁) ∧
      IsOpen N₂ ∧ (0 : E 0) ∈ N₂ ∧ N₂ ⊆ N₁ ∧
      (∀ u ∈ U ∩ N₂, IsStrongBundleMap.base Ψ u ∈ 𝒮.G.U 0 ∧
        IsStrongBundleMap.base Ψ u ∈ U' ∩ W') ∧
      (∀ u ∈ U ∩ N₂, g u = 0 → u ∈ r R '' U) ∧
      (∀ u ∈ r R '' U ∩ N₂, g u = 0 ↔ 𝒮.fsum h' (IsStrongBundleMap.base Ψ u) = 0) ∧
      IsStrongBundleMap.base Ψ '' {u ∈ r R '' U ∩ N₂ | g u = 0} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' := by
  classical
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set sb : E 0 → F 0 := fun u => F.toBase 1 (t₀ u) with hsbdef
  have hOU : r R '' U ⊆ U := fun z hz => mem_U_of_mem_O hR hz
  have hCq : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  have hC'q : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0U hψ0
  have hψsc : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc.isSc1.isSc0.continuousOn_base
  have hψcont : ContinuousOn ψ U := hψsc.isSc1.isSc0.continuousOn_base
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  have hψ'C : MapsTo ψ' U' C := fun u hu => hU.subset_quadrant (hψ'U hu)
  -- the neighbourhood `N₁` of `0` where the identities of the filling and the conjugation hold
  have hN₀ : ∀ᶠ u in 𝓝 (0 : E 0), (u ∈ r R '' U → fb u = g u) ∧
      (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
      (u ∈ U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := by
    have h1 := hfill.eq_on
    have h2 := hfill.mem_of_fixed
    refine (h1.and (h2.and hev)).mono fun u hu => ⟨hu.1, hu.2.1, fun huU => ?_⟩
    exact hu.2.2 huU
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hN₀
  have hN₁ : ∀ u ∈ N₁, (u ∈ r R '' U → fb u = g u) ∧
      (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
      (u ∈ U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := fun u hu => hN₁sub hu
  have hgO : ∀ u ∈ U, u ∈ N₁ → g u = 0 → u ∈ r R '' U := fun u hu huN hgu =>
    (hN₁ u huN).2.1 hu (by
      rw [hgu]
      exact ((ρ_isLinear hR (r_mem hR hu)).map_zero).symm)
  have hg0 : g 0 = 0 := by rw [← (hN₁ 0 h0N₁).1 h0O, hfb0]
  have ht00 : t₀ 0 = 0 := by
    apply F.toBase_injective 1
    rw [ht₀0, hg0, map_zero]
  -- `G` lies in `U'` level by level and `ψ'` maps it into `G_g` and `G_s`
  have hGsub : ∀ m, G.U m ⊆ (ScBanach.paramProd Pn W).lvlSet U' m := fun m z hz =>
    hG (G.toBase_mem hz)
  have hψ'G : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := E) G ψ' :=
    (hψ'sc.isScSmoothGerm hC'q hU'.relOpen h0U').mono hC'q hGsub
  -- the push-forward sc⁺-germ `t = Ψ[1]_*(t₀)` on `G`
  set t : (ScBanach.paramProd Pn W) 0 → (ScBanach.paramProd Q W).shift 0 :=
    fun u' => (shiftFiber Ψ (ψ' u', t₀ (ψ' u'))).2 with htdef
  have htG : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift)
      G t := by
    -- `t₀ ∘ ψ'` is a germ on `ψ'⁻¹(G_s) ⊇ G`
    have ht₀ψ' : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := F.shift) G (t₀ ∘ ψ') := by
      refine (ht₀.comp_preimage hCq hC'q hU'.relOpen h0U' hψ'sc hψ'0 hψ'C).mono hC'q ?_
      intro m z hz
      exact ⟨by rw [ScNbhdGerm.ofSet_U]; exact hGsub m hz, (hGψ' m z hz).2⟩
    have hpair : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := E.prod F.shift) G
        (pairMap (F := E) (G := F.shift) ψ' (t₀ ∘ ψ')) :=
      IsScSmoothGerm.pair (F := E) (G := F.shift) hC'q hψ'G ht₀ψ'
    have hUF := (hU.prod_univ F.shift).isScDomain
    have hmaps : MapsTo (pairMap (F := E) (G := F.shift) ψ' (t₀ ∘ ψ')) (G.U 0) (U ×ˢ univ) :=
      fun u' hu' => ⟨hψ'U (hG hu'), mem_univ _⟩
    have hcomp := IsScSmooth.comp_germ hC'q hUF hΨ.toFun.isScSmooth_one hpair hmaps
    intro k
    exact (IsSckGerm.operator_comp hC'q
      ((ScBanach.paramProd Pn W).prodSndOp (ScBanach.paramProd Q W).shift) (hcomp k)).congr hC'q
      fun _ _ => rfl
  have ht0 : t 0 = 0 := by
    simp only [htdef, hψ'0, ht00]
    unfold shiftFiber
    simp only [map_zero]
    rw [hΨ.toFun.snd_zero h0U]
    have := Function.leftInverse_invFun ((ScBanach.paramProd Q W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the key identity: for `u ∈ U ∩ N₁`, `Ψ_*(g)(ψ u) = h(ψ u) + ι t(ψ u)`
  have hkey : ∀ u ∈ U, u ∈ N₁ →
      pushforward Ψ Ψ' g (ψ u) = h (ψ u) + (ScBanach.paramProd Q W).toBase 1 (t (ψ u)) := by
    intro u hu huN
    have e1 : t (ψ u) = (shiftFiber Ψ (u, t₀ u)).2 := by
      simp only [htdef]; rw [hψψ' u hu]
    have e2 : (ScBanach.paramProd Q W).toBase 1 (shiftFiber Ψ (u, t₀ u)).2 = (Ψ (u, sb u)).2 :=
      hΨ.toFun.toBase_shiftFiber_snd (p := (u, t₀ u)) hu
    have e3 : h (ψ u) = (Ψ (u, g u - sb u)).2 := ((hN₁ u huN).2.2 hu).symm
    rw [e1, e2, e3, hΨ.toFun.snd_sub hu, sub_add_cancel]
    show (Ψ (ψ' (ψ u), g (ψ' (ψ u)))).2 = (Ψ (u, g u)).2
    rw [hψψ' u hu]
  -- the basic germ `h' = h + (t_{ℝᴺ}, 0)` and the data of Theorem 3.38 with `s = t_W`
  set h' : Pn × W 0 → Q × W 0 := fun x => h x + ScBanach.qPartOp Q W 0 (t x) with hh'def
  have hh' : IsBasicGerm Ct G h' Bc :=
    { isScSmooth := by
        have hq : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := ScBanach.paramProd Q W) G
            (ScBanach.qPartOp Q W 0 ∘ t) :=
          fun k => IsSckGerm.operator_comp hC'q (ScBanach.qPartOp Q W) (htG k)
        have hp : IsScSmoothGerm (E := ScBanach.paramProd Pn W)
            (F := (ScBanach.paramProd Q W).prod (ScBanach.paramProd Q W)) G
            (pairMap (F := ScBanach.paramProd Q W) (G := ScBanach.paramProd Q W) h
              (ScBanach.qPartOp Q W 0 ∘ t)) :=
          IsScSmoothGerm.pair (F := ScBanach.paramProd Q W) (G := ScBanach.paramProd Q W) hC'q
            hh.isScSmooth hq
        intro k
        exact (IsSckGerm.operator_comp hC'q (ScBanach.paramProd Q W).addOp (hp k)).congr hC'q
          fun x _ => rfl
      f_zero := by
        show h 0 + ScBanach.qPartOp Q W 0 (t 0) = 0
        rw [hh.f_zero, ht0, map_zero, add_zero]
      snd_eq := fun x hx => by
        show (h x + ScBanach.qPartOp Q W 0 (t x)).2 = x.2 - Bc x
        rw [Prod.snd_add, hh.snd_eq x hx, ScBanach.qPartOp_apply, add_zero]
      contraction := hh.contraction }
  have hsW : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := W.shift) G
      (fun x => (t x).2) := fun k =>
    (IsSckGerm.operator_comp hC'q (ScBanach.wPartOp Q W) (htG k)).congr hC'q fun _ _ => rfl
  have hsW0 : ((t 0).2 : W 1) = 0 := by rw [ht0]; rfl
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := StabilityData.exists_of_scPlus hsW hsW0
  have hh'𝒮 : IsBasicGerm Ct 𝒮.G h' Bc := by rw [h𝒮G]; exact hh'
  have hfsum : ∀ x, 𝒮.fsum h' x = h x + (ScBanach.paramProd Q W).toBase 1 (t x) := fun x => by
    rw [StabilityData.fsum_apply, h𝒮s, ScBanach.paramProd_toBase]
    change h x + ((t x).1, (0 : W 0)) + ((0 : Q), W.toBase 1 (t x).2) = h x + ((t x).1, W.toBase 1 (t x).2)
    rw [add_assoc]
    congr 1
    ext <;> simp
  -- the push-forward: surjective Fredholm linearization with kernel in good position
  have hconj' : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (t₀ u) :=
    ⟨Pn, Q, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance,
      W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩
  have hDgF : IsFredholm (Dg 0) := by
    obtain ⟨-, -, -, hF, -⟩ := proposition_3_52_local hU hR h0U h0O hfill hfb0 hfK hGg hDg
      ((ht₀ 1).1.isSc1GermWith_scDerivGerm) ht₀0 hconj'
    exact hF
  obtain ⟨-, hpush1, -, hsurjP, -, hposP⟩ := theorem_3_54_pushforward hU hR h0U h0O hfill
    hfb0 hfK hGg hg hDg hDgF T hT hK hgp hU' hΨ hψ0
  -- `G ⊆ ψ'⁻¹(G_g)`: the push-forward is an sc¹-germ on `G`
  have hGpull : ∀ m, G.U m ⊆ (hΨ.pullGerm hU hU' h0U hψ0 Gg).U m := fun m z hz =>
    ⟨hGsub m hz, (hGψ' m z hz).1⟩
  have hpushG : IsSc1GermWith G (pushforward Ψ Ψ' g)
      (pushforwardDeriv U U' Ψ ψ' g Dg) := hpush1.mono hGpull
  -- `D(𝒮.fsum h')(0) = D(Ψ_*g)(0)`: the two maps agree near `0`
  have hW' : ∀ᶠ u' in 𝓝 (0 : (ScBanach.paramProd Pn W) 0), u' ∈ U' → ψ' u' ∈ N₁ := by
    have h1 : Tendsto ψ' (𝓝[U'] 0) (𝓝 0) := by
      have := hψ'cont 0 h0U'
      rwa [ContinuousWithinAt, hψ'0] at this
    exact eventually_nhdsWithin_iff.1 (h1 (hN₁open.mem_nhds h0N₁))
  obtain ⟨W', hW'sub, hW'open, h0W'⟩ := mem_nhds_iff.1 hW'
  obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
  obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 0
  obtain ⟨Og₁, hOg₁, hGeq₁⟩ := G.relOpen 1
  have hGmem : ∀ u', u' ∈ G.U 0 ↔ u' ∈ Og ∧ u' ∈ Ct ×ˢ univ := fun u' => by
    rw [hGeq]; rfl
  have hagree : ∀ u' ∈ U', u' ∈ W' → 𝒮.fsum h' u' = pushforward Ψ Ψ' g u' := by
    intro u' hu' huW
    have hu := hΨ.invFun.base_mem hu'
    rw [hfsum, ← hψ'ψ u' hu', hkey (ψ' u') hu (hW'sub huW hu')]
  have hDeq : 𝒮.Dfs h' = pushforwardDeriv U U' Ψ ψ' g Dg 0 := by
    have hfs1 := (𝒮.fsum_isScSmoothGerm (hCt.isQuadrantLike) (h𝒮G ▸ hh'.isScSmooth) 1).1
      |>.isSc1GermWith_scDerivGerm
    have h₁ := hfs1.hasFDerivWithinAt 0 (𝒮.G.zero_mem 1)
    have h₂ := hpushG.hasFDerivWithinAt 0 (G.zero_mem 1)
    refine scDeriv_eq_of_eqOn_nhds hC'q h₁ h₂
      (W₁ := (ScBanach.paramProd Pn W).lvlSet (W' ∩ Uo) 1 ∩ Og₁)
      (((ScBanach.paramProd Pn W).isOpen_lvlSet (hW'open.inter hUo) 1).inter hOg₁)
      ⟨by rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨h0W', hU'eq ▸ h0U' |>.1⟩,
        (hGeq₁ ▸ G.zero_mem 1 : (0 : (ScBanach.paramProd Pn W) 1) ∈ Og₁ ∩ _).1⟩
      ?_ ?_ (by rw [ScBanach.mem_lvlSet, map_zero]; exact hU'C h0U') ?_
    · rintro x ⟨⟨-, hxOg⟩, hxC⟩
      rw [h𝒮G, hGeq₁]; exact ⟨hxOg, hxC⟩
    · rintro x ⟨⟨-, hxOg⟩, hxC⟩
      rw [hGeq₁]; exact ⟨hxOg, hxC⟩
    · rintro x ⟨⟨hxW, -⟩, hxC⟩
      have hxU' : (ScBanach.paramProd Pn W).toBase 1 x ∈ U' := by
        rw [hU'eq]; exact ⟨(hxW : _ ∈ W' ∩ Uo).2, hxC⟩
      exact hagree _ hxU' (hxW : _ ∈ W' ∩ Uo).1
  have hsurj : Surjective (𝒮.Dfs h') := by rw [hDeq]; exact hsurjP
  have hpos : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) := by rw [hDeq]; exact hposP
  -- Theorem 3.47 for `h + t`
  obtain ⟨Yc, V₀, σ, hYc, hYcc, hYcp, hV₀rel, hV₀0, hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, U'',
    hU''o, h0U'', hU''⟩ := theorem_3_47_proj hCt 𝒮 hh'𝒮 hsurj hpos
  -- the open set `Ω = U'' ∩ W'` of `E'` and the shrunken `V'`
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set ((ScBanach.paramProd Pn W) 0), Ω = U'' ∩ W' := ⟨_, rfl⟩
  have hΩo : IsOpen Ω := hΩdef ▸ hU''o.inter hW'open
  have h0Ω : (0 : (ScBanach.paramProd Pn W) 0) ∈ Ω := hΩdef ▸ ⟨h0U'', h0W'⟩
  have hΩW' : ∀ z ∈ Ω, z ∈ W' := fun z hz => (hΩdef ▸ hz : z ∈ U'' ∩ W').2
  have hΩU'' : ∀ z ∈ Ω, z ∈ U'' := fun z hz => (hΩdef ▸ hz : z ∈ U'' ∩ W').1
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0,
    Γ = fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v :=
    ⟨_, rfl⟩
  have hΓ : ∀ v, Γ v = (v : Pn × W 0) + σ v := fun v => by rw [hΓdef]
  have hΓcont : ContinuousOn Γ V₀ := by
    rw [hΓdef]; exact continuous_subtype_val.continuousOn.add hσC.continuousOn
  obtain ⟨O₁, hO₁, hO₁eq⟩ := (continuousOn_iff'.1 hΓcont) Ω hΩo
  obtain ⟨V', hV'def⟩ : ∃ V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
    V' = V₀ ∩ O₁ := ⟨_, rfl⟩
  have hV'sub : V' ⊆ V₀ := hV'def ▸ inter_subset_left
  have hV'Ω : ∀ v ∈ V', Γ v ∈ Ω := fun v hv => by
    have : v ∈ O₁ ∩ V₀ := ⟨(hV'def ▸ hv : v ∈ V₀ ∩ O₁).2, (hV'def ▸ hv : v ∈ V₀ ∩ O₁).1⟩
    rw [← hO₁eq] at this
    exact this.1
  have hmemV' : ∀ v ∈ V₀, Γ v ∈ Ω → v ∈ V' := fun v hv hΩv => by
    have : v ∈ Γ ⁻¹' Ω ∩ V₀ := ⟨hΩv, hv⟩
    rw [hO₁eq] at this
    rw [hV'def]; exact ⟨hv, this.1⟩
  have hV'rel : ∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
    obtain ⟨O₀, hO₀, hV₀⟩ := hV₀rel
    refine ⟨O₀ ∩ O₁, hO₀.inter hO₁, ?_⟩
    rw [hV'def, hV₀]
    ext v; simp only [mem_inter_iff]; tauto
  have h0V' : (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ V' :=
    hmemV' 0 hV₀0 (by rw [hΓ, Submodule.coe_zero, hσ0, add_zero]; exact h0Ω)
  -- the neighbourhood `N₂` of `0` in `E`: `N₁ ∩ (ψ⁻¹(Ω ∩ Og) relative to U)`
  obtain ⟨O₂, hO₂, hO₂eq⟩ := (continuousOn_iff'.1 hψcont) (Ω ∩ Og) (hΩo.inter hOg)
  obtain ⟨N₂, hN₂def⟩ : ∃ N₂ : Set (E 0), N₂ = N₁ ∩ O₂ := ⟨_, rfl⟩
  have hN₂o : IsOpen N₂ := hN₂def ▸ hN₁open.inter hO₂
  have h0O₂ : (0 : E 0) ∈ O₂ := by
    have : (0 : E 0) ∈ ψ ⁻¹' (Ω ∩ Og) ∩ U :=
      ⟨by rw [mem_preimage, hψ0]; exact ⟨h0Ω, ((hGmem 0).1 (G.zero_mem 0)).1⟩, h0U⟩
    rw [hO₂eq] at this; exact this.1
  have h0N₂ : (0 : E 0) ∈ N₂ := hN₂def ▸ ⟨h0N₁, h0O₂⟩
  have hN₂N₁ : N₂ ⊆ N₁ := hN₂def ▸ inter_subset_left
  have hN₂ψ : ∀ u ∈ U, u ∈ N₂ → ψ u ∈ Ω ∧ ψ u ∈ Og := fun u hu huN => by
    have : u ∈ O₂ ∩ U := ⟨(hN₂def ▸ huN : u ∈ N₁ ∩ O₂).2, hu⟩
    rw [← hO₂eq] at this
    exact this.1
  have hmemN₂ : ∀ u ∈ U, u ∈ N₁ → ψ u ∈ Ω → ψ u ∈ Og → u ∈ N₂ := fun u hu huN hΩ hOg => by
    have : u ∈ ψ ⁻¹' (Ω ∩ Og) ∩ U := ⟨⟨hΩ, hOg⟩, hu⟩
    rw [hO₂eq] at this
    rw [hN₂def]; exact ⟨huN, this.1⟩
  -- for `u ∈ U ∩ N₂`: `ψ u ∈ G.U 0`, and the zeros
  have hN₂G : ∀ u ∈ U, u ∈ N₂ → ψ u ∈ G.U 0 := fun u hu huN =>
    (hGmem _).2 ⟨(hN₂ψ u hu huN).2, hU'C (hψU' hu)⟩
  have hzero : ∀ u ∈ r R '' U, u ∈ N₂ → (g u = 0 ↔ 𝒮.fsum h' (ψ u) = 0) := by
    intro u huO huN
    have huU : u ∈ U := hOU huO
    rw [hfsum, ← hkey _ huU (hN₂N₁ huN)]
    show g u = 0 ↔ (Ψ (ψ' (ψ u), g (ψ' (ψ u)))).2 = 0
    rw [hψψ' _ huU]
    exact (hΨ.snd_eq_zero_iff huU).symm
  -- `Dσ(0) = 0` on the smaller `V'`
  have hDσ' : fderivWithin ℝ σ V' 0 = 0 := by
    have hd : HasFDerivWithinAt σ (0 : _ →L[ℝ] Pn × W 0) V₀ 0 := by
      have := (hσC.differentiableOn one_ne_zero 0 hV₀0).hasFDerivWithinAt
      rwa [hDσ] at this
    have huniq : UniqueDiffWithinAt ℝ V' 0 := uniqueDiffWithinAt_relOpen_cone hCt hpos hV'rel h0V'
    exact (hd.mono hV'sub).fderivWithin huniq
  -- the `C^k` lifts on the smaller `V'`
  have hlift' : ∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
      (∃ O : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
        IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
      (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V' ∧
      ∃ σk : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) k,
        ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd Pn W).toBase k (σk y) = σ y := by
    intro k hk
    obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, h0k, hVkV₀, σk, hσk, hσkeq⟩ := hlift k hk
    refine ⟨Vk ∩ O₁, ⟨Ok ∩ O₁, hOk.inter hO₁, ?_⟩, ⟨h0k, (hV'def ▸ h0V' : (0 : _) ∈ V₀ ∩ O₁).2⟩,
      fun y hy => ?_, σk, hσk.mono inter_subset_left, fun y hy => hσkeq y hy.1⟩
    · rw [hVk, inter_right_comm]
    · rw [hV'def]; exact ⟨hVkV₀ hy.1, hy.2⟩
  refine ⟨𝒮, h', Yc, V', σ, W', N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, hDeq, hW'open, h0W',
    fun u' hu' => hagree u' hu'.1 hu'.2, hYc, hYcc, hYcp, hV'rel, h0V', hσY, hσ1, hσC.mono hV'sub,
    hσ0, hDσ', fun y hy => hsol y (hV'sub hy), hlift', hN₁open, h0N₁, hN₁,
    fun u' hu' => hW'sub hu'.2 hu'.1, hN₂o, h0N₂, hN₂N₁,
    fun u hu => ⟨h𝒮G ▸ hN₂G u hu.1 hu.2, hψU' hu.1, hΩW' _ (hN₂ψ u hu.1 hu.2).1⟩,
    fun u hu hgu => hgO u hu.1 (hN₂N₁ hu.2) hgu, fun u hu => hzero u hu.1 hu.2, ?_⟩
  -- the graph description
  ext z
  constructor
  · rintro ⟨u, ⟨⟨huO, huN⟩, hgu⟩, rfl⟩
    have huU : u ∈ U := hOU huO
    have hz0 : 𝒮.fsum h' (ψ u) = 0 := (hzero u huO huN).1 hgu
    obtain ⟨v, hv, hveq⟩ := hU'' (ψ u) ⟨hΩU'' _ (hN₂ψ u huU huN).1, h𝒮G ▸ hN₂G u huU huN⟩ hz0
    refine ⟨v, hmemV' v hv ?_, hveq.symm⟩
    rw [hΓ, ← hveq]; exact (hN₂ψ u huU huN).1
  · rintro ⟨v, hv, rfl⟩
    have hvV₀ : v ∈ V₀ := hV'sub hv
    obtain ⟨hzG, hz0⟩ := hsol v hvV₀
    have hzG' : (v : Pn × W 0) + σ v ∈ G.U 0 := h𝒮G ▸ hzG
    have hzU' : (v : Pn × W 0) + σ v ∈ U' := hG hzG'
    have hvΩ : (v : Pn × W 0) + σ v ∈ Ω := hΓ v ▸ hV'Ω v hv
    have huN : ψ' ((v : Pn × W 0) + σ v) ∈ N₁ := hW'sub (hΩW' _ hvΩ) hzU'
    have huU : ψ' ((v : Pn × W 0) + σ v) ∈ U := hΨ.invFun.base_mem hzU'
    have hgu : g (ψ' ((v : Pn × W 0) + σ v)) = 0 := by
      have h1 := hkey _ huU huN
      rw [hψ'ψ _ hzU', ← hfsum, hz0] at h1
      have h2 : (Ψ (ψ' ((v : Pn × W 0) + σ v), g (ψ' ((v : Pn × W 0) + σ v)))).2 = 0 := by
        exact h1
      exact (hΨ.snd_eq_zero_iff huU).1 h2
    have huO : ψ' ((v : Pn × W 0) + σ v) ∈ r R '' U := hgO _ huU huN hgu
    refine ⟨ψ' ((v : Pn × W 0) + σ v), ⟨⟨huO, hmemN₂ _ huU huN ?_ ?_⟩, hgu⟩, hψ'ψ _ hzU'⟩
    · rw [hψ'ψ _ hzU']; exact hvΩ
    · rw [hψ'ψ _ hzU']; exact ((hGmem _).1 hzG').1

end ChartGraph

end Polyfold
