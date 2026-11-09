import Polyfold.Chapter3.GlobalIFTNearbySurj
import Polyfold.Chapter3.GlobalIFTNearbyKernelG
import Polyfold.Chapter3.GlobalIFTG
import Polyfold.Chapter3.LinearizationChartsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54 (1) — the kernel of the linearization at the nearby zeros for a section, and "at every
point `y ∈ S` the germ `(f, y)` is in good position" under the filler condition (3) at the
nearby zeros — **in the text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# Theorem 3.6.8 (preprint 3.54) (1) for sections, germ reading

## What is formalized

* `Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ`: Proposition 3.1.5 (preprint 3.5) (1) at a zero
  `z₀ ∈ O` of a filling germ (the germ form of `exists_range_scDeriv_eq_ρ_of_normal_injective`,
  with `Dg(z₀₁)` the value of the derivative family at a level-`1` point of the germ).
* (`Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt`, zeros of a regularizing
  section are smooth points, now lives in `TameGermsG.lean`, where Chapter 5 reaches it.)
* `Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense`: Definition 3.6.6 (preprint 3.53) in a tame chart
  centred at a zero `y`, germ reading, from the germ data of `IsScFredholmGermTame` and the
  kernel and range conditions of `Dg(z)` in any chart around `y`
  (`isGoodPositionAtGerm_of_chart_dense` with Proposition 3.6.5 (preprint 3.52) for germs).
* `Polyfold.theorem_3_6_8_nearby_kernel`: the germ form of `theorem_3_6_8_nearby_kernel_wholeChart`: in
  the data of `theorem_3_6_8_graph`, for every zero `y ∈ Vx₂` the level-`1` point `z₀₁` over
  `ϕ(y)` lies in the germ `G_g` of the filling, `Dg(z₀₁)` is onto, and `ker Dg(z₀₁) ⊆ T_{z₀}O` is
  in good position to `C_{z₀}` inside `T_{z₀}O`.
* `Polyfold.StrongBundle.IsGoodPositionGermFilled`: the germ form of `IsGoodPositionGermFilledWholeChart`
  (condition (3) of Definition 3.1.4 (preprint 3.4) at the nearby zeros `z₁ ∈ G₁`, for the derivative family `Dg`).
* `Polyfold.theorem_3_6_8_one`: **Theorem 3.6.8 (preprint 3.54) (1)** under `IsGoodPositionGermFilled`, germ
  reading: every zero near `x₀` is in good position in a tame chart in the germ reading.

## What the text leaves implicit, and the choices made (the findings)

* The G″ design makes every nearby zero `z₀` a point whose level-`1` lift `z₀₁ = ψ'₁(x₁)` lies in
  the germ `G_g` of the filling; the derivative `Dg(z₀₁)` of the text's "`f'(y)`" is the value of
  the derivative family there.  The condition (3) of `IsGoodPositionGermFilled` is imposed on
  these points `z₁ ∈ (G_g)₁` only (the old `IsGoodPositionGermFilledWholeChart` imposed it at every
  level-`1` point over `O ∩ N`; `IsGoodPositionGermFilledWholeChart.isGoodPositionGermFilled`).
* The chart independence at `y` (`isGoodPositionAtGerm_of_chart_dense`, `LinearizationChartsG.lean`)
  needs the Fredholm property of `Dg'(0)` in the chart centred at `y`, which is Proposition 3.6.5 (preprint 3.52)
  for germs (`proposition_3_6_5_local`) applied to the tame germ data of
  `IsScFredholmSectionTame` at `y`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Proposition 3.1.5 (preprint 3.5) (1) at a zero of a filling germ -/

section Surj

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.1.5 (preprint 3.5) (1) at a zero `z₀ ∈ O` of a filling germ** (germ reading, phase 2; the germ
form of `exists_range_scDeriv_eq_ρ_of_normal_injective`): for `g` an sc¹-germ on `G₁` with
derivative family `Dg`, `z ∈ (G₁)₁` over a zero `z₀ ∈ O` of `f̂ = g` near `z₀`, if `Dg(z)` is
surjective and `(1 − ρ(z₀))Dg(z)` is injective on `ker Dr(z)`, then for every `k ∈ F`,
`ρ(z₀)k = Dg(z)x` for some `x ∈ T_{z₀}O`. -/
theorem exists_range_deriv_eq_ρ_of_normal_injective_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R)) {G₁ : ScNbhdGerm E C}
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U) (hzG : z ∈ G₁.U 1) (hfz : fb (E.toBase 1 z) = 0)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (hsurj : Surjective (Dg z))
    (hinj : ∀ b : E 0, scDeriv U (r R) z b = 0 →
      ρ R (E.toBase 1 z) (Dg z b) = Dg z b → b = 0) (k : F 0) :
    ∃ x ∈ rangeS (scDeriv U (r R) z), Dg z x = ρ R (E.toBase 1 z) k := by
  have hzU : E.toBase 1 z ∈ U := mem_U_of_mem_O hR hzO
  obtain ⟨e, he⟩ := hsurj (ρ R (E.toBase 1 z) k)
  set a := scDeriv U (r R) z e with hadef
  set b := e - a with hbdef
  have hb : scDeriv U (r R) z b = 0 := by
    rw [hbdef, map_sub, hadef, scDeriv_r_idem_at hU hR hzO, sub_self]
  -- `Dg(z₀)a = D(f̂ ∘ r)(z₀)e` has values in `K_{z₀}`
  have hDa : Dg z a = scDeriv U (fb ∘ r R) z e := by
    rw [scDeriv_comp_r_eq_germ hU hR h0 h0O hfr hg hzO hzG heq]; rfl
  have hρa : ρ R (E.toBase 1 z) (Dg z a) = Dg z a := by
    rw [hDa]
    exact rho_scDeriv_comp_r hU hR hfr hfK hzO hfz e
  have hρb : ρ R (E.toBase 1 z) (Dg z b) = Dg z b := by
    have hlin := ρ_isLinear hR hzU
    rw [hbdef, map_sub, hlin.map_sub, hρa, he, ρ_ρ hR hzO]
  have hb0 : b = 0 := hinj b hb hρb
  have hea : e = a := by rw [← sub_eq_zero]; exact hb0
  exact ⟨a, ⟨e, rfl⟩, by rw [← hea]; exact he⟩

end Surj

/-! ### Theorem 3.6.8 (preprint 3.54) (1) at the nearby zeros, for a section of a strong bundle, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Definition 3.6.6 (preprint 3.53) at a zero in a tame chart, from a filling germ in a non-centred chart,
germ reading, dense form** (phase 2; the tame, section-level form of
`isGoodPositionAtGerm_of_chart_dense`): if `(f, y)` has tame germ data in the germ reading
(`IsScFredholmGermTame`), `f(y) = 0`, and in some chart `c` around `y` a germ `g` with derivative
family `Dg` agrees with `f̂` on `O` near `ϕ(y)`, with `Dg(z)(T_zO) ⊇ ρ(z)F_∞` and
`ker Dg(z) ∩ T_zO` in good position to `C_{ϕ(y)}` inside `T_zO` at a level-`1` point `z ∈ G₁`
over `ϕ(y)`, then `(f, y)` is in good position in the tame chart of the germ data
(`IsGoodPositionGermTame`).  The Fredholm property of `Dg'(0)` in the chart centred at `y` is
Proposition 3.6.5 (preprint 3.52) for germs (`proposition_3_6_5_local`). -/
theorem StrongBundle.isGoodPositionGermTame_of_chart_dense (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGermTame f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U)
    {g : c.φ.model.E 0 → c.F 0} {G : ScNbhdGerm c.φ.model.E c.φ.model.C}
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg) (hzG : z ∈ G.U 1)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x ∈ rangeS (scDeriv c.U (r c.R) z),
      Dg z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (r c.R) z))) :
    B.IsGoodPositionGermTame f y := by
  obtain ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', ⟨Gs', hGs', hs'⟩, hs0', hconj'⟩ := hy
  obtain ⟨h0O', hfb0', hfK'⟩ := c'.zero_data hf.1 hyV' hφ0 hy0
  obtain ⟨G', hG'U, hg'sm, -⟩ := hfill'.germ
  have hg' := (hg'sm 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨-, -, -, hDgF', -⟩ := proposition_3_6_5_local c'.relOpen c'.isRetraction h0U' h0O'
    hfill' hfb0' hfK' hG'U hg' ((hs' 1).1.isSc1GermWith_scDerivGerm) hs0' hconj'
  exact ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', ⟨Gs', hGs', hs'⟩, hs0', hconj', G', _,
    hG'U, hg', StrongBundle.isGoodPositionAtGerm_of_chart_dense hf hy0 hc hyV hz h0U h0O hg hzG
      hfg T hT hsurj hker hc'.1 hyV' hφ0 h0U' hfill' hG'U hg' hDgF'⟩

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1) at the nearby zeros, the kernel, in the chart at `x₀`, for a section, germ
reading** (phase 2; the germ form of `theorem_3_6_8_nearby_kernel_wholeChart`).  In the setting of
`theorem_3_6_8_graph` (whose conclusion is restated), with the filling germ `g` of
`f̂ = c.principal f` on the germ `G_g` (derivative family `Dg`) and its sc⁺-germ `t₀` exposed:
there is an open neighbourhood `Vx₂ ⊆ Vx` of `x₀` such that for every zero `y ∈ Vx₂` of `f`, with
`z₀ = ϕ(y)` and `z = ψ(z₀) = v + σ(v)`, `v ∈ V'`, there are the level-`1` points
`z₀₁ ∈ U₁ ∩ (G_g)₁` over `z₀` and `x₁ = ψ₁(z₀₁) ∈ G₁` over `z` with: (i) `D(h + t)(x₁)` a
surjective Fredholm operator of index `n − N`; (a) `N_v = ker D(h + t)(x₁)`;
(b) `D(Ψ_*g)(x₁) = D(h + t)(x₁)` and `ker Dg(z₀₁) = Dψ'(x₁)(ker D(h + t)(x₁))`, `Dg(z₀₁)` onto;
(c) `ker Dg(z₀₁) ⊆ T_{z₀}O`; (d) `ker Dg(z₀₁)` in good position to `C_{z₀}` inside `T_{z₀}O`.
Moreover `f̂ = g` on `O` near `z₀` and `g(z₀) = 0`. -/
theorem theorem_3_6_8_nearby_kernel (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0U : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (t₀ : c.φ.model.E 0 → c.F 1)
      (Gg : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (Ψ : c.φ.model.E 0 × c.F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0)
      (Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → c.φ.model.E 0 × c.F 0)
      (_ : IsStrongBundleIso c.U U' Ψ Ψ') (_ : IsStrongBundleMap.base Ψ 0 = 0)
      (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X)
      (n' : ℕ) (Wq : ScBanach)
      (T : ScIso c.φ.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq)) (Vx₂ : Set X),
      IsFillingGerm c.relOpen c.isRetraction h0U (c.principal f) g ∧
      IsScPlusGerm c.φ.model.C c.U t₀ ∧ c.F.toBase 1 (t₀ 0) = g 0 ∧
      IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (t₀ u)) ∧
      Gg.U 0 ⊆ c.U ∧ IsScSmoothGerm Gg g ∧ IsSc1GermWith Gg g Dg ∧
      IsGoodPositionAtGerm c.relOpen c.isRetraction h0U (Dg 0) ∧
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) ≤ (ScBanach.paramProd Pn W).smooth ∧
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
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (IsStrongBundleMap.base Ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (IsStrongBundleMap.base Ψ (c.φ y)) = 0) ∧
      (IsStrongBundleMap.base Ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' ∧
      c.φ.model.C = T 0 ⁻¹' quadrant n' Wq 0 ∧
      IsOpen Vx₂ ∧ x₀ ∈ Vx₂ ∧ Vx₂ ⊆ Vx ∧
      ∀ y ∈ Vx₂, IsZeroAt P f y →
        (∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x) ∧ g (c.φ y) = 0 ∧
        ∃ (v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) (_ : v ∈ V')
          (z₀₁ : c.φ.model.E 1) (x₁ : (ScBanach.paramProd Pn W) 1),
          c.φ.model.E.toBase 1 z₀₁ = c.φ y ∧ z₀₁ ∈ c.φ.model.E.lvlSet c.U 1 ∧ z₀₁ ∈ Gg.U 1 ∧
          (ScBanach.paramProd Pn W).toBase 1 x₁ = (v : Pn × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
          levelMap (IsStrongBundleMap.base Ψ) 1 z₀₁ = x₁ ∧
          IsStrongBundleMap.base Ψ (c.φ y) = (v : Pn × W 0) + σ v ∧
          IsFredholm (𝒮.Dfs' h' x₁) ∧
          fredholmIndex (𝒮.Dfs' h' x₁) = finrank ℝ Pn - finrank ℝ Q ∧
          Surjective (𝒮.Dfs' h' x₁) ∧
          graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) (fderivWithin ℝ σ V' v) =
            LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0) ∧
          pushforwardDeriv c.U U' Ψ (IsStrongBundleMap.base Ψ') g Dg x₁ = 𝒮.Dfs' h' x₁ ∧
          LinearMap.ker (Dg z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0) =
            (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)).map
              (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ : Pn × W 0 →ₗ[ℝ] c.φ.model.E 0) ∧
          Surjective (Dg z₀₁) ∧
          LinearMap.ker (Dg z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤
            rangeS (scDeriv c.U (r c.R) z₀₁) ∧
          IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z₀₁))
            (partialQuadrantAtWith T (c.φ y))
            (LinearMap.ker (Dg z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) := by
  classical
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, hsP, ht₀0, hconj, G₀, Dg₀, -, hDg₀, hgp₀⟩ := hg
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
  -- notation and the data of the chart
  set ψ := IsStrongBundleMap.base d'.Ψ with hψdef
  set ψ' := IsStrongBundleMap.base d'.Ψ' with hψ'def
  have hΨ := d'.iso
  have hψ0 := d'.base_zero
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    exact mem_U_of_mem_O c.isRetraction hz
  obtain ⟨h0O', hfb0, hfK⟩ := c.zero_data hf hxV h0 hx₀
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK := hc.range_id_sub_scDeriv_le hxV h0 T hT
  -- the graph description in the chart, on `G″`
  obtain ⟨𝒮, h', Yc, V', σ, Wo, N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, -, hWo, h0Wo, hagree, hYc, hYcc,
    -, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hN₁o, h0N₁, hN₁, hψ'N₁, hN₂o, h0N₂,
    hN₂N₁, hN₂ψ, hgO, hzero, himage⟩ :=
    theorem_3_6_8_chart_graph hU c.isRetraction h0U h0O' hfill hfb0 hfK hGg hgsm hDg ht₀ ht₀0
      d'.quadrant d'.relOpen hΨ hψ0 d'.germ_subset d'.basic hGψ' d'.conj T hT hK hgp
  have hGψ'g : ∀ m, ∀ x ∈ 𝒮.G.U m, levelMap ψ' m x ∈ Gg.U m := fun m x hx => by
    rw [h𝒮G] at hx; exact (hGψ' m x hx).1
  -- the kernel at the nearby zeros
  obtain ⟨N₃, hN₃o, h0N₃, hN₃N₂, hker⟩ := theorem_3_6_8_chart_kernel hU c.isRetraction h0U
    h0O' hfill hfb0 hGg hDg d'.quadrant d'.relOpen hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂
    (h𝒮G ▸ d'.germ_subset) hh'𝒮 hsurj hpos hGψ'g hWo hagree hYc hYcc hV'rel h0V' hσY hσC hσ0 hDσ
    hsol hlift hN₂o h0N₂ hN₂ψ himage
  -- the neighbourhoods `Vx`, `Vx₂` of `x₀`
  have hφ : ContinuousOn c.φ c.φ.source := c.φ.continuousOn_toFun
  obtain ⟨Vx, hVxdef⟩ : ∃ Vx : Set X, Vx = c.φ.source ∩ c.φ ⁻¹' N₂ := ⟨_, rfl⟩
  have hmemVx : ∀ y, y ∈ Vx ↔ y ∈ c.φ.source ∧ c.φ y ∈ N₂ := fun y => by rw [hVxdef]; rfl
  have hVxo : IsOpen Vx := hVxdef ▸ hφ.isOpen_inter_preimage c.φ.isOpen_source hN₂o
  have hx₀Vx : x₀ ∈ Vx := (hmemVx x₀).2 ⟨hxV, by rw [h0]; exact h0N₂⟩
  have hVxsub : Vx ⊆ c.φ.source := fun y hy => ((hmemVx y).1 hy).1
  have hVxN₂ : ∀ y ∈ Vx, c.φ y ∈ N₂ := fun y hy => ((hmemVx y).1 hy).2
  obtain ⟨Vx₂, hVx₂def⟩ : ∃ Vx₂ : Set X, Vx₂ = c.φ.source ∩ c.φ ⁻¹' N₃ := ⟨_, rfl⟩
  have hmemVx₂ : ∀ y, y ∈ Vx₂ ↔ y ∈ c.φ.source ∧ c.φ y ∈ N₃ := fun y => by rw [hVx₂def]; rfl
  have hVx₂o : IsOpen Vx₂ := hVx₂def ▸ hφ.isOpen_inter_preimage c.φ.isOpen_source hN₃o
  have hx₀Vx₂ : x₀ ∈ Vx₂ := (hmemVx₂ x₀).2 ⟨hxV, by rw [h0]; exact h0N₃⟩
  have hVx₂Vx : Vx₂ ⊆ Vx := fun y hy =>
    (hmemVx y).2 ⟨((hmemVx₂ y).1 hy).1, hN₃N₂ ((hmemVx₂ y).1 hy).2⟩
  -- the zeros in `Vx`: `f̂(ϕ y) = g(ϕ y)`
  have hfbg : ∀ y ∈ Vx, fb (c.φ y) = g (c.φ y) := fun y hy =>
    (hN₁ _ (hN₂N₁ (hVxN₂ y hy))).1 (c.r_image ▸ c.φ.mapsTo_model y (hVxsub hy))
  have hzero' : ∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0 := fun y hy => by
    rw [c.isZeroAt_iff hf (hVxsub hy), ← hfbdef, hfbg y hy]
    exact hzero _ ⟨c.r_image ▸ c.φ.mapsTo_model y (hVxsub hy), hVxN₂ y hy⟩
  refine ⟨c, hc, hxV, h0, h0U, g, t₀, Gg, Dg, d'.Pn, d'.Q, d'.i1, d'.i2, d'.i3, d'.i4, d'.i5,
    d'.i6, d'.W, d'.Ct, d'.quadrant, d'.U', d'.relOpen, d'.Ψ, d'.Ψ', hΨ, hψ0, 𝒮, h', d'.Bc, hh'𝒮,
    hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, hsP, ht₀0, hconj, hGg, hgsm, hDg, hgp,
    hYc, hYcc, 𝒮.ker_Dfs_le_smooth d'.quadrant hh'𝒮, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol,
    hlift, hVxo, hx₀Vx, hVxsub, ?_, hzero', ?_, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, ?_⟩
  · -- injectivity of `ψ ∘ ϕ` on `Vx`
    intro y hy y' hy' heq
    have h1 : ψ' (ψ (c.φ y)) = ψ' (ψ (c.φ y')) := congrArg ψ' heq
    rw [hψψ' _ (hOU (c.φ.mapsTo_model y (hVxsub hy))),
      hψψ' _ (hOU (c.φ.mapsTo_model y' (hVxsub hy')))] at h1
    exact c.φ.toPartialEquiv.injOn (hVxsub hy) (hVxsub hy') h1
  · -- the graph description
    rw [← himage]
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyz⟩, rfl⟩
      refine ⟨c.φ y, ⟨⟨c.r_image ▸ c.φ.mapsTo_model y (hVxsub hy), hVxN₂ y hy⟩, ?_⟩, rfl⟩
      rw [← hfbg y hy]; exact (c.isZeroAt_iff hf (hVxsub hy)).1 hyz
    · rintro ⟨u, ⟨⟨huO, huN⟩, hgu⟩, rfl⟩
      have huO' : u ∈ c.φ.model.O := c.r_image ▸ huO
      have hyV : c.φ.symm u ∈ c.φ.source := c.φ.symm_mapsTo huO'
      have hyVx : c.φ.symm u ∈ Vx :=
        (hmemVx _).2 ⟨hyV, by rw [c.φ.apply_symm_apply huO']; exact huN⟩
      refine ⟨c.φ.symm u, ⟨hyVx, ?_⟩, ?_⟩
      · have h1 := hfbg _ hyVx
        rw [c.φ.apply_symm_apply huO'] at h1
        rw [c.isZeroAt_iff hf hyV, c.φ.apply_symm_apply huO', ← hfbdef, h1]
        exact hgu
      · show ψ (c.φ (c.φ.symm u)) = ψ u
        rw [c.φ.apply_symm_apply huO']
  · -- the zeros in `Vx₂`
    intro y hy hy0
    have hyV : y ∈ c.φ.source := hVxsub (hVx₂Vx hy)
    have hyO : c.φ y ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model y hyV
    have hyN₃ : c.φ y ∈ N₃ := ((hmemVx₂ y).1 hy).2
    have hgy : g (c.φ y) = 0 := by
      rw [← hfbg y (hVx₂Vx hy)]; exact (c.isZeroAt_iff hf hyV).1 hy0
    refine ⟨?_, hgy, hker (c.φ y) ⟨hyO, hyN₃⟩ hgy⟩
    filter_upwards [hN₁o.mem_nhds (hN₂N₁ (hN₃N₂ hyN₃))] with x hx hxO
    exact (hN₁ x hx).1 (c.r_image ▸ hxO)

/-! ### Theorem 3.6.8 (preprint 3.54) (1) under the filler condition (3) at the nearby zeros, germ reading -/

variable (B) in
/-- **Definition 3.6.6 (preprint 3.53) with a filling germ satisfying condition (3) of Definition 3.1.4 (preprint 3.4) at the nearby
zeros, germ reading** (phase 2; the germ form of `IsGoodPositionGermFilledWholeChart`): the data of
`StrongBundle.IsGoodPositionGermTame` (a tame chart centred at `x₀`, a filling germ `g` of `f̂`,
an sc⁺-germ `s` with `g − s` conjugated to a basic germ, a germ `G ⊆ U` with a derivative family
`Dg` of `g`, the germ in good position at `Dg(0)`), together with: on a neighbourhood `N` of `0`,
at every zero `z₀ ∈ O` of `g` and every level-`1` point `z₁ ∈ G₁` over `z₀`, the operator
`(1 − ρ(z₀))Dg(z₁)` is injective on `ker Dr(z₁)`. -/
def StrongBundle.IsGoodPositionGermFilled (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
      IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0) ∧
      ∃ N : Set (c.φ.model.E 0), IsOpen N ∧ (0 : c.φ.model.E 0) ∈ N ∧
        ∀ z₁ ∈ G.U 1, c.φ.model.E.toBase 1 z₁ ∈ c.φ.model.O ∩ N →
          g (c.φ.model.E.toBase 1 z₁) = 0 →
          ∀ b : c.φ.model.E 0, scDeriv c.U (r c.R) z₁ b = 0 →
            ρ c.R (c.φ.model.E.toBase 1 z₁) (Dg z₁ b) = Dg z₁ b → b = 0

/-- The strengthened good position implies Definition 3.6.6 (preprint 3.53) in a tame chart (germ reading). -/
theorem StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame {x₀ : X}
    (h : B.IsGoodPositionGermFilled f x₀) : B.IsGoodPositionGermTame f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg, hgp, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg, hgp⟩

/-- The strengthened good position implies Definition 3.6.6 (preprint 3.53) (germ reading). -/
theorem StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm {x₀ : X}
    (h : B.IsGoodPositionGermFilled f x₀) : B.IsGoodPositionGerm f x₀ :=
  h.isGoodPositionGermTame.isGoodPositionGerm

/-- **Project ⇒ germ reading** for the strengthened good position (phase 2): with the germ
`ofSet U` and `Dg = scDeriv U g`. -/
theorem StrongBundle.IsGoodPositionGermFilledWholeChart.isGoodPositionGermFilled {x₀ : X}
    (h : B.IsGoodPositionGermFilledWholeChart f x₀) : B.IsGoodPositionGermFilled f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp, N, hNo, h0N, h3⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hsm.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj,
    ScNbhdGerm.ofSet c.relOpen.relOpen h0, scDeriv c.U g, fun _ hu => hu,
    hfill.isScSmooth.isSc1.isSc1GermWith_ofSet c.relOpen.relOpen h0,
    isGoodPositionAt_iff_germ.1 hgp, N, hNo, h0N, fun z₁ _ hz₁ hg₁ => h3 z₁ hz₁ hg₁⟩

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1), germ reading** ("at every point `y ∈ S` the sc-Fredholm germ `(f, y)` is
in good position"; phase 2, the germ form of `theorem_3_6_8_one_wholeChart`), under the **added hypothesis**
that the filling germ at `x₀` satisfies condition (3) of Definition 3.1.4 (preprint 3.4) at the nearby zeros
(`IsGoodPositionGermFilled`).  Let `f` be an sc-Fredholm section with tame germ data in the germ
reading (`IsScFredholmSectionTame`), `f(x₀) = 0`, and `(f, x₀)` in good position in a tame chart
with such a filling germ.  Then there is an open neighbourhood `Vx` of `x₀` such that `(f, y)` is
in good position in a tame chart in the germ reading (`IsGoodPositionGermTame`) at every zero
`y ∈ Vx`.  Proof: in the chart `c` at `x₀`, `theorem_3_6_8_chart_kernel` gives
`z₀₁ ∈ (G_g)₁`, `ker Dg(z₀₁) ⊆ T_{z₀}O` in good position to `C_{z₀}` inside `T_{z₀}O` and
`Dg(z₀₁)` onto; condition (3) at `z₀₁` turns the latter into the surjectivity of
`Tf̃(z₀) : T_{z₀}O → K_{z₀}` (`exists_range_deriv_eq_ρ_of_normal_injective_germ`), and the chart
independence `isGoodPositionGermTame_of_chart_dense` transports both to the tame chart of the
germ data at `y`. -/
theorem theorem_3_6_8_one (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermFilled f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame f y := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, hsP, ht₀0, hconj, G₁, Dg, hG₁, hDg₁, hgp, N, hNo,
    h0N, h3⟩ := hg
  obtain ⟨Gs, -, ht₀⟩ := id hsP
  obtain ⟨Gg', -, hgsm', -⟩ := hfill.germ
  -- the germ `G_g = G₁ ∩ G_g'`, on which `g` is sc-smooth with the derivative family `Dg`
  set Gg := G₁.inter Gg' with hGgdef
  have hGg : Gg.U 0 ⊆ c.U := fun x hx => hG₁ hx.1
  have hgsm : IsScSmoothGerm Gg g := hgsm'.mono c.isQuadrantLike (G₁.inter_subset_right Gg')
  have hDg : IsSc1GermWith Gg g Dg := hDg₁.mono (G₁.inter_subset_left Gg')
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
  refine ⟨c.φ.source ∩ c.φ ⁻¹' (N₃ ∩ N),
    hφ.isOpen_inter_preimage c.φ.isOpen_source (hN₃o.inter hNo),
    ⟨hxV, by rw [mem_preimage, h0]; exact ⟨h0N₃, h0N⟩⟩, ?_⟩
  rintro y ⟨hyV, hyN⟩ hy0
  rw [mem_preimage] at hyN
  have hyO : c.φ y ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model y hyV
  have hyN₁ : c.φ y ∈ N₁ := hN₂N₁ (hN₃N₂ hyN.1)
  have hfbg : fb (c.φ y) = g (c.φ y) := (hN₁ _ hyN₁).1 hyO
  have hfy : fb (c.φ y) = 0 := (c.isZeroAt_iff hfs hyV).1 hy0
  have hgy : g (c.φ y) = 0 := hfbg ▸ hfy
  obtain ⟨v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, hz₀₁G, hx₁, hx₁G, hlev, hveq, hF, hind, hsurj', hker',
    hDeq, hkerb, hgsurj, hcle, hgpIn⟩ := hker (c.φ y) ⟨hyO, hyN.1⟩ hgy
  have hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x := by
    filter_upwards [hN₁o.mem_nhds hyN₁] with x hx hxO
    exact (hN₁ x hx).1 (c.r_image ▸ hxO)
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc.1
  have hysm : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  refine StrongBundle.isGoodPositionGermTame_of_chart_dense hf.isScSmooth (hf.germTame y hysm)
    hy0 hc.1 hyV hz₀₁ h0U h0O' hDg hz₀₁G hfg T hT (fun k _ => ?_) ?_
  · -- surjectivity onto `ρ(z₀)F` from condition (3) at `z₀₁ ∈ (G₁)₁`
    have hzO : c.φ.model.E.toBase 1 z₀₁ ∈ r c.R '' c.U := by rw [hz₀₁]; exact hyO
    have hinj := h3 z₀₁ hz₀₁G.1 (by rw [hz₀₁]; exact ⟨c.r_image ▸ hyO, hyN.2⟩)
      (by rw [hz₀₁]; exact hgy)
    have := exists_range_deriv_eq_ρ_of_normal_injective_germ hU c.isRetraction h0U h0O' hfr hDg
      hfK hzO hz₀₁G (by rw [hz₀₁]; exact hfy) (by rw [hz₀₁, c.r_image]; exact hfg) hgsurj hinj k
    rwa [hz₀₁] at this
  · -- the kernel condition: `ker Dg(z₀₁) ∩ T_{z₀}O = ker Dg(z₀₁)`
    rwa [inf_eq_left.2 hcle]

end Bundle

end Polyfold
