import Polyfold.Chapter3.GlobalIFTNearbyKernel
import Polyfold.Chapter3.LinearizationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1)**: "at every point `y ∈ S` the sc-Fredholm germ `(f, y)` is in good position".
The kernel part in the chart at `x₀` (`GlobalIFTNearbyKernel.lean`) is combined here with the
chart independence of `LinearizationCharts.lean`; the surjectivity of the intrinsic linearization
`Tf̃(z₀) : T_{z₀}O → K_{z₀}` at the nearby zeros is obtained under the **added hypothesis** that
the filler satisfies condition (3) of Definition 3.4 at the nearby zeros as well (injectivity of
`(1 − ρ(z₀))Dg(z₀)` on `ker Dr(z₀)`).

# Theorem 3.54 (1) at the nearby zeros

## The text, paraphrased

(Proof of Theorem 3.54, (4)) "For every `y ∈ V` satisfying `f(y) = 0`, so that
`ψ ∘ ϕ(y) = v + σ(v)`, the kernel `ker f'(y)` is in good position to the partial cone `C_yX ⊆ T_yX`, and `f'(y)` is
surjective.  Property (4) follows from Corollary 3.41 and from Lemma 3.55."

## What is formalized

* `Polyfold.exists_range_scDeriv_eq_ρ_of_normal_injective`: **the surjectivity of `Tf̃(z₀)` from
  that of `Dg(z₀)`** when `(1 − ρ(z₀))Dg(z₀)` is injective on `ker Dr(z₀)` (condition (3) of
  Definition 3.4 at `z₀`): the block form `Dg(z₀) = [[A, B], [0, C]]` with respect to
  `E = T_{z₀}O ⊕ ker Dr(z₀)`, `F = K_{z₀} ⊕ ker ρ(z₀)` and `C` injective gives `range A = K_{z₀}`
  (Proposition 3.5 (1) at `z₀`).
* `Polyfold.theorem_3_54_nearby_kernel_wholeChart`: **Theorem 3.54 (1) at the nearby zeros, the kernel, in
  the chart at `x₀`**, in the form of `theorem_3_54_graph_wholeChart` (whose conclusion is restated so that the
  chart `c` is shared) together with, for every zero `y` in an open `Vx₂ ∋ x₀`, with `z₀ = ϕ(y)`,
  `z = ψ(z₀) = v + σ(v)`: the level-`1` points `z₀₁`, `x₁`; `D(h + t)(x₁)` surjective Fredholm of
  index `n − N`; `N_v = ker D(h + t)(x₁)`; `D(Ψ_*g)(x₁) = D(h + t)(x₁)`;
  `ker Dg(z₀) = Dψ'(x₁)(N_v)`; `Dg(z₀)` surjective; `ker Dg(z₀) ⊆ T_{z₀}O`; `ker Dg(z₀)` in
  good position to `C_{z₀}` inside `T_{z₀}O`.
* `Polyfold.StrongBundle.IsGoodPositionGermFilledWholeChart`: Definition 3.53 in a tame chart with a filler
  satisfying condition (3) at the zeros of `g` in `O` near `0` (as the fillers of the
  applications do).
* `Polyfold.theorem_3_54_one_wholeChart`: **Theorem 3.54 (1)** under this added hypothesis: for an
  sc-Fredholm section `f` with tame germ data (`IsScFredholmSectionTameWholeChart`), `f(x₀) = 0` and
  `(f, x₀)` in good position with such a filler, there is an open `Vx ∋ x₀` such that `(f, y)` is
  in good position in a tame chart (`IsGoodPositionGermTameWholeChart`) at every zero `y ∈ Vx` — by
  `isGoodPositionGerm_of_chart_dense` (the chart independence), fed with the data in the chart at
  `x₀`, and `IsGoodPositionGermWholeChart.toTame`.

## What the text leaves implicit, and the choices made (the findings)

* **The surjectivity of `f'(y)` at the nearby zeros is not a consequence of Corollary 3.41 and
  Lemma 3.55** (Finding 91 (b)): Corollary 3.41 gives the surjectivity of the filled
  `Dg(z₀) : E → F`; passing to `Tf̃(z₀) = Dg(z₀)|_{T_{z₀}O} : T_{z₀}O → K_{z₀}` is Proposition
  3.5 (1) at `z₀`, which needs condition (3) of Definition 3.4 at `z₀`.  With respect to
  `E = T_{z₀}O ⊕ ker Dr(z₀)`, `F = K_{z₀} ⊕ ker ρ(z₀)` one has `Dg(z₀) = [[A, B], [0, C]]`
  (the lower left block vanishes at a zero, `ρ(z₀)Dg(z₀)Dr(z₀) = Dg(z₀)Dr(z₀)`), `C` is onto,
  and `coker A ≅ ker C` through `b ↦ [Bb]`; so `A = Tf̃(z₀)` is onto iff `C` is injective.
  Definition 3.4 imposes (3) at `0` only, and it does not propagate (`u ↦ Dg(u)` is strongly, not
  norm, continuous).  Here (3) at the nearby zeros is an **added hypothesis**
  (`IsGoodPositionGermFilledWholeChart`), recorded in the Findings; the statement of the kernel part
  (`theorem_3_54_nearby_kernel_wholeChart`) needs no added hypothesis.  (Later files remove the hypothesis:
  Theorem 3.54 (1) with the text's hypotheses is `theorem_3_54_one'_wholeChart`, `GlobalIFTNearbyOnto.lean`,
  and `isGoodPositionGermFilled_of_isGoodPositionGerm_wholeChart`, `GlobalIFTIndex.lean`, shows that the
  filler condition itself follows from good position; Findings 180, 174.)
* **Equivalently, `coker Tf̃(z₀) = 0` is the local constancy of the index** `ind(f, y) = ind(f, x₀)`
  along the solution set (Proposition 6.2 of the text): `ind Dg(z₀) = dim K` at all nearby zeros
  (Corollary 3.41), `ind Dg(z₀) = ind A + ind C = dim ker A`, and `ind(f, y) = ind A =
  dim K − dim coker A`; the text's proof of Proposition 6.2 uses the same step ("`F'` is
  surjective" for the intrinsic linearization, from Corollary 3.41 for the filled one).
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Condition (3) of Definition 3.4 at `z₀` gives the surjectivity of `Tf̃(z₀)` -/

section Surj

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.5 (1) at a zero `z₀ ∈ O` of a filler**: if `Dg(z₀)` is surjective and
`(1 − ρ(z₀))Dg(z₀)` is injective on `ker Dr(z₀)` (condition (3) of Definition 3.4 at `z₀`), then
for every `k ∈ F`, `ρ(z₀)k = Dg(z₀)x` for some `x ∈ T_{z₀}O`: write `Dg(z₀)e = ρ(z₀)k` and
`e = Dr(z₀)e + b`, `b ∈ ker Dr(z₀)`; then `ρ(z₀)Dg(z₀)b = Dg(z₀)b` (the values of
`Dg(z₀)Dr(z₀) = D(f̂ ∘ r)(z₀)` lie in `K_{z₀}`), so `b = 0`. -/
theorem exists_range_scDeriv_eq_ρ_of_normal_injective (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R))
    (hg : IsSc1 U g) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U) (hfz : fb (E.toBase 1 z) = 0)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (hsurj : Surjective (scDeriv U g z))
    (hinj : ∀ b : E 0, scDeriv U (r R) z b = 0 →
      ρ R (E.toBase 1 z) (scDeriv U g z b) = scDeriv U g z b → b = 0) (k : F 0) :
    ∃ x ∈ rangeS (scDeriv U (r R) z), scDeriv U g z x = ρ R (E.toBase 1 z) k := by
  have hzU : E.toBase 1 z ∈ U := mem_U_of_mem_O hR hzO
  obtain ⟨e, he⟩ := hsurj (ρ R (E.toBase 1 z) k)
  set a := scDeriv U (r R) z e with hadef
  set b := e - a with hbdef
  have hb : scDeriv U (r R) z b = 0 := by
    rw [hbdef, map_sub, hadef, scDeriv_r_idem_at hU hR hzO, sub_self]
  -- `Dg(z₀)a = D(f̂ ∘ r)(z₀)e` has values in `K_{z₀}`
  have hDa : scDeriv U g z a = scDeriv U (fb ∘ r R) z e :=
    (scDeriv_comp_r_eq_of_eventuallyEq hU hR hfr hg hzO heq e).symm
  have hρa : ρ R (E.toBase 1 z) (scDeriv U g z a) = scDeriv U g z a := by
    rw [hDa]
    exact rho_scDeriv_comp_r hU hR hfr hfK hzO hfz e
  have hρb : ρ R (E.toBase 1 z) (scDeriv U g z b) = scDeriv U g z b := by
    have hlin := ρ_isLinear hR hzU
    rw [hbdef, map_sub, hlin.map_sub, hρa, he, ρ_ρ hR hzO]
  have hb0 : b = 0 := hinj b hb hρb
  have hea : e = a := by rw [← sub_eq_zero]; exact hb0
  exact ⟨a, ⟨e, rfl⟩, by rw [← hea]; exact he⟩

end Surj

/-! ### Theorem 3.54 (1) at the nearby zeros, the kernel, for a section of a strong bundle -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- The principal part composed with the retraction, `f̂ ∘ r`, is sc¹ on `U` for an sc-smooth
section (it is the fibre component of the sc-smooth map `u ↦ Φ(f(ϕ⁻¹(r(u))))`). -/
lemma StrongBundle.IsScSmoothSection.isSc1_principal_comp_r (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) : IsSc1 c.U (c.principal f ∘ r c.R) := by
  have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  exact ((h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.54 (1) at the nearby zeros, the kernel, in the chart at `x₀`.**  In the setting of
`theorem_3_54_graph_wholeChart` (whose conclusion is restated, so that the chart `c`, the conjugating
sc-diffeomorphism `ψ` with inverse `ψ'`, the germ `h + t = 𝒮.fsum h'`, the good complement `Yc`
and the solution graph `σ : V' → Yc` are the same), with the filled version `g` of `f̂ = c.principal f`
and its sc⁺-section `t₀` exposed: there is an open neighbourhood `Vx₂ ⊆ Vx` of `x₀` such that for
every zero `y ∈ Vx₂` of `f`, with `z₀ = ϕ(y)` and `z = ψ(z₀) = v + σ(v)`, `v ∈ V'`, there are the
level-`1` points `z₀₁ ∈ U₁` over `z₀` and `x₁ = ψ₁(z₀₁) ∈ G₁` over `z` with:
(i) `D(h + t)(x₁)` is a surjective Fredholm operator of index `n − N` (Corollary 3.41);
(a) `N_v = {n + Dσ(v)n} = ker D(h + t)(x₁)`;
(b) `D(Ψ_*g)(x₁) = D(h + t)(x₁)` and `ker Dg(z₀) = Dψ'(x₁)(ker D(h + t)(x₁))`, `Dg(z₀)` onto;
(c) `ker Dg(z₀) ⊆ T_{z₀}O = Dr(z₀)E`;
(d) `ker Dg(z₀)` is in good position to `C_{z₀}` inside `T_{z₀}O` (`IsInGoodPositionIn`).
Moreover `f̂ = g` on `O` near `z₀` and `g(z₀) = 0`. -/
theorem theorem_3_54_nearby_kernel_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0U : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (t₀ : c.φ.model.E 0 → c.F 1)
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
      IsFilledVersion c.relOpen c.isRetraction h0U (c.principal f) g ∧
      IsScSmooth (F := c.F.shift) c.U t₀ ∧ c.F.toBase 1 (t₀ 0) = g 0 ∧
      IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (t₀ u)) ∧
      IsGoodPositionAt c.relOpen c.isRetraction h0U g ∧
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
          c.φ.model.E.toBase 1 z₀₁ = c.φ y ∧ z₀₁ ∈ c.φ.model.E.lvlSet c.U 1 ∧
          (ScBanach.paramProd Pn W).toBase 1 x₁ = (v : Pn × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
          levelMap (IsStrongBundleMap.base Ψ) 1 z₀₁ = x₁ ∧
          IsStrongBundleMap.base Ψ (c.φ y) = (v : Pn × W 0) + σ v ∧
          IsFredholm (𝒮.Dfs' h' x₁) ∧
          fredholmIndex (𝒮.Dfs' h' x₁) = finrank ℝ Pn - finrank ℝ Q ∧
          Surjective (𝒮.Dfs' h' x₁) ∧
          graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) (fderivWithin ℝ σ V' v) =
            LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0) ∧
          scDeriv U' (pushforward Ψ Ψ' g) x₁ = 𝒮.Dfs' h' x₁ ∧
          LinearMap.ker (scDeriv c.U g z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0) =
            (LinearMap.ker (𝒮.Dfs' h' x₁ : Pn × W 0 →ₗ[ℝ] Q × W 0)).map
              (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ : Pn × W 0 →ₗ[ℝ] c.φ.model.E 0) ∧
          Surjective (scDeriv c.U g z₀₁) ∧
          LinearMap.ker (scDeriv c.U g z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤
            rangeS (scDeriv c.U (r c.R) z₀₁) ∧
          IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z₀₁))
            (partialQuadrantAtWith T (c.φ y))
            (LinearMap.ker (scDeriv c.U g z₀₁ : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) := by
  classical
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj, hgp⟩ := hg
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  -- notation and the data of the chart
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    exact mem_U_of_mem_O c.isRetraction hz
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x₀ hxV
  have h0O' : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have hfb0 : fb 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [h0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, fb x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hf (c.r_image ▸ hx)
  have hRt : (c.isRetraction.baseRetraction c.relOpen).IsTame := hc.2
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK : LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 := by
    have hRtT := hRt n' Wq T hT
    have h01 : (0 : c.φ.model.E 1) ∈
        c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact h0O
    have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
      change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
      rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
    have h235 := (proposition_2_35 hT hRtT h01 hs).1
    rw [map_zero] at h235
    exact h235
  have hψcont : ContinuousOn ψ c.U := (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.continuousOn_base
  -- the graph description in the chart
  obtain ⟨𝒮, h', Yc, V', σ, Wo, N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, hWo, h0Wo, hagree, hYc, hYcc,
    hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hN₁o, h0N₁, hN₁, hψ'N₁, hN₂o, h0N₂, hN₂N₁,
    hN₂ψ, hgO, hzero, himage⟩ :=
    theorem_3_54_chart_graph_wholeChart hU c.isRetraction h0U h0O' hfill hfb0 hfK ht₀ ht₀0 hCt hU' hΨ hψ0 hG
      hh hev T hT hK hgp
  -- the kernel at the nearby zeros
  obtain ⟨N₃, hN₃o, h0N₃, hN₃N₂, hker⟩ := theorem_3_54_chart_kernel_wholeChart hU c.isRetraction h0U h0O'
    hfill hfb0 hCt hU' hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂ (h𝒮G ▸ hG) hh'𝒮 hsurj hpos hWo hagree hYc
    hYcc hV'rel h0V' hσY hσC hσ0 hDσ hsol hlift hN₂o h0N₂ hN₂ψ himage
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
  refine ⟨c, hc, hxV, h0, h0U, g, t₀, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', Ψ, Ψ',
    hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀, ht₀0,
    ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩,
    hgp, hYc, hYcc, 𝒮.ker_Dfs_le_smooth hCt hh'𝒮, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift,
    hVxo, hx₀Vx, hVxsub, ?_, hzero', ?_, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, ?_⟩
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

/-! ### Theorem 3.54 (1) under the filler condition (3) at the nearby zeros -/

variable (B) in
/-- **Definition 3.53 with a filler satisfying condition (3) of Definition 3.4 at the nearby zeros**:
the data of `StrongBundle.IsGoodPositionGermTameWholeChart` (a tame strong bundle chart centred at
`x₀` (Definition 3.50), a filled version `g` of `f̂`, the sc⁺-section `s` with `g − s` conjugated to
a basic germ, the germ in good position), together with: on a neighbourhood of `0`, at every zero
`z₀ ∈ O` of `g` and every level-`1` point `z₁` over `z₀`, the operator `(1 − ρ(z₀))Dg(z₁)` is
injective on `ker Dr(z₁)`. (Definition 3.4 imposes (3) at `0` only; the fillers of the applications
satisfy it at every point.) This is the project's original whole-chart reading, stricter than the
text (Findings, Chapter 3, items 220–221, 260–266); the text's germ reading is
`IsGoodPositionGermFilled` (`GlobalIFTNearbySurjG.lean`, phase 2, items 270–330). -/
def StrongBundle.IsGoodPositionGermFilledWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    IsGoodPositionAt c.relOpen c.isRetraction h0 g ∧
    ∃ N : Set (c.φ.model.E 0), IsOpen N ∧ (0 : c.φ.model.E 0) ∈ N ∧
      ∀ z₁ : c.φ.model.E 1, c.φ.model.E.toBase 1 z₁ ∈ c.φ.model.O ∩ N →
        g (c.φ.model.E.toBase 1 z₁) = 0 →
        ∀ b : c.φ.model.E 0, scDeriv c.U (r c.R) z₁ b = 0 →
          ρ c.R (c.φ.model.E.toBase 1 z₁) (scDeriv c.U g z₁ b) = scDeriv c.U g z₁ b → b = 0

/-- The strengthened good position implies Definition 3.53 in a tame chart. -/
theorem StrongBundle.IsGoodPositionGermFilledWholeChart.isGoodPositionGermTame {x₀ : X}
    (h : B.IsGoodPositionGermFilledWholeChart f x₀) : B.IsGoodPositionGermTameWholeChart f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩

/-- The strengthened good position implies Definition 3.53. -/
theorem StrongBundle.IsGoodPositionGermFilledWholeChart.isGoodPositionGerm {x₀ : X}
    (h : B.IsGoodPositionGermFilledWholeChart f x₀) : B.IsGoodPositionGermWholeChart f x₀ :=
  h.isGoodPositionGermTame.isGoodPositionGerm

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.54 (1)** ("at every point `y ∈ S` the sc-Fredholm germ `(f, y)` is in good
position"), under the **added hypothesis** that the filler at `x₀` satisfies condition (3) of
Definition 3.4 at the nearby zeros (`IsGoodPositionGermFilledWholeChart`).  Let `f` be an sc-Fredholm section
of the strong bundle `P : Y → X` with tame germ data (Definition 3.51, `IsScFredholmSectionTameWholeChart`),
`f(x₀) = 0`, and `(f, x₀)` in good position in a tame chart with such a filler.  Then there is an
open neighbourhood `Vx` of `x₀` such that `(f, y)` is in good position in a tame chart (Definition
3.53, `IsGoodPositionGermTameWholeChart`) at every zero `y ∈ Vx`.
Proof: in the chart `c` at `x₀`, `theorem_3_54_chart_kernel_wholeChart` gives `ker Dg(z₀) ⊆ T_{z₀}O` in good
position to `C_{z₀}` inside `T_{z₀}O` and `Dg(z₀)` onto; condition (3) at `z₀` turns the latter
into the surjectivity of `Tf̃(z₀) : T_{z₀}O → K_{z₀}` (Proposition 3.5 (1) at `z₀`); the chart
independence `isGoodPositionGerm_of_chart_dense` transports both to the chart centred at `y`, and
`IsGoodPositionGermWholeChart.toTame` to the tame chart of the germ data at `y`. -/
theorem theorem_3_54_one_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermFilledWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj, hgp, N, hNo, h0N, h3⟩ := hg
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x₀ hxV
  have h0O' : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have hfb0 : fb 0 = 0 := by
    have := (c.isZeroAt_iff hfs hxV).1 hx₀
    rwa [h0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, fb x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hfs (c.r_image ▸ hx)
  have hRt : (c.isRetraction.baseRetraction c.relOpen).IsTame := hc.2
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK : LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 := by
    have hRtT := hRt n' Wq T hT
    have h01 : (0 : c.φ.model.E 1) ∈
        c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact h0O
    have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
      change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
      rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
    have h235 := (proposition_2_35 hT hRtT h01 hs).1
    rw [map_zero] at h235
    exact h235
  obtain ⟨𝒮, h', Yc, V', σ, Wo, N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, hWo, h0Wo, hagree, hYc, hYcc,
    hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hN₁o, h0N₁, hN₁, hψ'N₁, hN₂o, h0N₂, hN₂N₁,
    hN₂ψ, hgO, hzero, himage⟩ :=
    theorem_3_54_chart_graph_wholeChart hU c.isRetraction h0U h0O' hfill hfb0 hfK ht₀ ht₀0 hCt hU' hΨ hψ0 hG
      hh hev T hT hK hgp
  obtain ⟨N₃, hN₃o, h0N₃, hN₃N₂, hker⟩ := theorem_3_54_chart_kernel_wholeChart hU c.isRetraction h0U h0O'
    hfill hfb0 hCt hU' hΨ hψ0 T hT 𝒮 h' Yc V' σ Wo N₂ (h𝒮G ▸ hG) hh'𝒮 hsurj hpos hWo hagree hYc
    hYcc hV'rel h0V' hσY hσC hσ0 hDσ hsol hlift hN₂o h0N₂ hN₂ψ himage
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
  obtain ⟨v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, hx₁, hx₁G, hlev, hveq, hF, hind, hsurj', hker', hDeq, hkerb,
    hgsurj, hcle, hgpIn⟩ := hker (c.φ y) ⟨hyO, hyN.1⟩ hgy
  have hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x := by
    filter_upwards [hN₁o.mem_nhds hyN₁] with x hx hxO
    exact (hN₁ x hx).1 (c.r_image ▸ hxO)
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc.1
  have hysm : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  refine StrongBundle.IsGoodPositionGermWholeChart.toTame hf.isScSmooth
    (StrongBundle.isGoodPositionGerm_of_chart_dense hf.isScSmooth (hf.germ y hysm) hy0 hc.1 hyV
      hz₀₁ hfill.isScSmooth.isSc1 hfg T hT (fun k _ => ?_) ?_) (hf.germTame y hysm) hy0
  · -- surjectivity onto `ρ(z₀)F` from condition (3) at `z₀`
    have hzO : c.φ.model.E.toBase 1 z₀₁ ∈ r c.R '' c.U := by rw [hz₀₁]; exact hyO
    have hinj := h3 z₀₁ (by rw [hz₀₁]; exact ⟨c.r_image ▸ hyO, hyN.2⟩) (by rw [hz₀₁]; exact hgy)
    have := exists_range_scDeriv_eq_ρ_of_normal_injective hU c.isRetraction hfr
      hfill.isScSmooth.isSc1 hfK hzO (by rw [hz₀₁]; exact hfy)
      (by rw [hz₀₁, c.r_image]; exact hfg) hgsurj hinj k
    rwa [hz₀₁] at this
  · -- the kernel condition: `ker Dg(z₀) ∩ T_{z₀}O = ker Dg(z₀)`
    rwa [inf_eq_left.2 hcle]

end Bundle

end Polyfold
