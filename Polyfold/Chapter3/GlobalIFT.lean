import Polyfold.Chapter3.GoodPositionGerm
import Polyfold.Chapter3.TameGerms
import Polyfold.Chapter3.LocalSolvability
import Polyfold.Chapter3.LocalSolvabilityClosed
import Polyfold.Chapter3.SolutionGermRegularity
import Polyfold.Chapter3.SectionCompactness
import Polyfold.Chapter3.TangentGerm
import Polyfold.Chapter3.FredholmGermIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54** (the fundamental implicit function theorem), the step "(3)" of its proof: the
solution set of an sc-Fredholm section near a zero in good position is, in the chart conjugating
the filled version to a basic germ, the graph of a `C¹`-map `σ : V' → Y'` over the kernel of the
linearization (Corollary 3.47 applied to `Ψ_*(g) = h + t`).

# Theorem 3.54: the graph description of the solution set

## The text, paraphrased

(Proof of Theorem 3.54, after the linear part) "Then we can apply Theorem 3.47 about the local germ
solvability and find an open neighbourhood `V' ⊂ N' ∩ C'` of `0` and a map `σ : V' → (Y')¹`
with (1) `σ` of class `C¹`, `σ(0) = 0`, `Dσ(0) = 0`; (2) `σ : O(N' ∩ C', 0) → (Y', 0)` is an
sc-smooth germ; (3) `ψ ∘ ϕ({y ∈ V | f(y) = 0}) = ψ({u ∈ O | f̃(u) = 0}) = ψ({u ∈ O | g(u) = 0})
= {u' ∈ U' | (h + t)(u') = 0} = {v + σ(v) | v ∈ V'}` by (48), (49) and Corollary 3.47."

## What is formalized

* `Polyfold.ScBanach.qPartOp`, `ScBanach.wPartOp`: the two components of an sc⁺-germ
  `t : U' → (ℝᴺ ⊕ W)¹`, as sc-operators.
* `Polyfold.scDeriv_eq_of_eqOn_nhds`: two sc¹-derivatives at `0` of maps that agree near `0` in
  the partial quadrant coincide (uniqueness of the derivative on level `1` and density).
* `Polyfold.finrank_ker_eq_fredholmIndex_of_surjective`: `dim ker u = ind u` for a surjective
  Fredholm operator.
* `Polyfold.theorem_3_54_graph_wholeChart`: **Theorem 3.54, the graph description (3)**.  For a section `f`
  of a strong bundle with `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart
  (`IsGoodPositionGermTameWholeChart`), there are the tame chart `c` of Definition 3.53, the conjugating sc-diffeomorphism `ψ`, a basic germ `h' = h + (t_{ℝᴺ}, 0)` and
  the data `𝒮` of Theorem 3.38 with `𝒮.fsum h' = h + t = Ψ_*(g)` near `0`, a good complement `Y`
  of `K = ker D(h + t)(0)`, a relatively open neighbourhood `V'` of `0` in `K ∩ C'` and
  `σ : V' → Y` of class `C¹` with values on level `1`, `σ(0) = 0`, `Dσ(0) = 0`, and an open
  neighbourhood `Vx` of `x₀` in `X` on which `ψ ∘ ϕ` is injective and carries the zero set of `f`
  onto `{v + σ(v) | v ∈ V'}`.
* `Polyfold.theorem_3_54_graph_proj_wholeChart`: the same with the good complement `Y` chosen so that the
  projection onto `K` along `Y` maps `C' = C̃ ⊕ W` into `K ∩ C'` (`ProjectsInto`, from
  `theorem_3_47_proj`; Findings 130–133); `theorem_3_54_graph_wholeChart` is its corollary.
* `Polyfold.theorem_3_54_graph_proj_conj_wholeChart`: `theorem_3_54_graph_proj_wholeChart` with the data of Definition
  3.53 in the chart `c` exposed (the filled version `g`, the sc⁺-section `s`, the good position
  `IsGoodPositionAt`, and conjugation data `dc` of `g − s` to a basic germ, `ConjugationData`)
  together with `dim K = dim dc.Pn − dim dc.Q`: the dimension of the kernel is the index `n − N` of
  the conjugation in the chart, hence the Fredholm index of `f'(x₀)` (`proposition_3_52_index_wholeChart`;
  `GlobalIFTIndex.lean`, Finding 170).

## What the text leaves implicit, and the choices made (the findings)

* **"Ψ_*(g) = h + t with t = Ψ_*(s) an sc⁺-section `U' → F'`"**: `t` has an `ℝᴺ`-component, while
  the data of Theorem 3.38/3.47 (`StabilityData`) carry only the `W`-component of the sc⁺-germ.
  The `ℝᴺ`-component is absorbed into the basic germ: `h' = h + (t_{ℝᴺ}, 0)` is again a basic germ
  with the same contraction `B` (Definition 3.7 constrains the `W`-component only), and
  `h' + ι t_W = h + ι t`.
* **The derivative `D(h + t)(0)` of the text is the derivative of the germ `𝒮.fsum h'`**; the
  hypotheses of Theorem 3.47 (surjectivity, good position of the kernel) are those of
  `theorem_3_54_pushforward_wholeChart` for `Ψ_*(g)`, transported through
  `scDeriv_eq_of_eqOn_nhds` since `Ψ_*(g) = h + ι t` only on a neighbourhood of `0`.
* **Tameness** enters only through `(1 − Dr(0))E ⊆ E₀` (Proposition 2.35), as in
  `theorem_3_54_linear_wholeChart`, for the base retraction of the chart of Definition 3.53 at `x₀`: the
  germ is assumed in good position in a tame chart (`IsGoodPositionGermTameWholeChart`; Definition 3.50:
  "where `K → O` is a tame strong local bundle", `TameGerms.lean`), and the chart `c` of the
  conclusions is that tame chart (`IsTameChart`).  (An earlier version assumed the base retraction
  of every compatible strong bundle chart tame, which no strong bundle over a nonempty base
  satisfies; Findings, Chapter 3 items 190–199.)
* **The neighbourhood `V` of `x₀`**: the identity `ψ ∘ ϕ(S ∩ V) = graph σ` needs `V` so small that
  (i) the identities of the filler and of the conjugation hold on `ϕ(V)`, (ii) `ψ ∘ ϕ(V)` lies
  in the neighbourhood `U''` of Theorem 3.47 where every zero of `h + t` is on the graph, and
  (iii) `ψ⁻¹` maps the graph points back into (i); `V'` is shrunk accordingly (`σ` is continuous
  with `σ(0) = 0`).  The text does not say which `V`.
* **The rest of Theorem 3.54 is in later files.**  (1), good position at the nearby zeros: the
  kernel in the chart at `x₀` is `theorem_3_54_nearby_kernel_wholeChart` (`GlobalIFTNearbyKernel.lean`,
  `GlobalIFTNearbySurj.lean`), the chart independence of `f'(y)` and of good position is
  `LinearizationCharts.lean` (`linAt_chart_independence`, `isGoodPositionGerm_of_chart_dense`),
  and the surjectivity of `f'(y)` with the text's hypotheses is `theorem_3_54_one'_wholeChart`
  (`GlobalIFTNearbyOnto*.lean`).  (2): the data of Definition 3.25 (2) at `x₀` in the chart
  `ψ ∘ ϕ` (`MChart.compDiffeo`, `theorem_3_54_tangentGermChart_proj_wholeChart`, `GlobalIFTCenter.lean`),
  their regularity away from the centre by re-centring (`SolutionGermRecentre.lean`), and the
  assembly `theorem_3_54_two_wholeChart`, `theorem_3_54'_wholeChart` (`GlobalIFTTheorems.lean`,
  `GlobalIFTNearbyOnto.lean`); the dimension as the Fredholm index is `GlobalIFTIndex.lean`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### The two components of an sc⁺-germ into `(ℝᴺ ⊕ W)¹` -/

section Parts

variable (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  (W : ScBanach)

/-- The `ℝᴺ`-component `(q, w) ↦ (q, 0)` of `(ℝᴺ ⊕ W)¹ → ℝᴺ ⊕ W` as an sc-operator. -/
def ScBanach.qPartOp : ScOperator (ScBanach.paramProd Q W).shift (ScBanach.paramProd Q W) where
  lvl m := (ContinuousLinearMap.inl ℝ Q (W m)).comp (ContinuousLinearMap.fst ℝ Q (W (m + 1)))
  incl_comm m x := by
    change ((x.1, W.incl m (0 : W (m + 1))) : Q × W m) = (x.1, (0 : W m))
    rw [map_zero]

@[simp] lemma ScBanach.qPartOp_apply (x : (ScBanach.paramProd Q W).shift 0) :
    ScBanach.qPartOp Q W 0 x = ((x.1, 0) : Q × W 0) := rfl

/-- The `W`-component `(q, w) ↦ w` of `(ℝᴺ ⊕ W)¹ → W¹` as an sc-operator. -/
def ScBanach.wPartOp : ScOperator (ScBanach.paramProd Q W).shift W.shift where
  lvl m := ContinuousLinearMap.snd ℝ Q (W (m + 1))
  incl_comm _ _ := rfl

@[simp] lemma ScBanach.wPartOp_apply (x : (ScBanach.paramProd Q W).shift 0) :
    ScBanach.wPartOp Q W 0 x = x.2 := rfl

end Parts

/-! ### Uniqueness of the derivative at `0` for maps agreeing near `0` -/

section DerivEq

variable {E F : ScBanach} {C : Set (E 0)}

/-- Two derivatives at `0` (in the sense of the sc¹-structures, `E₁ → F₀` composed with the
inclusion) of maps `f₁`, `f₂` that agree on a relatively open neighbourhood of `0` in `C` on level
`1` coincide: uniqueness of the derivative within the quadrant on level `1`, then density of `E₁`
in `E₀`. -/
theorem scDeriv_eq_of_eqOn_nhds (hC : IsQuadrantLike E C) {S₁ S₂ : Set (E 1)} {f₁ f₂ : E 0 → F 0}
    {D₁ D₂ : E 0 →L[ℝ] F 0}
    (h₁ : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₁.comp (E.toBase 1)) S₁ 0)
    (h₂ : HasFDerivWithinAt (f₂ ∘ E.toBase 1) (D₂.comp (E.toBase 1)) S₂ 0)
    {W₁ : Set (E 1)} (hW : IsOpen W₁) (h0 : (0 : E 1) ∈ W₁) (hS₁ : W₁ ∩ E.lvlSet C 1 ⊆ S₁)
    (hS₂ : W₁ ∩ E.lvlSet C 1 ⊆ S₂) (h0C : (0 : E 1) ∈ E.lvlSet C 1)
    (heq : ∀ x ∈ W₁ ∩ E.lvlSet C 1, f₁ (E.toBase 1 x) = f₂ (E.toBase 1 x)) : D₁ = D₂ := by
  have h0S : (0 : E 1) ∈ W₁ ∩ E.lvlSet C 1 := ⟨h0, h0C⟩
  have huniq : UniqueDiffWithinAt ℝ (W₁ ∩ E.lvlSet C 1) 0 := hC.uniqueDiffWithinAt hW h0S
  have h₁' : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₁.comp (E.toBase 1)) (W₁ ∩ E.lvlSet C 1) 0 :=
    h₁.mono hS₁
  have h₂' : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₂.comp (E.toBase 1)) (W₁ ∩ E.lvlSet C 1) 0 :=
    (h₂.mono hS₂).congr (fun x hx => heq x hx) (heq 0 h0S)
  have hcomp : D₁.comp (E.toBase 1) = D₂.comp (E.toBase 1) := huniq.eq h₁' h₂'
  have hdense : DenseRange (E.toBase 1) := E.denseRange_incl 0
  ext x
  have := hdense.equalizer D₁.continuous D₂.continuous (by
    ext y
    exact congrArg (fun L : E 1 →L[ℝ] F 0 => L y) hcomp)
  exact congrFun this x

end DerivEq

/-! ### The dimension of the kernel of a surjective Fredholm operator -/

section Finrank

variable {E₀ F₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup F₀]
  [NormedSpace ℝ F₀]

/-- For a surjective Fredholm operator, `dim ker u = ind u`. -/
theorem finrank_ker_eq_fredholmIndex_of_surjective {u : E₀ →L[ℝ] F₀} (_hu : u.IsFredholm)
    (hs : Surjective u) :
    (finrank ℝ (LinearMap.ker (u : E₀ →ₗ[ℝ] F₀)) : ℤ) = fredholmIndex u := by
  have hcoker : finrank ℝ (F₀ ⧸ LinearMap.range (u : E₀ →ₗ[ℝ] F₀)) = 0 := by
    have : Subsingleton (F₀ ⧸ LinearMap.range (u : E₀ →ₗ[ℝ] F₀)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [(Submodule.Quotient.mk_eq_zero _).2 (hs a), (Submodule.Quotient.mk_eq_zero _).2 (hs b)]
    exact Module.finrank_zero_of_subsingleton
  unfold fredholmIndex linIndex
  rw [hcoker]
  simp

end Finrank

/-! ### Theorem 3.54: the graph description of the solution set -/

section Thm354

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

set_option maxHeartbeats 800000 in
/-- **Theorem 3.54, the graph description (3), with the conjugation exposed**:
`theorem_3_54_graph_proj_wholeChart` (a corollary of this theorem) together with the data of Definition 3.53
in the chart `c` — the filled version `g` of `f̂`, the sc⁺-section `s` with `s(0) = g(0)`, the good
position `IsGoodPositionAt` of `g` at `0`, and conjugation data `dc` of `g − s` to a basic germ
(`ConjugationData`) — with `dim K = dim dc.Pn − dim dc.Q` for the kernel
`K = ker D(h + t)(0)`: `D(h + t)(0)` is surjective and Fredholm of index `n − N`
(`StabilityData.isFredholm_Dfs`), and `n`, `N` are the dimensions of the conjugation of `g − s` in
the chart `c`, whose index is that of `f'(x₀)` (`proposition_3_52_local_index_wholeChart`).  This is what
identifies the dimension of the solution set with the Fredholm index (`GlobalIFTIndex.lean`,
Finding 170). -/
theorem theorem_3_54_graph_proj_conj_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (ψ : c.φ.model.E 0 → (ScBanach.paramProd Pn W) 0) (_ : IsScSmooth c.U ψ) (_ : ψ 0 = 0)
      (_ : MapsTo ψ c.U U') (ψ' : (ScBanach.paramProd Pn W) 0 → c.φ.model.E 0)
      (_ : IsScSmooth U' ψ') (_ : MapsTo ψ' U' c.U) (_ : ∀ u ∈ c.U, ψ' (ψ u) = u)
      (_ : ∀ u' ∈ U', ψ (ψ' u') = u') (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X),
      (∃ (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1)
        (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (_ : IsGoodPositionAt c.relOpen c.isRetraction h0 g)
        (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)),
        (finrank ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) : ℤ) =
          finrank ℝ dc.Pn - finrank ℝ dc.Q) ∧
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      ProjectsInto (Ct ×ˢ univ) (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
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
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0) ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' := by
  classical
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj, hgp⟩ := hg
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set fb := c.principal f with hfbdef
  set sb : c.φ.model.E 0 → c.F 0 := fun u => c.F.toBase 1 (t₀ u) with hsbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x₀ hxV
  have hC'q : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0U hψ0
  have hψsc : IsScSmooth c.U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc.isSc1.isSc0.continuousOn_base
  have hψcont : ContinuousOn ψ c.U := hψsc.isSc1.isSc0.continuousOn_base
  have hψU' : MapsTo ψ c.U U' := fun u hu => hΨ.toFun.base_mem hu
  -- the neighbourhood `N₁` of `0` where the identities of the filler and the conjugation hold
  have hN₀ : ∀ᶠ u in 𝓝 (0 : c.φ.model.E 0), (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := by
    have h1 := hfill.filler.eq_on
    have h2 := hfill.filler.mem_of_fixed
    rw [c.r_image] at h1 h2
    refine (h1.and (h2.and hev)).mono fun u hu => ⟨hu.1, hu.2.1, fun huU => ?_⟩
    exact hu.2.2 huU
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hN₀
  have hN₁ : ∀ u ∈ N₁, (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := fun u hu => hN₁sub hu
  have hgO : ∀ u ∈ c.U, u ∈ N₁ → g u = 0 → u ∈ c.φ.model.O := fun u hu huN hgu =>
    (hN₁ u huN).2.1 hu (by
      rw [hgu]
      exact ((StrongRetr.ρ_isLinear c.isRetraction (StrongRetr.r_mem c.isRetraction hu)).map_zero).symm)
  have hfb0 : fb 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [h0] at this
  have hg0 : g 0 = 0 := by rw [← (hN₁ 0 h0N₁).1 h0O, hfb0]
  have ht00 : t₀ 0 = 0 := by
    apply c.F.toBase_injective 1
    rw [ht₀0, hg0, map_zero]
  -- the push-forward sc⁺-germ `t = Ψ[1]_*(t₀)` on `E'`
  set t : (ScBanach.paramProd Pn W) 0 → (ScBanach.paramProd Q W).shift 0 :=
    fun u' => (shiftFiber Ψ (ψ' u', t₀ (ψ' u'))).2 with htdef
  have htsc : IsScSmooth (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) U' t := by
    have hpair : IsScSmooth (E := ScBanach.paramProd Pn W) (F := c.φ.model.E.prod c.F.shift) U'
        (scPair (F := c.φ.model.E) (G := c.F.shift) ψ' (fun u' => t₀ (ψ' u'))) := by
      refine hψ'sc.scPair hU'.isScDomain ?_
      exact IsScSmooth.comp hU'.isScDomain hU.isScDomain ht₀ hψ'sc fun u' hu' =>
        hΨ.invFun.base_mem hu'
    have hUF := (hU.prod_univ c.F.shift).isScDomain
    have hmaps : MapsTo (scPair (F := c.φ.model.E) (G := c.F.shift) ψ' (fun u' => t₀ (ψ' u'))) U'
        (c.U ×ˢ univ) := fun u' hu' =>
      ⟨hΨ.invFun.base_mem hu', mem_univ _⟩
    have := IsScSmooth.comp hU'.isScDomain hUF hΨ.toFun.isScSmooth_one hpair hmaps
    exact (this.snd hU'.isScDomain).congr hU'.isScDomain fun _ _ => rfl
  have hGsub : ∀ m, G.U m ⊆ (ScBanach.paramProd Pn W).lvlSet U' m := fun m z hz =>
    hG (G.toBase_mem hz)
  have htG : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) G t :=
    (htsc.isScSmoothGerm hC'q hU'.relOpen h0U').mono hC'q hGsub
  have ht0 : t 0 = 0 := by
    simp only [htdef, hψ'0, ht00]
    unfold shiftFiber
    simp only [map_zero]
    rw [hΨ.toFun.snd_zero h0U]
    have := Function.leftInverse_invFun ((ScBanach.paramProd Q W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the key identity: for `u ∈ U ∩ N₁`, `Ψ_*(g)(ψ u) = h(ψ u) + ι t(ψ u)`
  have hkey : ∀ u ∈ c.U, u ∈ N₁ →
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
  have hRt : (c.isRetraction.baseRetraction c.relOpen).IsTame := hc.2
  obtain ⟨n, Wc, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK : LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 := by
    have hRtT := hRt n Wc T hT
    have h01 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact h0O
    have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
      change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
      rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
    have h235 := (proposition_2_35 hT hRtT h01 hs).1
    rw [map_zero] at h235
    exact h235
  have hfK : ∀ x ∈ r c.R '' c.U, (x, fb x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩
  have hconj' : IsConjugateToBasicGerm c.U fun u => g u - c.F.toBase 1 (t₀ u) :=
    ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩
  obtain ⟨hpush, -, hsurjP, -, hposP⟩ := theorem_3_54_pushforward_wholeChart c.relOpen c.isRetraction h0U
    (c.r_image ▸ h0O) hfill hfb0 hfK ht₀ ht₀0 hconj' T hT hK hgp hU' hΨ hψ0
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
  have hDeq : 𝒮.Dfs h' = scDeriv U' (pushforward Ψ Ψ' g) 0 := by
    have hfs1 := (𝒮.fsum_isScSmoothGerm (hCt.isQuadrantLike) (h𝒮G ▸ hh'.isScSmooth) 1).1
      |>.isSc1GermWith_scDerivGerm
    have h₁ := hfs1.hasFDerivWithinAt 0 (𝒮.G.zero_mem 1)
    have h₂ := hpush.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0
      (by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U')
    refine scDeriv_eq_of_eqOn_nhds hC'q h₁ h₂
      (W₁ := (ScBanach.paramProd Pn W).lvlSet (W' ∩ Uo) 1 ∩ Og₁)
      (((ScBanach.paramProd Pn W).isOpen_lvlSet (hW'open.inter hUo) 1).inter hOg₁)
      ⟨by rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨h0W', hU'eq ▸ h0U' |>.1⟩,
        (hGeq₁ ▸ G.zero_mem 1 : (0 : (ScBanach.paramProd Pn W) 1) ∈ Og₁ ∩ _).1⟩
      ?_ ?_ (by rw [ScBanach.mem_lvlSet, map_zero]; exact hU'C h0U') ?_
    · rintro x ⟨⟨-, hxOg⟩, hxC⟩
      rw [h𝒮G, hGeq₁]; exact ⟨hxOg, hxC⟩
    · rintro x ⟨⟨hxW, -⟩, hxC⟩
      rw [ScBanach.mem_lvlSet, hU'eq]
      exact ⟨(hxW : _ ∈ W' ∩ Uo).2, hxC⟩
    · rintro x ⟨⟨hxW, -⟩, hxC⟩
      have hxU' : (ScBanach.paramProd Pn W).toBase 1 x ∈ U' := by
        rw [hU'eq]; exact ⟨(hxW : _ ∈ W' ∩ Uo).2, hxC⟩
      exact hagree _ hxU' (hxW : _ ∈ W' ∩ Uo).1
  have hsurj : Surjective (𝒮.Dfs h') := by rw [hDeq]; exact hsurjP
  have hpos : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) := by rw [hDeq]; exact hposP
  -- Theorem 3.47 for `h + t`
  obtain ⟨Yc, V₀, σ, hYc, hYcc, hYcp, hV₀rel, hV₀0, hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, U'', hU''o,
    h0U'', hU''⟩ := theorem_3_47_proj hCt 𝒮 hh'𝒮 hsurj hpos
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
  -- the neighbourhood `Vx` of `x₀` in `X`
  obtain ⟨Vx, hVxdef⟩ : ∃ Vx : Set X,
    Vx = (c.φ.source ∩ c.φ ⁻¹' N₁) ∩ (c.φ.source ∩ (ψ ∘ c.φ) ⁻¹' (Ω ∩ Og)) := ⟨_, rfl⟩
  have hmemVx : ∀ y, y ∈ Vx ↔ y ∈ c.φ.source ∧ c.φ y ∈ N₁ ∧ ψ (c.φ y) ∈ Ω ∧ ψ (c.φ y) ∈ Og := by
    intro y; rw [hVxdef]
    simp only [mem_inter_iff, mem_preimage, Function.comp_apply]; tauto
  have hψφ : ContinuousOn (ψ ∘ c.φ) c.φ.source :=
    hψcont.comp c.φ.continuousOn_toFun fun y hy => hOU (c.φ.mapsTo_model y hy)
  have hVxo : IsOpen Vx := by
    rw [hVxdef]
    exact (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hN₁open).inter
      (hψφ.isOpen_inter_preimage c.φ.isOpen_source (hΩo.inter hOg))
  have hx₀Vx : x₀ ∈ Vx := by
    rw [hmemVx, h0, hψ0]
    exact ⟨hxV, h0N₁, h0Ω, ((hGmem 0).1 (G.zero_mem 0)).1⟩
  have hVxsub : Vx ⊆ c.φ.source := fun y hy => ((hmemVx y).1 hy).1
  -- for `y ∈ Vx`: `ψ(ϕ y) ∈ G.U 0`, and the zeros
  have hVxG : ∀ y ∈ Vx, ψ (c.φ y) ∈ G.U 0 := fun y hy =>
    (hGmem _).2 ⟨((hmemVx y).1 hy).2.2.2, hU'C (hψU' (hOU (c.φ.mapsTo_model y (hVxsub hy))))⟩
  have hzero : ∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0 := by
    intro y hy
    obtain ⟨hy1, hyN, -, -⟩ := (hmemVx y).1 hy
    have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hy1
    have hyU : c.φ y ∈ c.U := hOU hyO
    rw [c.isZeroAt_iff hf hy1, hfsum, ← hkey _ hyU hyN]
    have hfbg : fb (c.φ y) = g (c.φ y) := (hN₁ _ hyN).1 hyO
    change fb (c.φ y) = 0 ↔ _
    rw [hfbg]
    show g (c.φ y) = 0 ↔ (Ψ (ψ' (ψ (c.φ y)), g (ψ' (ψ (c.φ y))))).2 = 0
    rw [hψψ' _ hyU]
    exact (hΨ.snd_eq_zero_iff hyU).symm
  -- `Dσ(0) = 0` on the smaller `V'`
  have hDσ' : fderivWithin ℝ σ V' 0 = 0 := by
    have hd : HasFDerivWithinAt σ (0 : _ →L[ℝ] Pn × W 0) V₀ 0 := by
      have := (hσC.differentiableOn one_ne_zero 0 hV₀0).hasFDerivWithinAt
      rwa [hDσ] at this
    have hCt0 : Convex ℝ Ct := by
      have h := hCt.isQuadrantLike.convex 0
      rwa [ScBanach.const_lvlSet] at h
    have hconv : Convex ℝ (Subtype.val ⁻¹' (Ct ×ˢ univ) :
        Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))) :=
      (hCt0.prod convex_univ).linear_preimage
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).subtype
    have huniqV₀ : UniqueDiffWithinAt ℝ V₀ 0 := by
      obtain ⟨O₀, hO₀, hV₀⟩ := hV₀rel
      have h0' : (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈
          O₀ ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := hV₀ ▸ hV₀0
      rw [hV₀, inter_comm]
      exact (uniqueDiffWithinAt_convex hconv hpos.interior_nonempty (subset_closure h0'.2)).inter
        (hO₀.mem_nhds h0'.1)
    have huniq : UniqueDiffWithinAt ℝ V' 0 := by
      rw [hV'def]
      exact huniqV₀.inter (hO₁.mem_nhds (hV'def ▸ h0V' : (0 : _) ∈ V₀ ∩ O₁).2)
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
  refine ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, fun u' hu' => hΨ.invFun.base_mem hu', hψψ', hψ'ψ,
    𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx,
    ⟨h0U, g, t₀, hfill, ht₀, ht₀0, hgp,
      ⟨Pn, Q, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩, by
        rw [finrank_ker_eq_fredholmIndex_of_surjective (𝒮.isFredholm_Dfs hCt hh'𝒮).1 hsurj,
          (𝒮.isFredholm_Dfs hCt hh'𝒮).2]⟩,
    hYc, hYcc, hYcp, 𝒮.ker_Dfs_le_smooth hCt hh'𝒮, hV'rel,
    h0V', hσY, hσ1, hσC.mono hV'sub,
    hσ0, hDσ', fun y hy => hsol y (hV'sub hy), hlift', hVxo, hx₀Vx, hVxsub, ?_, hzero, ?_⟩
  · -- injectivity of `ψ ∘ ϕ` on `Vx`
    intro y hy y' hy' heq
    have h1 : ψ' (ψ (c.φ y)) = ψ' (ψ (c.φ y')) := congrArg ψ' heq
    rw [hψψ' _ (hOU (c.φ.mapsTo_model y (hVxsub hy))),
      hψψ' _ (hOU (c.φ.mapsTo_model y' (hVxsub hy')))] at h1
    exact c.φ.toPartialEquiv.injOn (hVxsub hy) (hVxsub hy') h1
  · -- the graph description
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyz⟩, rfl⟩
      obtain ⟨-, -, hyΩ, -⟩ := (hmemVx y).1 hy
      have hz0 : 𝒮.fsum h' (ψ (c.φ y)) = 0 := (hzero y hy).1 hyz
      obtain ⟨v, hv, hveq⟩ := hU'' (ψ (c.φ y)) ⟨hΩU'' _ hyΩ, h𝒮G ▸ hVxG y hy⟩ hz0
      refine ⟨v, hmemV' v hv ?_, hveq.symm⟩
      rw [hΓ, ← hveq]; exact hyΩ
    · rintro ⟨v, hv, rfl⟩
      have hvV₀ : v ∈ V₀ := hV'sub hv
      obtain ⟨hzG, hz0⟩ := hsol v hvV₀
      have hzG' : (v : Pn × W 0) + σ v ∈ G.U 0 := h𝒮G ▸ hzG
      have hzU' : (v : Pn × W 0) + σ v ∈ U' := hG hzG'
      have hvΩ : (v : Pn × W 0) + σ v ∈ Ω := hΓ v ▸ hV'Ω v hv
      have huN : ψ' ((v : Pn × W 0) + σ v) ∈ N₁ := hW'sub (hΩW' _ hvΩ) hzU'
      have huU : ψ' ((v : Pn × W 0) + σ v) ∈ c.U := hΨ.invFun.base_mem hzU'
      have hgu : g (ψ' ((v : Pn × W 0) + σ v)) = 0 := by
        have h1 := hkey _ huU huN
        rw [hψ'ψ _ hzU', ← hfsum, hz0] at h1
        have h2 : (Ψ (ψ' ((v : Pn × W 0) + σ v), g (ψ' ((v : Pn × W 0) + σ v)))).2 = 0 := by
          exact h1
        exact (hΨ.snd_eq_zero_iff huU).1 h2
      have huO : ψ' ((v : Pn × W 0) + σ v) ∈ c.φ.model.O := hgO _ huU huN hgu
      refine ⟨c.φ.symm (ψ' ((v : Pn × W 0) + σ v)), ⟨(hmemVx _).2 ⟨c.φ.symm_mapsTo huO, ?_, ?_, ?_⟩, ?_⟩,
        ?_⟩
      · rw [c.φ.apply_symm_apply huO]; exact huN
      · rw [c.φ.apply_symm_apply huO, hψ'ψ _ hzU']; exact hvΩ
      · rw [c.φ.apply_symm_apply huO, hψ'ψ _ hzU']; exact ((hGmem _).1 hzG').1
      · rw [c.isZeroAt_iff hf (c.φ.symm_mapsTo huO), c.φ.apply_symm_apply huO]
        change fb _ = 0
        rw [(hN₁ _ huN).1 huO, hgu]
      · show ψ (c.φ (c.φ.symm (ψ' ((v : Pn × W 0) + σ v)))) = (v : Pn × W 0) + σ v
        rw [c.φ.apply_symm_apply huO, hψ'ψ _ hzU']

/-- **Theorem 3.54, the graph description (3), with a good complement whose projection maps the
partial quadrant into itself**: `theorem_3_54_graph_wholeChart` (a corollary of this theorem) with the
additional conclusion `ProjectsInto (C̃ ⊕ W) K Yc`: the projection onto `K = ker D(h + t)(0)` along
the good complement `Yc` maps `C' = C̃ ⊕ W` into `K ∩ C'` (`theorem_3_47_proj`, Findings
130–133).  This gives condition (b) of `TangentGermChart.IsRegular` for the chart `ψ ∘ ϕ`
(`theorem_3_54_tangentGermChart_proj_wholeChart`).  The proof is that of `theorem_3_54_graph_wholeChart` with
`theorem_3_47_proj` in place of `theorem_3_47_closed`; the shrinking of `V'` does not touch `Yc`.
(A corollary of `theorem_3_54_graph_proj_conj_wholeChart`, which also exposes the conjugation.) -/
theorem theorem_3_54_graph_proj_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (ψ : c.φ.model.E 0 → (ScBanach.paramProd Pn W) 0) (_ : IsScSmooth c.U ψ) (_ : ψ 0 = 0)
      (_ : MapsTo ψ c.U U') (ψ' : (ScBanach.paramProd Pn W) 0 → c.φ.model.E 0)
      (_ : IsScSmooth U' ψ') (_ : MapsTo ψ' U' c.U) (_ : ∀ u ∈ c.U, ψ' (ψ u) = u)
      (_ : ∀ u' ∈ U', ψ (ψ' u') = u') (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X),
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      ProjectsInto (Ct ×ˢ univ) (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
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
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0) ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' := by
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, -, hrest⟩ :=
    theorem_3_54_graph_proj_conj_wholeChart hf hg hx₀
  exact ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hrest⟩

/-- **Theorem 3.54, the graph description (3) of the solution set.**  Let `f` be a section of the
strong bundle `P : Y → X`, `f(x₀) = 0`, and let `(f, x₀)` be an sc-Fredholm germ in good position
(Definition 3.53) in a tame strong bundle chart (`IsGoodPositionGermTameWholeChart`, Definition 3.50).  Then
there are: the tame strong bundle chart `c` centred at `x₀` of Definition 3.53, the conjugating sc-diffeomorphism
`ψ : U → U' ⊆ C' = C̃ ⊕ W` with `ψ(0) = 0` (and its inverse `ψ'`), the data `𝒮` of Theorem 3.38 (germ `G`, sc⁺-germ
`t_W`) and a basic germ `h'` on `G` (the text's `h + t = Ψ_*(g)` with the `ℝᴺ`-component of `t`
absorbed into `h`) with `D(h + t)(0) = D(𝒮.fsum h')(0)` surjective with kernel `K` in good
position to `C'`; a good complement `Y` of `K`; a relatively open neighbourhood `V'` of `0` in
`K ∩ C'`; a map `σ : V' → Y` of class `C¹` with values on level `1`, `σ(0) = 0`, `Dσ(0) = 0`;
and an open neighbourhood `Vx` of `x₀` in the chart domain such that `ψ ∘ ϕ` is injective on `Vx`
and `ψ ∘ ϕ({y ∈ Vx | f(y) = 0}) = {v + σ(v) | v ∈ V'}`; moreover `h + t` vanishes at
`ψ ∘ ϕ(y)` for `y ∈ Vx` exactly when `f(y) = 0`.  Recorded in addition (from
`theorem_3_47_closed`): `Y` is closed, and `σ` is an sc-smooth germ in the sense of Theorem 3.47
(1): for every `k ≥ 1` it lifts on a relatively open neighbourhood `V_k ⊆ V'` of `0` to a
`C^k`-map `σ_k : V_k → E'_k` (hence `IsScInftyGermAt`, by `isScInftyGermAt_of_lifts`); the kernel
`K` is a smooth subspace (`ker_Dfs_le_smooth`); and every `v + σ(v)`, `v ∈ V'`, is a zero of
`h + t` in `U'`.  These are the data of Definition 3.25 (2) for the solution set at `x₀` in the
chart `ψ ∘ ϕ`, except for that chart itself (the tameness of `ψ(O)`, see the module docstring).
(A corollary of `theorem_3_54_graph_proj_wholeChart`.) -/
theorem theorem_3_54_graph_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsGoodPositionGermTameWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (ψ : c.φ.model.E 0 → (ScBanach.paramProd Pn W) 0) (_ : IsScSmooth c.U ψ) (_ : ψ 0 = 0)
      (_ : MapsTo ψ c.U U') (ψ' : (ScBanach.paramProd Pn W) 0 → c.φ.model.E 0)
      (_ : IsScSmooth U' ψ') (_ : MapsTo ψ' U' c.U) (_ : ∀ u ∈ c.U, ψ' (ψ u) = u)
      (_ : ∀ u' ∈ U', ψ (ψ' u') = u') (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X),
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
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0) ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' := by
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hYc, hYcc, -, hrest⟩ :=
    theorem_3_54_graph_proj_wholeChart hf hg hx₀
  exact ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hYc, hYcc, hrest⟩

end Thm354

/-! ### Theorems 3.56 and 3.57: the global implicit function theorem, given the tangent germ
property of the solution set -/

section Global

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- The solution set `S = {y ∈ X | f(y) = 0}` of a section. -/
def solutionSet (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y) : Set X :=
  {y | IsZeroAt P f y}

/-- **Theorem 3.57 (global implicit function theorem, boundary case), the step from the tangent
germ property.**  The text derives Theorem 3.57 from Theorem 3.54: at every zero the germ is in
good position, so the solution set `S` has the `d`-dimensional tangent germ property near every
point and Theorem 3.27 applies.  This is the second step, for a fixed dimension `n`: if `S` has
the regular tangent germ property (`TangentGermChart` with `IsRegular` at every point), then `S`
is a sub-M-polyfold of `X` whose induced structure is tame and that of an `n`-dimensional
manifold with boundary with corners.  The first step (the regular data at every zero, from the
graph description of `theorem_3_54_graph_wholeChart`, the sc^∞-germ property of Theorem 3.43 (1) and the
re-centring at the nearby zeros) is `theorem_3_54_two_wholeChart`, and the assembled theorem, with locally
constant dimension, is `theorem_3_57_wholeChart` (`GlobalIFTTheorems.lean`). -/
theorem theorem_3_57_of_tangentGerm {f : X → Y} {n : ℕ} (hne : (solutionSet P f).Nonempty)
    (hS : ∀ x ∈ solutionSet P f, ∃ d : PX.TangentGermChart (solutionSet P f) x n, d.IsRegular) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n := by
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_27 PX hne hS
  exact ⟨hsub, h1, h2⟩

/-- **Theorem 3.56 (global implicit function theorem, `∂X = ∅`), the step from the tangent germ
property**: as `theorem_3_57_of_tangentGerm`, for an M-polyfold without boundary; the induced
structure on `S` is then a manifold without boundary: its degeneracy index vanishes (Lemma 2.26,
`d_S ≤ d_X = 0`). -/
theorem theorem_3_56_of_tangentGerm (hX : PX.IsWithoutBoundary) {f : X → Y} {n : ℕ}
    (hne : (solutionSet P f).Nonempty)
    (hS : ∀ x ∈ solutionSet P f, ∃ d : PX.TangentGermChart (solutionSet P f) x n, d.IsRegular) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hsub, -, h2, -⟩ := theorem_3_27 PX hne hS
  refine ⟨hsub, h2, fun y => ?_⟩
  have := lemma_2_26 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

end Global

end Polyfold
