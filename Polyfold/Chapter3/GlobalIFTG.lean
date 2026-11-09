import Polyfold.Chapter3.GlobalIFT
import Polyfold.Chapter3.GlobalIFTNearbyGraphG
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54, the graph description (3) of the solution set, **in the text's germ reading of Definition
3.11** (phase 2): the hypothesis `IsGoodPositionGermTameWholeChart` of `GlobalIFT.lean` (filled version `g`
and sc⁺-section `s` sc-smooth on the whole chart) is replaced by `IsGoodPositionGermTame`
(filling germ `g` on `G_g`, sc⁺-germ `s` on `G_s`, good position at `Dg(0)`).

# Theorem 3.6.8 (preprint 3.54) (3), germ reading

## What is formalized

* `Polyfold.theorem_3_6_8_graph_proj_conj`: **Theorem 3.6.8 (preprint 3.54) (3) with the conjugation exposed,
  germ reading** — the germ form of `theorem_3_6_8_graph_proj_conj_wholeChart`: the same conclusions (the
  tame chart `c`, the sc-diffeomorphism `ψ`, the data `𝒮` of Theorem 3.4.2 (preprint 3.38), the basic germ `h'`,
  the good complement `Yc` with `ProjectsInto`, `σ : V' → Yc`, the neighbourhood `Vx` of `x₀`
  with `ψ ∘ ϕ(S ∩ Vx) = graph σ`), with the data of Definition 3.6.6 (preprint 3.53) in `c` now in the germ
  reading (`IsFillingGerm`, `IsScPlusGerm`, a germ `G` with a derivative family `Dg` of `g`,
  `IsGoodPositionAtGerm` at `Dg(0)`, conjugation data `dc`) and
  `dim K = dim dc.Pn − dim dc.Q`.
* `Polyfold.theorem_3_6_8_graph_proj`, `Polyfold.theorem_3_6_8_graph`: the corollaries,
  with the **same conclusions** as `theorem_3_6_8_graph_proj_wholeChart` and `theorem_3_6_8_graph_wholeChart`.

## What the text leaves implicit, and the choices made (the findings)

* **The G″ design.**  The conjugation data `d` of `g − s` are shrunk to
  `d.shrink (G_g ∩ G_s)` (`BasicGermShrink.lean`): same `Ψ`, `h`, `B`, and the basic germ on the
  germ `G″` of the points that `ψ'` sends into `G_g ∩ G_s` level by level.  The chart-level
  theorem `theorem_3_6_8_chart_graph` builds the data `𝒮` of Theorem 3.4.2 (preprint 3.38) on `G″`; the
  level-`0` neighbourhood `Vx` is chosen with `ψ ∘ ϕ(Vx) ⊆ G″₀`.  Every nearby zero that the
  implicit function theorem produces then lies in `𝒮.G = G″`, where `g` and `s` are sc¹ at the
  preimages (`GlobalIFTNearbyKernelG.lean`).
* The old statements follow from the germ ones: `IsGoodPositionGermTameWholeChart.isGoodPositionGermTame`
  (`TameGermsG.lean`), and the conclusions of `theorem_3_6_8_graph_proj` and
  `theorem_3_6_8_graph` are literally those of the old theorems.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section Thm354

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- The tameness input `(1 − Dr(0))E ⊆ E₀` of Theorem 3.6.8 (preprint 3.54) at a zero `x₀` of a section in a
tame chart centred at `x₀` (Proposition 2.5.3 (preprint 2.35) for the base retraction of the chart). -/
theorem StrongBundle.IsTameChart.range_id_sub_scDeriv_le {c : StrongBundleChart PX P}
    (hc : B.IsTameChart c) {x₀ : X} (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) :
    LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 := by
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x₀ hxV
  have hRtT := hc.2 n Wq T hT
  have h01 : (0 : c.φ.model.E 1) ∈
      c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact h0O
  have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  have h235 := (proposition_2_5_3 hT hRtT h01 hs).1
  rw [map_zero] at h235
  exact h235

set_option maxHeartbeats 800000 in
/-- **Theorem 3.6.8 (preprint 3.54), the graph description (3), with the conjugation exposed, germ reading**
(phase 2; the germ form of `theorem_3_6_8_graph_proj_conj_wholeChart`): for a section `f` with `f(x₀) = 0` and
`(f, x₀)` in good position in a tame chart in the germ reading (`IsGoodPositionGermTame`), the
conclusions of `theorem_3_6_8_graph_proj_wholeChart` together with the data of Definition 3.6.6 (preprint 3.53) in the chart
`c` in the germ reading — the filling germ `g` of `f̂`, the sc⁺-germ `s` with `s(0) = g(0)`, a
germ `G ⊆ U` with a derivative family `Dg` of `g`, the good position `IsGoodPositionAtGerm` at
`Dg(0)`, and conjugation data `dc` of `g − s` — with `dim K = dim dc.Pn − dim dc.Q` for the kernel
`K = ker D(h + t)(0)`.  The data `𝒮` of Theorem 3.4.2 (preprint 3.38) are built on the germ `G″` of
`dc.shrink (G_g ∩ G_s)`, so that `ψ ∘ ϕ(Vx) ⊆ 𝒮.G₀` and every nearby zero that the implicit
function theorem produces is a point where `g` and `s` are sc¹ (the G″ design). -/
theorem theorem_3_6_8_graph_proj_conj (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
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
        (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0)
        (_ : G.U 0 ⊆ c.U) (_ : IsSc1GermWith G g Dg)
        (_ : IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0))
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
  have hψ'ψ : ∀ u' ∈ d'.U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    exact mem_U_of_mem_O c.isRetraction hz
  obtain ⟨h0O', hfb0, hfK⟩ := c.zero_data hf hxV h0 hx₀
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hK := hc.range_id_sub_scDeriv_le hxV h0 T hT
  have hψsc : IsScSmooth c.U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth d'.U' ψ' := hΨ.invFun.base_isScSmooth d'.relOpen
  have hψU' : MapsTo ψ c.U d'.U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' d'.U' c.U := fun u hu => hΨ.invFun.base_mem hu
  -- the graph description in the chart, on `G″`
  obtain ⟨𝒮, h', Yc, V', σ, Wo, N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, -, hWo, h0Wo, hagree, hYc, hYcc,
    hYcp, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hN₁o, h0N₁, hN₁, hψ'N₁, hN₂o, h0N₂,
    hN₂N₁, hN₂ψ, hgO, hzero, himage⟩ :=
    theorem_3_6_8_chart_graph hU c.isRetraction h0U h0O' hfill hfb0 hfK hGg hgsm hDg ht₀ ht₀0
      d'.quadrant d'.relOpen hΨ hψ0 d'.germ_subset d'.basic hGψ' d'.conj T hT hK hgp
  -- the neighbourhood `Vx` of `x₀`
  have hφ : ContinuousOn c.φ c.φ.source := c.φ.continuousOn_toFun
  obtain ⟨Vx, hVxdef⟩ : ∃ Vx : Set X, Vx = c.φ.source ∩ c.φ ⁻¹' N₂ := ⟨_, rfl⟩
  have hmemVx : ∀ y, y ∈ Vx ↔ y ∈ c.φ.source ∧ c.φ y ∈ N₂ := fun y => by rw [hVxdef]; rfl
  have hVxo : IsOpen Vx := hVxdef ▸ hφ.isOpen_inter_preimage c.φ.isOpen_source hN₂o
  have hx₀Vx : x₀ ∈ Vx := (hmemVx x₀).2 ⟨hxV, by rw [h0]; exact h0N₂⟩
  have hVxsub : Vx ⊆ c.φ.source := fun y hy => ((hmemVx y).1 hy).1
  have hVxN₂ : ∀ y ∈ Vx, c.φ y ∈ N₂ := fun y hy => ((hmemVx y).1 hy).2
  -- the zeros in `Vx`: `f̂(ϕ y) = g(ϕ y)`
  have hfbg : ∀ y ∈ Vx, fb (c.φ y) = g (c.φ y) := fun y hy =>
    (hN₁ _ (hN₂N₁ (hVxN₂ y hy))).1 (c.r_image ▸ c.φ.mapsTo_model y (hVxsub hy))
  have hzero' : ∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0 := fun y hy => by
    rw [c.isZeroAt_iff hf (hVxsub hy), ← hfbdef, hfbg y hy]
    exact hzero _ ⟨c.r_image ▸ c.φ.mapsTo_model y (hVxsub hy), hVxN₂ y hy⟩
  refine ⟨c, hc, hxV, h0, d'.Pn, d'.Q, d'.i1, d'.i2, d'.i3, d'.i4, d'.i5, d'.i6, d'.W, d'.Ct,
    d'.quadrant, d'.U', d'.relOpen, ψ, hψsc, hψ0, hψU', ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', d'.Bc,
    hh'𝒮, hsurj, hpos, Yc, V', σ, Vx,
    ⟨h0U, g, t₀, hfill, hsP, ht₀0, Gg, Dg, hGg, hDg, hgp, d, by
      rw [finrank_ker_eq_fredholmIndex_of_surjective (𝒮.isFredholm_Dfs d'.quadrant hh'𝒮).1 hsurj,
        (𝒮.isFredholm_Dfs d'.quadrant hh'𝒮).2]
      rfl⟩,
    hYc, hYcc, hYcp, 𝒮.ker_Dfs_le_smooth d'.quadrant hh'𝒮, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ,
    hsol, hlift, hVxo, hx₀Vx, hVxsub, ?_, hzero', ?_⟩
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

/-- **Theorem 3.6.8 (preprint 3.54), the graph description (3), with `ProjectsInto`, germ reading** (phase 2; the
germ form of `theorem_3_6_8_graph_proj_wholeChart`, with the same conclusions): a corollary of
`theorem_3_6_8_graph_proj_conj`. -/
theorem theorem_3_6_8_graph_proj (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
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
    theorem_3_6_8_graph_proj_conj hf hg hx₀
  exact ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hrest⟩

/-- **Theorem 3.6.8 (preprint 3.54), the graph description (3) of the solution set, germ reading** (phase 2; the
germ form of `theorem_3_6_8_graph_wholeChart`, with the same conclusions): for a section `f` with
`f(x₀) = 0` and `(f, x₀)` an sc-Fredholm germ in good position in a tame chart in the text's germ
reading (`IsGoodPositionGermTame`), the tame chart `c` centred at `x₀`, the conjugating
sc-diffeomorphism `ψ`, the data `𝒮` of Theorem 3.4.2 (preprint 3.38) and the basic germ `h'` with
`D(𝒮.fsum h')(0)` surjective with kernel `K` in good position, a closed good complement `Y` of
`K`, `σ : V' → Y` of class `C¹` with `C^k`-lifts, `σ(0) = 0`, `Dσ(0) = 0`, and an open
neighbourhood `Vx` of `x₀` with `ψ ∘ ϕ` injective on `Vx` and
`ψ ∘ ϕ({y ∈ Vx | f(y) = 0}) = {v + σ(v) | v ∈ V'}`.  A corollary of `theorem_3_6_8_graph_proj`. -/
theorem theorem_3_6_8_graph (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
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
    theorem_3_6_8_graph_proj hf hg hx₀
  exact ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hYc, hYcc, hrest⟩

end Thm354

end Polyfold
