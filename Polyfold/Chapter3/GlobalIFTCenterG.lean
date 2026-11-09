import Polyfold.Chapter3.GlobalIFTCenter
import Polyfold.Chapter3.GlobalIFTG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54 (2) at the centre `x₀` — the data of Definition 3.2.1 (preprint 3.25) (2) for the solution set in the chart
`ψ ∘ ϕ` — **in the text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# Theorem 3.6.8 (preprint 3.54) (2) at the centre, germ reading

## What is formalized

* `Polyfold.theorem_3_6_8_tangentGermChart_proj_conj`: the germ form of
  `theorem_3_6_8_tangentGermChart_proj_conj_wholeChart`: the regular data `D` of Definition 3.2.1 (preprint 3.25) (2) with
  `π(O') ⊆ C'` at `x₀` for `S = {y ∈ Vx | f(y) = 0}`, with the data of Definition 3.6.6 (preprint 3.53) in the
  chart `c` in the germ reading and `d = dim dc.Pn − dim dc.Q`.
* `Polyfold.theorem_3_6_8_tangentGermChart_proj`, `Polyfold.theorem_3_6_8_tangentGermChart`:
  the corollaries, with the same conclusions as the old theorems.

The proofs are those of `GlobalIFTCenter.lean` from `theorem_3_6_8_graph_proj_conj`: the
chart `ψ ∘ ϕ` (`MChart.compDiffeo`), the tame retract `ψ(O)`, and the data `N`, `Y`, `V'`, `σ`
of Theorem 3.5.11 (preprint 3.47) on the `E'`-side; nothing of the filling `g` or the sc⁺-section `s` enters.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section Center

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

set_option maxHeartbeats 800000 in
/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀`, with the conjugation exposed, germ reading** (phase 2;
the germ form of `theorem_3_6_8_tangentGermChart_proj_conj_wholeChart`): the data of Definition 3.2.1 (preprint 3.25) (2) for
`S = {y ∈ Vx | f(y) = 0}` at `x₀` with `π(O') ⊆ C'`, built from the chart `ψ ∘ ϕ` of
`theorem_3_6_8_graph_proj_conj`, together with the data of Definition 3.6.6 (preprint 3.53) in the chart `c`
in the germ reading (filling germ `g`, sc⁺-germ `s`, derivative family `Dg` on a germ `G`, good
position at `Dg(0)`, conjugation data `dc`) and `d = dim dc.Pn − dim dc.Q`. -/
theorem theorem_3_6_8_tangentGermChart_proj_conj (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
        (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1)
        (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0)
        (_ : G.U 0 ⊆ c.U) (_ : IsSc1GermWith G g Dg)
        (_ : IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0))
        (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)),
        (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q := by
  classical
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hconjd, hYc, hYcc,
    hYcp, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hVxo, hx₀Vx, hVxsub, hinj, hzero,
    himage⟩ := theorem_3_6_8_graph_proj_conj hf hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh').1.finite_ker
  -- the sc-diffeomorphism `ψ : U → U'` and the tame retract `ψ(O)`
  have hd : IsScDiffeoQuadrant c.relOpen hU' ψ ψ' := ⟨hψsc, hψ'sc, hψU', hψ'U, hψψ', hψ'ψ⟩
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have htameO : IsTameRetract (ScBanach.paramProd Pn W) (Ct ×ˢ univ) (ψ '' c.φ.model.O) := by
    have := hd.isTameRetract_image (c.isRetraction.baseRetraction c.relOpen) rfl hc.2
    rwa [c.base_retract] at this
  -- the chart `ψ ∘ ϕ`
  set χ := c.φ.compDiffeo hd hOU htameO.isScRetract with hχ
  have hDσ' : fderivWithin ℝ σ (Subtype.val ⁻¹' (Ct ×ˢ univ)) 0 = 0 := by
    obtain ⟨O, hO, hV'eq⟩ := hV'rel
    have h0O : (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ O := (hV'eq ▸ h0V').1
    rw [hV'eq, inter_comm, fderivWithin_inter (hO.mem_nhds h0O)] at hDσ
    exact hDσ
  refine ⟨Vx, finrank ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)), hVxo, hx₀Vx,
    ⟨?_, ?_⟩, c, hc, hxV, h0, hconjd⟩
  exact
    { φ := χ
      isChart := c.φ.compDiffeo_isChart c.isChart hd hOU htameO.isScRetract
      mem_source := hxV
      φ_zero := by show ψ (c.φ x₀) = 0; rw [h0, hψ0]
      tame := htameO
      N := LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)
      finiteDimensional := hKfin
      finrank_eq := rfl
      smooth := hKsm
      goodPosition := hpos
      Y := Yc
      goodComplement := hYc
      isClosed_Y := hYcc
      V := V'
      V_relOpen := hV'rel
      zero_mem_V := h0V'
      δ := σ
      δ_mem_Y := hσY
      continuousOn := hσC.continuousOn
      image_eq := by
        show (ψ ∘ c.φ) '' ({y ∈ Vx | IsZeroAt P f y} ∩ c.φ.source) = _
        rw [inter_eq_left.2 fun y hy => hVxsub hy.1]
        exact himage
      germ := by
        have := hKfin
        exact isScInftyGermAt_of_lifts (N := LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
          (E := ScBanach.paramProd Pn W) (D := Subtype.val ⁻¹' (Ct ×ˢ univ)) (σ := σ) fun k hk => by
          obtain ⟨Vk, h1, h2, -, σk, h3, h4⟩ := hlift k hk
          exact ⟨Vk, h1, h2, σk, h3, h4⟩
      δ_zero := hσ0
      fderivWithin_zero := hDσ' }
  -- condition (b) of `IsRegular`: `π(ψ(O)) ⊆ C'`, from the choice of `Y` (`ProjectsInto`)
  exact MPolyfold.TangentGermChart.π_mem_of_projectsInto _ hYcp

/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀` with condition (b) of `IsRegular`, germ reading**
(phase 2; the germ form of `theorem_3_6_8_tangentGermChart_proj_wholeChart`, with the same conclusion). -/
theorem theorem_3_6_8_tangentGermChart_proj (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C := by
  obtain ⟨Vx, d, h1, h2, hD, -⟩ := theorem_3_6_8_tangentGermChart_proj_conj hf hg hx₀
  exact ⟨Vx, d, h1, h2, hD⟩

/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀`: the data of Definition 3.2.1 (preprint 3.25) (2) for the solution set,
germ reading** (phase 2; the germ form of `theorem_3_6_8_tangentGermChart_wholeChart`, with the same
conclusion). -/
theorem theorem_3_6_8_tangentGermChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      Nonempty (PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d) := by
  obtain ⟨Vx, d, h1, h2, D, -⟩ := theorem_3_6_8_tangentGermChart_proj hf hg hx₀
  exact ⟨Vx, d, h1, h2, ⟨D⟩⟩

end Center

end Polyfold
