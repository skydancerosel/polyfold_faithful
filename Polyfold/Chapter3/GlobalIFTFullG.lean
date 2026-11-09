import Polyfold.Chapter3.GlobalIFTFull
import Polyfold.Chapter3.GlobalIFTG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54 (1) in the chart at `x₀` (Corollary 3.5.3 (preprint 3.41) and Lemma 3.6.9 (preprint 3.55) at the points of the solution
graph), **in the text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# Theorem 3.6.8 (preprint 3.54) (1) in the chart at `x₀`, germ reading

## What is formalized

`Polyfold.theorem_3_6_8_nearby`: the germ form of `theorem_3_6_8_nearby_wholeChart`, with the same
conclusions, under the hypothesis `IsGoodPositionGermTame` of the germ reading.  The proof is
that of `theorem_3_6_8_nearby_wholeChart` from `theorem_3_6_8_graph` in place of `theorem_3_6_8_graph_wholeChart`:
only the data of Theorem 3.5.11 (preprint 3.47) on the `E'`-side are used (Corollary 3.5.3 (preprint 3.41) along the graph, Lemma
3.55), nothing of the filling `g` or the sc⁺-section `s`.
-/

open Set Filter Topology Function Module Metric ContinuousLinearMap

noncomputable section

namespace Polyfold

section Thm354Nearby

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

set_option maxHeartbeats 800000 in
/-- **Theorem 3.6.8 (preprint 3.54) (1) in the chart at `x₀`, germ reading** (phase 2; the germ form of
`theorem_3_6_8_nearby_wholeChart`, with the same conclusions): in the data of `theorem_3_6_8_graph`
there are a presentation `T` of `C' = C̃ ⊕ W` and an open neighbourhood `Vx₁ ⊆ Vx` of `x₀` such
that for every zero `y ∈ Vx₁` of `f`, with `z = ψ ∘ ϕ(y) = v + σ(v)`, `v ∈ V'`: (i) `z` lies on
level `1` and `D(h + t)(z)` is a surjective Fredholm operator of index `n − N` (Corollary 3.5.3 (preprint 3.41));
(ii) `z ∈ C'`, and the tangent space `N_v` of the graph at `z` is in good position to `C'_z` with
`Y` as a good complement (Lemma 3.6.9 (preprint 3.55)). -/
theorem theorem_3_6_8_nearby (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (ψ : c.φ.model.E 0 → (ScBanach.paramProd Pn W) 0) (_ : IsScSmooth c.U ψ) (_ : ψ 0 = 0)
      (_ : MapsTo ψ c.U U') (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X)
      (n' : ℕ) (W' : ScBanach)
      (T : ScIso (ScBanach.paramProd Pn W) ((ScBanach.const (Fin n' → ℝ)).prod W')) (Vx₁ : Set X),
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V' ∧
      (∀ y, σ y ∈ Yc) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (∀ y ∈ V', (y : Pn × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum h' ((y : Pn × W 0) + σ y) = 0) ∧
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0) ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' ∧
      Ct ×ˢ (univ : Set (W 0)) = T 0 ⁻¹' quadrant n' W' 0 ∧
      IsOpen Vx₁ ∧ x₀ ∈ Vx₁ ∧ Vx₁ ⊆ Vx ∧
      ∀ y ∈ Vx₁, IsZeroAt P f y → ∃ v ∈ V', ψ (c.φ y) = (v : Pn × W 0) + σ v ∧
        (∃ x₁ : (ScBanach.paramProd Pn W) 1,
          (ScBanach.paramProd Pn W).toBase 1 x₁ = (v : Pn × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
          IsFredholm (𝒮.Dfs' h' x₁) ∧
          fredholmIndex (𝒮.Dfs' h' x₁) = Module.finrank ℝ Pn - Module.finrank ℝ Q ∧
          Surjective (𝒮.Dfs' h' x₁)) ∧
        ((v : Pn × W 0) + σ v ∈ Ct ×ˢ univ) ∧
        IsGoodComplement (ScBanach.paramProd Pn W)
          (partialQuadrantAtWith T ((v : Pn × W 0) + σ v))
          (graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
            (fderivWithin ℝ σ V' v)) Yc ∧
        IsInGoodPosition (ScBanach.paramProd Pn W)
          (partialQuadrantAtWith T ((v : Pn × W 0) + σ v))
          (graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
            (fderivWithin ℝ σ V' v)) := by
  classical
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    -, -, -, -, -,
    𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hYc, hYcc, -, hV'rel, h0V', hσY, hσ1, hσC, hσ0,
    hDσ, hsol, -, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage⟩ := theorem_3_6_8_graph hf hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh').1.finite_ker
  obtain ⟨n', W', T, hT⟩ := hCt.prod_univ W
  -- Corollary 3.5.3 (preprint 3.41) and Lemma 3.6.9 (preprint 3.55) at the graph points
  obtain ⟨ρ₁, hρ₁, hA⟩ := 𝒮.exists_surjective_Dfs'_graph hCt hh' hsurj h0V' hσC.continuousOn hσ0
    hsol
  obtain ⟨ρ₂, hρ₂, hB⟩ := lemma_3_6_9_relOpen T hT hpos hYc hYcc hV'rel h0V' σ hσY hσC hσ0 hDσ
  -- the projection onto `K` along `Y`
  have hTC : Submodule.IsTopCompl (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hYc.isCompl.symm hYcc).symm
  set π : Pn × W 0 →L[ℝ] LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) :=
    (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).projectionOntoL Yc hTC with hπdef
  have hπ : ∀ v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), ∀ y ∈ Yc,
      π ((v : Pn × W 0) + y) = v := fun v y hy => by
    rw [map_add, Submodule.projectionOntoL_apply_left hTC v,
      (Submodule.projectionOntoL_apply_eq_zero_iff hTC).2 hy, add_zero]
  set ρ := min ρ₁ ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  set ρ' := ρ / (‖π‖ + 1) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  -- the neighbourhood `Vx₁`
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have hψφ : ContinuousOn (ψ ∘ c.φ) Vx :=
    (hψsc.isSc1.isSc0.continuousOn_base.comp (c.φ.continuousOn_toFun.mono hVxsub)
      fun y hy => hOU (c.φ.mapsTo_model y (hVxsub hy)))
  refine ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, n', W', T, Vx ∩ (ψ ∘ c.φ) ⁻¹' ball 0 ρ',
    hYc, hYcc, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage,
    hT,
    hψφ.isOpen_inter_preimage hVxo isOpen_ball, ⟨hx₀Vx, ?_⟩, inter_subset_left, ?_⟩
  · show ψ (c.φ x₀) ∈ ball 0 ρ'
    rw [h0, hψ0]; exact mem_ball_self hρ'
  · rintro y ⟨hyVx, hyball⟩ hy0
    have hz : ψ (c.φ y) ∈ (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) =>
        (v : Pn × W 0) + σ v) '' V' := by
      rw [← himage]; exact ⟨y, ⟨hyVx, hy0⟩, rfl⟩
    obtain ⟨v, hv, hveq⟩ := hz
    have hvnorm : ‖v‖ < ρ := by
      have h1 : π (ψ (c.φ y)) = v := by rw [← hveq]; exact hπ v _ (hσY v)
      have h2 : ‖ψ (c.φ y)‖ < ρ' := by
        have := hyball; rwa [mem_preimage, Function.comp_apply, mem_ball_zero_iff] at this
      calc ‖v‖ = ‖π (ψ (c.φ y))‖ := by rw [h1]
        _ ≤ ‖π‖ * ‖ψ (c.φ y)‖ := π.le_opNorm _
        _ ≤ ‖π‖ * ρ' := by gcongr
        _ < (‖π‖ + 1) * ρ' := by gcongr; linarith
        _ = ρ := by rw [hρ'def]; field_simp
    obtain ⟨hzC, hgc, hgp⟩ := hB v hv (hvnorm.trans_le (min_le_right _ _))
    exact ⟨v, hv, hveq.symm, hA v hv (hvnorm.trans_le (min_le_left _ _)), hzC, hgc, hgp⟩

end Thm354Nearby

end Polyfold
