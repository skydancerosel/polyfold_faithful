import Polyfold.Chapter3.LocalSolvability
import Polyfold.Chapter3.GoodComplementProjection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.5,
**Theorem 3.43** and **Corollary 3.47** (local germ solvability) with the **closedness of the good
complement `Y`** recorded in the statement.

# Local germ solvability: the good complement is closed

The text's good complement `Y'` of `N' = ker Dg(0)` in Theorem 3.43 is `Z ⊕ W` for a subspace
`Z ⊆ ℝⁿ'` (Lemma 3.46), an sc-complement, hence closed; Corollary 3.47 transports it by the
linear coordinate change `ψ⁻¹` of Theorem 3.38 (Finding 69).  `Polyfold.theorem_3_43_sc_smooth`
and `Polyfold.theorem_3_47_sc_smooth` (in `LocalSolvability.lean`) hide `Y` in an existential
without recording its closedness, which Lemma 3.55 (`lemma_3_55`, added hypothesis `Y` closed,
Finding 49) and Definition 3.25 (`TangentGermChart.isClosed_Y`, Finding 81) need at the nearby
zeros in the proof of Theorem 3.54.  This file restates both theorems with the conjunct
`IsClosed Y`:

* `Polyfold.theorem_3_43_closed`: `theorem_3_43_sc_smooth` with `Y = Z ⊕ W` closed.
* `Polyfold.theorem_3_47_proj`: `theorem_3_47_sc_smooth` with `Y = ψ⁻¹(Z ⊕ W)` closed and with
  the projection onto `ker D(f + s)(0)` along `Y` mapping `C̃ ⊕ W` into itself (`ProjectsInto`,
  Findings 130–133): the complement of Theorem 3.43 is that of `theorem_3_43_proj`
  (`GoodComplementProjection.lean`), and both properties are carried through the linear
  homeomorphism `ψ⁻¹` of Theorem 3.38, which maps `(C̃ ⊕ ℝᴺ') ⊕ X` onto `C̃ ⊕ W`.  The proof is that
  of `theorem_3_47_sc_smooth` with the two properties carried along.
* `Polyfold.theorem_3_47_closed`: `theorem_3_47_sc_smooth` with `Y = ψ⁻¹(Z ⊕ W)` closed (a
  corollary of `theorem_3_47_proj`).
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

namespace ShiftedBasicData

/-- **Theorem 3.43 with the closedness of the good complement recorded**: `theorem_3_43_sc_smooth`
with the additional conclusion `IsClosed Y` (the complement is `Y' = Z ⊕ W` with `Z ⊆ ℝⁿ'`, a
closed subspace; the text's `Y'` is an sc-complement, hence closed).  Needed by Lemma 3.55 at the
nearby zeros (added hypothesis there, Finding 49) and by Definition 3.25
(`TangentGermChart.isClosed_Y`, Finding 81). -/
theorem _root_.Polyfold.theorem_3_43_closed (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒟 : ShiftedBasicData Ct W Q) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K')
    (hreg : ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒟.G₀.U 0, 𝒟.g x = 0 → ‖x‖ < r →
      ∃ w₁ : W 1, W.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε) :
    ∃ (Y : Submodule ℝ (P × W 0)) (V : Set 𝒟.K') (τ : 𝒟.K' → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K' Y ∧
      IsClosed (Y : Set (P × W 0)) ∧
      (∃ O : Set 𝒟.K', IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ (0 : 𝒟.K') ∈ V ∧
      (∀ y, τ y ∈ Y) ∧ (∀ y, (τ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 τ V ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + τ y ∈ 𝒟.G₀.U 0 ∧ 𝒟.g ((y : P × W 0) + τ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set 𝒟.K',
        (∃ O : Set 𝒟.K', IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : 𝒟.K') ∈ Vk ∧ Vk ⊆ V ∧
        ∃ τk : 𝒟.K' → (ScBanach.paramProd P W) k, ContDiffOn ℝ k τk Vk ∧
          ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (τk y) = τ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒟.G₀.U 0, 𝒟.g x = 0 → ∃ y ∈ V, x = (y : P × W 0) + τ y := by
  obtain ⟨𝒮⟩ := 𝒟.exists_sol hC hsurj hpos
  refine ⟨𝒮.Z.prod ⊤, 𝒮.V, 𝒮.τ, 𝒮.hY, ?_, 𝒮.V_relOpen, 𝒮.zero_mem_V, 𝒮.τ_mem_Y, 𝒮.snd_τ_mem_range,
    𝒮.τ_contDiffOn, 𝒮.τ_zero, 𝒮.fderivWithin_τ hC.isQuadrantLike hpos,
    fun _ hy => 𝒮.sol_mem_and_eq_zero hy,
    fun k hk => 𝒮.exists_contDiffOn_level hC hsurj hpos k hk, 𝒮.exists_eq_add_τ hreg⟩
  rw [Submodule.prod_coe, Submodule.top_coe]
  exact 𝒮.Z.closed_of_finiteDimensional.prod isClosed_univ

end ShiftedBasicData

namespace StabilityData

variable (𝒮 : StabilityData Ct W) {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- **Theorem 3.47 with a closed good complement whose projection maps the partial quadrant into
itself**: `theorem_3_47_sc_smooth` with the additional conclusions `IsClosed Y` and
`ProjectsInto (C̃ ⊕ W) K Y`, i.e. the projection onto `K = ker D(f + s)(0)` along
`Y = ψ⁻¹(Z ⊕ W)` maps `C' = C̃ ⊕ W` into `K ∩ C'`.  The complement `Y'` of Theorem 3.43 for the
conjugated germ is that of `theorem_3_43_proj` (chosen with `ProjectsInto`, Finding 132), and
both properties are carried by the linear homeomorphism `ψ⁻¹` of Theorem 3.38, which maps
`(C̃ ⊕ ℝᴺ') ⊕ X` onto `C̃ ⊕ W` (`ProjectsInto.mapL`).  (The proof is that of
`theorem_3_47_sc_smooth` in `LocalSolvability.lean`, with the two properties carried along.) -/
theorem _root_.Polyfold.theorem_3_47_proj (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒮 : StabilityData Ct W) (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))) :
    ∃ (Y : Submodule ℝ (P × W 0))
      (V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y ∧
      IsClosed (Y : Set (P × W 0)) ∧
      ProjectsInto (Ct ×ˢ univ) (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y ∧
      (∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V ∧
      (∀ y, σ y ∈ Y) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
        (∃ O : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
          IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V ∧
        ∃ σk : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd P W) k,
          ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (σk y) = σ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒮.G.U 0, 𝒮.fsum f x = 0 → ∃ y ∈ V, x = (y : P × W 0) + σ y := by
  classical
  have hCq := hC.isQuadrantLike
  set K := LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) with hKdef
  set 𝒟 := 𝒮.toShiftedBasicData hCq hf with h𝒟
  -- the linear coordinate change `S = ψ` on level `0`
  let S : (P × W 0) ≃L[ℝ] 𝒮.E₀' 0 :=
    ContinuousLinearEquiv.equivOfInverse (𝒮.split₀ 0) (𝒮.glue₀ 0) (𝒮.glue₀_split₀ 0)
      (𝒮.split₀_glue₀ 0)
  have hS : ∀ x, S x = 𝒮.split₀ 0 x := fun _ => rfl
  have hS' : ∀ y, S.symm y = 𝒮.glue₀ 0 y := fun _ => rfl
  have hDg : 𝒟.Dg = (𝒮.fiber₀ 0).comp ((𝒮.Dfs f).comp (𝒮.glue₀ 0)) :=
    𝒮.scDerivGerm_pushMap₀ hCq hf.isScSmooth
  have hDg_apply : ∀ y, 𝒟.Dg y = 𝒮.fiber₀ 0 (𝒮.Dfs f (𝒮.glue₀ 0 y)) := fun y => by rw [hDg]; rfl
  -- the kernel
  have hK' : 𝒟.K' = K.map (S : P × W 0 →ₗ[ℝ] 𝒮.E₀' 0) := by
    ext y
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · intro hy
      refine ⟨𝒮.glue₀ 0 y, ?_, 𝒮.split₀_glue₀ 0 y⟩
      rw [LinearMap.mem_ker]
      have : 𝒟.Dg y = 0 := hy
      rw [hDg_apply] at this
      exact (𝒮.fiber₀_eq_zero_iff 0 _).1 this
    · rintro ⟨x, hx, rfl⟩
      change 𝒟.Dg (𝒮.split₀ 0 x) = 0
      rw [hDg_apply, 𝒮.glue₀_split₀]
      have : 𝒮.Dfs f x = 0 := hx
      rw [this, map_zero]
  have hS_mem : ∀ x : P × W 0, x ∈ Ct ×ˢ (univ : Set (W 0)) ↔
      S x ∈ (Ct ×ˢ univ) ×ˢ (univ : Set (𝒮.XB 0)) := fun x => by
    rw [hS, split₀_apply]
    constructor
    · intro h; exact ⟨⟨h.1, mem_univ _⟩, mem_univ _⟩
    · intro h; exact ⟨h.1.1, mem_univ _⟩
  have hS'_mem : ∀ y : 𝒮.E₀' 0, y ∈ (Ct ×ˢ univ) ×ˢ (univ : Set (𝒮.XB 0)) ↔
      S.symm y ∈ Ct ×ˢ (univ : Set (W 0)) := fun y => by
    rw [hS_mem (S.symm y), ContinuousLinearEquiv.apply_symm_apply]
  -- the restricted coordinate changes `K ≃ K'`
  have hSK : ∀ y : K, S y ∈ 𝒟.K' := fun y => by
    rw [hK']; exact ⟨y, y.2, rfl⟩
  have hSK' : ∀ y' : 𝒟.K', S.symm y' ∈ K := fun y' => by
    have hy : (y' : 𝒮.E₀' 0) ∈ K.map (S : P × W 0 →ₗ[ℝ] 𝒮.E₀' 0) := by rw [← hK']; exact y'.2
    obtain ⟨x, hx, hxy⟩ := hy
    have : S.symm y' = x := by rw [← hxy]; exact S.symm_apply_apply x
    rw [this]; exact hx
  have hKmap : 𝒟.K'.map (S.symm : 𝒮.E₀' 0 →ₗ[ℝ] P × W 0) = K := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y', hy', rfl⟩; exact hSK' ⟨y', hy'⟩
    · intro hx; exact ⟨S x, hSK ⟨x, hx⟩, S.symm_apply_apply x⟩
  -- finite dimensionality of the kernels (Lemma 3.44)
  have hC' : IsPartialQuadrant (ScBanach.const (P × 𝒮.Cs)) (Ct ×ˢ (univ : Set 𝒮.Cs)) :=
    hC.const_prod_univ 𝒮.Cs
  have hfinK' : FiniteDimensional ℝ 𝒟.K' := by
    obtain ⟨𝒱⟩ := 𝒟.exists_deriv hC'.isQuadrantLike
    have hker : 𝒟.K' = _ := 𝒱.ker_Dg_eq hC'.isQuadrantLike
    rw [hker]
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (graphMap_injective 𝒱.L) _)
  have hfinK : FiniteDimensional ℝ K := by
    rw [← hKmap]
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ S.symm.injective _)
  have hpos' : IsInGoodPosition 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) 𝒟.K' := by
    rw [hK']; exact hpos.map S hS_mem
  have hsurj' : Surjective 𝒟.Dg := by
    intro z
    obtain ⟨x, hx⟩ := hsurj (𝒮.fiberInv₀ 0 z)
    refine ⟨𝒮.split₀ 0 x, ?_⟩
    rw [hDg_apply, 𝒮.glue₀_split₀, hx, 𝒮.fiber₀_fiberInv₀]
  obtain ⟨Y', V', τ, hY', hY'c, hY'p, hV'rel, hV'0, hτY, hτ1, hτC, hτ0, hDτ, hsol, hlev, U'', hU''o,
    hU''0, hU''⟩ := theorem_3_43_proj hC' 𝒟 hsurj' hpos' (𝒮.lemma_3_42 hC hf)
  let SK : K →L[ℝ] 𝒟.K' :=
    { toFun := fun y => ⟨S y, hSK y⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
      cont := (S.continuous.comp continuous_subtype_val).subtype_mk _ }
  have hSK_apply : ∀ y : K, ((SK y : 𝒟.K') : 𝒮.E₀' 0) = S y := fun _ => rfl
  let GK : 𝒟.K' → K := fun y' => ⟨S.symm y', hSK' y'⟩
  have hSK_GK : ∀ y', SK (GK y') = y' := fun y' => Subtype.ext (S.apply_symm_apply _)
  -- the complement, the neighbourhood and the map
  refine ⟨Y'.map (S.symm : 𝒮.E₀' 0 →ₗ[ℝ] P × W 0), SK ⁻¹' V', fun y => S.symm (τ (SK y)),
    ?_, ?_, ?_, ?_, ?_, fun y => ⟨τ (SK y), hτY _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Y` is a good complement of `K` (Lemma 3.45 for the linear `ψ⁻¹`)
    have h := hY'.map (E' := ScBanach.paramProd P W) (C' := Ct ×ˢ univ) S.symm hS'_mem
    rwa [hKmap] at h
  · -- `Y` is closed: the image of the closed `Y'` under the linear homeomorphism `ψ⁻¹`
    rw [Submodule.map_coe]
    exact S.symm.toHomeomorph.isClosed_image.2 hY'c
  · -- the projection along `Y` maps `C̃ ⊕ W` into itself: transported by the linear `ψ⁻¹`,
    -- which carries `(C̃ ⊕ ℝᴺ') ⊕ X` onto `C̃ ⊕ W`
    have h := hY'p.mapL S.symm hS'_mem
    rwa [hKmap] at h
  · obtain ⟨O', hO', hV'⟩ := hV'rel
    refine ⟨SK ⁻¹' O', hO'.preimage SK.continuous, ?_⟩
    ext y
    simp only [mem_preimage, hV', mem_inter_iff, hSK_apply]
    rw [hS_mem]
  · show SK 0 ∈ V'
    rw [map_zero]; exact hV'0
  · -- the values lie on level `1`
    intro y
    obtain ⟨w₁, hw₁⟩ := hτ1 (SK y)
    have hc : ((τ (SK y)).1.2 : W 0) ∈ W.smooth := 𝒮.Cs_le_smooth (τ (SK y)).1.2.2
    obtain ⟨c₁, hc₁⟩ := (ScScale.mem_smooth_iff _).1 hc 1
    refine ⟨c₁ + w₁.val, ?_⟩
    show W.toBase 1 (c₁ + w₁.val) = (S.symm (τ (SK y))).2
    rw [map_add, hc₁, hS', glue₀_apply]
    change _ = 𝒮.liftC 0 (τ (SK y)).1.2 + (τ (SK y)).2.val
    rw [ScBanach.finLift_zero_apply, ← hw₁]
    congr 1
  · exact S.symm.contDiff.comp_contDiffOn (hτC.comp SK.contDiff.contDiffOn fun _ hy => hy)
  · show S.symm (τ (SK 0)) = 0
    rw [map_zero, hτ0, map_zero]
  · -- `Dσ(0) = 0`
    have hτd : HasFDerivWithinAt τ (0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0) V' 0 := by
      have := (hτC.differentiableOn one_ne_zero 0 hV'0).hasFDerivWithinAt
      rwa [hDτ] at this
    have hSK0 : SK 0 = 0 := map_zero _
    have hτd' : HasFDerivWithinAt τ (0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0) V' (SK 0) := by rw [hSK0]; exact hτd
    have h1 := hτd'.comp (0 : K) SK.hasFDerivWithinAt fun _ hy => hy
    have h2 := (S.symm : 𝒮.E₀' 0 →L[ℝ] P × W 0).hasFDerivAt.comp_hasFDerivWithinAt (0 : K) h1
    have huniq : UniqueDiffWithinAt ℝ (SK ⁻¹' V') (0 : K) := by
      obtain ⟨O', hO', hV'⟩ := hV'rel
      have hV : SK ⁻¹' V' = (SK ⁻¹' O') ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
        ext y
        simp only [mem_preimage, hV', mem_inter_iff, hSK_apply]
        rw [hS_mem]
      have h0 : (0 : K) ∈ SK ⁻¹' V' := by show SK 0 ∈ V'; rw [hSK0]; exact hV'0
      rw [hV] at h0 ⊢
      have hconv : Convex ℝ (Subtype.val ⁻¹' (Ct ×ˢ univ) : Set K) := by
        have hC'' : Convex ℝ (Ct ×ˢ (univ : Set (W 0))) := by
          have := hCq.convex 0
          rw [ScBanach.const_lvlSet] at this
          exact this.prod convex_univ
        exact hC''.linear_preimage K.subtype
      rw [inter_comm]
      exact (uniqueDiffWithinAt_convex hconv hpos.interior_nonempty (subset_closure h0.2)).inter
        ((hO'.preimage SK.continuous).mem_nhds h0.1)
    have h3 : HasFDerivWithinAt (fun y : K => S.symm (τ (SK y)))
        ((S.symm : 𝒮.E₀' 0 →L[ℝ] P × W 0).comp ((0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0).comp SK))
        (SK ⁻¹' V') 0 := h2
    rw [h3.fderivWithin huniq, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  · -- `y + σ(y)` is a zero
    intro y hy
    obtain ⟨hmem, hzero⟩ := hsol (SK y) hy
    have heq : (y : P × W 0) + S.symm (τ (SK y)) = 𝒮.glue₀ 0 ((SK y : 𝒮.E₀' 0) + τ (SK y)) := by
      rw [← hS', map_add, hSK_apply, S.symm_apply_apply]
    rw [heq]
    refine ⟨hmem, ?_⟩
    have : 𝒮.fiber₀ 0 (𝒮.fsum f (𝒮.glue₀ 0 ((SK y : 𝒮.E₀' 0) + τ (SK y)))) = 0 := hzero
    exact (𝒮.fiber₀_eq_zero_iff 0 _).1 this
  · -- the regularity on all levels, transported by the linear `ψ⁻¹`
    intro k hk
    obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, hVk0, hVkV, τk, hτkC, hτk⟩ := hlev k hk
    refine ⟨SK ⁻¹' Vk, ⟨SK ⁻¹' Ok, hOk.preimage SK.continuous, ?_⟩, ?_, fun y hy => hVkV hy,
      fun y => 𝒮.glue₀ k (τk (SK y)),
      (𝒮.glue₀ k).contDiff.comp_contDiffOn (hτkC.comp SK.contDiff.contDiffOn fun _ hy => hy),
      fun y hy => ?_⟩
    · ext y
      simp only [mem_preimage, hVk, mem_inter_iff, hSK_apply]
      rw [hS_mem]
    · show SK 0 ∈ Vk
      rw [map_zero]; exact hVk0
    · show (ScBanach.paramProd P W).toBase k (𝒮.glue₀ k (τk (SK y))) = S.symm (τ (SK y))
      rw [𝒮.glue₀.toBase_comm, hτk _ hy, hS']
  · -- every zero near `0` is of this form
    refine ⟨S ⁻¹' U'', hU''o.preimage S.continuous, by rw [mem_preimage, map_zero]; exact hU''0, ?_⟩
    rintro x ⟨hxU, hxG⟩ hx0
    have hSxG : S x ∈ 𝒮.pushGerm₀.U 0 := by
      rw [mem_pushGerm₀_U, ← hS', S.symm_apply_apply]; exact hxG
    have hSx0 : 𝒮.pushMap₀ f (S x) = 0 := by
      change 𝒮.fiber₀ 0 (𝒮.fsum f (𝒮.glue₀ 0 (S x))) = 0
      rw [← hS', S.symm_apply_apply, hx0, map_zero]
    obtain ⟨y', hy', hxy'⟩ := hU'' (S x) ⟨hxU, hSxG⟩ hSx0
    refine ⟨GK y', by show SK (GK y') ∈ V'; rw [hSK_GK]; exact hy', ?_⟩
    change x = (GK y' : P × W 0) + S.symm (τ (SK (GK y')))
    rw [hSK_GK]
    change x = S.symm y' + S.symm (τ y')
    rw [← map_add, ← hxy', S.symm_apply_apply]

/-- **Theorem 3.47 with the closedness of the good complement recorded**: `theorem_3_47_sc_smooth`
with the additional conclusion `IsClosed Y`, `Y = ψ⁻¹(Z ⊕ W)` the image of a closed subspace under
the linear homeomorphism `ψ⁻¹` of Theorem 3.38.  (A corollary of `theorem_3_47_proj`.) -/
theorem _root_.Polyfold.theorem_3_47_closed (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒮 : StabilityData Ct W) (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))) :
    ∃ (Y : Submodule ℝ (P × W 0))
      (V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y ∧
      IsClosed (Y : Set (P × W 0)) ∧
      (∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V ∧
      (∀ y, σ y ∈ Y) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
        (∃ O : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
          IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V ∧
        ∃ σk : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd P W) k,
          ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (σk y) = σ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒮.G.U 0, 𝒮.fsum f x = 0 → ∃ y ∈ V, x = (y : P × W 0) + σ y := by
  obtain ⟨Y, V, σ, h1, h2, -, h3⟩ := theorem_3_47_proj hC 𝒮 hf hsurj hpos
  exact ⟨Y, V, σ, h1, h2, h3⟩

end StabilityData

end Polyfold
