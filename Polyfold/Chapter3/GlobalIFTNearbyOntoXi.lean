import Polyfold.Chapter3.GlobalIFTNearbyOntoCurve
import Polyfold.Chapter3.GlobalIFTNearbyKernel

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1), the surjectivity of `f'(y)` at the nearby zeros: the perturbation family in
the normalized coordinates (Lemma 2 of the argument).**

# The perturbation `Ξ(u', λ) = Θ(θ⁻¹u', ρ(r(θ⁻¹u'))λ)` and its bounds

## The text, paraphrased

Nothing in the text (the repair of the gap of Finding 100, see `GlobalIFTNearbyOntoLemmas.lean`).
The perturbed section `g + μ ρ(r(·)) λ` of the chart at `x₀` is transported to the normal form of
Theorem 3.38 by the strong bundle isomorphism `Θ = Λ ∘ Ψ` (`Ψ` the conjugation of Definition
3.11, `Λ = (split, fiber)` the linear change of Theorem 3.38): its push-forward is `G + μ ê_λ`
with `ê_λ(u') = Γ_Θ(θ⁻¹u') ρ(r(θ⁻¹u')) λ`.

## What is formalized

* `Polyfold.xiMap`: the joint map `Ξ(y, κ) = fiber(Ψ[1](ψ⁻¹(glue y), (R[1](r(ψ⁻¹(glue y)), κ))_F))_F'`
  on `ψ(U) ⊕ F¹`, with values in the index-raised target; `xiMap_isScSmooth`: it is sc-smooth
  (a composition of the strong bundle maps `R[1]`, `Ψ[1]` with sc-smooth maps); `xiMap_smul`,
  `levelMap_xiMap_smul`: it is linear in `κ` on every level.
* `Polyfold.ehat`: `ê_λ(y) = Ξ(y, λ₁)` for a smooth `λ` with level-`1` representative `λ₁`;
  `ehat_isScSmoothGerm`: an sc⁺-perturbation on the germ `ψ(U)` of Theorem 3.38
  (`isScSmooth_const_of_smooth`: constant maps with a smooth value are sc-smooth).
* `Polyfold.exists_xi_bounds` (**Lemma 2**): for every level `m` there are a radius `δ_m > 0` and
  a constant `M_m` such that on `{‖a‖ < δ_m} × {‖w‖_{m+1} < δ_m} × {‖κ‖_{m+2} < δ_m}` the level map
  `Ξ_m` is bounded by `1` and `M_m`-Lipschitz in `w` (Proposition 1.18 and the continuity of `Ξ_m`
  and of its derivative at `0`).
* `Polyfold.exists_xi_radii_bounds`: the bounds `c_m(λ) = (2|λ|_{m+2}/δ_m) max(1, M_m)` of
  `(ê_λ)_W` on the λ-independent regions `{‖a‖ < ν_m} × {‖w‖ < ρ_m}` with `ν_m, ρ_m ≤ δ_m`, by
  the scaling `Ξ_m(y, κ) = (2|κ|/δ_m) Ξ_m(y, (δ_m/2|κ|) κ)`.

## What the text leaves implicit, and the choices made (the findings)

Finding 183: the bounds are uniform in `λ` on fixed neighbourhoods because `Ξ` is sc-smooth
jointly in `(u', λ)` and linear in `λ`; this is where the index raise of Theorem 3.38 is used
(`Ξ` is `C¹` from level `m+1` to level `m+1`, i.e. from shifted level `m` to shifted level `m`).
-/

open Set Filter Topology Function Module ContinuousLinearMap Metric

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-! ### Constant maps with a smooth value -/

/-- A constant map with a smooth value `k₁ ∈ F¹` (i.e. `ι k₁ ∈ F_∞`) is sc-smooth into `F¹`. -/
theorem isScSmooth_const_of_smooth {G : ScBanach} {V : Set (G 0)} (hV : IsScDomain G V)
    {k₁ : F 1} (hk : F.toBase 1 k₁ ∈ F.smooth) :
    IsScSmooth (E := G) (F := F.shift) V (fun _ => k₁) := by
  refine IsScSmooth.of_contDiffOn_levels hV (fun m _ _ => ?_) fun m => ?_
  · obtain ⟨y, hy⟩ := F.mem_smooth_iff.1 hk (m + 1)
    refine ⟨y, F.toBase_injective 1 ?_⟩
    rw [← F.shift_toBase, hy]
  · obtain ⟨y, hy⟩ := F.mem_smooth_iff.1 hk (m + 1)
    have hy' : F.shift.toBase m y = k₁ := F.toBase_injective 1 (by rw [← F.shift_toBase, hy])
    have : ∀ x ∈ G.lvlSet V m, levelMap (E := G) (F := F.shift) (fun _ => k₁) m x = y :=
      fun x _ => levelMap_eq_of_toBase_eq hy'
    exact (contDiffOn_const).congr this

/-! ### The joint perturbation map `Ξ` -/

section Xi

variable {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {W : ScBanach} {Ct : Set Pn} {U' : Set ((ScBanach.paramProd Pn W) 0)}
  {Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0}
  {Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0}

open StrongRetr

/-- **The joint perturbation map** `Ξ(y, κ) = fiber(Ψ[1](ψ⁻¹(glue y), (R[1](r(ψ⁻¹(glue y)), κ))_F))_F'`
on `ψ(U) ⊕ F¹`, with values in the index-raised normalized target. -/
def xiMap (𝒮 : StabilityData Ct W)
    (Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0)
    (Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0)
    (R : E 0 × F 0 → E 0 × F 0) : (𝒮.E₀'.prod F.shift) 0 → 𝒮.F' Q 0 :=
  fun p => 𝒮.fiber 0 (shiftFiber Ψ (IsStrongBundleMap.base Ψ' (𝒮.glue₀ 0 p.1),
    (shiftFiber R (r R (IsStrongBundleMap.base Ψ' (𝒮.glue₀ 0 p.1)), p.2)).2)).2

/-- The domain `ψ(U) ⊕ F¹` of `Ξ`. -/
def xiDom (𝒮 : StabilityData Ct W) (U' : Set ((ScBanach.paramProd Pn W) 0)) (F : ScBanach) :
    Set ((𝒮.E₀'.prod F.shift) 0) := (𝒮.glue₀ 0 ⁻¹' U') ×ˢ (univ : Set (F 1))

variable {𝒮 : StabilityData Ct W}

lemma mem_xiDom {p : (𝒮.E₀'.prod F.shift) 0} : p ∈ xiDom 𝒮 U' F ↔ 𝒮.glue₀ 0 p.1 ∈ U' := by
  simp [xiDom]

/-- `ψ(U) = glue⁻¹(U')` is relatively open in `(C̃ ⊕ C) ⊕ X`. -/
theorem glue₀_preimage_relOpen (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U') :
    IsRelOpenInQuadrant 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) (𝒮.glue₀ 0 ⁻¹' U') := by
  refine ⟨(hCt.const_prod_univ 𝒮.Cs).prod_univ 𝒮.XB, ?_⟩
  obtain ⟨O, hO, hU'O⟩ := hU'.relOpen
  refine ⟨𝒮.glue₀ 0 ⁻¹' O, hO.preimage (𝒮.glue₀ 0).continuous, ?_⟩
  ext y
  rw [hU'O, mem_preimage, mem_inter_iff, mem_inter_iff, mem_preimage, StabilityData.glue₀_apply]
  simp [mem_prod]

theorem xiDom_relOpen (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U') :
    IsRelOpenInQuadrant (𝒮.E₀'.prod F.shift) (((Ct ×ˢ univ) ×ˢ univ) ×ˢ univ)
      (xiDom 𝒮 U' F) :=
  (glue₀_preimage_relOpen (𝒮 := 𝒮) hCt hU').prod_univ F.shift

/-- **`Ξ` is sc-smooth** on `ψ(U) ⊕ F¹`: the composition of the linear `glue`, `ψ⁻¹ × 1`,
`(u, κ) ↦ (u, (R[1](r(u), κ))_F)`, `Ψ[1]`, the projection and the linear `fiber`. -/
theorem xiMap_isScSmooth (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') :
    IsScSmooth (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiDom 𝒮 U' F)
      (xiMap 𝒮 Ψ Ψ' R) := by
  have hD := (xiDom_relOpen (𝒮 := 𝒮) (F := F) hCt hU').isScDomain
  have hU'F := (hU'.prod_univ F.shift).isScDomain
  have hUF := (hU.prod_univ F.shift).isScDomain
  have hψ'sc : IsScSmooth U' (IsStrongBundleMap.base Ψ') := hΨ.invFun.base_isScSmooth hU'
  have hrsc : IsScSmooth U (r R) := hR.toIsStrongBundleMap.base_isScSmooth hU
  -- `S₁ = glue × 1`
  have hS₁ : IsScSmooth (E := 𝒮.E₀'.prod F.shift) (F := (ScBanach.paramProd Pn W).prod F.shift)
      (xiDom 𝒮 U' F) ((𝒮.glue₀.prodMap (ScOperator.id F.shift)) 0) :=
    (𝒮.glue₀.prodMap (ScOperator.id F.shift)).isScSmooth hD
  have hS₁m : MapsTo ((𝒮.glue₀.prodMap (ScOperator.id F.shift)) 0) (xiDom 𝒮 U' F)
      (U' ×ˢ univ) := fun p hp => ⟨(mem_xiDom.1 hp), mem_univ _⟩
  -- `S₂ = ψ⁻¹ × 1`
  have hS₂ : IsScSmooth (E := (ScBanach.paramProd Pn W).prod F.shift) (F := E.prod F.shift)
      (U' ×ˢ univ) (Prod.map (IsStrongBundleMap.base Ψ') id) :=
    IsScSmooth.prodMap hU'.isScDomain (isScDomain_univ F.shift) hU'F hψ'sc
      (isScSmooth_id (isScDomain_univ F.shift))
  have hS₂m : MapsTo (Prod.map (IsStrongBundleMap.base Ψ') id) (U' ×ˢ (univ : Set (F 1)))
      (U ×ˢ univ) := fun p hp => ⟨hΨ.invFun.base_mem hp.1, mem_univ _⟩
  -- `S₃ = (u, κ) ↦ (u, (R[1](r u, κ))_F)`
  have hr1 : IsScSmooth (E := E.prod F.shift) (F := E.prod F.shift) (U ×ˢ univ)
      (Prod.map (r R) id) :=
    IsScSmooth.prodMap hU.isScDomain (isScDomain_univ F.shift) hUF hrsc
      (isScSmooth_id (isScDomain_univ F.shift))
  have hr1m : MapsTo (Prod.map (r R) id) (U ×ˢ (univ : Set (F 1))) (U ×ˢ univ) :=
    fun p hp => ⟨r_mem hR hp.1, mem_univ _⟩
  have hS₃' : IsScSmooth (E := E.prod F.shift) (F := F.shift) (U ×ˢ univ)
      (ScBanach.prodSndOp E F.shift 0 ∘ (shiftFiber R ∘ Prod.map (r R) id)) :=
    IsScSmooth.comp hUF (isScDomain_univ _) ((ScBanach.prodSndOp E F.shift).isScSmooth
      (isScDomain_univ _)) (IsScSmooth.comp hUF hUF hR.isScSmooth_one hr1 hr1m) (mapsTo_univ _ _)
  have hS₃ : IsScSmooth (E := E.prod F.shift) (F := E.prod F.shift) (U ×ˢ univ)
      (scPair (F := E) (G := F.shift) (ScBanach.prodFstOp E F.shift 0)
        (ScBanach.prodSndOp E F.shift 0 ∘ (shiftFiber R ∘ Prod.map (r R) id))) :=
    IsScSmooth.scPair hUF ((ScBanach.prodFstOp E F.shift).isScSmooth hUF) hS₃'
  have hS₃m : MapsTo (scPair (F := E) (G := F.shift) (ScBanach.prodFstOp E F.shift 0)
      (ScBanach.prodSndOp E F.shift 0 ∘ (shiftFiber R ∘ Prod.map (r R) id)))
      (U ×ˢ (univ : Set (F 1))) (U ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
  -- `S₄ = Ψ[1]`, `S₅ = fiber ∘ pr₂`
  have hS₄ := hΨ.toFun.isScSmooth_one
  have hS₄m : MapsTo (shiftFiber Ψ) (U ×ˢ (univ : Set (F 1))) (U' ×ˢ univ) := fun p hp =>
    ⟨by
      have := hΨ.toFun.base_mem hp.1
      rwa [IsStrongBundleMap.base, ← hΨ.toFun.fst_independent _ hp.1 (F.toBase 1 p.2) 0] at this,
      mem_univ _⟩
  have hU'F' := (hU'.prod_univ (ScBanach.paramProd Q W).shift).isScDomain
  have hS₅ : IsScSmooth (E := (ScBanach.paramProd Pn W).prod (ScBanach.paramProd Q W).shift)
      (F := 𝒮.F' Q) (U' ×ˢ univ)
      (𝒮.fiber 0 ∘ ScBanach.prodSndOp (ScBanach.paramProd Pn W) (ScBanach.paramProd Q W).shift 0) :=
    IsScSmooth.comp hU'F' (isScDomain_univ _) (𝒮.fiber.isScSmooth (isScDomain_univ _))
      ((ScBanach.prodSndOp _ _).isScSmooth hU'F') (mapsTo_univ _ _)
  have h₁ := IsScSmooth.comp hD hU'F hS₂ hS₁ hS₁m
  have h₁m := hS₂m.comp hS₁m
  have h₂ := IsScSmooth.comp hD hUF hS₃ h₁ h₁m
  have h₂m := hS₃m.comp h₁m
  have h₃ := IsScSmooth.comp hD hUF hS₄ h₂ h₂m
  have h₃m := hS₄m.comp h₂m
  have h := IsScSmooth.comp hD hU'F' hS₅ h₃ h₃m
  exact h.congr hD fun _ _ => rfl

/-- `Ξ` is linear in `κ`: `Ξ(y, sκ) = sΞ(y, κ)` for `y ∈ ψ(U)`. -/
theorem xiMap_smul (hR : IsStrongBundleRetraction U R) (hΨ : IsStrongBundleIso U U' Ψ Ψ')
    {y : 𝒮.E₀' 0} (hy : 𝒮.glue₀ 0 y ∈ U') (s : ℝ) (κ : F 1) :
    xiMap 𝒮 Ψ Ψ' R (y, s • κ) = s • xiMap 𝒮 Ψ Ψ' R (y, κ) := by
  set u := IsStrongBundleMap.base Ψ' (𝒮.glue₀ 0 y) with hu
  have huU : u ∈ U := hΨ.invFun.base_mem hy
  have hru : r R u ∈ U := r_mem hR huU
  -- `(R[1](r u, sκ))_F = s (R[1](r u, κ))_F`
  have h1 : (shiftFiber R (r R u, s • κ)).2 = s • (shiftFiber R (r R u, κ)).2 := by
    apply F.toBase_injective 1
    rw [map_smul, hR.toBase_shiftFiber_snd (p := (r R u, s • κ)) hru,
      hR.toBase_shiftFiber_snd (p := (r R u, κ)) hru, map_smul]
    exact (hR.fiber_linear _ hru).map_smul s _
  -- `(Ψ[1](u, sκ'))_F' = s (Ψ[1](u, κ'))_F'`
  have h2 : ∀ κ' : F 1, (shiftFiber Ψ (u, s • κ')).2 = s • (shiftFiber Ψ (u, κ')).2 := by
    intro κ'
    apply (ScBanach.paramProd Q W).toBase_injective 1
    rw [map_smul, hΨ.toFun.toBase_shiftFiber_snd (p := (u, s • κ')) huU,
      hΨ.toFun.toBase_shiftFiber_snd (p := (u, κ')) huU, map_smul]
    exact (hΨ.toFun.fiber_linear _ huU).map_smul s _
  simp only [xiMap]
  rw [← hu, h1, h2, map_smul]

/-- `Ξ(y, 0) = 0` for `y ∈ ψ(U)`. -/
theorem xiMap_zero (hR : IsStrongBundleRetraction U R) (hΨ : IsStrongBundleIso U U' Ψ Ψ')
    {y : 𝒮.E₀' 0} (hy : 𝒮.glue₀ 0 y ∈ U') : xiMap 𝒮 Ψ Ψ' R (y, 0) = 0 := by
  have := xiMap_smul (𝒮 := 𝒮) hR hΨ hy 0 0
  rwa [zero_smul, zero_smul] at this

/-- The level maps of `Ξ` are linear in `κ`. -/
theorem levelMap_xiMap_smul (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') {m : ℕ} {y : 𝒮.E₀' m} {κ : F (m + 1)}
    (hp : ((y, κ) : (𝒮.E₀'.prod F.shift) m) ∈
      (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) m) (s : ℝ) :
    levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m (y, s • κ) =
      s • levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m (y, κ) := by
  have hsc := (xiMap_isScSmooth (𝒮 := 𝒮) hU hR hCt hU' hΨ).isSc1.isSc0
  have hy : 𝒮.glue₀ 0 (𝒮.E₀'.toBase m y) ∈ U' := by
    have := hp
    rw [ScBanach.mem_lvlSet, mem_xiDom, ScBanach.prod_toBase] at this
    exact this
  apply levelMap_eq_of_toBase_eq
  rw [map_smul, hsc.toBase_levelMap hp, ScBanach.prod_toBase 𝒮.E₀' F.shift m (y, κ),
    ScBanach.prod_toBase 𝒮.E₀' F.shift m (y, s • κ), map_smul]
  exact (xiMap_smul (𝒮 := 𝒮) hR hΨ hy s _).symm

/-! ### The perturbation `ê_λ` -/

/-- `ê_λ(y) = Ξ(y, λ₁)`, the push-forward of `u ↦ ρ(r(u)) λ` to the normalized coordinates, for
the level-`1` representative `λ₁` of a smooth `λ`. -/
def ehat (𝒮 : StabilityData Ct W)
    (Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0)
    (Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0)
    (R : E 0 × F 0 → E 0 × F 0) (k₁ : F 1) : 𝒮.E₀' 0 → 𝒮.F' Q 0 :=
  fun y => xiMap 𝒮 Ψ Ψ' R (y, k₁)

/-- **`ê_λ` is sc-smooth into the index-raised target** on `ψ(U)`. -/
theorem ehat_isScSmooth (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') {k₁ : F 1} (hk : F.toBase 1 k₁ ∈ F.smooth) :
    IsScSmooth (E := 𝒮.E₀') (F := 𝒮.F' Q) (𝒮.glue₀ 0 ⁻¹' U') (ehat 𝒮 Ψ Ψ' R k₁) := by
  have hD := (glue₀_preimage_relOpen (𝒮 := 𝒮) hCt hU').isScDomain
  have hpair : IsScSmooth (E := 𝒮.E₀') (F := 𝒮.E₀'.prod F.shift) (𝒮.glue₀ 0 ⁻¹' U')
      (scPair (F := 𝒮.E₀') (G := F.shift) id (fun _ => k₁)) :=
    IsScSmooth.scPair hD (isScSmooth_id hD) (isScSmooth_const_of_smooth hD hk)
  have hmaps : MapsTo (scPair (F := 𝒮.E₀') (G := F.shift) id (fun _ => k₁)) (𝒮.glue₀ 0 ⁻¹' U')
      (xiDom 𝒮 U' F) := fun y hy => by rw [mem_xiDom]; exact hy
  have := IsScSmooth.comp hD (xiDom_relOpen (𝒮 := 𝒮) (F := F) hCt hU').isScDomain
    (xiMap_isScSmooth (𝒮 := 𝒮) hU hR hCt hU' hΨ) hpair hmaps
  exact this.congr hD fun _ _ => rfl

/-- `ψ(U)_m ⊇ U⁰_m`: the germ of Theorem 3.38 lies in `glue⁻¹(U')`. -/
lemma pushGerm₀_U_subset (hG : 𝒮.G.U 0 ⊆ U') (m : ℕ) :
    𝒮.pushGerm₀.U m ⊆ 𝒮.E₀'.lvlSet (𝒮.glue₀ 0 ⁻¹' U') m := by
  intro y hy
  rw [StabilityData.mem_pushGerm₀_U] at hy
  rw [ScBanach.mem_lvlSet, mem_preimage, ← 𝒮.glue₀.toBase_comm]
  exact hG (𝒮.G.toBase_mem hy)

/-- **`ê_λ` is an sc⁺-perturbation on the germ `ψ(U)` of Theorem 3.38.** -/
theorem ehat_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (h0U : (0 : E 0) ∈ U)
    (hG : 𝒮.G.U 0 ⊆ U') {k₁ : F 1} (hk : F.toBase 1 k₁ ∈ F.smooth) :
    IsScSmoothGerm (E := 𝒮.E₀') (F := 𝒮.F' Q) 𝒮.pushGerm₀ (ehat 𝒮 Ψ Ψ' R k₁) := by
  have hE' : IsQuadrantLike 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) :=
    (glue₀_preimage_relOpen (𝒮 := 𝒮) hCt hU').isPartialQuadrant.isQuadrantLike
  have hrel := (glue₀_preimage_relOpen (𝒮 := 𝒮) hCt hU').relOpen
  have h0 : (0 : 𝒮.E₀' 0) ∈ 𝒮.glue₀ 0 ⁻¹' U' := by
    rw [mem_preimage, map_zero, ← hψ0]; exact hΨ.toFun.base_mem h0U
  have h1 := (ehat_isScSmooth (𝒮 := 𝒮) hU hR hCt hU' hΨ hk).isScSmoothGerm hE' hrel h0
  exact h1.mono hE' fun m => by rw [ScNbhdGerm.ofSet_U]; exact pushGerm₀_U_subset hG m

/-- The level maps of `ê_λ`: `(ê_λ)_m(y) = Ξ_m(y, λ_{m+1})` for a lift `λ_{m+1}` of `λ₁`. -/
theorem levelMap_ehat (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') {k₁ : F 1} {m : ℕ} {y : 𝒮.E₀' m}
    (hy : y ∈ 𝒮.E₀'.lvlSet (𝒮.glue₀ 0 ⁻¹' U') m) {κ : F (m + 1)} (hκ : F.shift.toBase m κ = k₁) :
    levelMap (E := 𝒮.E₀') (F := 𝒮.F' Q) (ehat 𝒮 Ψ Ψ' R k₁) m y =
      levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m (y, κ) := by
  have hsc := (xiMap_isScSmooth (𝒮 := 𝒮) hU hR hCt hU' hΨ).isSc1.isSc0
  have hp : ((y, κ) : (𝒮.E₀'.prod F.shift) m) ∈
      (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) m := by
    rw [ScBanach.mem_lvlSet, mem_xiDom, ScBanach.prod_toBase]
    exact hy
  apply levelMap_eq_of_toBase_eq
  rw [hsc.toBase_levelMap hp, ScBanach.prod_toBase 𝒮.E₀' F.shift m (y, κ), hκ]
  rfl

/-! ### The bounds (Lemma 2) -/

/-- **Lemma 2, the uniform bounds of `Ξ` on a level**: for every `m` there are `δ > 0` and
`M ≥ 0` such that, for `‖a‖ < δ`, `‖κ‖_{m+2} < δ` and a convex set `S` of `w ∈ X_{m+1}` with
`‖w‖ < δ` on `S` whose points `((a, w), κ)` lie in the level-`(m+1)` domain of `Ξ`, the level
map `Ξ_m = Ξ_m ∘ ι` satisfies `‖Ξ_m((a, w), κ)‖ ≤ 1` and
`‖Ξ_m((a, w), κ) − Ξ_m((a, w'), κ)‖ ≤ M ‖w − w'‖` on `S`.  (Continuity of `Ξ_m` and of its
derivative at `0` — Proposition 1.18 — and the mean value inequality.) -/
theorem exists_xi_bounds (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (h0U : (0 : E 0) ∈ U)
    (m : ℕ) :
    ∃ δ > 0, ∃ M ≥ 0, ∀ (a : Pn × 𝒮.Cs) (κ : F (m + 2)) (S : Set (𝒮.XB (m + 1))), Convex ℝ S →
      ‖a‖ < δ → ‖κ‖ < δ →
      (∀ w ∈ S, ‖w‖ < δ ∧ (((a, w), κ) : (𝒮.E₀'.prod F.shift) (m + 1)) ∈
        (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) (m + 1)) →
      (∀ w ∈ S, ‖levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
        ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), κ))‖ ≤ 1) ∧
      ∀ w ∈ S, ∀ w' ∈ S,
        ‖levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), κ)) -
          levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w'), κ))‖ ≤ M * ‖w - w'‖ := by
  classical
  set Dm := (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) (m + 1) with hDm
  set Ξm : (𝒮.E₀'.prod F.shift) (m + 1) → 𝒮.F' Q m :=
    levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m ∘
      (𝒮.E₀'.prod F.shift).inclK m 1 with hΞm
  have hD := (xiDom_relOpen (𝒮 := 𝒮) (F := F) hCt hU').isScDomain
  have hsc := xiMap_isScSmooth (𝒮 := 𝒮) hU hR hCt hU' hΨ
  have hC1 : ContDiffOn ℝ 1 Ξm Dm := hsc.contDiffOn_levels hD m 1
  have hUD : UniqueDiffOn ℝ Dm := fun p hp => hD.uniqueDiffWithinAt (m + 1) p hp
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := by
    rw [← hψ0]; exact hΨ.toFun.base_mem h0U
  have h0D : (0 : (𝒮.E₀'.prod F.shift) (m + 1)) ∈ Dm := by
    rw [hDm, ScBanach.mem_lvlSet, map_zero, mem_xiDom]
    change 𝒮.glue₀ 0 (0 : 𝒮.E₀' 0) ∈ U'
    rw [map_zero]; exact h0U'
  -- `Ξ_m(0) = 0`
  have hΞ0 : Ξm 0 = 0 := by
    apply (𝒮.F' Q).toBase_injective m
    rw [map_zero]
    have hmem : (𝒮.E₀'.prod F.shift).inclK m 1 (0 : (𝒮.E₀'.prod F.shift) (m + 1)) ∈
        (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) m := by
      rw [map_zero, ScBanach.mem_lvlSet, map_zero, mem_xiDom]
      change 𝒮.glue₀ 0 (0 : 𝒮.E₀' 0) ∈ U'
      rw [map_zero]; exact h0U'
    have h2 := hsc.isSc1.isSc0.toBase_levelMap hmem
    simp only [hΞm, Function.comp_apply]
    rw [h2, map_zero, map_zero]
    have h0' : (0 : (𝒮.E₀'.prod F.shift) 0) = ((0 : 𝒮.E₀' 0), (0 : F 1)) := rfl
    rw [h0']
    exact xiMap_zero (𝒮 := 𝒮) hR hΨ (by rw [map_zero]; exact h0U')
  -- continuity of `Ξ_m` and of its derivative at `0`
  have hcont := (hC1.continuousOn 0 h0D)
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hcont 1 one_pos
  have hdcont := (hC1.continuousOn_fderivWithin hUD le_rfl) 0 h0D
  rw [Metric.continuousWithinAt_iff] at hdcont
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hdcont 1 one_pos
  set M : ℝ := ‖fderivWithin ℝ Ξm Dm 0‖ + 1 with hM
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, M, by positivity, fun a κ S hS ha hκ hSw => ?_⟩
  have hnorm : ∀ w : 𝒮.XB (m + 1), ‖w‖ < min δ₁ δ₂ →
      ‖(((a, w), κ) : (𝒮.E₀'.prod F.shift) (m + 1))‖ < min δ₁ δ₂ := by
    intro w hw
    rw [Prod.norm_def, Prod.norm_def]
    exact max_lt (max_lt ha hw) hκ
  refine ⟨fun w hw => ?_, fun w hw w' hw' => ?_⟩
  · have hmem := (hSw w hw).2
    have h1 := hδ₁' hmem (by rw [dist_zero_right]; exact (hnorm w (hSw w hw).1).trans_le (min_le_left _ _))
    rw [hΞ0, dist_zero_right] at h1
    exact h1.le
  · -- the mean value inequality on `S` for `w ↦ Ξ_m((a, w), κ)`
    have hdiff : ∀ w ∈ S, HasFDerivWithinAt (fun w => Ξm ((a, w), κ))
        ((fderivWithin ℝ Ξm Dm ((a, w), κ)).comp
          ((ContinuousLinearMap.inl (𝒮.E₀' (m + 1)) (F (m + 2)) (R := ℝ)).comp
            (ContinuousLinearMap.inr ℝ (Pn × 𝒮.Cs) (𝒮.XB (m + 1))))) S w := by
      intro w hw
      have hmem := (hSw w hw).2
      have h1 := (hC1.differentiableOn one_ne_zero _ hmem).hasFDerivWithinAt
      have haff : HasFDerivWithinAt (fun w : 𝒮.XB (m + 1) =>
          (((a, w), κ) : (𝒮.E₀'.prod F.shift) (m + 1)))
          ((ContinuousLinearMap.inl (𝒮.E₀' (m + 1)) (F (m + 2)) (R := ℝ)).comp
            (ContinuousLinearMap.inr ℝ (Pn × 𝒮.Cs) (𝒮.XB (m + 1)))) S w := by
        have := (((ContinuousLinearMap.inl (𝒮.E₀' (m + 1)) (F (m + 2)) (R := ℝ)).comp
            (ContinuousLinearMap.inr ℝ (Pn × 𝒮.Cs) (𝒮.XB (m + 1)))).hasFDerivWithinAt
            (s := S) (x := w)).const_add ((((a, 0), κ)) : (𝒮.E₀'.prod F.shift) (m + 1))
        refine this.congr (fun w' _ => ?_) ?_ <;> simp
      exact h1.comp w haff fun w' hw' => (hSw w' hw').2
    have hbound : ∀ w ∈ S, ‖(fderivWithin ℝ Ξm Dm ((a, w), κ)).comp
        ((ContinuousLinearMap.inl (𝒮.E₀' (m + 1)) (F (m + 2)) (R := ℝ)).comp
          (ContinuousLinearMap.inr ℝ (Pn × 𝒮.Cs) (𝒮.XB (m + 1))))‖ ≤ M := by
      intro w hw
      have hmem := (hSw w hw).2
      have h1 := hδ₂' hmem (by
        rw [dist_zero_right]; exact (hnorm w (hSw w hw).1).trans_le (min_le_right _ _))
      rw [dist_eq_norm] at h1
      have h2 : ‖fderivWithin ℝ Ξm Dm ((a, w), κ)‖ ≤ M := by
        have h3 := norm_sub_norm_le (fderivWithin ℝ Ξm Dm ((a, w), κ)) (fderivWithin ℝ Ξm Dm 0)
        rw [hM]; linarith
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      calc ‖(fderivWithin ℝ Ξm Dm ((a, w), κ)) (((0, v), 0) : (𝒮.E₀'.prod F.shift) (m + 1))‖
          ≤ ‖fderivWithin ℝ Ξm Dm ((a, w), κ)‖ *
              ‖(((0, v), 0) : (𝒮.E₀'.prod F.shift) (m + 1))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * ‖v‖ := by
            rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_zero, max_eq_right (norm_nonneg v),
              max_eq_left (norm_nonneg v)]
            exact mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound hw' hw
    simpa [hΞm] using this

/-- **Lemma 2 for `ê_λ` on the contraction regions**: there are radii `δ_m > 0` (depending on
`Ξ` only) such that for every system of contraction regions `R` with `ν_m, ρ_m ≤ δ_m` and every
smooth `λ` (level-`1` representative `λ₁`) there are constants `c_m ≥ 0` bounding `(ê_λ)_m` and
its Lipschitz constant in `w` on `{‖a‖ < ν_m} × {‖w‖ < ρ_m}`: `c_m = (2|λ|_{m+2}/δ_m)(M_m + 1)`,
by the scaling `Ξ_m(y, κ) = (2|κ|/δ_m) Ξ_m(y, (δ_m/2|κ|) κ)`. -/
theorem exists_xi_radii_bounds (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (h0U : (0 : E 0) ∈ U)
    (hG : 𝒮.G.U 0 ⊆ U') :
    ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
      ∀ (h' : Pn × W 0 → Q × W 0) (Bc : Pn × W 0 → W 0) (hh'𝒮 : IsBasicGerm Ct 𝒮.G h' Bc)
        (Rd : (𝒮.toShiftedBasicData hCt.isQuadrantLike hh'𝒮).Radii),
        (∀ m, Rd.ν m ≤ δ m ∧ Rd.ρ m ≤ δ m) →
        ∀ (k₁ : F 1), F.toBase 1 k₁ ∈ F.smooth →
        ∃ c : ℕ → ℝ, (∀ m, 0 ≤ c m) ∧ ∀ m, ∀ a ∈ Ct ×ˢ (univ : Set 𝒮.Cs), ‖a‖ < Rd.ν m →
          ∀ w w' : 𝒮.XB (m + 1), ‖w‖ < Rd.ρ m → ‖w'‖ < Rd.ρ m →
          ‖levelB (W := 𝒮.XB.shift) (perturbEW (ehat 𝒮 Ψ Ψ' R k₁)) m (a, w)‖ ≤ c m ∧
          ‖levelB (W := 𝒮.XB.shift) (perturbEW (ehat 𝒮 Ψ Ψ' R k₁)) m (a, w) -
            levelB (W := 𝒮.XB.shift) (perturbEW (ehat 𝒮 Ψ Ψ' R k₁)) m (a, w')‖ ≤
              c m * ‖w - w'‖ := by
  classical
  choose δ hδ M hM hbound using fun m =>
    exists_xi_bounds (𝒮 := 𝒮) hU hR hCt hU' hΨ hψ0 h0U m
  refine ⟨δ, hδ, fun h' Bc hh'𝒮 Rd hRd k₁ hk => ?_⟩
  have hê := ehat_isScSmoothGerm (𝒮 := 𝒮) hU hR hCt hU' hΨ hψ0 h0U hG hk
  -- the lifts of `λ`
  have hlift : ∀ m, ∃ κ : F (m + 2), F.toBase (m + 2) κ = F.toBase 1 k₁ := fun m =>
    F.mem_smooth_iff.1 hk (m + 2)
  choose κ hκ using hlift
  have hκ' : ∀ m, F.shift.toBase m (F.shift.incl m (κ m)) = k₁ := fun m => by
    apply F.toBase_injective 1
    have h := hκ m
    rw [ScScale.toBase_succ, F.shift_toBase] at h
    exact h
  -- the constants
  refine ⟨fun m => 2 * ‖κ m‖ / δ m * (M m + 1), fun m => by have := hδ m; have := hM m; positivity,
    fun m a ha haν w w' hw hw' => ?_⟩
  -- membership of the points in the domains
  have hmem : ∀ w : 𝒮.XB (m + 1), ‖w‖ < Rd.ρ m →
      ((a, w) : (Pn × 𝒮.Cs) × 𝒮.XB (m + 1)) ∈
        (𝒮.toShiftedBasicData hCt.isQuadrantLike hh'𝒮).G₁.U m :=
    fun w hw => Rd.mem_G m a ha haν w hw
  have hmem' : ∀ w : 𝒮.XB (m + 1), ‖w‖ < Rd.ρ m →
      ((a, w) : 𝒮.E₀' (m + 1)) ∈ 𝒮.E₀'.lvlSet (𝒮.glue₀ 0 ⁻¹' U') (m + 1) := fun w hw => by
    have h1 := hmem w hw
    change ((a, w) : 𝒮.E₀' (m + 1)) ∈ 𝒮.pushGerm₀.U (m + 1) at h1
    exact pushGerm₀_U_subset hG (m + 1) h1
  have hmemx : ∀ (w : 𝒮.XB (m + 1)) (κ' : F (m + 2)), ‖w‖ < Rd.ρ m →
      (((a, w), κ') : (𝒮.E₀'.prod F.shift) (m + 1)) ∈
        (𝒮.E₀'.prod F.shift).lvlSet (xiDom 𝒮 U' F) (m + 1) := fun w κ' hw => by
    rw [ScBanach.mem_lvlSet, mem_xiDom, ScBanach.prod_toBase]
    exact hmem' w hw
  -- `(ê_λ)_m(a, w) = (Ξ_m((a, w), κ_m))_X`
  have hlev : ∀ w : 𝒮.XB (m + 1), ‖w‖ < Rd.ρ m →
      levelB (W := 𝒮.XB.shift) (perturbEW (ehat 𝒮 Ψ Ψ' R k₁)) m (a, w) =
        (levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), κ m))).2 := fun w hw => by
    rw [(𝒮.toShiftedBasicData hCt.isQuadrantLike hh'𝒮).levelB_eW hê (hmem w hw)]
    congr 1
    have h1 : (𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1))) ∈
        𝒮.E₀'.lvlSet (𝒮.glue₀ 0 ⁻¹' U') m := by
      rw [ScBanach.mem_lvlSet, 𝒮.E₀'.toBase_inclK]
      exact hmem' w hw
    exact levelMap_ehat (𝒮 := 𝒮) hU hR hCt hU' hΨ h1 (hκ' m)
  -- the scaling
  set s : ℝ := 2 * ‖κ m‖ / δ m with hs
  have hs0 : 0 ≤ s := by have := hδ m; positivity
  have hscale : ∀ w : 𝒮.XB (m + 1), ‖w‖ < Rd.ρ m →
      levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), κ m)) =
        s • levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), (δ m / (2 * ‖κ m‖)) • κ m)) := by
    intro w hw
    by_cases hκ0 : κ m = 0
    · have h1 := levelMap_xiMap_smul (𝒮 := 𝒮) hU hR hCt hU' hΨ
        (m := m) (y := 𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1)))
        (κ := F.shift.incl m (κ m)) (by
          rw [ScBanach.mem_lvlSet, mem_xiDom, ScBanach.prod_toBase, 𝒮.E₀'.toBase_inclK]
          exact hmem' w hw) 0
      rw [zero_smul, zero_smul] at h1
      have h2 : s = 0 := by rw [hs, hκ0, norm_zero]; simp
      rw [h2, zero_smul]
      change levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
        (𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1)), F.shift.incl m (κ m)) = 0
      rw [hκ0, map_zero]
      exact h1
    · have hn : 0 < ‖κ m‖ := norm_pos_iff.2 hκ0
      have h1 := levelMap_xiMap_smul (𝒮 := 𝒮) hU hR hCt hU' hΨ
        (m := m) (y := 𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1)))
        (κ := F.shift.incl m ((δ m / (2 * ‖κ m‖)) • κ m)) (by
          rw [ScBanach.mem_lvlSet, mem_xiDom, ScBanach.prod_toBase, 𝒮.E₀'.toBase_inclK]
          exact hmem' w hw) s
      have hκeq : F.shift.incl m (κ m) = s • F.shift.incl m ((δ m / (2 * ‖κ m‖)) • κ m) := by
        rw [map_smul, smul_smul]
        have : s * (δ m / (2 * ‖κ m‖)) = 1 := by
          have hn' : ‖κ m‖ ≠ 0 := hn.ne'
          have hδ' : δ m ≠ 0 := (hδ m).ne'
          rw [hs]; field_simp
        rw [this, one_smul]
      change levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
        (𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1)), F.shift.incl m (κ m)) =
        s • levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          (𝒮.E₀'.inclK m 1 ((a, w) : 𝒮.E₀' (m + 1)),
            F.shift.incl m ((δ m / (2 * ‖κ m‖)) • κ m))
      rw [hκeq]
      exact h1
  have hkhat : ‖(δ m / (2 * ‖κ m‖)) • κ m‖ < δ m := by
    by_cases hκ0 : κ m = 0
    · rw [hκ0, smul_zero, norm_zero]; exact hδ m
    · have hn : 0 < ‖κ m‖ := norm_pos_iff.2 hκ0
      rw [norm_smul, Real.norm_of_nonneg (by have := hδ m; positivity)]
      have := hδ m
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
  -- the bounds of `Ξ_m` on the ball
  have hball := hbound m a ((δ m / (2 * ‖κ m‖)) • κ m) (ball (0 : 𝒮.XB (m + 1)) (Rd.ρ m))
    (convex_ball _ _) (haν.trans_le (hRd m).1) hkhat (fun w hw => by
      rw [mem_ball, dist_zero_right] at hw
      exact ⟨hw.trans_le (hRd m).2, hmemx w _ hw⟩)
  have hwb : w ∈ ball (0 : 𝒮.XB (m + 1)) (Rd.ρ m) := by rw [mem_ball, dist_zero_right]; exact hw
  have hw'b : w' ∈ ball (0 : 𝒮.XB (m + 1)) (Rd.ρ m) := by rw [mem_ball, dist_zero_right]; exact hw'
  have hM1 : M m ≤ M m + 1 := by linarith
  have h1le : (1 : ℝ) ≤ M m + 1 := by linarith [hM m]
  constructor
  · rw [hlev w hw, hscale w hw]
    calc ‖(s • levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), (δ m / (2 * ‖κ m‖)) • κ m))).2‖
        ≤ ‖s • levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
          ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), (δ m / (2 * ‖κ m‖)) • κ m))‖ := norm_snd_le _
      _ ≤ s * 1 := by
          rw [norm_smul, Real.norm_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left (hball.1 w hwb) hs0
      _ ≤ s * (M m + 1) := by gcongr
  · rw [hlev w hw, hlev w' hw', hscale w hw, hscale w' hw', ← Prod.snd_sub, ← smul_sub]
    calc ‖(s • (levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), (δ m / (2 * ‖κ m‖)) • κ m)) -
          levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w'), (δ m / (2 * ‖κ m‖)) • κ m)))).2‖
        ≤ ‖s • (levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w), (δ m / (2 * ‖κ m‖)) • κ m)) -
          levelMap (E := 𝒮.E₀'.prod F.shift) (F := 𝒮.F' Q) (xiMap 𝒮 Ψ Ψ' R) m
            ((𝒮.E₀'.prod F.shift).inclK m 1 ((a, w'), (δ m / (2 * ‖κ m‖)) • κ m)))‖ :=
          norm_snd_le _
      _ ≤ s * (M m * ‖w - w'‖) := by
          rw [norm_smul, Real.norm_of_nonneg hs0]
          exact mul_le_mul_of_nonneg_left (hball.2 w hwb w' hw'b) hs0
      _ ≤ s * (M m + 1) * ‖w - w'‖ := by
          rw [mul_assoc]
          gcongr

end Xi

end Polyfold
