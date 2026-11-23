import Polyfold.Chapter15.RestrictedSeedsPre
import Polyfold.Chapter15.LinearizationLocalIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9**, steps (c)–(d), pp. 698–699: the surjectivity (15.1) relative to `Λ₀` under a
local strong bundle isomorphism.

# (15.1) relative to `Λ₀` along a local strong bundle isomorphism

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`isParamOntoVecRel_localIso`**: for a local strong bundle isomorphism `L : W|U → W'|U'`,
  sc-Fredholm section functors with `f = Ψ ∘ f' ∘ ϕ` on `U`, `Λ = Λ' ∘ Φ` over `U`, a point
  `x ∈ U` and vectors `v_j ∈ W_x` with images `v'_j = Φ(v_j) ∈ W'_{ϕ(x)}`: (15.1) relative to
  `Λ'` at `ϕ(x)` with the `v'_j` gives (15.1) relative to `Λ` at `x` with the `v_j`.

## Reading

The operators of `T(f, Λ)(x)` are those of `T(f', Λ')(ϕ x)` read through the carried chart
(`isReducedOntoAtLevel_localIso_iff` is the case without vectors).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15 StrongBundle

variable {A A' : SEP.{u}} {U : Set A.Obj} {U' : Set A'.Obj}

set_option maxHeartbeats 800000 in
-- the carried chart and local representation, as for general position
open scoped Classical in
/-- **(15.1) relative to `Λ₀` along a local strong bundle isomorphism**: for sc-Fredholm section
functors `f` of `W` and `f'` of `W'` with `f = Ψ ∘ f' ∘ ϕ` on `U`, an sc⁺-multisection `Λ'` of
`W'` and a function `Λ` with `Λ = Λ' ∘ Φ` over `U`, and vectors `v_j ∈ W_x`, `v'_j = Φ(v_j)`:
(15.1) relative to `Λ'` at `ϕ(x)` with the `v'_j` gives (15.1) relative to `Λ` at `x` with the
`v_j`. -/
theorem isParamOntoVecRel_localIso (L : StrongBundle.LocalIso A.B A'.B U U')
    {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hf' : A'.E.IsScFredholmSectionFunctor f')
    {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (hΛ' : IsScPlusMultisection A' Λ')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hΛL : ∀ w, A.P w ∈ U → Λ w = Λ' (L.Φ w))
    {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1} (hxU : A.X.PObj.levelVal 1 x ∈ U)
    (hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x') {ℓ : ℕ}
    {v : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}}
    {v' : Fin ℓ → A'.P ⁻¹' {A'.X.PObj.levelVal 1 x'}}
    (hv : ∀ j, L.Φ (v j : A.W) = (v' j : A'.W)) (H : IsParamOntoVecRel f' Λ' x' v') :
    IsParamOntoVecRel f Λ x v := by
  obtain ⟨d⟩ := nonempty_localLinData hΛ' x'
  have hy'U : (A'.X.PObj.levelVal 1 x') ∈ U' := hϕ ▸ L.base.mapsTo hxU
  have hso : IsOpen (d.c.φ.source ∩ U') := d.c.φ.isOpen_source.inter L.isOpen_U'
  set c' := d.c.restrict inter_subset_left hso with hc'def
  have hc' : A'.B.IsChart c' := d.isChart.restrict inter_subset_left hso
  have hsub : c'.φ.source ⊆ U' := fun z hz => hz.2
  have hx' : (A'.X.PObj.levelVal 1 x') ∈ c'.φ.source := ⟨d.mem, hy'U⟩
  set O' := d.O ∩ U' with hO'def
  have hO' : IsOpen O' := d.isOpen.inter L.isOpen_U'
  have hrep' : IsLocalRepOn A' Λ' O' d.s d.σ := d.rep.mono hO' inter_subset_left
  have hsubO : c'.φ.source ⊆ O' := fun z hz => ⟨d.sub hz.1, hz.2⟩
  set c := L.transportChart c' hsub with hcdef
  have hx : (A.X.PObj.levelVal 1 x) ∈ c.φ.source := ⟨hxU, by rw [mem_preimage, hϕ]; exact hx'⟩
  have hrep : IsLocalRepOn A Λ (isoSet L O') (fun i => isoSec L (d.s i)) d.σ :=
    isLocalRepOn_isoSec L hΛL hO' inter_subset_right hrep'
  have hcsub : c.φ.source ⊆ isoSet L O' := fun z hz => ⟨hz.1, hsubO hz.2⟩
  let dx' : LocalLinData A' Λ' x' := ⟨O', hO', d.k, d.s, d.σ, hrep', c', hc', hsubO, hx'⟩
  let dx : LocalLinData A Λ x :=
    ⟨isoSet L O', isOpen_isoSet L hO', d.k, fun i => isoSec L (d.s i), d.σ, hrep, c,
      L.isChart_transportChart c' hsub hc', hcsub, hx⟩
  have hsec : IsSection A.P f := hf.1.1.1
  have hsec' : IsSection A'.P f' := hf'.1.1.1
  have hbr : ∀ i, isoSec L (d.s i) (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x) ↔
      d.s i (A'.X.PObj.levelVal 1 x') = f' (A'.X.PObj.levelVal 1 x') := fun i => by
    have e1 : isoSec L (d.s i) (A.X.PObj.levelVal 1 x) =
        L.Ψ (d.s i (A'.X.PObj.levelVal 1 x')) := by rw [isoSec, hϕ]
    have e2 : f (A.X.PObj.levelVal 1 x) = L.Ψ (f' (A'.X.PObj.levelVal 1 x')) := by
      rw [hfL hxU]; simp only [Function.comp_apply, hϕ]
    rw [e1, e2]
    constructor
    · intro h
      have h1 : d.s i (A'.X.PObj.levelVal 1 x') ∈ A'.P ⁻¹' U' := by
        change A'.P (d.s i (A'.X.PObj.levelVal 1 x')) ∈ U'
        rw [(hrep'.2.1 i).1 _ (hsubO hx')]; exact hy'U
      have h2 : f' (A'.X.PObj.levelVal 1 x') ∈ A'.P ⁻¹' U' := by
        change A'.P (f' (A'.X.PObj.levelVal 1 x')) ∈ U'
        rw [hsec' (A'.X.PObj.levelVal 1 x')]; exact hy'U
      rw [← L.zero.right_inv _ h1, ← L.zero.right_inv _ h2, h]
    · intro h; rw [h]
  have hl : levelLift c.φ 1 (A.X.PObj.levelVal 1 x) =
      levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x') := levelLift_transportChart L hsub hϕ
  have hzU : c'.φ.model.E.toBase 1 (levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x')) ∈ c'.U := by
    rw [A'.X.PObj.toBase_levelLift c'.isChart hx' (levelVal_mem x')]
    exact mem_U_of_mem_O c'.isRetraction (c'.r_image ▸ c'.φ.mapsTo_model _ hx')
  have hD : ∀ i, subDeriv c f (isoSec L (d.s i)) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) =
      subDeriv c' f' (d.s i) (levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x')) := fun i => by
    rw [hl]
    exact subDeriv_transportChart L hsub hf'.1.1 hfL (hrep'.2.1 i) hc' hsubO hzU
  obtain ⟨k, V, T, hT⟩ := c'.φ.model.isPartialQuadrant
  intro L₀ hL₀ ψ hψ hyψ m V' T' hT' w
  rw [linearization_eq hf dx] at hL₀
  obtain ⟨i, hi, rfl⟩ := (mem_support_linSumIntr_iff hsec hrep.1
    (fun j => (hrep.2.1 j).1) hcsub hx _).1 hL₀
  have hL : toIntr c' hx' (subDeriv c' f' (d.s i) (levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x'))) ∈
      (linearization f' Λ' x').support := by
    rw [linearization_eq hf' dx']
    exact (mem_support_linSumIntr_iff hsec' hrep'.1 (fun j => (hrep'.2.1 j).1) hsubO hx'
      _).2 ⟨i, (hbr i).1 hi, rfl⟩
  obtain ⟨w', hw'⟩ := exists_fiberLin_eq L hsub hϕ hx hx' w
  obtain ⟨u', hu', τ, hτ⟩ := H _ hL c'.φ c'.isChart hx' k V T hT w'
  set τiso := tangentIso L hsub hϕ hx hx' with hτiso
  refine ⟨τiso.symm u', ?_, τ, ?_⟩
  · rw [reducedTangentFiber_eq hψ hyψ T' c.isChart hx T hT' hT,
      ← mem_reducedTangentFiber_tangentIso_iff L hsub hϕ hx hx' T, τiso.apply_symm_apply]
    exact hu'
  · apply c.fiberLin_injective hx
    have hvj : ∀ j, c.fiberLin hx (v j) = c'.fiberLin hx' (v' j) := fun j => by
      rw [StrongBundleChart.fiberLin_apply, StrongBundleChart.fiberLin_apply,
        L.transportChart_apply, hv j]
    rw [map_add, map_sum]
    simp only [map_smul]
    rw [hD i, ← fiberLin_toIntr_tangentIso L hsub hϕ hx hx' _ (τiso.symm u'),
      τiso.apply_symm_apply, ← hw', ← hτ, map_add, map_sum]
    simp only [map_smul, hvj]
    rfl

end SBLocalization

end Polyfold
