import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.FredholmGermLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, the
push-forward `Ψ_*(g)` of (49), **for germs**.

# The push-forward of a germ by a strong bundle isomorphism

## What is formalized

The push-forward `Ψ_*(g)(u') = (Ψ(ψ⁻¹(u'), g(ψ⁻¹(u'))))₂` (`Polyfold.pushforward`, moved here from
`GoodPositionGerm.lean`), and for an sc-smooth germ `g` on `G`: `Ψ_*(g)` is an sc-smooth germ on the
germ `pullGerm` of the points that `ψ⁻¹` maps into `G` (`IsStrongBundleIso.pushforward_isScSmoothGerm`,
`pushforward_isSc1GermWith`), with `D(Ψ_*g)(0) = Γ(0) ∘ Dg(0) ∘ Dψ⁻¹(0)`
(`IsStrongBundleIso.pushforwardDeriv_zero`).  Written in `GermCalculusParam.lean` (Findings,
Chapter 3, items 270–274) and placed here, below `GoodPositionGerm.lean`, so that §3.6 can use it.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

section PushforwardDef

variable {E F E' F' : ScBanach} (Ψ : E 0 × F 0 → E' 0 × F' 0) (Ψ' : E' 0 × F' 0 → E 0 × F 0)

/-- The **push-forward** `Ψ_*(g)(u') = (Ψ(ψ⁻¹(u'), g(ψ⁻¹(u'))))₂` of a principal part `g : U → F`
under a strong bundle isomorphism `Ψ` with inverse `Ψ'` (the text's `h + t = Ψ_*(g)`, (49)). -/
def pushforward (g : E 0 → F 0) : E' 0 → F' 0 :=
  fun u' => (Ψ (IsStrongBundleMap.base Ψ' u', g (IsStrongBundleMap.base Ψ' u'))).2

end PushforwardDef

/-! ### The push-forward by a strong bundle isomorphism -/

section PushforwardIso

variable {E F E' F' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

/-- `D[(Ψ(·, k(·)))₂](0) = Γ(0) ∘ Dk(0)` for the explicit derivative family `fiberCompDeriv`,
when `k(0) = 0` (`IsStrongBundleMap.scDeriv_fiber_zero`). -/
theorem fiberCompDeriv_zero_eq (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hΨ : IsStrongBundleMap U U' Ψ) {k : E 0 → F 0} (hk0 : k 0 = 0)
    (Dk : E 1 → E 0 →L[ℝ] F 0) :
    fiberCompDeriv U Ψ k Dk 0 = (hΨ.fiberCLM h0).comp (Dk 0) := by
  rw [fiberCompDeriv_zero hk0]
  ext h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  exact hΨ.scDeriv_fiber_zero hU h0 h (Dk 0 h)

/-- **`D(Ψ_*k)(0) = Γ(0) ∘ Dk(0) ∘ Dψ'(0)`** for the explicit derivative family
`pushforwardDeriv` of the push-forward along `ψ'` with `ψ'(0) = 0`, when `k(0) = 0`. -/
theorem pushforwardDeriv_zero_eq (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hΨ : IsStrongBundleMap U U' Ψ) {ψ' : E' 0 → E 0} (hψ'0 : ψ' 0 = 0) {k : E 0 → F 0}
    (hk0 : k 0 = 0) (Dk : E 1 → E 0 →L[ℝ] F 0) :
    pushforwardDeriv U U' Ψ ψ' k Dk 0 =
      (hΨ.fiberCLM h0).comp ((Dk 0).comp (scDeriv U' ψ' 0)) := by
  unfold pushforwardDeriv
  rw [levelMap_one_zero_of_zero hψ'0, fiberCompDeriv_zero_eq hU h0 hΨ hk0]
  rfl

namespace IsStrongBundleIso

variable {hU : IsRelOpenInQuadrant E C U} {hU' : IsRelOpenInQuadrant E' C' U'}

lemma zero_mem' (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) : (0 : E' 0) ∈ U' :=
  hψ0 ▸ hΨ.toFun.base_mem h0

/-- `ψ' = ψ⁻¹` maps `U'` into `C`. -/
lemma base_inv_mapsTo_quadrant (hU : IsRelOpenInQuadrant E C U)
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') : MapsTo (IsStrongBundleMap.base Ψ') U' C :=
  fun _ hu' => hU.subset_quadrant (hΨ.invFun.base_mem hu')

/-- `ψ'` is an sc⁰-germ on `ofSet U'`. -/
lemma base_inv_isSc0Germ (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ')
    (h0U' : (0 : E' 0) ∈ U') :
    IsSc0Germ (ScNbhdGerm.ofSet hU'.relOpen h0U') (IsStrongBundleMap.base Ψ') :=
  (hΨ.invFun.base_isScSmooth hU').isSc1.isSc0.isSc0Germ hU'.relOpen h0U'

/-- **The germ `ψ'⁻¹(G)`** of the points of `U'` that the inverse base map `ψ' = ψ⁻¹` sends
into `G`, level by level (`ScNbhdGerm.preimage` inside `ofSet U'`): the germ on which the
push-forward `Ψ_*(k)` of a germ `k` on `G` lives. -/
def pullGerm (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (G₁ : ScNbhdGerm E C) : ScNbhdGerm E' C' :=
  (ScNbhdGerm.ofSet hU'.relOpen (hΨ.zero_mem' h0 hψ0)).preimage G₁
    (hΨ.base_inv_isSc0Germ hU' (hΨ.zero_mem' h0 hψ0)) (hΨ.base_zero' h0 hψ0)
    (hΨ.base_inv_mapsTo_quadrant hU)

variable (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
  (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (G₁ : ScNbhdGerm E C)

lemma pullGerm_U (m : ℕ) :
    (hΨ.pullGerm hU hU' h0 hψ0 G₁).U m =
      {x ∈ E'.lvlSet U' m | levelMap (IsStrongBundleMap.base Ψ') m x ∈ G₁.U m} := rfl

lemma pullGerm_subset (m : ℕ) :
    (hΨ.pullGerm hU hU' h0 hψ0 G₁).U m ⊆ E'.lvlSet U' m := fun _ hx => hx.1

lemma pullGerm_mapsToGerm :
    (hΨ.pullGerm hU hU' h0 hψ0 G₁).MapsToGerm G₁ (IsStrongBundleMap.base Ψ') :=
  fun _ _ hx => hx.2

lemma pushforward_eq (k : E 0 → F 0) :
    pushforward Ψ Ψ' k = (fun u => (Ψ (u, k u)).2) ∘ IsStrongBundleMap.base Ψ' := rfl

variable {G₁}

/-- **The push-forward of a germ by a strong bundle isomorphism is a germ** (Definition 3.1.11 (preprint 3.11),
"`Ψ_*(g)`"): for `k` an sc-smooth germ on `G ⊆ U`, `Ψ_*(k) = (Ψ(ψ'(·), k(ψ'(·))))₂` is an
sc-smooth germ on `ψ'⁻¹(G)`. -/
theorem pushforward_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hG : G₁.U 0 ⊆ U) {k : E 0 → F 0}
    (hk : IsScSmoothGerm G₁ k) :
    IsScSmoothGerm (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' k) :=
  hΨ.toFun.pushforward_isScSmoothGerm hU hU' (hΨ.zero_mem' h0 hψ0) hG
    (hΨ.invFun.base_isScSmooth hU') (hΨ.base_zero' h0 hψ0) (hΨ.base_inv_mapsTo_quadrant hU) hk

/-- **The chain rule for the push-forward**: `pushforwardDeriv U U' Ψ ψ' k Dk`, i.e.
`x ↦ D[(Ψ(·, k(·)))₂](ψ'(x)) ∘ Dψ'(x)`, is a derivative family of `Ψ_*(k)` on `ψ'⁻¹(G)`. -/
theorem pushforward_isSc1GermWith (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hG : G₁.U 0 ⊆ U) {k : E 0 → F 0}
    {Dk : E 1 → E 0 →L[ℝ] F 0} (hk : IsSc1GermWith G₁ k Dk) :
    IsSc1GermWith (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' k)
      (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') k Dk) :=
  hΨ.toFun.pushforward_isSc1GermWith hU hU' (hΨ.zero_mem' h0 hψ0) hG
    (hΨ.invFun.base_isScSmooth hU').isSc1 (hΨ.base_zero' h0 hψ0)
    (hΨ.base_inv_mapsTo_quadrant hU) hk

include hψ0 in
/-- **`D(Ψ_*k)(0) = Γ(0) ∘ Dk(0) ∘ Dψ'(0)`** (`k(0) = 0`): the form of
`IsStrongBundleIso.pushforward_linearization_wholeChart`, whose `Γ` is `fiberCLM h0` and whose `S.symm` is
`scDeriv U' ψ' 0`. -/
theorem pushforwardDeriv_zero (hU : IsRelOpenInQuadrant E C U) {k : E 0 → F 0} (hk0 : k 0 = 0)
    (Dk : E 1 → E 0 →L[ℝ] F 0) :
    pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') k Dk 0 =
      (hΨ.toFun.fiberCLM h0).comp ((Dk 0).comp (scDeriv U' (IsStrongBundleMap.base Ψ') 0)) :=
  pushforwardDeriv_zero_eq hU h0 hΨ.toFun (hΨ.base_zero' h0 hψ0) hk0 Dk

end IsStrongBundleIso

end PushforwardIso

end Polyfold
