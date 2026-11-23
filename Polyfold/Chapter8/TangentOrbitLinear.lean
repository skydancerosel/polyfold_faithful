import Polyfold.Chapter8.TangentOrbit
import Polyfold.Chapter2.TangentMapLinear
import Polyfold.Chapter7.NaturalRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.1, proof of Theorem 8.1.15 (2017: Theorem 8.4, p. 268): **the action of `G_x` on `TU(x)` is
linear on the fibres**.  The text takes `TU(x)`, as a bundle over `U(x)₁`, with "an sc-smooth
bundle action of `G_x`"; Chapter 8's `NaturalRep.tangentMulAction` is the action by the tangent
maps `TΦ(g)`.  Here its linearity is stated in the linear structure of Definition 2.3.14 (V2.19).

## What is formalized (namespace `Polyfold.EpGroupoid.NaturalRep`)

* `tangentSmulCLM g hy hz : T_yX →L[ℝ] T_zX`, for `y ∈ U(x) ∩ X₁` and `z = Φ(g)(y)`: the tangent
  map `TΦ(g)` on the fibre (Part I's `tangentMapOnCLM`); `tangentSmulCLM_apply`: it is the action
  `v ↦ g • v` of `tangentMulAction`.
* `tangentSmulCLE g hy hz : T_yX ≃L[ℝ] T_zX`, with inverse the action of `g⁻¹`.
* **`tangentMulAction_linear`**: for every `g ∈ G_x` and `y ∈ U(x) ∩ X₁`, the action of `g` maps
  `T_yX` onto `T_{Φ(g)y}X` by a bounded linear isomorphism (additive and homogeneous).
* Witness: `exists_naturalRep_tangentMulAction_linear`: every `x` has a natural representation
  (Theorem 7.6.1) and every point of `U(x) ∩ X₁` (e.g. `x` itself when `x ∈ X₁`) has such a
  fibre isomorphism.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace NaturalRep

variable {x : Obj} (R : X.NaturalRep x)

lemma mem_tangentU_of_mem_fiber {y : X.PObj.Level 1} (hy : X.PObj.levelVal 1 y ∈ R.U)
    (α : X.PObj.tangentFiber y) : α.1 ∈ R.tangentU :=
  MPolyfold.tangentFiber_subset_tangentPreimage hy α.2

/-- **`TΦ(g) : T_yX →L[ℝ] T_zX`**, `z = Φ(g)(y)`, `y ∈ U(x) ∩ X₁`: the action of `g` on the fibre
over `y` is a bounded linear map (2021 p. 368, proof of Theorem 8.1.15). -/
def tangentSmulCLM (g : X.Isotropy x) {y z : X.PObj.Level 1} (hy : X.PObj.levelVal 1 y ∈ R.U)
    (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z) :
    X.PObj.tangentFiber y →L[ℝ] X.PObj.tangentFiber z :=
  MPolyfold.tangentMapOnCLM (R.isScDiffeoOn_Φ g).isScSmoothOn hy hz

/-- `tangentSmulCLM` is the action `v ↦ g • v` of `G_x` on `TU(x)`. -/
theorem tangentSmulCLM_apply (g : X.Isotropy x) {y z : X.PObj.Level 1}
    (hy : X.PObj.levelVal 1 y ∈ R.U) (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z)
    (α : X.PObj.tangentFiber y) :
    (R.tangentSmulCLM g hy hz α : X.PObj.TangentSpace) =
      (g • (⟨α.1, R.mem_tangentU_of_mem_fiber hy α⟩ : R.tangentU) : R.tangentU).1 :=
  MPolyfold.tangentMapOnCLM_apply _ hy hz α

theorem tangentSmulCLM_apply' (g : X.Isotropy x) {y z : X.PObj.Level 1}
    (hy : X.PObj.levelVal 1 y ∈ R.U) (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z)
    (α : X.PObj.tangentFiber y) :
    (R.tangentSmulCLM g hy hz α : X.PObj.TangentSpace) = R.tΦ g α.1 :=
  MPolyfold.tangentMapOnCLM_apply _ hy hz α

lemma Φ_inv_eq (g : X.Isotropy x) {y z : X.PObj.Level 1} (hy : X.PObj.levelVal 1 y ∈ R.U)
    (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z) :
    R.Φ g⁻¹ (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 y := by
  rw [← hz]; exact (R.isScDiffeoOn_Φ g).left_inv _ hy

lemma mem_U_of_Φ_eq (g : X.Isotropy x) {y z : X.PObj.Level 1} (hy : X.PObj.levelVal 1 y ∈ R.U)
    (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z) : X.PObj.levelVal 1 z ∈ R.U := by
  rw [← hz]; exact R.mapsTo_Φ g hy

lemma tΦ_inv_tΦ (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    R.tΦ g⁻¹ (R.tΦ g v) = v := by
  rw [← R.tΦ_mul g⁻¹ g hv, inv_mul_cancel, R.tΦ_one hv]

/-- **The action of `g` is a bounded linear isomorphism `T_yX ≃L[ℝ] T_{Φ(g)y}X`**, with inverse
the action of `g⁻¹`. -/
def tangentSmulCLE (g : X.Isotropy x) {y z : X.PObj.Level 1} (hy : X.PObj.levelVal 1 y ∈ R.U)
    (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z) :
    X.PObj.tangentFiber y ≃L[ℝ] X.PObj.tangentFiber z :=
  ContinuousLinearEquiv.equivOfInverse (R.tangentSmulCLM g hy hz)
    (R.tangentSmulCLM g⁻¹ (R.mem_U_of_Φ_eq g hy hz) (R.Φ_inv_eq g hy hz))
    (fun α => Subtype.ext (by
      rw [tangentSmulCLM_apply', tangentSmulCLM_apply']
      exact R.tΦ_inv_tΦ g (R.mem_tangentU_of_mem_fiber hy α)))
    (fun β => Subtype.ext (by
      rw [tangentSmulCLM_apply', tangentSmulCLM_apply']
      have h := R.tΦ_inv_tΦ g⁻¹ (R.mem_tangentU_of_mem_fiber (R.mem_U_of_Φ_eq g hy hz) β)
      rwa [inv_inv] at h))

theorem tangentSmulCLE_apply (g : X.Isotropy x) {y z : X.PObj.Level 1}
    (hy : X.PObj.levelVal 1 y ∈ R.U) (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z)
    (α : X.PObj.tangentFiber y) :
    (R.tangentSmulCLE g hy hz α : X.PObj.TangentSpace) = R.tΦ g α.1 :=
  R.tangentSmulCLM_apply' g hy hz α

/-- **The action of `G_x` on `TU(x)` is linear on the fibres** (2021 p. 368, proof of
Theorem 8.1.15; 2017 p. 268): for `g ∈ G_x` and `y ∈ U(x) ∩ X₁`, `v ↦ g • v` maps `T_yX` onto
`T_{Φ(g)y}X` and is there a bounded linear isomorphism; in particular it is additive and
homogeneous. -/
theorem tangentMulAction_linear (g : X.Isotropy x) {y z : X.PObj.Level 1}
    (hy : X.PObj.levelVal 1 y ∈ R.U) (hz : R.Φ g (X.PObj.levelVal 1 y) = X.PObj.levelVal 1 z) :
    ∃ L : X.PObj.tangentFiber y ≃L[ℝ] X.PObj.tangentFiber z,
      (∀ α : X.PObj.tangentFiber y,
        (L α : X.PObj.TangentSpace) =
          (g • (⟨α.1, R.mem_tangentU_of_mem_fiber hy α⟩ : R.tangentU) : R.tangentU).1) ∧
      (∀ α β : X.PObj.tangentFiber y, L (α + β) = L α + L β) ∧
      (∀ (c : ℝ) (α : X.PObj.tangentFiber y), L (c • α) = c • L α) :=
  ⟨R.tangentSmulCLE g hy hz, R.tangentSmulCLM_apply g hy hz, fun α β => map_add _ α β,
    fun c α => map_smul _ c α⟩

end NaturalRep

/-- **Witness**: for `x ∈ X₁`, there is a natural representation at `x` (Theorem 7.6.1), and for
every `g ∈ G_x` the action of `g` is a bounded linear isomorphism of `T_xX` onto
`T_{Φ(g)x}X = T_xX`. -/
theorem exists_naturalRep_tangentMulAction_linear (X : EpGroupoid Obj Mor) (x : X.PObj.Level 1)
    (g : X.Isotropy (X.PObj.levelVal 1 x)) :
    ∃ (R : X.NaturalRep (X.PObj.levelVal 1 x)) (hx : X.PObj.levelVal 1 x ∈ R.U)
      (hz : R.Φ g (X.PObj.levelVal 1 x) = X.PObj.levelVal 1 x),
      Nonempty (X.PObj.tangentFiber x ≃L[ℝ] X.PObj.tangentFiber x) ∧
      ∀ α : X.PObj.tangentFiber x,
        (R.tangentSmulCLE g hx hz α : X.PObj.TangentSpace) = R.tΦ g α.1 := by
  obtain ⟨D, R, -, -, -, -⟩ :=
    NatRepConstruction.exists_naturalRep_sheets X (X.PObj.levelVal 1 x) isOpen_univ (mem_univ _)
  exact ⟨R, R.mem_U, R.Φ_self g, ⟨R.tangentSmulCLE g R.mem_U (R.Φ_self g)⟩,
    R.tangentSmulCLE_apply g R.mem_U (R.Φ_self g)⟩

end EpGroupoid

end Polyfold
