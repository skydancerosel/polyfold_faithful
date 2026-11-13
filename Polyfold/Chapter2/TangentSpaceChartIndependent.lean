import Polyfold.Chapter2.TangentConeQuadrant

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, p. 39 and §2.5,
Definition 2.5.8, p. 57 (preprint Definitions 2.20 and 2.38).

# The sc-structure of `T_xX` does not depend on the chart

At a smooth `x`, `T_xX` carries, through a chart `φ`, the sc-structure of the sc-subspace
`T_{φ(x)}O` (`isScSubspace_tangentFiberModel`), transported by `Tφ(x)`.  This file proves that two
charts give the same sc-structure, and the same partial quadrant `C_xX`:

* `ScBanach.subspaceIso` (general): an sc-operator `L : E → F` with an sc-operator inverse
  `L' : F → E` on sc-subspaces `A ⊆ E`, `B ⊆ F` (`L(A) ⊆ B`, `L'(B) ⊆ A`, `L'L = 1` on `A`,
  `LL' = 1` on `B`) restricts to an sc-isomorphism `A ≅ B`.
* `MPolyfold.tangentFiberScIso`: for charts `φ`, `ψ` around a smooth `x`, the transition derivative
  `D(ψ ∘ φ⁻¹)(φ(x))` restricts to an sc-isomorphism `T_{φ(x)}O ≅ T_{ψ(x)}O'`, and
  `tangentFiberScIso_comp`: it carries `Tφ(x)α` to `Tψ(x)α` for every `α ∈ T_xX`; so the
  identity of `T_xX` is an sc-isomorphism between the two transported structures.
* `MPolyfold.tangentFiberScIso_image_partialConeFiberModel`: it maps the model of `C_xX` in the
  chart `φ` onto the model in the chart `ψ`.
* `MPolyfold.definition_2_5_8_scStructure`: the summary, Definition 2.5.8 for tame charts with
  chart independence.
-/

open Set Function Topology Module

noncomputable section

namespace Polyfold

namespace ScBanach

variable {E F : ScBanach} {A : Submodule ℝ (E 0)} {B : Submodule ℝ (F 0)}
  (hA : E.IsScSubspace A) (hB : F.IsScSubspace B)
  {L : E 0 →L[ℝ] F 0} (hL : IsScOperator L) (hLA : ∀ v ∈ A, L v ∈ B)

lemma IsScOperator.toBase_toScOperator {L : E 0 →L[ℝ] F 0} (hL : IsScOperator L) (m : ℕ)
    (x : E m) : F.toBase m (hL.toScOperator m x) = L (E.toBase m x) := by
  rw [hL.toScOperator.toBase_comm, hL.toScOperator_zero]

include hLA in
/-- The level-`m` restriction `A_m → B_m` of an sc-operator mapping `A` into `B`. -/
def restrLvl (m : ℕ) : E.levelSub A m →L[ℝ] F.levelSub B m :=
  ((hL.toScOperator m).comp (E.levelSub A m).subtypeL).codRestrict (F.levelSub B m) fun v => by
    change F.toBase m (hL.toScOperator m v) ∈ B
    rw [IsScOperator.toBase_toScOperator]
    exact hLA _ v.2

lemma coe_restrLvl (m : ℕ) (v : E.levelSub A m) :
    (restrLvl hL hLA m v : F m) = hL.toScOperator m v := rfl

lemma toBase_restrLvl (m : ℕ) (v : E.levelSub A m) :
    F.toBase m (restrLvl hL hLA m v : F m) = L (E.toBase m v) := by
  rw [coe_restrLvl, IsScOperator.toBase_toScOperator]

variable {L' : F 0 →L[ℝ] E 0} (hL' : IsScOperator L') (hL'B : ∀ w ∈ B, L' w ∈ A)
  (hinv : ∀ v ∈ A, L' (L v) = v) (hinv' : ∀ w ∈ B, L (L' w) = w)

/-- **An sc-isomorphism of sc-subspaces** from an sc-operator with an sc-operator inverse on the
subspaces. -/
def subspaceIso : ScIso (E.ofSubspace hA) (F.ofSubspace hB) where
  lvl m := ContinuousLinearEquiv.equivOfInverse (restrLvl hL hLA m) (restrLvl hL' hL'B m)
    (fun v => by
      obtain ⟨v, hv⟩ := (show E.levelSub A m from v)
      refine Subtype.ext <| E.toBase_injective m ?_
      change E.toBase m (hL'.toScOperator m (hL.toScOperator m v)) = E.toBase m v
      rw [IsScOperator.toBase_toScOperator, IsScOperator.toBase_toScOperator]
      exact hinv _ hv)
    (fun w => by
      obtain ⟨w, hw⟩ := (show F.levelSub B m from w)
      refine Subtype.ext <| F.toBase_injective m ?_
      change F.toBase m (hL.toScOperator m (hL'.toScOperator m w)) = F.toBase m w
      rw [IsScOperator.toBase_toScOperator, IsScOperator.toBase_toScOperator]
      exact hinv' _ hw)
  incl_comm m x := by
    obtain ⟨x, hx⟩ := (show E.levelSub A (m + 1) from x)
    exact Subtype.ext (hL.toScOperator.incl_comm m x)

lemma coe_subspaceIso_zero (v : E.levelSub A 0) :
    Subtype.val (show F.levelSub B 0 from subspaceIso hA hB hL hLA hL' hL'B hinv hinv' 0 v) =
      L v := by
  change F.toBase 0 (restrLvl hL hLA 0 v : F 0) = L (E.toBase 0 v)
  exact toBase_restrLvl hL hLA 0 v

end ScBanach

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ ψ : MChart X} {x : P.Level 1} (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source)
  (hψ : P.IsChart ψ) (hx' : P.levelVal 1 x ∈ ψ.source)

/-- `Tψ(x) = D(ψ ∘ φ⁻¹)(φ(x)) ∘ Tφ(x)` on `T_xX`. -/
lemma fiberCoord_eq_transitionCLM (α : P.tangentFiber x) :
    fiberCoord hψ hx' α = transitionCLM hφ hx hψ hx' (fiberCoord hφ hx α) := by
  have h := coe_tangentFiberEquiv_symm_trans hφ hx hψ hx' (tangentFiberEquiv hφ hx α)
  rw [Equiv.symm_apply_apply] at h
  rw [fiberCoord_eq_coe, fiberCoord_eq_coe, h]

/-- The transitions are inverse to each other on `T_{φ(x)}O`. -/
lemma transitionCLM_transitionCLM {v : φ.model.E 0} (hv : v ∈ tangentFiberModel hφ hx) :
    transitionCLM hψ hx' hφ hx (transitionCLM hφ hx hψ hx' v) = v :=
  congrArg Subtype.val (tangentFiberTransition_transition hφ hx hψ hx' ⟨v, hv⟩)

variable (hs : P.levelVal 1 x ∈ P.smoothSet)
  (hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx))
  (hA' : ψ.model.E.IsScSubspace (tangentFiberModel hψ hx'))

/-- **The transition `T_{φ(x)}O ≅ T_{ψ(x)}O'` as an sc-isomorphism** at a smooth `x`. -/
def tangentFiberScIso : ScIso (φ.model.E.ofSubspace hA) (ψ.model.E.ofSubspace hA') :=
  ScBanach.subspaceIso hA hA'
    (isScOperator_transitionCLM hφ hx hψ hx'
      ((mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hx).1 hs))
    (fun v hv => transitionCLM_mem hφ hx hψ hx' ⟨v, hv⟩)
    (isScOperator_transitionCLM hψ hx' hφ hx
      ((mem_smoothSet_iff_levelLift_mem_smoothLvl hψ hx').1 hs))
    (fun w hw => transitionCLM_mem hψ hx' hφ hx ⟨w, hw⟩)
    (fun _ hv => transitionCLM_transitionCLM hφ hx hψ hx' hv)
    (fun _ hw => transitionCLM_transitionCLM hψ hx' hφ hx hw)

lemma coe_tangentFiberScIso_zero (v : φ.model.E.levelSub (tangentFiberModel hφ hx) 0) :
    Subtype.val (show ψ.model.E.levelSub (tangentFiberModel hψ hx') 0 from
        tangentFiberScIso hφ hx hψ hx' hs hA hA' 0 v) =
      transitionCLM hφ hx hψ hx' v :=
  ScBanach.coe_subspaceIso_zero _ _ _ _ _ _ _ _ v

/-- `Tφ(x) α` as an element of level `0` of the sc-Banach space `T_{φ(x)}O`. -/
def fiberCoordSc (α : P.tangentFiber x) : φ.model.E.levelSub (tangentFiberModel hφ hx) 0 :=
  ⟨fiberCoord hφ hx α, (tangentFiberEquiv hφ hx α).2⟩

/-- **The sc-structure of `T_xX` does not depend on the chart**: the sc-isomorphism
`tangentFiberScIso` carries `Tφ(x)α` to `Tψ(x)α`, i.e. the identity of `T_xX` is an
sc-isomorphism between the structures transported through `φ` and through `ψ`. -/
theorem tangentFiberScIso_comp (α : P.tangentFiber x) :
    tangentFiberScIso hφ hx hψ hx' hs hA hA' 0 (fiberCoordSc hφ hx α) = fiberCoordSc hψ hx' α :=
  Subtype.ext ((coe_tangentFiberScIso_zero hφ hx hψ hx' hs hA hA' _).trans
    (fiberCoord_eq_transitionCLM hφ hx hψ hx' α).symm)

variable {n n' : ℕ} {W W' : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (T' : ScIso ψ.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
  (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hT' : ψ.model.C = T' 0 ⁻¹' quadrant n' W' 0)

lemma mem_partialConeFiberModel_fiberCoordSc (α : P.tangentFiber x) :
    fiberCoordSc hφ hx α ∈ partialConeFiberModel hφ hx T hA ↔ α ∈ partialConeFiber hφ hx T :=
  Iff.rfl

include hT hT' in
/-- **`C_xX` is the same partial quadrant in both charts**: the sc-isomorphism maps the model of
`C_xX` through `φ` onto the model through `ψ`. -/
theorem tangentFiberScIso_image_partialConeFiberModel :
    tangentFiberScIso hφ hx hψ hx' hs hA hA' 0 '' partialConeFiberModel hφ hx T hA =
      partialConeFiberModel hψ hx' T' hA' := by
  have hsurj : ∀ v : φ.model.E.levelSub (tangentFiberModel hφ hx) 0,
      ∃ α, fiberCoordSc hφ hx α = v := fun v =>
    ⟨(tangentFiberEquiv hφ hx).symm ⟨v, v.2⟩, Subtype.ext (by
      change ((tangentFiberEquiv hφ hx ((tangentFiberEquiv hφ hx).symm ⟨v, v.2⟩)) :
        φ.model.E 0) = v
      rw [Equiv.apply_symm_apply])⟩
  have hsurj' : ∀ w : ψ.model.E.levelSub (tangentFiberModel hψ hx') 0,
      ∃ α, fiberCoordSc hψ hx' α = w := fun w =>
    ⟨(tangentFiberEquiv hψ hx').symm ⟨w, w.2⟩, Subtype.ext (by
      change ((tangentFiberEquiv hψ hx' ((tangentFiberEquiv hψ hx').symm ⟨w, w.2⟩)) :
        ψ.model.E 0) = w
      rw [Equiv.apply_symm_apply])⟩
  have hC := partialConeFiber_eq hφ hx T hψ hx' T' hT hT'
  ext w
  obtain ⟨β, rfl⟩ := hsurj' w
  constructor
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨α, rfl⟩ := hsurj v
    rw [tangentFiberScIso_comp] at hvw
    have hαβ : fiberCoord hψ hx' α = fiberCoord hψ hx' β := congrArg Subtype.val hvw
    have hα : α ∈ partialConeFiber hφ hx T := hv
    rw [hC] at hα
    have h1 : fiberCoord hψ hx' α ∈ partialQuadrantAtWith T' (ψ (P.levelVal 1 x)) := hα
    rw [hαβ] at h1
    exact h1
  · intro hβ
    refine ⟨fiberCoordSc hφ hx β, ?_, tangentFiberScIso_comp hφ hx hψ hx' hs hA hA' β⟩
    have hβ' : β ∈ partialConeFiber hψ hx' T' := hβ
    rw [← hC] at hβ'
    exact hβ'

include hT hT' hs in
/-- **Definition 2.5.8 (2021 p. 57), with the chart independence of the sc-structure**: at a
smooth `x`, in a chart `φ` whose model is a tame retract, `C_xX` is a partial quadrant in the
sc-structure of `T_xX` transported by `Tφ(x)`, `d_X(x) = dim(T_xX/T^R_xX) = d_{C_xX}(0_x)`; and for
every other chart `ψ` (with a presentation of its partial quadrant) there is an sc-isomorphism
`T_{φ(x)}O ≅ T_{ψ(x)}O'` carrying `Tφ(x)α` to `Tψ(x)α` and the model of `C_xX` onto the model of
`C_xX`.  So the sc-structure of `T_xX` and the partial quadrant `C_xX` do not depend on the
chart. -/
theorem definition_2_5_8_scStructure (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) (htame : R.IsTameWith T) :
    ∃ (hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx))
      (hA' : ψ.model.E.IsScSubspace (tangentFiberModel hψ hx')),
      IsPartialQuadrant (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) ∧
      P.degIndex (P.levelVal 1 x) = finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) ∧
      finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) =
        Polyfold.degIndex (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) 0 ∧
      ∃ S : ScIso (φ.model.E.ofSubspace hA) (ψ.model.E.ofSubspace hA'),
        (∀ α, S 0 (fiberCoordSc hφ hx α) = fiberCoordSc hψ hx' α) ∧
        S 0 '' partialConeFiberModel hφ hx T hA = partialConeFiberModel hψ hx' T' hA' := by
  obtain ⟨hA, hq, hd1, hd2⟩ := definition_2_5_8_degIndex hφ hx T R hR hT htame hs
  have hA' := isScSubspace_tangentFiberModel hψ hx' hs
  exact ⟨hA, hA', hq, hd1, hd2, tangentFiberScIso hφ hx hψ hx' hs hA hA',
    tangentFiberScIso_comp hφ hx hψ hx' hs hA hA',
    tangentFiberScIso_image_partialConeFiberModel hφ hx hψ hx' hs hA hA' T T' hT hT'⟩

end MPolyfold

end Polyfold
