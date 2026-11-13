import Polyfold.Chapter2.ReducedTangentIntrinsic
import Polyfold.Chapter2.PartialConeQuadrant

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.5, Definition 2.5.8,
p. 57 (preprint Definition 2.38): for tame `X` and smooth `x`, `C_xX` is a partial quadrant in
`T_xX` and `d_X(x) = dim(T_xX / T^R_xX) = d_{C_xX}(0_x)`.

# `C_xX` as a partial quadrant, and `d_{C_xX}(0_x) = d_X(x)`

`ReducedTangentIntrinsic.lean` defines `T^R_xX` and `C_xX` inside `T_xX` and proves they do not
depend on the chart (gap G.13, first part).  This file adds the second part.

## What is formalized

* `degIndex_zero_eq_finrank_quotient` (general, Definition 1.3.3): for a partial quadrant `C` in
  an sc-Banach space `F`, `d_C(0) = dim(F₀ / (C ∩ −C))`.  So the degree of a partial quadrant at
  its apex depends only on the set `C`, not on any presentation or sc-structure.
* `MPolyfold.mem_reducedTangentFiber_iff_lineality`: `T^R_xX = C_xX ∩ −C_xX` inside `T_xX`; this
  holds for every `x ∈ X₁` and every chart.
* `MPolyfold.isPartialQuadrant_partialConeFiberModel`: at a smooth `x`, in any chart `φ` (tame or
  not), `T_{φ(x)}O` is an sc-subspace of the model space and the image of `C_xX` under the linear
  isomorphism `Tφ(x) : T_xX ≅ T_{φ(x)}O` is a partial quadrant in the sc-Banach space
  `T_{φ(x)}O` (from Remark 2.4.8 as formalized, `remark_2_4_8_isPartialQuadrant`);
  `MPolyfold.mem_partialConeFiberModel_iff` identifies the set with the image of `C_xX`.
* `MPolyfold.definition_2_5_8_degIndex`: for every such sc-structure, `d_{C_xX}(0_x)` computed in
  `T_{φ(x)}O` equals `dim(T_xX / T^R_xX)`, and in a tame chart both equal `d_X(x)`.

## Not formalized

The sc-structure of `T_xX` itself: here `T_xX` carries the sc-structure of `T_{φ(x)}O` transported
by `Tφ(x)`, for a chosen chart.  That two charts give the same sc-structure would need the
transition derivative `T_{φ(x)}O → T_{ψ(x)}O` to be an sc-isomorphism at a smooth point (only its
level-0 part, `transitionCLM`, is in the library).  The degree `d_{C_xX}(0_x)` does not depend on
the choice, by `degIndex_zero_eq_finrank_quotient` and `mem_reducedTangentFiber_iff_lineality`.
-/

open Set Function Topology Module

noncomputable section

namespace Polyfold

/-- **Definition 1.3.3 at the apex**: for a partial quadrant `C ⊆ F`, `d_C(0) = dim(F₀/(C ∩ −C))`,
for any subspace `S` with `S = C ∩ −C`. -/
theorem degIndex_zero_eq_finrank_quotient {F : ScBanach} {C : Set (F 0)}
    (hC : IsPartialQuadrant F C) (S : Submodule ℝ (F 0)) (hS : ∀ v, v ∈ S ↔ v ∈ C ∧ -v ∈ C) :
    degIndex F C 0 = finrank ℝ (F 0 ⧸ S) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  have h0 : (0 : F 0) ∈ T 0 ⁻¹' quadrant n W 0 := fun i => by simp
  have hSeq : S = minimalSubspaceWith T 0 := by
    ext v
    rw [hS, mem_minimalSubspaceWith]
    simp only [mem_preimage, quadrant, mem_ofPred_eq, map_neg, map_zero, Prod.fst_neg,
      Prod.fst_zero, Pi.neg_apply, Pi.zero_apply, neg_nonneg, true_implies]
    exact ⟨fun h i => le_antisymm (h.2 i) (h.1 i), fun h => ⟨fun i => (h i).ge, fun i => (h i).le⟩⟩
  rw [degIndex_eq T rfl h0, hSeq, finrank_quotient_minimalSubspaceWith]

/-- `C_e ∩ −C_e = E_e` for the partial quadrant `C_e` at `e` (presentation `T`). -/
lemma mem_minimalSubspaceWith_iff_lineality {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e v : E 0) :
    v ∈ minimalSubspaceWith T e ↔
      v ∈ partialQuadrantAtWith T e ∧ -v ∈ partialQuadrantAtWith T e := by
  rw [mem_minimalSubspaceWith]
  simp only [partialQuadrantAtWith, mem_ofPred_eq, map_neg, Prod.fst_neg, Pi.neg_apply,
    neg_nonneg]
  exact ⟨fun h => ⟨fun i hi => (h i hi).ge, fun i hi => (h i hi).le⟩,
    fun h i hi => le_antisymm (h.2 i hi) (h.1 i hi)⟩

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} {x : P.Level 1} (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source)
variable {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- **Definition 2.5.8 (2021 p. 57)**: `T^R_xX = C_xX ∩ −C_xX`, so `T^R_xX` is determined by the
set `C_xX`.  For every `x ∈ X₁` and every chart. -/
theorem mem_reducedTangentFiber_iff_lineality (α : P.tangentFiber x) :
    α ∈ reducedTangentFiber hφ hx T ↔
      α ∈ partialConeFiber hφ hx T ∧ -α ∈ partialConeFiber hφ hx T := by
  simp only [reducedTangentFiber, partialConeFiber, Submodule.mem_comap, mem_preimage, map_neg]
  exact mem_minimalSubspaceWith_iff_lineality T _ _

/-- The model of `C_xX` in the sc-Banach space `T_{φ(x)}O`: the `v ∈ T_{φ(x)}O` with
`v ∈ C_{φ(x)}`. -/
def partialConeFiberModel (hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx)) :
    Set ((φ.model.E.ofSubspace hA) 0) :=
  {v : φ.model.E.levelSub (tangentFiberModel hφ hx) 0 |
    (v : φ.model.E 0) ∈ partialQuadrantAtWith T (φ (P.levelVal 1 x))}

/-- The model set is the image of `C_xX` under `Tφ(x) : T_xX ≅ T_{φ(x)}O`. -/
theorem mem_partialConeFiberModel_iff (hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx))
    (v : φ.model.E.levelSub (tangentFiberModel hφ hx) 0) :
    v ∈ partialConeFiberModel hφ hx T hA ↔
      (tangentFiberLinearEquiv hφ hx).symm ⟨(v : φ.model.E 0), v.2⟩ ∈
        partialConeFiber hφ hx T := by
  rw [partialConeFiber, mem_preimage, fiberCoord]
  simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Submodule.coe_subtype]
  rfl

/-- **Definition 2.5.8 (2021 p. 57): `C_xX` is a partial quadrant** at a smooth `x`, in the
sc-structure of `T_{φ(x)}O` transported to `T_xX` by `Tφ(x)`: `T_{φ(x)}O` is an sc-subspace and
the model of `C_xX` is a partial quadrant in it.  No tameness is needed (Remark 2.4.8 as
formalized). -/
theorem isPartialQuadrant_partialConeFiberModel
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hs : P.levelVal 1 x ∈ P.smoothSet) :
    ∃ hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx),
      IsPartialQuadrant (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) := by
  set R := φ.model.isScRetract.choose with hRdef
  have hR : R.retract = φ.model.O := φ.model.isScRetract.choose_spec
  have haR : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR]; exact levelLift_mem_lvlSet_one hφ hx
  have has : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.smoothLvl 1 :=
    (mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hx).1 hs
  have heq : tangentFiberModel hφ hx =
      LinearMap.range (scDeriv R.U R (levelLift φ 1 (P.levelVal 1 x)) :
        φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    apply SetLike.coe_injective
    rw [coe_tangentFiberModel, ← hR]
    exact tangentSpace_eq_coe_submodule R haR
  obtain ⟨hA, -, hq⟩ := remark_2_4_8_isPartialQuadrant (R := R) hT haR has
  have hbase : φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) = φ (P.levelVal 1 x) :=
    P.toBase_levelLift hφ hx (levelVal_mem x)
  rw [hbase] at hq
  unfold partialConeFiberModel
  rw [heq]
  exact ⟨hA, hq⟩

/-- **Definition 2.5.8 (2021 p. 57): `d_{C_xX}(0_x) = dim(T_xX/T^R_xX)`**, for the sc-structure of
`T_{φ(x)}O` on `T_xX` (any chart `φ`, any `x ∈ X₁`, whenever the model of `C_xX` is a partial
quadrant). -/
theorem degIndex_partialConeFiberModel_eq_finrank
    (hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx))
    (hq : IsPartialQuadrant (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA)) :
    Polyfold.degIndex (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) 0 =
      finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) := by
  set A := tangentFiberModel hφ hx
  -- `T_xX ≃ T_{φ(x)}O ≃ (T_{φ(x)}O)₀`
  let e₁ : φ.model.E.levelSub A 0 ≃ₗ[ℝ] A :=
    LinearEquiv.ofEq _ _ (ScBanach.levelSub_zero φ.model.E A)
  let e : P.tangentFiber x ≃ₗ[ℝ] φ.model.E.levelSub A 0 :=
    (tangentFiberLinearEquiv hφ hx).trans e₁.symm
  have he : ∀ α, ((e α : φ.model.E.levelSub A 0) : φ.model.E 0) = fiberCoord hφ hx α :=
    fun _ => rfl
  set S := (reducedTangentFiber hφ hx T).map e.toLinearMap
  have hS : ∀ v, v ∈ S ↔ v ∈ partialConeFiberModel hφ hx T hA ∧
      -v ∈ partialConeFiberModel hφ hx T hA := by
    intro v
    have h1 : ∀ w, e.symm w ∈ partialConeFiber hφ hx T ↔
        (w : φ.model.E 0) ∈ partialQuadrantAtWith T (φ (P.levelVal 1 x)) := fun w => by
      change fiberCoord hφ hx (e.symm w) ∈ partialQuadrantAtWith T (φ (P.levelVal 1 x)) ↔ _
      rw [← he, e.apply_symm_apply]
    rw [Submodule.mem_map_equiv, mem_reducedTangentFiber_iff_lineality, ← map_neg, h1, h1]
    exact Iff.rfl
  rw [degIndex_zero_eq_finrank_quotient hq S hS]
  exact (LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e rfl)).symm

/-- **Definition 2.5.8 (2021 p. 57), as printed for tame `X`**: at a smooth `x`, in a chart whose
model is a tame retract, `C_xX` is a partial quadrant (for the sc-structure of `T_{φ(x)}O`
transported by `Tφ(x)`), and `d_X(x) = dim(T_xX / T^R_xX) = d_{C_xX}(0_x)`. -/
theorem definition_2_5_8_degIndex (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)
    (htame : R.IsTameWith T) (hs : P.levelVal 1 x ∈ P.smoothSet) :
    ∃ hA : φ.model.E.IsScSubspace (tangentFiberModel hφ hx),
      IsPartialQuadrant (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) ∧
      P.degIndex (P.levelVal 1 x) = finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) ∧
      finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) =
        Polyfold.degIndex (φ.model.E.ofSubspace hA) (partialConeFiberModel hφ hx T hA) 0 := by
  obtain ⟨hA, hq⟩ := isPartialQuadrant_partialConeFiberModel hφ hx T hT hs
  exact ⟨hA, hq, (finrank_quotient_reducedTangentFiber_eq_degIndex hφ hx T R hR hT htame hs).symm,
    (degIndex_partialConeFiberModel_eq_finrank hφ hx T hA hq).symm⟩

end MPolyfold

end Polyfold
