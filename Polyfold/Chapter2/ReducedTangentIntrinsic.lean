import Polyfold.Chapter2.TangentSpaceLinear
import Polyfold.Chapter2.TameRetracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.5, Definition 2.5.8,
p. 57 (preprint: Definition 2.38, p. 42): the reduced tangent space `T^R_xX` and the partial cone
`C_xX` of an M-polyfold at a smooth point, and `d_X(x) = dim(T_xX / T^R_xX)`.

# `T^R_xX` and `C_xX` inside `T_xX`

## The text, paraphrased

(2021 Definition 2.5.8, p. 57) For a smooth `x ∈ X` and a chart `ψ` around `x`, the reduced
tangent space `T^R_xX ⊆ T_xX` and the partial cone `C_xX ⊆ T_xX` are the preimages under
`Tψ(x) : T_xX → T_{ψ(x)}O` of `T^R_{ψ(x)}O` and `C_{ψ(x)}O` (Definition 2.4.7); by Proposition
2.4.10 they do not depend on the chart.  For tame `X`, `C_xX` is a partial quadrant in `T_xX` and
`d_X(x) = dim(T_xX / T^R_xX) = d_{C_xX}(0_x)`.

## What is formalized (gap G.13 of `Exposition/cmp/ch02.json`)

* `MPolyfold.fiberCoord hφ hx : T_xX →ₗ[ℝ] E`, the linear map `Tφ(x)` followed by the inclusion
  `T_{φ(x)}O ⊆ E` (through `tangentFiberLinearEquiv`, gap G.7).
* **`MPolyfold.reducedTangentFiber hφ hx T : Submodule ℝ (T_xX)`** (`T^R_xX`) and
  **`MPolyfold.partialConeFiber hφ hx T : Set (T_xX)`** (`C_xX`), defined through the chart `φ`
  and a presentation `T` of its partial quadrant; `mem_reducedTangentFiber_iff`,
  `mem_partialConeFiber_iff` identify them with the preimages of `T^R_{φ(x)}O`, `C_{φ(x)}O`
  (`reducedTangentSpaceWith`, `partialConeWith`, for any retraction onto an open piece of `O`
  around `φ(x)`).
* **`MPolyfold.reducedTangentFiber_eq`, `MPolyfold.partialConeFiber_eq`**: they do not depend on
  the chart or the presentation (Proposition 2.4.10, `proposition_2_4_10_reduced`,
  `proposition_2_4_10_cone`, applied to the transition germ on the overlap retracts, with the
  locality of `T_{φ(x)}O` and the identification of the transition derivative with the fibre
  transition `transitionCLM` of Definition 2.3.14).  This holds for every `x ∈ X₁`, not only
  smooth `x`.
* **`MPolyfold.finrank_quotient_reducedTangentFiber_eq_degIndex`**: in a tame chart at a smooth
  `x`, `dim(T_xX / T^R_xX) = d_X(x)` (Definition 2.5.8 with Proposition 2.5.6 (13),
  `quotDim_reducedTangentSpaceWith_eq`).

## What the text leaves implicit, and the choices made

* The text's "preimage under `Tψ(x)`" is the preimage of the chart model's `T^R_{ψ(x)}O`,
  `C_{ψ(x)}O` under the linear isomorphism `Tψ(x) : T_xX → T_{ψ(x)}O` of Definition 2.3.14;
  here these are `reducedTangentSpaceWith R T a ⊓ ...` pulled back along `fiberCoord`, where the
  retraction `R` drops out because `T_{φ(x)}O = Dr(φ(x))E` for every retraction.  The
  presentation `T` of `C` enters as in Definition 2.4.7 (`reducedTangentSpaceWith`), and the
  independence statement covers it.
* Not formalized: `C_xX` as a partial quadrant in `T_xX` and `d_{C_xX}(0_x) = d_X(x)` (the chart
  form is `proposition_2_5_6_partialCone`, `PartialCone.lean`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ ψ : MChart X} {x : P.Level 1} (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source)

/-- `Tφ(x) : T_xX → E`, the chart map on the fibre followed by `T_{φ(x)}O ⊆ E`. -/
def fiberCoord : P.tangentFiber x →ₗ[ℝ] φ.model.E 0 :=
  (tangentFiberModel hφ hx).subtype ∘ₗ (tangentFiberLinearEquiv hφ hx : _ →ₗ[ℝ] _)

lemma fiberCoord_apply (α : P.tangentFiber x) :
    fiberCoord hφ hx α = (tangentChartMap hφ α.1).2 := rfl

lemma fiberCoord_eq_coe (α : P.tangentFiber x) :
    fiberCoord hφ hx α = (tangentFiberEquiv hφ hx α : φ.model.E 0) := rfl

/-- `Tφ(x)(T_xX) ⊆ Dr(φ(x))E` for any retraction `r` onto an open piece `φ(s)` of `O` around
`φ(x)` (locality of `T_{φ(x)}O`). -/
lemma fiberCoord_mem_range_scDeriv {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    (hxs : P.levelVal 1 x ∈ s) (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ '' s)
    (α : P.tangentFiber x) :
    fiberCoord hφ hx α ∈ range (scDeriv R.U R (levelLift φ 1 (P.levelVal 1 x))) := by
  have haR : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, P.toBase_levelLift hφ hx (levelVal_mem x)]
    exact ⟨_, hxs, rfl⟩
  have h : ((levelLift φ 1 (P.levelVal 1 x), fiberCoord hφ hx α) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C (φ '' s) := by
    refine (TangentPre.mem_retractTangent_image_iff hs hso ?_).2
      ((mem_tangentFiberModel hφ hx).1 (tangentFiberEquiv hφ hx α).2)
    change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ '' s
    rw [P.toBase_levelLift hφ hx (levelVal_mem x)]
    exact ⟨_, hxs, rfl⟩
  rw [← hR, retractTangent_eq] at h
  exact (R.mem_tangent_iff_mem_range haR).1 h

/-- `Dr(a)v = v` for `v ∈ Dr(a)E`. -/
lemma _root_.Polyfold.ScRetraction.scDeriv_apply_eq_self_of_mem_range {E : ScBanach} {C : Set (E 0)}
    (R : ScRetraction E C) {a : E 1} (ha : a ∈ E.lvlSet R.retract 1) {v : E 0}
    (hv : v ∈ range (scDeriv R.U R a)) : scDeriv R.U R a v = v :=
  (R.mem_tangent_iff_of_mem ha).1 ((R.mem_tangent_iff_mem_range ha).2 hv)

variable {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- **Definition 2.5.8 (2021 p. 57): the reduced tangent space `T^R_xX ⊆ T_xX`**, the preimage of
`T^R_{φ(x)}O = T_{φ(x)}O ∩ E_{φ(x)}` under `Tφ(x)`, for a chart `φ` around `x` with a presentation
`T` of its partial quadrant.  Independent of `(φ, T)`: `reducedTangentFiber_eq`. -/
def reducedTangentFiber : Submodule ℝ (P.tangentFiber x) :=
  (minimalSubspaceWith T (φ (P.levelVal 1 x))).comap (fiberCoord hφ hx)

/-- **Definition 2.5.8 (2021 p. 57): the partial cone `C_xX ⊆ T_xX`**, the preimage of
`C_{φ(x)}O = T_{φ(x)}O ∩ C_{φ(x)}` under `Tφ(x)`.  Independent of `(φ, T)`:
`partialConeFiber_eq`. -/
def partialConeFiber : Set (P.tangentFiber x) :=
  fiberCoord hφ hx ⁻¹' partialQuadrantAtWith T (φ (P.levelVal 1 x))

/-- `T^R_xX` is the preimage of `T^R_{φ(x)}O` (Definition 2.4.7, `reducedTangentSpaceWith`) for any
retraction onto an open piece of `O` around `φ(x)`. -/
theorem mem_reducedTangentFiber_iff {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    (hxs : P.levelVal 1 x ∈ s) (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ '' s)
    {α : P.tangentFiber x} :
    α ∈ reducedTangentFiber hφ hx T ↔
      fiberCoord hφ hx α ∈ reducedTangentSpaceWith R T (levelLift φ 1 (P.levelVal 1 x)) := by
  rw [reducedTangentFiber, Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf,
    P.toBase_levelLift hφ hx (levelVal_mem x)]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  obtain ⟨u, hu⟩ := fiberCoord_mem_range_scDeriv hφ hx hs hso hxs R hR α
  exact ⟨u, hu⟩

/-- `C_xX` is the preimage of `C_{φ(x)}O` (Definition 2.4.7, `partialConeWith`). -/
theorem mem_partialConeFiber_iff {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    (hxs : P.levelVal 1 x ∈ s) (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ '' s)
    {α : P.tangentFiber x} :
    α ∈ partialConeFiber hφ hx T ↔
      fiberCoord hφ hx α ∈ partialConeWith R T (levelLift φ 1 (P.levelVal 1 x)) := by
  rw [partialConeFiber, mem_preimage, partialConeWith, mem_inter_iff,
    P.toBase_levelLift hφ hx (levelVal_mem x)]
  exact ⟨fun h => ⟨fiberCoord_mem_range_scDeriv hφ hx hs hso hxs R hR α, h⟩, fun h => h.2⟩

/-- `T^R_xX ⊆ C_xX` (Remark 2.4.8). -/
theorem reducedTangentFiber_subset_partialConeFiber :
    (reducedTangentFiber hφ hx T : Set (P.tangentFiber x)) ⊆ partialConeFiber hφ hx T :=
  fun _ h => minimalSubspaceWith_subset_partialQuadrantAtWith T _ h

/-! ### Independence of the chart (Proposition 2.4.10) -/

section Transition

variable (hψ : P.IsChart ψ) (hx' : P.levelVal 1 x ∈ ψ.source)

include hφ hψ hx hx' in
/-- The transition germ on the overlap retracts, and the identification of its derivative at
`φ(x)` with the fibre transition of Definition 2.3.14: for retractions `R` onto `φ(V ∩ V')` and
`R'` onto `ψ(V ∩ V')`, `(φ.transition ψ, ψ.transition φ)` is a germ of sc-diffeomorphisms,
`φ(x) ∈ R(U)₁`, `(ψ ∘ φ⁻¹ ∘ r)(φ(x)) = ψ(x)` on level `1`, and
`D(ψ ∘ φ⁻¹ ∘ r)(φ(x)) (Tφ(x) α) = Tψ(x) α` for every `α ∈ T_xX`. -/
theorem exists_isDiffeoGerm_transition :
    ∃ (R : ScRetraction φ.model.E φ.model.C) (R' : ScRetraction ψ.model.E ψ.model.C),
      R.retract = φ.overlap ψ ∧ R'.retract = ψ.overlap φ ∧
      R.IsDiffeoGerm R' (φ.transition ψ) (ψ.transition φ) ∧
      levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.retract 1 ∧
      levelMap (φ.transition ψ ∘ R) 1 (levelLift φ 1 (P.levelVal 1 x)) =
        levelLift ψ 1 (P.levelVal 1 x) ∧
      ∀ α : P.tangentFiber x,
        scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 (P.levelVal 1 x)) (fiberCoord hφ hx α) =
          fiberCoord hψ hx' α := by
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  obtain ⟨R', hR'⟩ := ψ.isScRetract_overlap φ
  have hcomp := (hφ.compatible hψ (P := P)).1
  have hcomp' := (hψ.compatible hφ (P := P)).1
  have hF : IsScSmoothRetractMap φ.model.E φ.model.C R.retract ψ.model.E ψ.model.C R'.retract
      (φ.transition ψ) := by rw [hR, hR']; exact hcomp
  have hG : IsScSmoothRetractMap ψ.model.E ψ.model.C R'.retract φ.model.E φ.model.C R.retract
      (ψ.transition φ) := by rw [hR, hR']; exact hcomp'
  have hgerm : R.IsDiffeoGerm R' (φ.transition ψ) (ψ.transition φ) := by
    refine hF.isDiffeoGerm hG ?_ ?_
    · rw [hR]; rintro _ ⟨y, hy, rfl⟩
      rw [φ.transition_apply ψ hy.1, ψ.transition_apply φ hy.2]
    · rw [hR']; rintro _ ⟨y, hy, rfl⟩
      rw [ψ.transition_apply φ hy.1, φ.transition_apply ψ hy.2]
  have hmemO : φ (P.levelVal 1 x) ∈ R.retract := by rw [hR]; exact φ.mem_overlap ψ hx hx'
  have haR : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ hx (levelVal_mem x)]; exact hmemO
  have haU : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.U 1 :=
    R.lvlSet_retract_subset 1 haR
  have hsm : IsScSmooth R.U (φ.transition ψ ∘ R) := hF.comp_isScSmooth R rfl
  refine ⟨R, R', hR, hR', hgerm, haR, ?_, fun α => ?_⟩
  · apply ψ.model.E.toBase_injective 1
    rw [hsm.isSc1.isSc0.toBase_levelMap haU, Function.comp_apply,
      P.toBase_levelLift hφ hx (levelVal_mem x), R.apply_eq_self_of_mem_retract hmemO,
      φ.transition_apply ψ hx, P.toBase_levelLift hψ hx' (levelVal_mem x)]
  · have hmem : ((levelLift φ 1 (P.levelVal 1 x), fiberCoord hφ hx α) : φ.model.E.tangent 0) ∈
        retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
      refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
        (φ.isOpen_source.inter ψ.isOpen_source) ?_).2
        ((mem_tangentFiberModel hφ hx).1 (tangentFiberEquiv hφ hx α).2)
      change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ '' (φ.source ∩ ψ.source)
      rw [P.toBase_levelLift hφ hx (levelVal_mem x)]
      exact ⟨_, ⟨hx, hx'⟩, rfl⟩
    have h1 := retractTangentMap_apply hcomp R hR hmem
    have h2 := transitionCLM_spec hφ hx hψ hx' (tangentFiberEquiv hφ hx α).2
    have h3 := coe_tangentFiberEquiv_symm_trans hφ hx hψ hx' (tangentFiberEquiv hφ hx α)
    rw [Equiv.symm_apply_apply] at h3
    calc scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 (P.levelVal 1 x)) (fiberCoord hφ hx α)
        = (retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
            (levelLift φ 1 (P.levelVal 1 x), fiberCoord hφ hx α)).2 := by rw [h1]
      _ = transitionCLM hφ hx hψ hx' (fiberCoord hφ hx α) := by
          rw [fiberCoord_eq_coe, h2]
      _ = fiberCoord hψ hx' α := h3.symm

variable {n' : ℕ} {W' : ScBanach} (T' : ScIso ψ.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
  (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hT' : ψ.model.C = T' 0 ⁻¹' quadrant n' W' 0)

include hT hT' in
/-- **Definition 2.5.8 (2021 p. 57), the well-definedness of `T^R_xX`** (Proposition 2.4.10,
preprint 2.30): the reduced tangent space does not depend on the chart or the presentation. -/
theorem reducedTangentFiber_eq :
    reducedTangentFiber hφ hx T = reducedTangentFiber hψ hx' T' := by
  obtain ⟨R, R', hR, hR', hgerm, haR, hb, hkey⟩ :=
    exists_isDiffeoGerm_transition hφ hx hψ hx'
  have hmap := proposition_2_4_10_reduced hgerm haR T hT T' hT'
  ext α
  rw [mem_reducedTangentFiber_iff hφ hx T inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source) ⟨hx, hx'⟩ R hR,
    mem_reducedTangentFiber_iff hψ hx' T' inter_subset_left
      (ψ.isOpen_source.inter φ.isOpen_source) ⟨hx', hx⟩ R' hR',
    ← hb, ← hkey α, ← hmap, Submodule.mem_map]
  constructor
  · intro hv; exact ⟨_, hv, rfl⟩
  · rintro ⟨u, hu, huv⟩
    have hv := fiberCoord_mem_range_scDeriv hφ hx inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source) ⟨hx, hx'⟩ R hR α
    have hu' : u ∈ range (scDeriv R.U R (levelLift φ 1 (P.levelVal 1 x))) := by
      obtain ⟨k, hk⟩ := hu.1; exact ⟨k, hk⟩
    have h1 := hgerm.deriv_inv_deriv haR u
    have h2 := hgerm.deriv_inv_deriv haR (fiberCoord hφ hx α)
    rw [R.scDeriv_apply_eq_self_of_mem_range haR hu'] at h1
    rw [R.scDeriv_apply_eq_self_of_mem_range haR hv] at h2
    change scDeriv R.U (φ.transition ψ ∘ R) _ u = scDeriv R.U (φ.transition ψ ∘ R) _ _ at huv
    rw [← h2, ← huv, h1]
    exact hu

include hT hT' in
/-- **Definition 2.5.8 (2021 p. 57), the well-definedness of `C_xX`** (Proposition 2.4.10,
preprint 2.30): the partial cone does not depend on the chart or the presentation. -/
theorem partialConeFiber_eq :
    partialConeFiber hφ hx T = partialConeFiber hψ hx' T' := by
  obtain ⟨R, R', hR, hR', hgerm, haR, hb, hkey⟩ :=
    exists_isDiffeoGerm_transition hφ hx hψ hx'
  have hmap := proposition_2_4_10_cone hgerm haR T hT T' hT'
  ext α
  rw [mem_partialConeFiber_iff hφ hx T inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source) ⟨hx, hx'⟩ R hR,
    mem_partialConeFiber_iff hψ hx' T' inter_subset_left
      (ψ.isOpen_source.inter φ.isOpen_source) ⟨hx', hx⟩ R' hR',
    ← hb, ← hkey α, ← hmap, mem_image]
  constructor
  · intro hv; exact ⟨_, hv, rfl⟩
  · rintro ⟨u, hu, huv⟩
    have hv := fiberCoord_mem_range_scDeriv hφ hx inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source) ⟨hx, hx'⟩ R hR α
    have h1 := hgerm.deriv_inv_deriv haR u
    have h2 := hgerm.deriv_inv_deriv haR (fiberCoord hφ hx α)
    rw [R.scDeriv_apply_eq_self_of_mem_range haR hu.1] at h1
    rw [R.scDeriv_apply_eq_self_of_mem_range haR hv] at h2
    rw [← h2, ← huv, h1]
    exact hu

end Transition

/-! ### `dim(T_xX / T^R_xX) = d_X(x)` in a tame chart -/

/-- `T^R_xX` corresponds to `T^R_{φ(x)}O ⊆ T_{φ(x)}O` under `Tφ(x) : T_xX ≃ₗ T_{φ(x)}O`. -/
theorem map_reducedTangentFiber (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) :
    (reducedTangentFiber hφ hx T).map (tangentFiberLinearEquiv hφ hx : _ →ₗ[ℝ] _) =
      (reducedTangentSpaceWith R T (levelLift φ 1 (P.levelVal 1 x))).comap
        (tangentFiberModel hφ hx).subtype := by
  have hR' : R.retract = φ '' φ.source := by rw [hR, φ.image_source]
  ext w
  rw [Submodule.mem_map, Submodule.mem_comap]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact (mem_reducedTangentFiber_iff hφ hx T subset_rfl φ.isOpen_source hx R hR').1 hα
  · intro hw
    refine ⟨(tangentFiberLinearEquiv hφ hx).symm w, ?_, by simp⟩
    rw [mem_reducedTangentFiber_iff hφ hx T subset_rfl φ.isOpen_source hx R hR',
      fiberCoord_eq_coe, tangentFiberLinearEquiv_symm_apply, Equiv.apply_symm_apply]
    exact hw

/-- **Definition 2.5.8 (2021 p. 57) with Proposition 2.5.6 (13): `d_X(x) = dim(T_xX / T^R_xX)`**
at a smooth `x`, in a chart whose model is a tame retract (for the presentation `T`). -/
theorem finrank_quotient_reducedTangentFiber_eq_degIndex (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (htame : R.IsTameWith T)
    (hs : P.levelVal 1 x ∈ P.smoothSet) :
    Module.finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) =
      P.degIndex (P.levelVal 1 x) := by
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
  have hxC : φ (P.levelVal 1 x) ∈ φ.model.C :=
    φ.model.isScRetract.choose.retract_subset_C (by
      rw [φ.model.isScRetract.choose_spec]; exact φ.mapsTo_model _ hx)
  have hquot : Module.finrank ℝ (P.tangentFiber x ⧸ reducedTangentFiber hφ hx T) =
      quotDim (tangentFiberModel hφ hx)
        (reducedTangentSpaceWith R T (levelLift φ 1 (P.levelVal 1 x))) :=
    LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ (tangentFiberLinearEquiv hφ hx)
      (map_reducedTangentFiber hφ hx T R hR))
  rw [hquot, quotDim_congr heq rfl, quotDim_reducedTangentSpaceWith_eq htame haR has,
    P.toBase_levelLift hφ hx (levelVal_mem x), ← degIndex_eq T hT hxC,
    degIndex_eq_chartDegIndex_of_isTameWith P hφ R hR hT htame hx]
  rfl

end MPolyfold

end Polyfold
