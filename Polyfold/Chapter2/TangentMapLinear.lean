import Polyfold.Chapter2.TangentSpaceLinear
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, Definition 2.3.14
and Theorem 2.3.16, pp. 39–40 (preprint: Definition 2.18 and the paragraph after Proposition 2.19,
pp. 26–27): the tangent map `Tf : TX → TY` of an sc-smooth map is linear on the fibres.

# Tangent maps are linear on the fibres `T_xX → T_{f(x)}Y`

## The text, paraphrased

(2021 p. 39) `T_xX` is a vector space, a Banach space through any chart, an sc-Banach space at a
smooth `x`.  (Theorem 2.3.16 and the discussion around it, p. 40) The tangent construction is
functorial, `Tf : TX → TY` is sc-smooth and covers `f`; in charts `Tf` is `T(ψ ∘ f ∘ φ⁻¹)`,
`(a, h) ↦ (g(a), Dg(a)h)` (Definition 2.1.14), so on each fibre it is the bounded linear map
`Dg(φ(x))`, an sc-operator at a smooth `x` (Proposition 1.2.3).

## What is formalized (gaps G.7 and G.70; rows V2.19, V2.21, V2.94)

* `MPolyfold.tangentMapOnFiber hf hxU hxy : T_xX → T_{f(x)}Y`, the restriction of `Tf` to the
  fibres, for a map `f` sc-smooth on an open set `U ∋ x` (Chapter 8's `tangentMapOn`).
* **`MPolyfold.exists_clm_tangentMapOnFiber`**: in charts `φ` around `x`, `ψ` around `f(x)`,
  `Tf` is given on the fibre by a continuous linear map `L = D(ψ ∘ f ∘ φ⁻¹ ∘ r)(φ(x)) : E → E'`
  (`Tψ ∘ Tf = L ∘ Tφ` on `T_xX`), and **`L` is an sc-operator if `x` is smooth**.
* **`MPolyfold.tangentMapOnCLM hf hxU hxy : T_xX →L[ℝ] T_{f(x)}Y`**: `Tf` is a continuous linear
  map on the fibres, in the linear structure of Definition 2.3.14
  (`tangentMapOnCLM_apply`); `MPolyfold.tangentMapCLM` is the version for a globally sc-smooth
  map (Part I's `tangentMap`).
* `MPolyfold.theorem_2_3_16_linear_2021`: the bundle (additive, homogeneous, continuous on the
  fibres, and the chart description).

## What the text leaves implicit, and the choices made

* The text never states fibrewise linearity of `Tf` separately; it is implicit in "`Tf` is a
  bundle map" and in the formula `Tf(a, h) = (f(a), Df(a)h)`.  The formal statement needs the
  chart-independent linear structure of `T_xX` (`TangentSpaceLinear.lean`), whose chart
  descriptions are `tangentFiberEquiv`.
* The continuous linear map `tangentMapOnCLM` is built through the chosen charts
  `P.fiberChart x`, `Q.fiberChart y`; its values do not depend on them (`tangentMapOnCLM_apply`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
variable {f : X → Y} {U : Set X} (hf : P.IsScSmoothOn Q f U) {x : P.Level 1} {y : Q.Level 1}
  (hxU : P.levelVal 1 x ∈ U) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y)

/-- **`Tf : T_xX → T_{f(x)}Y`**, the restriction of the tangent map of a map `f` sc-smooth on an
open set `U ∋ x` to the fibres. -/
def tangentMapOnFiber : P.tangentFiber x → Q.tangentFiber y := fun α =>
  ⟨tangentMapOn hf α.1, tangentMapOn_mapsTo_fiber hf x hxU y hxy α.2⟩

lemma tangentMapOnFiber_val (α : P.tangentFiber x) :
    (tangentMapOnFiber hf hxU hxy α : Q.TangentSpace) = tangentMapOn hf α.1 := rfl

/-- **`Tf` is linear in charts, and an sc-operator at a smooth point** (2021 pp. 39–40): for
charts `φ` around `x` and `ψ` around `f(x)`, `Tψ ∘ Tf = L ∘ Tφ` on `T_xX` for the continuous
linear map `L = D(ψ ∘ f ∘ φ⁻¹ ∘ r)(φ(x)) : E → E'` (Definition 2.1.14 through
`retractTangentMap_apply`); if `x` is smooth, `L` is an sc-operator (Proposition 1.2.3). -/
theorem exists_clm_tangentMapOnFiber {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ)
    (hψ : Q.IsChart ψ) (hxφ : P.levelVal 1 x ∈ φ.source) (hyψ : Q.levelVal 1 y ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      (∀ α : P.tangentFiber x,
        (tangentFiberEquiv hψ hyψ (tangentMapOnFiber hf hxU hxy α) : ψ.model.E 0) =
          L (tangentFiberEquiv hφ hxφ α)) ∧
      (P.levelVal 1 x ∈ P.smoothSet → IsScOperator L) := by
  have hVo : IsOpen (TangentPre.fdomOn U φ f ψ) := TangentPre.isOpen_fdomOn hf φ ψ
  have hVφ : TangentPre.fdomOn U φ f ψ ⊆ φ.source := TangentPre.fdomOn_subset _ _ _ _
  have hsm : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' TangentPre.fdomOn U φ f ψ)
      ψ.model.E ψ.model.C ψ.model.O (ψ ∘ f ∘ φ.symm) :=
    hf.smooth φ ψ hφ hψ _ hVo (fun _ h => h.1) (fun _ h => h.2)
  obtain ⟨R, hR⟩ := φ.isScRetract_image hVφ hVo
  have hxV : P.levelVal 1 x ∈ TangentPre.fdomOn U φ f ψ := by
    refine ⟨⟨hxU, hxφ⟩, ?_⟩
    change f (P.levelVal 1 x) ∈ ψ.source
    rw [hxy]; exact hyψ
  have haO : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, P.toBase_levelLift hφ hxφ (levelVal_mem x)]
    exact ⟨_, hxV, rfl⟩
  have haU : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet R.U 1 :=
    R.lvlSet_retract_subset 1 haO
  refine ⟨scDeriv R.U ((ψ ∘ f ∘ φ.symm) ∘ R) (levelLift φ 1 (P.levelVal 1 x)), fun α => ?_,
    fun hs => ?_⟩
  · have hmem : α.1 ∈ P.tangentPreimage (TangentPre.fdomOn U φ f ψ) := by
      rw [mem_tangentPreimage, tangentProj_eq_of_mem_fiber α.2]; exact hxV
    have hαV : tangentChartMap hφ α.1 ∈ retractTangent φ.model.E φ.model.C
        (φ '' TangentPre.fdomOn U φ f ψ) := by
      refine (TangentPre.mem_retractTangent_image_iff hVφ hVo ?_).2
        (tangentChartMap_mem hφ (mem_tangentChartSet_of_mem_fiber hxφ α.2))
      rw [tangentChartMap_fst_of_mem_fiber hφ hxφ α.2, P.toBase_levelLift hφ hxφ (levelVal_mem x)]
      exact ⟨_, hxV, rfl⟩
    rw [coe_tangentFiberEquiv_apply, coe_tangentFiberEquiv_apply, tangentMapOnFiber_val,
      tangentChartMap_tangentMapOn hf hφ hψ hmem, retractTangentMap_apply hsm R hR hαV]
    change scDeriv R.U _ (tangentChartMap hφ α.1).1 _ = _
    rw [tangentChartMap_fst_of_mem_fiber hφ hxφ α.2]
  · have has : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.smoothLvl 1 :=
      (mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hxφ).1 hs
    exact (hsm.comp_isScSmooth R hR).isSc1.isSc1With_scDeriv.scOperator_deriv haU has

/-- **`Tf : T_xX →L[ℝ] T_{f(x)}Y`** (2021 pp. 39–40): the tangent map of a map sc-smooth near
`x` is a continuous linear map on the fibres. -/
def tangentMapOnCLM : P.tangentFiber x →L[ℝ] Q.tangentFiber y :=
  fiberMapCLM (P.isChart_fiberChart x) (P.mem_fiberChart_source x) (Q.isChart_fiberChart y)
    (Q.mem_fiberChart_source y)
    (exists_clm_tangentMapOnFiber hf hxU hxy (P.isChart_fiberChart x) (Q.isChart_fiberChart y)
      (P.mem_fiberChart_source x) (Q.mem_fiberChart_source y)).choose
    (exists_clm_tangentMapOnFiber hf hxU hxy (P.isChart_fiberChart x) (Q.isChart_fiberChart y)
      (P.mem_fiberChart_source x) (Q.mem_fiberChart_source y)).choose_spec.1

theorem tangentMapOnCLM_apply (α : P.tangentFiber x) :
    (tangentMapOnCLM hf hxU hxy α : Q.TangentSpace) = tangentMapOn hf α.1 :=
  congrArg Subtype.val (fiberMapCLM_apply _ _ _ _ _ _ α)

theorem tangentMapOnCLM_eq (α : P.tangentFiber x) :
    tangentMapOnCLM hf hxU hxy α = tangentMapOnFiber hf hxU hxy α :=
  Subtype.ext (tangentMapOnCLM_apply hf hxU hxy α)

/-- **Theorem 2.3.16 (2021 p. 40), fibrewise**: `Tf : T_xX → T_{f(x)}Y` is additive,
homogeneous and continuous, and in charts it is a continuous linear map `L : E → E'`, an
sc-operator at a smooth `x`. -/
theorem theorem_2_3_16_linear_2021 :
    (∀ α β : P.tangentFiber x,
        tangentMapOnFiber hf hxU hxy (α + β) =
          tangentMapOnFiber hf hxU hxy α + tangentMapOnFiber hf hxU hxy β) ∧
      (∀ (c : ℝ) (α : P.tangentFiber x),
        tangentMapOnFiber hf hxU hxy (c • α) = c • tangentMapOnFiber hf hxU hxy α) ∧
      Continuous (tangentMapOnFiber hf hxU hxy) ∧
      ∀ {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ) (hψ : Q.IsChart ψ)
        (hxφ : P.levelVal 1 x ∈ φ.source) (hyψ : Q.levelVal 1 y ∈ ψ.source),
        ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
          (∀ α : P.tangentFiber x,
            (tangentFiberEquiv hψ hyψ (tangentMapOnFiber hf hxU hxy α) : ψ.model.E 0) =
              L (tangentFiberEquiv hφ hxφ α)) ∧
          (P.levelVal 1 x ∈ P.smoothSet → IsScOperator L) := by
  have heq : tangentMapOnFiber hf hxU hxy = tangentMapOnCLM hf hxU hxy :=
    funext fun α => (tangentMapOnCLM_eq hf hxU hxy α).symm
  refine ⟨fun α β => ?_, fun c α => ?_, ?_, fun hφ hψ hxφ hyψ =>
    exists_clm_tangentMapOnFiber hf hxU hxy hφ hψ hxφ hyψ⟩
  · rw [heq, map_add]
  · rw [heq, map_smul]
  · rw [heq]; exact (tangentMapOnCLM hf hxU hxy).continuous

/-! ### Globally sc-smooth maps -/

variable {g : X → Y} (hg : P.IsScSmoothMap Q g) (hxy' : g (P.levelVal 1 x) = Q.levelVal 1 y)

/-- `Tf : T_xX →L[ℝ] T_{f(x)}Y` for a globally sc-smooth `f` (Part I's `tangentMap`). -/
def tangentMapCLM : P.tangentFiber x →L[ℝ] Q.tangentFiber y :=
  tangentMapOnCLM hg (mem_univ _) hxy'

theorem tangentMapCLM_apply (α : P.tangentFiber x) :
    (tangentMapCLM hg hxy' α : Q.TangentSpace) = tangentMap hg α.1 :=
  (tangentMapOnCLM_apply (hf := (hg : P.IsScSmoothOn Q g univ)) (mem_univ _) hxy' α).trans
    (congrFun (tangentMapOn_univ hg) α.1)

end MPolyfold

end Polyfold
