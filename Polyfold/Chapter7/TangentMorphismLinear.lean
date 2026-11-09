import Polyfold.Chapter2.TangentSpaceLinear
import Polyfold.Chapter7.TangentMorphism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.1, Definition 7.1.4
and the paragraph before it, p. 289 (2017: Definition 7.4, p. 227): the tangent `Tφ` of a
morphism is a linear sc-isomorphism.

# `Tφ : T_xX → T_yX` is a bounded linear isomorphism, and an sc-isomorphism for smooth `φ`

## The text, paraphrased

(2021 p. 289) For a morphism `φ : x → y` with `φ ∈ 𝐗₁`, `Tφ := Tφ̂(x) : T_xX → T_yX` is a bounded
linear isomorphism on level `0`; for smooth `φ` it is an sc-isomorphism.  (Definition 7.1.4) A
smooth morphism `φ` has the associated local sc-diffeomorphism `φ̂` and its tangent `Tφ`.

## What is formalized (gap G.70 of `Exposition/cmp/ch07.json`, the linear part)

`TangentMorphism.lean` proved that `Tφ` is a bijection `T_{s(φ)}X → T_{t(φ)}X` given in charts by
continuous linear maps (`bijOn_tangentMor`, `tangentMor_chart_iso`).  With the linear structure
of `T_xX` from `Chapter2/TangentSpaceLinear.lean` (gap G.7) this becomes:

* `EpGroupoid.tangentMorFiber hφ hx hy : T_xX → T_yX`, the restriction of `Tφ` to the fibres
  (`x`, `y` the points `s(φ)`, `t(φ)` of `X₁`).
* **`EpGroupoid.tangentMor_chart_sc`**: in charts `χ` around `s(φ)`, `ψ` around `t(φ)`, `Tφ` is
  given on the fibre by the continuous linear map `L = D(ψ ∘ φ̂ ∘ χ⁻¹ ∘ r)(χ(s φ))`, and **`L` is
  an sc-operator when `φ` is smooth** (Proposition 1.2.3 / `scOperator_deriv`: the derivative of
  an sc-smooth map at a smooth point is an sc-operator).
* **`EpGroupoid.tangentMorCLM hφ hx hy : T_xX →L[ℝ] T_yX`** and
  **`EpGroupoid.tangentMorCLE hφ hx hy : T_xX ≃L[ℝ] T_yX`**: `Tφ` is a continuous linear
  isomorphism with inverse `T(φ⁻¹)` (`tangentMorCLM_apply`, `tangentMorCLE_apply`,
  `tangentMorCLE_symm_apply`).  This is the text's "bounded linear isomorphism on level `0`" in
  the (chart-independent) linear structure of Definition 2.3.14.
* **`EpGroupoid.definition_7_1_4_sc`**: for a smooth `φ`, in charts `χ`, `ψ`, `Tφ` and
  `T(φ⁻¹)` are represented by sc-operators `L`, `L'` which restrict to mutually inverse maps
  `T_{χ(s φ)}O ⇄ T_{ψ(t φ)}O'` between the sc-subspaces `T_{χ(s φ)}O`, `T_{ψ(t φ)}O'`
  (`isScSubspace_tangentFiberModel`): `Tφ` is an sc-isomorphism `T_{s(φ)}X → T_{t(φ)}X`.
* `EpGroupoid.definition_7_1_4_linear`: the bundle for `φ ∈ 𝐗₁`.

## What the text leaves implicit, and the choices made

* `Tφ` is Chapter 7's `tangentMor φ` (`Tt ∘ (Ts|T_φ𝐗)⁻¹`), equal to `Tφ̂(s(φ))` by Chapter 9's
  `tangentMor_eq_tangentMapOn_hat`.
* The sc-isomorphism property is stated in charts: `T_xX` carries its sc-Banach structure
  through the sc-subspace `T_{χ(x)}O ⊆ E` of any chart (`TangentSpaceLinear.lean`), and an
  sc-operator `L : E → E'` restricting to a bijection `T_{χ(x)}O → T_{ψ(y)}O'` with sc-operator
  inverse `L'` is an sc-isomorphism between these sc-Banach spaces; an `ScIso` between
  `ScBanach.ofSubspace` structures is not packaged.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `T_xX` as a `Level 1` fibre versus `tangentFiberAt`. -/
lemma mem_tangentFiber_iff_mem_tangentFiberAt {x : X.PObj.Level 1} {a : X.PObj.TangentSpace} :
    a ∈ X.PObj.tangentFiber x ↔ a ∈ X.tangentFiberAt (X.PObj.levelVal 1 x) := by
  change X.PObj.tangentProj a = x ↔ X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.PObj.levelVal 1 x
  exact ⟨fun h => by rw [h], fun h => MPolyfold.level_ext h⟩

/-- A smooth morphism has a smooth source. -/
lemma src_mem_smoothSet {φ : Mor} (hs : φ ∈ X.PMor.smoothSet) : X.src φ ∈ X.PObj.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter] at hs ⊢
  exact fun m => (X.mem_levelSet_src_iff φ m).2 (hs m)

/-- A smooth morphism has a smooth target. -/
lemma tgt_mem_smoothSet {φ : Mor} (hs : φ ∈ X.PMor.smoothSet) : X.tgt φ ∈ X.PObj.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter] at hs ⊢
  exact fun m => (X.mem_levelSet_tgt_iff φ m).2 (hs m)

lemma inv_mem_smoothSet {φ : Mor} (hs : φ ∈ X.PMor.smoothSet) : X.inv φ ∈ X.PMor.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter] at hs ⊢
  intro m
  rw [← X.mem_levelSet_src_iff, X.src_inv, X.mem_levelSet_tgt_iff]
  exact hs m

/-! ### `Tφ` in charts, with the sc-operator property at smooth `φ` -/

/-- **`Tφ` is linear in charts, and an sc-operator for smooth `φ`** (2021 p. 289): for `φ ∈ 𝐗₁`
and charts `χ` around `s(φ)`, `ψ` around `t(φ)`, there is a continuous linear `L : E → E'` with
`Tψ(Tφ(a)) = (ψ(t φ), L(Tχ(a)))` for `a ∈ T_{s(φ)}X`, namely `L = D(ψ ∘ φ̂ ∘ χ⁻¹ ∘ r)(χ(s φ))`;
if `φ` is smooth, `L` is an sc-operator. -/
theorem tangentMor_chart_sc {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {χ ψ : MChart Obj}
    (hχ : X.PObj.IsChart χ) (hψ : X.PObj.IsChart ψ) (hx : X.src φ ∈ χ.source)
    (hy : X.tgt φ ∈ ψ.source) :
    ∃ L : χ.model.E 0 →L[ℝ] ψ.model.E 0,
      (∀ a ∈ X.tangentFiberAt (X.src φ),
        MPolyfold.tangentChartMap hψ (X.tangentMor φ a) =
          (MPolyfold.levelLift ψ 1 (X.tgt φ), L (MPolyfold.tangentChartMap hχ a).2)) ∧
      (φ ∈ X.PMor.smoothSet → IsScOperator L) := by
  have hf := (X.isScDiffeoOn_hat φ).isScSmoothOn
  have hVo : IsOpen (MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ) :=
    MPolyfold.TangentPre.isOpen_fdomOn hf χ ψ
  have hVχ : MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ ⊆ χ.source :=
    MPolyfold.TangentPre.fdomOn_subset _ _ _ _
  have hsm : IsScSmoothRetractMap χ.model.E χ.model.C
      (χ '' MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ) ψ.model.E ψ.model.C
      ψ.model.O (ψ ∘ X.hat φ ∘ χ.symm) :=
    hf.smooth χ ψ hχ hψ _ hVo (fun _ h => h.1) (fun _ h => h.2)
  obtain ⟨R, hR⟩ := χ.isScRetract_image hVχ hVo
  have hx1 : X.src φ ∈ X.PObj.levelSet 1 := (X.mem_levelSet_src_iff φ 1).2 hφ
  have hxV : X.src φ ∈ MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ := by
    refine ⟨⟨X.src_mem_sheetAt φ, hx⟩, ?_⟩
    change X.hat φ (X.src φ) ∈ ψ.source
    rw [X.hat_src]; exact hy
  have haO : MPolyfold.levelLift χ 1 (X.src φ) ∈ χ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, X.PObj.toBase_levelLift hχ hx hx1]
    exact ⟨_, hxV, rfl⟩
  have haU : MPolyfold.levelLift χ 1 (X.src φ) ∈ χ.model.E.lvlSet R.U 1 :=
    R.lvlSet_retract_subset 1 haO
  refine ⟨scDeriv R.U ((ψ ∘ X.hat φ ∘ χ.symm) ∘ R) (MPolyfold.levelLift χ 1 (X.src φ)),
    fun α hα => ?_, fun hs => ?_⟩
  · have hα' : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ := hα
    have hβ : X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentMor φ α)) = X.tgt φ :=
      X.levelVal_tangentProj_tangentMor hφ hα'
    have hmem : α ∈ X.PObj.tangentPreimage
        (MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ) := by
      rw [MPolyfold.mem_tangentPreimage, hα']; exact hxV
    have hαχ : MPolyfold.tangentChartMap hχ α ∈ retractTangent χ.model.E χ.model.C
        (χ '' MPolyfold.TangentPre.fdomOn (X.sheetAt φ).srcSet χ (X.hat φ) ψ) := by
      refine (MPolyfold.TangentPre.mem_retractTangent_image_iff hVχ hVo ?_).2
        (MPolyfold.tangentChartMap_mem hχ (by
          change X.PObj.levelVal 1 (X.PObj.tangentProj α) ∈ χ.source
          rw [hα']; exact hx))
      rw [(MPolyfold.tangentChartMap_fiber hχ hx hα').1, X.PObj.toBase_levelLift hχ hx hx1]
      exact ⟨_, hxV, rfl⟩
    refine Prod.ext (MPolyfold.tangentChartMap_fiber hψ hy hβ).1 ?_
    rw [X.tangentMor_eq_tangentMapOn_hat hφ hα',
      MPolyfold.tangentChartMap_tangentMapOn hf hχ hψ hmem, retractTangentMap_apply hsm R hR hαχ]
    change scDeriv R.U _ (MPolyfold.tangentChartMap hχ α).1 _ = _
    rw [(MPolyfold.tangentChartMap_fiber hχ hx hα').1]
  · have has : MPolyfold.levelLift χ 1 (X.src φ) ∈ χ.model.E.smoothLvl 1 :=
      (MPolyfold.mem_smoothSet_iff_levelLift_mem_smoothLvl
        (x := X.PObj.levelMk 1 (X.src φ) hx1) hχ hx).1 (X.src_mem_smoothSet hs)
    exact (hsm.comp_isScSmooth R hR).isSc1.isSc1With_scDeriv.scOperator_deriv haU has

/-! ### `Tφ` as a continuous linear isomorphism `T_xX ≃L[ℝ] T_yX` -/

variable {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {x y : X.PObj.Level 1}
  (hx : X.PObj.levelVal 1 x = X.src φ) (hy : X.PObj.levelVal 1 y = X.tgt φ)

include hφ hx hy in
/-- `Tφ` maps `T_xX` into `T_yX`. -/
lemma tangentMor_mem_tangentFiber {a : X.PObj.TangentSpace} (ha : a ∈ X.PObj.tangentFiber x) :
    X.tangentMor φ a ∈ X.PObj.tangentFiber y := by
  rw [X.mem_tangentFiber_iff_mem_tangentFiberAt, hy, X.mem_tangentFiberAt]
  exact X.levelVal_tangentProj_tangentMor hφ
    (((X.mem_tangentFiberAt).1 ((X.mem_tangentFiber_iff_mem_tangentFiberAt).1 ha)).trans hx)

/-- **`Tφ : T_xX → T_yX`**, the restriction of `Tφ` to the fibres over `x = s(φ)`, `y = t(φ)`. -/
def tangentMorFiber : X.PObj.tangentFiber x → X.PObj.tangentFiber y := fun a =>
  ⟨X.tangentMor φ a.1, X.tangentMor_mem_tangentFiber hφ hx hy a.2⟩

lemma tangentMorFiber_val (a : X.PObj.tangentFiber x) :
    (X.tangentMorFiber hφ hx hy a : X.PObj.TangentSpace) = X.tangentMor φ a.1 := rfl

include hφ hx hy in
/-- In the fibre models of charts `χ` around `x`, `ψ` around `y`, `Tφ` is given by a continuous
linear map `L : E → E'`, an sc-operator if `φ` is smooth. -/
theorem exists_clm_tangentMorFiber {χ ψ : MChart Obj} (hχ : X.PObj.IsChart χ)
    (hψ : X.PObj.IsChart ψ) (hxχ : X.PObj.levelVal 1 x ∈ χ.source)
    (hyψ : X.PObj.levelVal 1 y ∈ ψ.source) :
    ∃ L : χ.model.E 0 →L[ℝ] ψ.model.E 0,
      (∀ a : X.PObj.tangentFiber x,
        (MPolyfold.tangentFiberEquiv hψ hyψ (X.tangentMorFiber hφ hx hy a) : ψ.model.E 0) =
          L (MPolyfold.tangentFiberEquiv hχ hxχ a)) ∧
      (φ ∈ X.PMor.smoothSet → IsScOperator L) := by
  obtain ⟨L, hL, hLs⟩ := X.tangentMor_chart_sc hφ hχ hψ (hx ▸ hxχ) (hy ▸ hyψ)
  refine ⟨L, fun a => ?_, hLs⟩
  rw [MPolyfold.coe_tangentFiberEquiv_apply, MPolyfold.coe_tangentFiberEquiv_apply,
    tangentMorFiber_val, hL a.1
      (((X.mem_tangentFiberAt).1 ((X.mem_tangentFiber_iff_mem_tangentFiberAt).1 a.2)).trans hx)]

/-- **`Tφ : T_xX →L[ℝ] T_yX`** (2021 p. 289: a bounded linear map on level `0`), for `φ ∈ 𝐗₁`. -/
def tangentMorCLM : X.PObj.tangentFiber x →L[ℝ] X.PObj.tangentFiber y :=
  MPolyfold.fiberMapCLM (X.PObj.isChart_fiberChart x) (X.PObj.mem_fiberChart_source x)
    (X.PObj.isChart_fiberChart y) (X.PObj.mem_fiberChart_source y)
    (X.exists_clm_tangentMorFiber hφ hx hy (X.PObj.isChart_fiberChart x)
      (X.PObj.isChart_fiberChart y) (X.PObj.mem_fiberChart_source x)
      (X.PObj.mem_fiberChart_source y)).choose
    (X.exists_clm_tangentMorFiber hφ hx hy (X.PObj.isChart_fiberChart x)
      (X.PObj.isChart_fiberChart y) (X.PObj.mem_fiberChart_source x)
      (X.PObj.mem_fiberChart_source y)).choose_spec.1

theorem tangentMorCLM_apply (a : X.PObj.tangentFiber x) :
    (X.tangentMorCLM hφ hx hy a : X.PObj.TangentSpace) = X.tangentMor φ a.1 :=
  congrArg Subtype.val (MPolyfold.fiberMapCLM_apply _ _ _ _ _ _ a)

lemma levelVal_eq_src_inv (hy : X.PObj.levelVal 1 y = X.tgt φ) :
    X.PObj.levelVal 1 y = X.src (X.inv φ) := by rw [X.src_inv]; exact hy

lemma levelVal_eq_tgt_inv (hx : X.PObj.levelVal 1 x = X.src φ) :
    X.PObj.levelVal 1 x = X.tgt (X.inv φ) := by rw [X.tgt_inv]; exact hx

/-- **`Tφ : T_xX ≃L[ℝ] T_yX` is a bounded linear isomorphism** (2021 p. 289, Definition 7.1.4;
gap G.70), with inverse `T(φ⁻¹)`, for `φ ∈ 𝐗₁`. -/
def tangentMorCLE : X.PObj.tangentFiber x ≃L[ℝ] X.PObj.tangentFiber y :=
  ContinuousLinearEquiv.equivOfInverse (X.tangentMorCLM hφ hx hy)
    (X.tangentMorCLM (X.inv_mem_levelSet_one hφ) (X.levelVal_eq_src_inv hy)
      (X.levelVal_eq_tgt_inv hx))
    (fun a => Subtype.ext (by
      rw [tangentMorCLM_apply, tangentMorCLM_apply]
      exact X.tangentMor_inv_tangentMor hφ
        (((X.mem_tangentFiberAt).1 ((X.mem_tangentFiber_iff_mem_tangentFiberAt).1 a.2)).trans hx)))
    (fun b => Subtype.ext (by
      rw [tangentMorCLM_apply, tangentMorCLM_apply]
      have hb : X.PObj.levelVal 1 (X.PObj.tangentProj b.1) = X.src (X.inv φ) :=
        ((X.mem_tangentFiberAt).1 ((X.mem_tangentFiber_iff_mem_tangentFiberAt).1 b.2)).trans
          (X.levelVal_eq_src_inv hy)
      have h := X.tangentMor_inv_tangentMor (X.inv_mem_levelSet_one hφ) hb
      rwa [X.inv_inv] at h))

theorem tangentMorCLE_apply (a : X.PObj.tangentFiber x) :
    (X.tangentMorCLE hφ hx hy a : X.PObj.TangentSpace) = X.tangentMor φ a.1 :=
  X.tangentMorCLM_apply hφ hx hy a

theorem tangentMorCLE_symm_apply (b : X.PObj.tangentFiber y) :
    ((X.tangentMorCLE hφ hx hy).symm b : X.PObj.TangentSpace) = X.tangentMor (X.inv φ) b.1 :=
  X.tangentMorCLM_apply (X.inv_mem_levelSet_one hφ) _ _ b

/-- **2021 p. 289 (2017 p. 227), gap G.70: `Tφ` is a bounded linear isomorphism
`T_{s(φ)}X → T_{t(φ)}X` for `φ ∈ 𝐗₁`**, in the linear structure of Definition 2.3.14: `Tφ` is
additive, homogeneous, continuous, bijective, with inverse `T(φ⁻¹)`. -/
theorem definition_7_1_4_linear :
    (∀ a b : X.PObj.tangentFiber x,
        X.tangentMorFiber hφ hx hy (a + b) =
          X.tangentMorFiber hφ hx hy a + X.tangentMorFiber hφ hx hy b) ∧
      (∀ (c : ℝ) (a : X.PObj.tangentFiber x),
        X.tangentMorFiber hφ hx hy (c • a) = c • X.tangentMorFiber hφ hx hy a) ∧
      Continuous (X.tangentMorFiber hφ hx hy) ∧
      Bijective (X.tangentMorFiber hφ hx hy) ∧
      (∀ a : X.PObj.tangentFiber x,
        X.tangentMor (X.inv φ) (X.tangentMor φ a.1) = a.1) := by
  have heq : X.tangentMorFiber hφ hx hy = X.tangentMorCLE hφ hx hy :=
    funext fun a => Subtype.ext (X.tangentMorCLE_apply hφ hx hy a).symm
  refine ⟨fun a b => ?_, fun c a => ?_, ?_, ?_, fun a => ?_⟩
  · rw [heq, map_add]
  · rw [heq, map_smul]
  · rw [heq]; exact (X.tangentMorCLE hφ hx hy).continuous
  · rw [heq]; exact (X.tangentMorCLE hφ hx hy).bijective
  · exact X.tangentMor_inv_tangentMor hφ
      (((X.mem_tangentFiberAt).1 ((X.mem_tangentFiber_iff_mem_tangentFiberAt).1 a.2)).trans hx)

/-! ### `Tφ` is an sc-isomorphism for smooth `φ` -/

/-- **2021 Definition 7.1.4 and p. 289 (2017: Definition 7.4, p. 227), gap G.70: for a smooth
morphism `φ`, `Tφ : T_{s(φ)}X → T_{t(φ)}X` is an sc-isomorphism.**  In charts `χ` around
`s(φ)`, `ψ` around `t(φ)`: `Tφ` and `T(φ⁻¹)` are represented on the fibres by sc-operators
`L : E → E'`, `L' : E' → E`, which restrict to mutually inverse maps between the sc-subspaces
`T_{χ(s φ)}O` and `T_{ψ(t φ)}O'` (the sc-Banach spaces `T_{s(φ)}X`, `T_{t(φ)}X` of
Definition 2.3.14, p. 39). -/
theorem definition_7_1_4_sc {φ : Mor} (hs : φ ∈ X.PMor.smoothSet) {χ ψ : MChart Obj}
    (hχ : X.PObj.IsChart χ) (hψ : X.PObj.IsChart ψ) (hx : X.src φ ∈ χ.source)
    (hy : X.tgt φ ∈ ψ.source) :
    ∃ (L : χ.model.E 0 →L[ℝ] ψ.model.E 0) (L' : ψ.model.E 0 →L[ℝ] χ.model.E 0),
      (∀ a ∈ X.tangentFiberAt (X.src φ),
        MPolyfold.tangentChartMap hψ (X.tangentMor φ a) =
          (MPolyfold.levelLift ψ 1 (X.tgt φ), L (MPolyfold.tangentChartMap hχ a).2)) ∧
      (∀ b ∈ X.tangentFiberAt (X.tgt φ),
        MPolyfold.tangentChartMap hχ (X.tangentMor (X.inv φ) b) =
          (MPolyfold.levelLift χ 1 (X.src φ), L' (MPolyfold.tangentChartMap hψ b).2)) ∧
      IsScOperator L ∧ IsScOperator L' ∧
      χ.model.E.IsScSubspace
        (MPolyfold.tangentFiberModel (x := X.PObj.levelMk 1 (X.src φ)
          (mem_iInter.1 (X.src_mem_smoothSet hs) 1)) hχ hx) ∧
      ψ.model.E.IsScSubspace
        (MPolyfold.tangentFiberModel (x := X.PObj.levelMk 1 (X.tgt φ)
          (mem_iInter.1 (X.tgt_mem_smoothSet hs) 1)) hψ hy) ∧
      MapsTo L
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ)))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (MPolyfold.levelLift ψ 1 (X.tgt φ))) ∧
      MapsTo L'
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O (MPolyfold.levelLift ψ 1 (X.tgt φ)))
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ))) ∧
      InvOn L' L
        (Polyfold.tangentSpace χ.model.E χ.model.C χ.model.O (MPolyfold.levelLift χ 1 (X.src φ)))
        (Polyfold.tangentSpace ψ.model.E ψ.model.C ψ.model.O
          (MPolyfold.levelLift ψ 1 (X.tgt φ))) := by
  have hφ : φ ∈ X.PMor.levelSet 1 := mem_iInter.1 hs 1
  obtain ⟨L, hL, hLs⟩ := X.tangentMor_chart_sc hφ hχ hψ hx hy
  obtain ⟨L', hL', hL's⟩ := X.tangentMor_chart_sc (X.inv_mem_levelSet_one hφ) hψ hχ
    (by rw [X.src_inv]; exact hy) (by rw [X.tgt_inv]; exact hx)
  rw [X.src_inv, X.tgt_inv] at hL'
  have hx1 : X.src φ ∈ X.PObj.levelSet 1 := (X.mem_levelSet_src_iff φ 1).2 hφ
  have hy1 : X.tgt φ ∈ X.PObj.levelSet 1 := (X.mem_levelSet_tgt_iff φ 1).2 hφ
  have hinv := X.invOn_tangentMor hφ
  obtain ⟨h1, h2, h3⟩ := MPolyfold.chart_invOn hχ hψ hx hx1 hy hy1
    (fun a ha => X.levelVal_tangentProj_tangentMor hφ ha)
    (fun b hb => X.tangentMor_inv_mapsTo hφ hb)
    (fun a ha => hinv.1 ha) (fun b hb => hinv.2 hb) L L' hL hL'
  exact ⟨L, L', hL, hL', hLs hs, hL's (X.inv_mem_smoothSet hs),
    MPolyfold.isScSubspace_tangentFiberModel (x := X.PObj.levelMk 1 (X.src φ) hx1) hχ hx
      (X.src_mem_smoothSet hs),
    MPolyfold.isScSubspace_tangentFiberModel (x := X.PObj.levelMk 1 (X.tgt φ) hy1) hψ hy
      (X.tgt_mem_smoothSet hs), h1, h2, h3⟩

end EpGroupoid

end Polyfold
