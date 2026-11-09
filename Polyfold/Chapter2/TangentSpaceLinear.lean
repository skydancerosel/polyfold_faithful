import Polyfold.Chapter1.ExpositionLemmas
import Polyfold.Chapter2.TangentBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.3, Definition 2.3.14 and
the paragraph after it, p. 39 (preprint: Definition 2.18, pp. 26–27): the linear structure of the
tangent space `T_xX`.

# The linear and Banach structure of `T_xX`

## The text, paraphrased

(2021 Definition 2.3.14, p. 39) For `x ∈ X₁` the tangent space `T_xX` is the set of classes
`[(x, V, φ, (O, C, E), h)]`, `h ∈ T_{φ(x)}O`.  It is a vector space with
`λ[(x, φ, h₁)] + μ[(x, φ, h₂)] = [(x, φ, λh₁ + μh₂)]`.  (p. 39, after the definition) For a chart
`φ` around `x`, `Tφ : T_xV → T_{φ(x)}O` is a linear isomorphism, so `T_xX` inherits the Banach
space structure of `T_{φ(x)}O ⊆ E₀`; if `x ∈ X_∞`, `T_xX` is an sc-Banach space, since
`T_{φ(x)}O` is one.  (Remark 2.3.13) `T_xO = {x} × Dr(x)E`.

## What is formalized (gap G.7 of `Exposition/cmp/ch02.json`; rows V2.19, V2.21)

* `Polyfold.tangentSubmodule hO ha`: `T_aO ⊆ E₀` as a **submodule** (its carrier is the set
  `tangentSpace E C O a` of `Retracts.lean`), `isClosed_tangentSubmodule` (it is the range of the
  continuous projection `Dr(a)`), and the instance `CompleteSpace`.
* `MPolyfold.tangentFiberModel hφ hx`: `T_{φ(x)}O` for a chart `φ` around `x ∈ X₁`, and
  **`MPolyfold.tangentFiberEquiv hφ hx : T_xX ≃ T_{φ(x)}O`**, the bijection `Tφ` restricted to the
  fibre, with inverse `h ↦ [(x, φ, h)]` (`tangentFiberMk`).
* **The transition maps are continuous linear** (`exists_transition_clm`,
  `MPolyfold.transitionCLM`, `MPolyfold.tangentFiberTransition`): for two charts `φ`, `ψ` around
  `x`,
  `Tψ ∘ (Tφ)⁻¹` on the fibre is the restriction of the continuous linear map
  `D(ψ ∘ φ⁻¹)(φ(x)) : E → E'` (the derivative of the transition, Theorem 2.1.15 / `theorem_2_8`
  through `retractTangentMap_apply`), it maps `T_{φ(x)}O` into `T_{ψ(x)}O'`
  (`tangentFiberEquiv_symm_trans`), and the two transitions are inverse to each other
  (`tangentFiberTransition_transition`).  At a smooth `x` the transition is an sc-operator
  (`isScOperator_transitionCLM`).
* **The vector space structure of `T_xX`** (Definition 2.3.14): the instances `AddCommGroup`
  and `Module ℝ` on `MPolyfold.tangentFiber x`, transported along `Tφ₀` for one chart
  `φ₀ = P.fiberChart x` around `x`; **for every chart `φ` around `x`**, `Tφ` is a linear
  isomorphism (`MPolyfold.tangentFiberLinearEquiv hφ hx : T_xX ≃ₗ[ℝ] T_{φ(x)}O`).  This is the
  chart independence of Definition 2.3.14.
* **The topology and the Banach structure** (p. 39, "`T_xX` inherits the Banach space structure
  from `T_{φ(x)}O ⊆ E`"): `T_xX ⊆ TX` carries the subspace topology of `TX`; `Tφ` is a
  homeomorphism onto `T_{φ(x)}O` (`continuous_tangentFiberEquiv`,
  `continuous_tangentFiberEquiv_symm`), so **for every chart `φ`**
  `MPolyfold.tangentFiberContinuousLinearEquiv hφ hx : T_xX ≃L[ℝ] T_{φ(x)}O` is a topological
  linear isomorphism onto a Banach space; `T_xX` is a topological vector space (the instances
  `IsTopologicalAddGroup`, `ContinuousSMul ℝ`).  The Banach norm through a chart is
  `MPolyfold.tangentFiberNormedAddCommGroup hφ hx` (a definition, not an instance: it depends on
  the chart up to equivalence), it induces the subspace topology
  (`tangentFiberNormedAddCommGroup_toTopologicalSpace`) and is complete
  (`completeSpace_tangentFiber`).
* The text's formula `λ[(x, φ, h₁)] + μ[(x, φ, h₂)] = [(x, φ, λh₁ + μh₂)]`:
  **`MPolyfold.definition_2_3_14_2021`**, for every chart `φ` around `x`.
* `MPolyfold.tangentFiberTransitionEquiv hφ hψ hx hx' : T_{φ(x)}O ≃L[ℝ] T_{ψ(x)}O'`, the
  transition as a Banach-space isomorphism, with `coe_tangentFiberTransitionEquiv`.
* **The sc-structure at a smooth point** (p. 39, "if `x ∈ X_∞` ... an sc-Banach space"):
  `MPolyfold.mem_smoothSet_iff_levelLift_mem_smoothLvl`,
  **`MPolyfold.isScSubspace_tangentFiberModel`** (`T_{φ(x)}O` is an sc-subspace of `E` for smooth
  `x`, so `T_xX` carries the sc-Banach structure `ScBanach.ofSubspace` through any chart), and
  `MPolyfold.transitionCLM_mem_range_toBase`: the transition maps level `m` of `T_{φ(x)}O` into
  level `m` of `T_{ψ(x)}O'`, so the sc-structures through two charts agree.

## What the text leaves implicit, and the choices made

* The text defines the linear structure through one chart and does not check that it is
  independent of the chart; the check is the linearity of the fibre transition maps, which is
  the formula `Tf(x, h) = (f(x), Df(x)h)` of Definition 2.1.14 (`retractTangentMap_apply`).
* The algebraic instances on `T_xX` use a chosen chart `P.fiberChart x` (through
  `Classical.choice` applied to `exists_isChart_mem_source`).  Every statement about them is
  proved for an arbitrary chart, so nothing depends on the choice.
* The text's "Banach space structure" is a norm depending on the chart; `T_xX` is given the
  topology of `TX` (which is the one of every chart norm) and the norms are definitions, one per
  chart, all equivalent since every chart map is a topological linear isomorphism.  A norm
  instance on `T_xX` would conflict with the subspace topology of `TX`.
* `MPolyfold.fiberMapCLM`: a map `T_xX → T_yY` which in charts is a continuous linear map
  `E → E'` is a continuous linear map; this is how tangent maps and `Tφ` of a morphism are made
  linear (`TangentMapLinear.lean`, `Chapter7/TangentMorphismLinear.lean`).
* The sc-Banach space structure of `T_xX` at a smooth `x` is formalized as the sc-subspace
  property of the model `T_{φ(x)}O ⊆ E` for every chart (`ScBanach.ofSubspace` then gives the
  sc-Banach space) together with the level-preservation of the transition maps; an `ScIso`
  between the models through two charts is not packaged.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

/-! ### `T_aO` as a closed subspace of `E₀` -/

section LocalLinear

variable {E : ScBanach} {C O : Set (E 0)}

/-- `T_aO ⊆ E₀` is a closed subspace, for `a ∈ O₁`: it is `Dr(a)E`, the range of a continuous
projection (Remark 2.3.13 (2021), the remark after Definition 2.17 (preprint)). -/
theorem exists_submodule_eq_tangentSpace (hO : IsScRetract E C O) {a : E 1}
    (ha : a ∈ E.lvlSet O 1) :
    ∃ S : Submodule ℝ (E 0), (S : Set (E 0)) = tangentSpace E C O a ∧ IsClosed (S : Set (E 0)) := by
  obtain ⟨R, rfl⟩ := hO
  refine ⟨LinearMap.range (scDeriv R.U R a : E 0 →ₗ[ℝ] E 0),
    (tangentSpace_eq_coe_submodule R ha).symm, ?_⟩
  have hidem : IsIdempotentElem (scDeriv R.U R a) := R.scDeriv_comp_self ha
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hidem

/-- **`T_aO` as a submodule of `E₀`** (2021 Definition 2.3.14, p. 39, and Remark 2.3.13), for
`a ∈ O₁`.  Its carrier is the set `tangentSpace E C O a = {h | (a, h) ∈ TO}`. -/
def tangentSubmodule (hO : IsScRetract E C O) {a : E 1} (ha : a ∈ E.lvlSet O 1) :
    Submodule ℝ (E 0) where
  carrier := tangentSpace E C O a
  add_mem' {v w} hv hw := by
    obtain ⟨S, hS, -⟩ := exists_submodule_eq_tangentSpace hO ha
    change v ∈ tangentSpace E C O a at hv
    change w ∈ tangentSpace E C O a at hw
    change v + w ∈ tangentSpace E C O a
    rw [← hS] at hv hw ⊢
    exact S.add_mem hv hw
  zero_mem' := by
    obtain ⟨S, hS, -⟩ := exists_submodule_eq_tangentSpace hO ha
    change (0 : E 0) ∈ tangentSpace E C O a
    rw [← hS]; exact S.zero_mem
  smul_mem' c {v} hv := by
    obtain ⟨S, hS, -⟩ := exists_submodule_eq_tangentSpace hO ha
    change v ∈ tangentSpace E C O a at hv
    change c • v ∈ tangentSpace E C O a
    rw [← hS] at hv ⊢
    exact S.smul_mem c hv

variable (hO : IsScRetract E C O) {a : E 1} (ha : a ∈ E.lvlSet O 1)

lemma mem_tangentSubmodule {v : E 0} :
    v ∈ tangentSubmodule hO ha ↔ ((a, v) : E.tangent 0) ∈ retractTangent E C O := Iff.rfl

lemma coe_tangentSubmodule : (tangentSubmodule hO ha : Set (E 0)) = tangentSpace E C O a := rfl

/-- `T_aO` is closed in `E₀`. -/
theorem isClosed_tangentSubmodule : IsClosed (tangentSubmodule hO ha : Set (E 0)) := by
  obtain ⟨S, hS, hcl⟩ := exists_submodule_eq_tangentSpace hO ha
  rw [coe_tangentSubmodule, ← hS]; exact hcl

/-- `T_aO` is a Banach space (a closed subspace of `E₀`). -/
instance : CompleteSpace (tangentSubmodule hO ha) :=
  (completeSpace_coe_iff_isComplete (s := (tangentSubmodule hO ha : Set (E 0)))).2
    (isClosed_tangentSubmodule hO ha).isComplete

end LocalLinear

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ ψ : MChart X} {x : P.Level 1}

/-! ### The model `T_{φ(x)}O` of the fibre `T_xX` in a chart -/

/-- The base point `φ(x) ∈ O₁` of the fibre over `x ∈ X₁` in the chart `φ`. -/
lemma levelLift_mem_lvlSet_one (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source) :
    levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.lvlSet φ.model.O 1 := by
  rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ hx (levelVal_mem x)]
  exact φ.mapsTo_model _ hx

/-- **The model of `T_xX` in the chart `φ`**: the closed subspace `T_{φ(x)}O ⊆ E₀`. -/
def tangentFiberModel (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source) :
    Submodule ℝ (φ.model.E 0) :=
  tangentSubmodule φ.model.isScRetract (levelLift_mem_lvlSet_one hφ hx)

variable (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source)

lemma mem_tangentFiberModel {v : φ.model.E 0} :
    v ∈ tangentFiberModel hφ hx ↔
      ((levelLift φ 1 (P.levelVal 1 x), v) : φ.model.E.tangent 0) ∈
        retractTangent φ.model.E φ.model.C φ.model.O := Iff.rfl

lemma coe_tangentFiberModel :
    (tangentFiberModel hφ hx : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C φ.model.O (levelLift φ 1 (P.levelVal 1 x)) := rfl

theorem isClosed_tangentFiberModel : IsClosed (tangentFiberModel hφ hx : Set (φ.model.E 0)) :=
  isClosed_tangentSubmodule _ _

instance : CompleteSpace (tangentFiberModel hφ hx) :=
  inferInstanceAs (CompleteSpace (tangentSubmodule φ.model.isScRetract
    (levelLift_mem_lvlSet_one hφ hx)))

/-! ### `Tφ` restricted to the fibre -/

lemma tangentProj_eq_of_mem_fiber {α : P.TangentSpace} (hα : α ∈ P.tangentFiber x) :
    P.tangentProj α = x := hα

include hx in
lemma mem_tangentChartSet_of_mem_fiber {α : P.TangentSpace} (hα : α ∈ P.tangentFiber x) :
    α ∈ tangentChartSet φ := by
  change P.levelVal 1 (P.tangentProj α) ∈ φ.source
  rw [tangentProj_eq_of_mem_fiber hα]; exact hx

include hx in
lemma tangentChartMap_fst_of_mem_fiber {α : P.TangentSpace} (hα : α ∈ P.tangentFiber x) :
    (tangentChartMap hφ α).1 = levelLift φ 1 (P.levelVal 1 x) := by
  rw [tangentChartMap_fst hφ (mem_tangentChartSet_of_mem_fiber hx hα),
    tangentProj_eq_of_mem_fiber hα]

include hx in
/-- `Tφ` maps `T_xX` into `{φ(x)} × T_{φ(x)}O`. -/
lemma tangentChartMap_snd_mem_model {α : P.TangentSpace} (hα : α ∈ P.tangentFiber x) :
    (tangentChartMap hφ α).2 ∈ tangentFiberModel hφ hx := by
  rw [mem_tangentFiberModel, ← tangentChartMap_fst_of_mem_fiber hφ hx hα]
  exact tangentChartMap_mem hφ (mem_tangentChartSet_of_mem_fiber hx hα)

include hx in
lemma ofVec_x_eq {v : φ.model.E 0}
    (hv : ((levelLift φ 1 (P.levelVal 1 x), v) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O) :
    (TangentPre.ofVec hφ hv).x = P.levelVal 1 x := by
  rw [TangentPre.ofVec_x]
  change φ.symm (φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x))) = _
  rw [P.toBase_levelLift hφ hx (levelVal_mem x), φ.symm_apply_apply hx]

include hx in
/-- `[(x, φ, h)] ∈ T_xX` for `h ∈ T_{φ(x)}O`. -/
lemma mk_ofVec_mem_fiber {v : φ.model.E 0}
    (hv : ((levelLift φ 1 (P.levelVal 1 x), v) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O) :
    TangentSpace.mk (TangentPre.ofVec hφ hv) ∈ P.tangentFiber x := by
  change P.tangentProj _ = x
  apply level_ext
  rw [tangentProj_mk, ofVec_x_eq hφ hx hv]

/-- **`Tφ : T_xX → T_{φ(x)}O` is a bijection** (2021 p. 39: "`Tφ : T_xV → T_{φ(x)}O` is a linear
isomorphism", the bijectivity), with inverse `h ↦ [(x, φ, h)]`. -/
def tangentFiberEquiv : P.tangentFiber x ≃ tangentFiberModel hφ hx where
  toFun α := ⟨(tangentChartMap hφ α.1).2, tangentChartMap_snd_mem_model hφ hx α.2⟩
  invFun v := ⟨TangentSpace.mk (TangentPre.ofVec hφ ((mem_tangentFiberModel hφ hx).1 v.2)),
    mk_ofVec_mem_fiber hφ hx _⟩
  left_inv α := by
    apply Subtype.ext
    refine tangentChartMap_injOn hφ
      (mem_tangentChartSet_of_mem_fiber hx (mk_ofVec_mem_fiber hφ hx _))
      (mem_tangentChartSet_of_mem_fiber hx α.2) ?_
    rw [tangentChartMap_mk_ofVec]
    symm
    exact Prod.ext (tangentChartMap_fst_of_mem_fiber hφ hx α.2) rfl
  right_inv v := by
    apply Subtype.ext
    exact congrArg Prod.snd (tangentChartMap_mk_ofVec hφ _)

lemma coe_tangentFiberEquiv_apply (α : P.tangentFiber x) :
    (tangentFiberEquiv hφ hx α : φ.model.E 0) = (tangentChartMap hφ α.1).2 := rfl

lemma coe_tangentFiberEquiv_symm_apply (v : tangentFiberModel hφ hx) :
    ((tangentFiberEquiv hφ hx).symm v : P.TangentSpace) =
      TangentSpace.mk (TangentPre.ofVec hφ ((mem_tangentFiberModel hφ hx).1 v.2)) := rfl

/-- `Tφ[(x, φ, h)] = (φ(x), h)`. -/
lemma tangentChartMap_tangentFiberEquiv_symm (v : tangentFiberModel hφ hx) :
    tangentChartMap hφ ((tangentFiberEquiv hφ hx).symm v).1 =
      (levelLift φ 1 (P.levelVal 1 x), (v : φ.model.E 0)) :=
  tangentChartMap_mk_ofVec hφ _

/-- The class `[(x, φ, h)] ∈ T_xX` of a vector `h ∈ T_{φ(x)}O` (Definition 2.3.14). -/
def tangentFiberMk (v : tangentFiberModel hφ hx) : P.tangentFiber x :=
  (tangentFiberEquiv hφ hx).symm v

/-! ### The transition maps are linear -/

variable (hψ : P.IsChart ψ) (hx' : P.levelVal 1 x ∈ ψ.source)

include hψ hx' in
/-- **The fibre transition map is continuous linear**: for charts `φ`, `ψ` around `x ∈ X₁`,
`T(ψ ∘ φ⁻¹)(φ(x), h) = (ψ(x), L h)` on `T_{φ(x)}O` for a continuous linear `L : E → E'`, namely
`L = D(ψ ∘ φ⁻¹ ∘ r)(φ(x))` (Definition 2.1.14 and `retractTangentMap_apply`); at a smooth `x`,
`L` is an sc-operator (Proposition 1.2.3 / `scOperator_deriv`). -/
theorem exists_transition_clm :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      (∀ v ∈ tangentFiberModel hφ hx,
        retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
            (levelLift φ 1 (P.levelVal 1 x), v) =
          (levelLift ψ 1 (P.levelVal 1 x), L v)) ∧
      (levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.smoothLvl 1 → IsScOperator L) := by
  set a := levelLift φ 1 (P.levelVal 1 x) with ha_def
  have hO : IsScRetract φ.model.E φ.model.C (φ.overlap ψ) := φ.isScRetract_overlap ψ
  have hcomp := (hφ.compatible hψ (P := P)).1
  have hunfold : retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) =
      tangentMap hO.choose.U (φ.transition ψ ∘ hO.choose) := by
    rw [retractTangentMap, dif_pos hO]
  set R := hO.choose with hR
  have hRret : R.retract = φ.overlap ψ := hO.choose_spec
  have hmem : φ (P.levelVal 1 x) ∈ R.retract := by
    rw [hRret]; exact φ.mem_overlap ψ hx hx'
  have ha1 : a ∈ φ.model.E.lvlSet R.U 1 := by
    refine R.lvlSet_retract_subset 1 ?_
    rw [ScBanach.mem_lvlSet, ha_def, P.toBase_levelLift hφ hx (levelVal_mem x)]
    exact hmem
  have hsm := hcomp.comp_isScSmooth R hRret
  refine ⟨scDeriv R.U (φ.transition ψ ∘ R) a, fun v _ => ?_, fun hs => ?_⟩
  · rw [hunfold]
    change (levelMap (φ.transition ψ ∘ R) 1 a, scDeriv R.U (φ.transition ψ ∘ R) a v) = _
    congr 1
    apply ψ.model.E.toBase_injective 1
    rw [hsm.isSc1.isSc0.toBase_levelMap ha1, Function.comp_apply, ha_def,
      P.toBase_levelLift hφ hx (levelVal_mem x), R.apply_eq_self_of_mem_retract hmem,
      φ.transition_apply ψ hx, P.toBase_levelLift hψ hx' (levelVal_mem x)]
  · exact hsm.isSc1.isSc1With_scDeriv.scOperator_deriv ha1 hs

/-- The continuous linear map `D(ψ ∘ φ⁻¹)(φ(x)) : E → E'` representing the fibre transition. -/
def transitionCLM : φ.model.E 0 →L[ℝ] ψ.model.E 0 :=
  (exists_transition_clm hφ hx hψ hx').choose

theorem transitionCLM_spec {v : φ.model.E 0} (hv : v ∈ tangentFiberModel hφ hx) :
    retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
        (levelLift φ 1 (P.levelVal 1 x), v) =
      (levelLift ψ 1 (P.levelVal 1 x), transitionCLM hφ hx hψ hx' v) :=
  (exists_transition_clm hφ hx hψ hx').choose_spec.1 v hv

/-- At a smooth point the fibre transition is an sc-operator. -/
theorem isScOperator_transitionCLM (hs : levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.smoothLvl 1) :
    IsScOperator (transitionCLM hφ hx hψ hx') :=
  (exists_transition_clm hφ hx hψ hx').choose_spec.2 hs

/-- **`Tψ ∘ (Tφ)⁻¹ = D(ψ ∘ φ⁻¹)(φ(x))` on the fibre** (formula (2.7) of Remark 2.3.13). -/
theorem coe_tangentFiberEquiv_symm_trans (v : tangentFiberModel hφ hx) :
    (tangentFiberEquiv hψ hx' ((tangentFiberEquiv hφ hx).symm v) : ψ.model.E 0) =
      transitionCLM hφ hx hψ hx' v := by
  rw [coe_tangentFiberEquiv_apply, coe_tangentFiberEquiv_symm_apply]
  have hov : ((levelLift φ 1 (P.levelVal 1 x), (v : φ.model.E 0)) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
      (φ.isOpen_source.inter ψ.isOpen_source) ?_).2 ((mem_tangentFiberModel hφ hx).1 v.2)
    change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ '' (φ.source ∩ ψ.source)
    rw [P.toBase_levelLift hφ hx (levelVal_mem x)]
    exact ⟨_, ⟨hx, hx'⟩, rfl⟩
  rw [tangentChartMap_mk_ofVec_of_mem hφ hψ _ hov, transitionCLM_spec hφ hx hψ hx' v.2]

/-- The transition maps `T_{φ(x)}O` into `T_{ψ(x)}O'`. -/
lemma transitionCLM_mem (v : tangentFiberModel hφ hx) :
    transitionCLM hφ hx hψ hx' v ∈ tangentFiberModel hψ hx' := by
  rw [← coe_tangentFiberEquiv_symm_trans]; exact (tangentFiberEquiv hψ hx' _).2

/-- **The fibre transition `T_{φ(x)}O → T_{ψ(x)}O'`** as a continuous linear map. -/
def tangentFiberTransition : tangentFiberModel hφ hx →L[ℝ] tangentFiberModel hψ hx' :=
  ((transitionCLM hφ hx hψ hx').comp (tangentFiberModel hφ hx).subtypeL).codRestrict _
    (transitionCLM_mem hφ hx hψ hx')

lemma coe_tangentFiberTransition (v : tangentFiberModel hφ hx) :
    (tangentFiberTransition hφ hx hψ hx' v : ψ.model.E 0) = transitionCLM hφ hx hψ hx' v := rfl

/-- `Tψ ∘ (Tφ)⁻¹` on the fibre is the transition map. -/
theorem tangentFiberEquiv_symm_trans (v : tangentFiberModel hφ hx) :
    tangentFiberEquiv hψ hx' ((tangentFiberEquiv hφ hx).symm v) =
      tangentFiberTransition hφ hx hψ hx' v :=
  Subtype.ext (coe_tangentFiberEquiv_symm_trans hφ hx hψ hx' v)

/-- `Tψ = T(ψ ∘ φ⁻¹) ∘ Tφ` on the fibre. -/
theorem tangentFiberEquiv_eq_transition (α : P.tangentFiber x) :
    tangentFiberEquiv hψ hx' α =
      tangentFiberTransition hφ hx hψ hx' (tangentFiberEquiv hφ hx α) := by
  rw [← tangentFiberEquiv_symm_trans, Equiv.symm_apply_apply]

/-- The transitions `φ → ψ` and `ψ → φ` are inverse to each other. -/
theorem tangentFiberTransition_transition (v : tangentFiberModel hφ hx) :
    tangentFiberTransition hψ hx' hφ hx (tangentFiberTransition hφ hx hψ hx' v) = v := by
  rw [← tangentFiberEquiv_symm_trans, ← tangentFiberEquiv_symm_trans, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

/-! ### The vector space structure of `T_xX` (Definition 2.3.14) -/

variable (P) in
/-- A chart around `x ∈ X₁`, used to define the linear structure of `T_xX`. -/
def fiberChart (x : P.Level 1) : MChart X :=
  (P.exists_isChart_mem_source (P.levelVal 1 x)).choose

variable (P) in
lemma isChart_fiberChart (x : P.Level 1) : P.IsChart (P.fiberChart x) :=
  (P.exists_isChart_mem_source (P.levelVal 1 x)).choose_spec.1

variable (P) in
lemma mem_fiberChart_source (x : P.Level 1) : P.levelVal 1 x ∈ (P.fiberChart x).source :=
  (P.exists_isChart_mem_source (P.levelVal 1 x)).choose_spec.2

variable (x) in
/-- `Tφ₀ : T_xX ≃ T_{φ₀(x)}O₀` for the chosen chart `φ₀`. -/
abbrev tangentFiberBaseEquiv :
    P.tangentFiber x ≃ tangentFiberModel (P.isChart_fiberChart x) (P.mem_fiberChart_source x) :=
  tangentFiberEquiv (P.isChart_fiberChart x) (P.mem_fiberChart_source x)

/-- **Definition 2.3.14 (2021 p. 39)**: the vector space structure of `T_xX`, transported from
`T_{φ₀(x)}O₀` along `Tφ₀`.  Independent of the chart: `tangentFiberLinearEquiv`. -/
instance : AddCommGroup (P.tangentFiber x) := (tangentFiberBaseEquiv x).addCommGroup

instance : Module ℝ (P.tangentFiber x) := (tangentFiberBaseEquiv x).module ℝ

variable (x) in
/-- `Tφ₀` as a linear isomorphism (by construction). -/
def tangentFiberBaseLinearEquiv :
    P.tangentFiber x ≃ₗ[ℝ] tangentFiberModel (P.isChart_fiberChart x) (P.mem_fiberChart_source x) :=
  (tangentFiberBaseEquiv x).linearEquiv ℝ

lemma tangentFiberBaseLinearEquiv_apply (α : P.tangentFiber x) :
    tangentFiberBaseLinearEquiv x α = tangentFiberBaseEquiv x α := rfl

lemma tangentFiberBaseLinearEquiv_symm_apply
    (v : tangentFiberModel (P.isChart_fiberChart x) (P.mem_fiberChart_source x)) :
    (tangentFiberBaseLinearEquiv x).symm v = (tangentFiberBaseEquiv x).symm v := rfl

/-- **`Tφ : T_xX → T_{φ(x)}O` is a linear isomorphism for every chart `φ` around `x`**
(2021 p. 39): the linear structure of Definition 2.3.14 does not depend on the chart. -/
def tangentFiberLinearEquiv : P.tangentFiber x ≃ₗ[ℝ] tangentFiberModel hφ hx :=
  { tangentFiberEquiv hφ hx with
    map_add' := fun α β => by
      change tangentFiberEquiv hφ hx (α + β) = tangentFiberEquiv hφ hx α + tangentFiberEquiv hφ hx β
      have h := fun γ => tangentFiberEquiv_eq_transition (P.isChart_fiberChart x)
        (P.mem_fiberChart_source x) hφ hx γ
      rw [h (α + β), h α, h β, ← tangentFiberBaseLinearEquiv_apply,
        ← tangentFiberBaseLinearEquiv_apply, ← tangentFiberBaseLinearEquiv_apply, map_add, map_add]
    map_smul' := fun c α => by
      change tangentFiberEquiv hφ hx (c • α) = c • tangentFiberEquiv hφ hx α
      have h := fun γ => tangentFiberEquiv_eq_transition (P.isChart_fiberChart x)
        (P.mem_fiberChart_source x) hφ hx γ
      rw [h (c • α), h α, ← tangentFiberBaseLinearEquiv_apply, ← tangentFiberBaseLinearEquiv_apply,
        map_smul, map_smul] }

lemma tangentFiberLinearEquiv_apply (α : P.tangentFiber x) :
    tangentFiberLinearEquiv hφ hx α = tangentFiberEquiv hφ hx α := rfl

lemma tangentFiberLinearEquiv_symm_apply (v : tangentFiberModel hφ hx) :
    (tangentFiberLinearEquiv hφ hx).symm v = (tangentFiberEquiv hφ hx).symm v := rfl

lemma coe_tangentFiberLinearEquiv_apply (α : P.tangentFiber x) :
    (tangentFiberLinearEquiv hφ hx α : φ.model.E 0) = (tangentChartMap hφ α.1).2 := rfl

/-- **Definition 2.3.14 (2021 p. 39; preprint 2.18)**: the text's formula
`λ[(x, φ, h₁)] + μ[(x, φ, h₂)] = [(x, φ, λh₁ + μh₂)]`, for every chart `φ` around `x`. -/
theorem definition_2_3_14_2021 (l m : ℝ) (v w : tangentFiberModel hφ hx) :
    l • tangentFiberMk hφ hx v + m • tangentFiberMk hφ hx w =
      tangentFiberMk hφ hx (l • v + m • w) := by
  simp only [tangentFiberMk, ← tangentFiberLinearEquiv_symm_apply, map_add, map_smul]

/-! ### The topology of `T_xX` (as a subspace of `TX`) and the Banach structure -/

/-- `Tφ : T_xX → T_{φ(x)}O` is continuous, for the subspace topology of `T_xX ⊆ TX`. -/
theorem continuous_tangentFiberEquiv : Continuous (tangentFiberEquiv hφ hx) := by
  set α₀ : P.TangentSpace := ((tangentFiberEquiv hφ hx).symm 0).1
  have hc : ContinuousOn (tangentChartMap hφ) (tangentChartSet φ) :=
    (tangentChart hφ α₀).continuousOn_toFun
  refine Continuous.subtype_mk ?_ _
  exact (hc.comp_continuous continuous_subtype_val
    fun α => mem_tangentChartSet_of_mem_fiber hx α.2).snd

/-- `(Tφ)⁻¹ : T_{φ(x)}O → T_xX` is continuous, for the subspace topology of `T_xX ⊆ TX`. -/
theorem continuous_tangentFiberEquiv_symm : Continuous (tangentFiberEquiv hφ hx).symm := by
  set α₀ : P.TangentSpace := ((tangentFiberEquiv hφ hx).symm 0).1
  have hinv : ContinuousOn (tangentChartInv hφ α₀)
      (retractTangent φ.model.E φ.model.C φ.model.O) :=
    (tangentChart hφ α₀).continuousOn_invFun
  have hfun : (fun v : tangentFiberModel hφ hx => ((tangentFiberEquiv hφ hx).symm v).1) =
      fun v : tangentFiberModel hφ hx =>
        tangentChartInv hφ α₀ (levelLift φ 1 (P.levelVal 1 x), (v : φ.model.E 0)) := by
    funext v
    rw [coe_tangentFiberEquiv_symm_apply,
      tangentChartInv_of_mem hφ α₀ ((mem_tangentFiberModel hφ hx).1 v.2)]
  refine Continuous.subtype_mk ?_ _
  change Continuous fun v : tangentFiberModel hφ hx => ((tangentFiberEquiv hφ hx).symm v).1
  rw [hfun]
  exact hinv.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    fun v => (mem_tangentFiberModel hφ hx).1 v.2

/-- **`Tφ : T_xX → T_{φ(x)}O` is a topological linear isomorphism for every chart `φ` around `x`**
(2021 p. 39: "`T_xX` inherits the Banach space structure from `T_{φ(x)}O ⊆ E`"), where `T_xX`
carries the subspace topology of `TX`: the topology of Definition 2.3.14 is the one of `TX`, and
the Banach norms through different charts are equivalent. -/
def tangentFiberContinuousLinearEquiv : P.tangentFiber x ≃L[ℝ] tangentFiberModel hφ hx :=
  { tangentFiberLinearEquiv hφ hx with
    continuous_toFun := continuous_tangentFiberEquiv hφ hx
    continuous_invFun := continuous_tangentFiberEquiv_symm hφ hx }

lemma tangentFiberContinuousLinearEquiv_apply (α : P.tangentFiber x) :
    tangentFiberContinuousLinearEquiv hφ hx α = tangentFiberEquiv hφ hx α := rfl

lemma tangentFiberContinuousLinearEquiv_symm_apply (v : tangentFiberModel hφ hx) :
    (tangentFiberContinuousLinearEquiv hφ hx).symm v = (tangentFiberEquiv hφ hx).symm v := rfl

/-- `T_xX` is a topological vector space: a topological additive group ... -/
instance : IsTopologicalAddGroup (P.tangentFiber x) :=
  (tangentFiberContinuousLinearEquiv (P.isChart_fiberChart x)
    (P.mem_fiberChart_source x)).toHomeomorph.isInducing.topologicalAddGroup
    (tangentFiberContinuousLinearEquiv (P.isChart_fiberChart x) (P.mem_fiberChart_source x))

/-- ... with continuous scalar multiplication. -/
instance : ContinuousSMul ℝ (P.tangentFiber x) :=
  (tangentFiberContinuousLinearEquiv (P.isChart_fiberChart x)
    (P.mem_fiberChart_source x)).toHomeomorph.isInducing.continuousSMul continuous_id
    fun {c v} => map_smul (tangentFiberContinuousLinearEquiv (P.isChart_fiberChart x)
      (P.mem_fiberChart_source x)) c v

/-- **The transition `T_{φ(x)}O → T_{ψ(x)}O'` is a Banach-space isomorphism**
(`Tψ ∘ (Tφ)⁻¹` on the fibre). -/
def tangentFiberTransitionEquiv : tangentFiberModel hφ hx ≃L[ℝ] tangentFiberModel hψ hx' :=
  (tangentFiberContinuousLinearEquiv hφ hx).symm.trans (tangentFiberContinuousLinearEquiv hψ hx')

lemma coe_tangentFiberTransitionEquiv (v : tangentFiberModel hφ hx) :
    (tangentFiberTransitionEquiv hφ hx hψ hx' v : ψ.model.E 0) = transitionCLM hφ hx hψ hx' v :=
  coe_tangentFiberEquiv_symm_trans hφ hx hψ hx' v

lemma tangentFiberTransitionEquiv_apply (v : tangentFiberModel hφ hx) :
    tangentFiberTransitionEquiv hφ hx hψ hx' v = tangentFiberTransition hφ hx hψ hx' v :=
  tangentFiberEquiv_symm_trans hφ hx hψ hx' v

/-- **The Banach norm of `T_xX` through the chart `φ`** (2021 p. 39), pulled back along `Tφ`.
Not an instance: the norm depends on the chart (up to equivalence). -/
abbrev tangentFiberNormedAddCommGroup : NormedAddCommGroup (P.tangentFiber x) :=
  NormedAddCommGroup.induced (P.tangentFiber x) _ (tangentFiberLinearEquiv hφ hx).toLinearMap
    (tangentFiberLinearEquiv hφ hx).injective

/-- The normed-space structure of `T_xX` through the chart `φ`. -/
abbrev tangentFiberNormedSpace :
    @NormedSpace ℝ (P.tangentFiber x) _
      (tangentFiberNormedAddCommGroup hφ hx).toSeminormedAddCommGroup :=
  NormedSpace.induced ℝ (P.tangentFiber x) _ (tangentFiberLinearEquiv hφ hx).toLinearMap

/-- The norm through any chart induces the subspace topology of `T_xX ⊆ TX`. -/
theorem tangentFiberNormedAddCommGroup_toTopologicalSpace :
    @UniformSpace.toTopologicalSpace _
        (@PseudoMetricSpace.toUniformSpace _
          (tangentFiberNormedAddCommGroup hφ hx).toPseudoMetricSpace) =
      (instTopologicalSpaceSubtype : TopologicalSpace (P.tangentFiber x)) :=
  (UniformSpace.toTopologicalSpace_comap).trans
    ((tangentFiberContinuousLinearEquiv hφ hx).toHomeomorph.isInducing.eq_induced).symm

/-- `T_xX` is a Banach space for the norm through any chart (2021 p. 39). -/
theorem completeSpace_tangentFiber :
    @CompleteSpace (P.tangentFiber x)
      (@PseudoMetricSpace.toUniformSpace _
        (tangentFiberNormedAddCommGroup hφ hx).toPseudoMetricSpace) := by
  let _ := tangentFiberNormedAddCommGroup hφ hx
  exact (IsometryEquiv.completeSpace_iff
    ⟨(tangentFiberLinearEquiv hφ hx).toEquiv, Isometry.of_dist_eq fun _ _ => rfl⟩).2 inferInstance

/-! ### The sc-structure at a smooth point -/

include hφ hx in
/-- `x` is smooth iff `φ(x)` is a smooth point of `E`, for any chart `φ` around `x`. -/
theorem mem_smoothSet_iff_levelLift_mem_smoothLvl :
    P.levelVal 1 x ∈ P.smoothSet ↔ levelLift φ 1 (P.levelVal 1 x) ∈ φ.model.E.smoothLvl 1 := by
  rw [smoothSet, mem_iInter, ScScale.mem_smoothLvl_iff]
  constructor
  · intro h j
    obtain ⟨y, hy⟩ := (P.mem_levelSet_iff hφ hx).1 (h j)
    exact ⟨y, by rw [hy, P.toBase_levelLift hφ hx (levelVal_mem x)]⟩
  · intro h m
    obtain ⟨y, hy⟩ := h m
    refine (P.mem_levelSet_iff hφ hx).2 ⟨y, ?_⟩
    rw [hy, P.toBase_levelLift hφ hx (levelVal_mem x)]

/-- **`T_{φ(x)}O` is an sc-subspace of `E` at a smooth `x`** (2021 p. 39: "if `x ∈ X_∞`, the
tangent space `T_xX` is an sc-Banach space"): `T_xX` carries the sc-Banach space structure
`ScBanach.ofSubspace` of `T_{φ(x)}O = Dr(φ(x))E`, the range of the idempotent sc-operator
`Dr(φ(x))`. -/
theorem isScSubspace_tangentFiberModel (hs : P.levelVal 1 x ∈ P.smoothSet) :
    φ.model.E.IsScSubspace (tangentFiberModel hφ hx) := by
  set a := levelLift φ 1 (P.levelVal 1 x) with ha_def
  have has : a ∈ φ.model.E.smoothLvl 1 := (mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hx).1 hs
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have haR : a ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR]; exact levelLift_mem_lvlSet_one hφ hx
  have haU : a ∈ φ.model.E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 haR
  have heq : tangentFiberModel hφ hx =
      LinearMap.range (scDeriv R.U R a : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    apply SetLike.coe_injective
    rw [coe_tangentFiberModel, ← hR]
    exact tangentSpace_eq_coe_submodule R haR
  rw [heq]
  have hop : IsScOperator (scDeriv R.U R a) :=
    R.isSc1.isSc1With_scDeriv.scOperator_deriv haU has
  have hidem : ∀ v, hop.toScOperator 0 (hop.toScOperator 0 v) = hop.toScOperator 0 v := by
    rw [hop.toScOperator_zero]
    exact fun v => congrArg (fun L : φ.model.E 0 →L[ℝ] φ.model.E 0 => L v) (R.scDeriv_comp_self haR)
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.1

/-- At a smooth `x`, the fibre transition maps level `m` of `T_{φ(x)}O` into level `m` of
`T_{ψ(x)}O'`: the sc-structures of `T_xX` through two charts agree. -/
theorem transitionCLM_mem_range_toBase (hs : P.levelVal 1 x ∈ P.smoothSet) (m : ℕ)
    {v : φ.model.E 0} (hv : v ∈ range (φ.model.E.toBase m)) :
    transitionCLM hφ hx hψ hx' v ∈ range (ψ.model.E.toBase m) := by
  obtain ⟨Lm, hLm⟩ := isScOperator_transitionCLM hφ hx hψ hx'
    ((mem_smoothSet_iff_levelLift_mem_smoothLvl hφ hx).1 hs) m
  obtain ⟨w, rfl⟩ := hv
  exact ⟨Lm w, hLm w⟩

/-! ### Maps between fibres given in charts by linear maps -/

section FiberMap

universe v

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
variable {ψ' : MChart Y} {y : Q.Level 1} (hψ' : Q.IsChart ψ') (hy : Q.levelVal 1 y ∈ ψ'.source)
variable {F : P.tangentFiber x → Q.tangentFiber y}

/-- A map `F : T_xX → T_yY` which in charts `φ` around `x`, `ψ'` around `y` is given by a
continuous linear map `L : E → E'` (`Tψ' ∘ F = L ∘ Tφ`) maps `T_{φ(x)}O` into `T_{ψ'(y)}O'`
by `L`. -/
lemma mapsTo_of_chart_linear (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a))
    (v : tangentFiberModel hφ hx) : L v ∈ tangentFiberModel hψ' hy := by
  have := hL ((tangentFiberEquiv hφ hx).symm v)
  rw [Equiv.apply_symm_apply] at this
  rw [← this]; exact (tangentFiberEquiv hψ' hy _).2

/-- **A map between fibres which is linear in charts is a continuous linear map**: `F : T_xX → T_yY`
with `Tψ' ∘ F = L ∘ Tφ` for a continuous linear `L : E → E'` is `(Tψ')⁻¹ ∘ L ∘ Tφ`, a continuous
linear map `T_xX →L T_yY`. -/
def fiberMapCLM (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a)) :
    P.tangentFiber x →L[ℝ] Q.tangentFiber y :=
  ((tangentFiberContinuousLinearEquiv hψ' hy).symm : tangentFiberModel hψ' hy →L[ℝ] _).comp
    ((((L.comp (tangentFiberModel hφ hx).subtypeL).codRestrict (tangentFiberModel hψ' hy)
        (mapsTo_of_chart_linear hφ hx hψ' hy L hL))).comp
      (tangentFiberContinuousLinearEquiv hφ hx : P.tangentFiber x →L[ℝ] _))

theorem fiberMapCLM_apply (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a))
    (a : P.tangentFiber x) : fiberMapCLM hφ hx hψ' hy L hL a = F a := by
  apply (tangentFiberEquiv hψ' hy).injective
  apply Subtype.ext
  change ((tangentFiberEquiv hψ' hy) ((tangentFiberEquiv hψ' hy).symm _) : ψ'.model.E 0) = _
  rw [Equiv.apply_symm_apply]
  exact (hL a).symm

/-- A map between fibres which is linear in charts is additive and homogeneous. -/
theorem map_add_of_chart_linear (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a))
    (a b : P.tangentFiber x) : F (a + b) = F a + F b := by
  rw [← fiberMapCLM_apply hφ hx hψ' hy L hL, ← fiberMapCLM_apply hφ hx hψ' hy L hL a,
    ← fiberMapCLM_apply hφ hx hψ' hy L hL b, map_add]

theorem map_smul_of_chart_linear (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a))
    (c : ℝ) (a : P.tangentFiber x) : F (c • a) = c • F a := by
  rw [← fiberMapCLM_apply hφ hx hψ' hy L hL, ← fiberMapCLM_apply hφ hx hψ' hy L hL a, map_smul]

theorem continuous_of_chart_linear (L : φ.model.E 0 →L[ℝ] ψ'.model.E 0)
    (hL : ∀ a, (tangentFiberEquiv hψ' hy (F a) : ψ'.model.E 0) = L (tangentFiberEquiv hφ hx a)) :
    Continuous F := by
  have : F = fiberMapCLM hφ hx hψ' hy L hL :=
    funext fun a => (fiberMapCLM_apply hφ hx hψ' hy L hL a).symm
  rw [this]; exact (fiberMapCLM hφ hx hψ' hy L hL).continuous

end FiberMap

end MPolyfold

end Polyfold
