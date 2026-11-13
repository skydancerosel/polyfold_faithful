import Polyfold.Chapter4.VectorFieldsGlobal
import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter2.StrongBundlePullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4, **Proposition 4.4.5**
(p. 196) and Appendix 4.5, **Lemma 4.5.1** (p. 201): the **pull-back bundle `TX|X² → X²`** of which
the Lie bracket `[A, B]` is an sc-smooth section (gap G.92, second half).

# The pull-back bundle `TX|X² → X²`

## The text, paraphrased

(Proposition 4.4.5) For sc-smooth vector fields `A`, `B` on `X`, `[A, B]` is an sc-smooth section of
the bundle `TX|X² → X²`, the pull-back of `p : TX → X¹` by the inclusion `X² → X¹`.

## What is formalized

* `MPolyfold.tangentPullback P = {(x, α) ∈ X² × TX | p(α) = x}` (the total space of the pull-back,
  as in Definition 2.6.7 for strong bundles).
* `MPolyfold.isSubMPolyfold_tangentPullback`: it is a **sub-M-polyfold** of `X² × TX`.  Near a
  point, in the product chart `(z, (y, v))` of `X² × TX` (built from a chart `φ` of `X`), the
  retraction is `(z, (y, v)) ↦ (z, Tr(ι z, v))`, with `r` a retraction onto the model `O` of `φ`
  and `ι : E² → E¹` the inclusion: the composite of a linear sc-operator and `id × Tr`.
* `MPolyfold.tangentPullbackPolyfold`: the M-polyfold `TX|X²` (Proposition 2.3.19);
  `isScSmoothMap_tangentPullbackProj` (the projection `TX|X² → X²` is sc-smooth),
  `isScSmoothMap_tangentPullbackVec` (`TX|X² → TX` is sc-smooth), `tangentPullbackFiberEquiv`
  (the fibre over `x` is `T_xX`), `isScSmoothMap_tangentPullback_mk` (a pair `(g, s)` of
  sc-smooth maps with `p ∘ s = g` is sc-smooth into `TX|X²`).
* `MPolyfold.lieBracketSection` and `proposition_4_4_5_section` (**Proposition 4.4.5** in the
  text's form): `x ↦ (x, [A, B](x))` is an sc-smooth section of `TX|X² → X²`.
* `MPolyfold.tangentPullbackMap hf = (f₂, Tf) : TX|X² → TY|Y²` (sc-smooth,
  `isScSmoothMap_tangentPullbackMap`) and `lemma_4_5_1_section` (**Lemma 4.5.1** on sections):
  for `f` with `Tf ∘ A = A' ∘ f₁`, `Tf ∘ B = B' ∘ f₁`, `(f₂, Tf) ∘ [A, B] = [A', B'] ∘ f₂`.

## The reading

* The text gives no structure on `TX|X²`; we use the sub-M-polyfold structure inside `X² × TX`,
  the M-polyfold analogue of the pull-back of Definition 2.6.7.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### The local retraction `(z, (y, v)) ↦ (z, Tr(ι z, v))` -/

section Local

variable {E : ScBanach}

/-- The sc-operator `(z, (y, v)) ↦ (z, (ι z, v))` of `E² ⊕ TE`, `ι : E² → E¹` the inclusion. -/
def tangentPullbackOp (E : ScBanach) :
    ScOperator (E.shift.shift.prod E.tangent) (E.shift.shift.prod E.tangent) where
  lvl m := (ContinuousLinearMap.fst ℝ (E.shift.shift m) (E.tangent m)).prod
    (((E.shift.incl m).comp (ContinuousLinearMap.fst ℝ (E.shift.shift m) (E.tangent m))).prod
      ((ContinuousLinearMap.snd ℝ (E.shift m) (E m)).comp
        (ContinuousLinearMap.snd ℝ (E.shift.shift m) (E.tangent m))))
  incl_comm _ _ := rfl

/-- The model `O² × TO` of the product chart of `X² × TX`. -/
def tangentPullbackModel (E : ScBanach) (C O : Set (E 0)) :
    Set ((E.shift.shift.prod E.tangent) 0) :=
  E.shift.lvlSet (E.lvlSet O 1) 1 ×ˢ retractTangent E C O

variable {C O : Set (E 0)} (R : ScRetraction E C)

/-- The local retraction `(z, (y, v)) ↦ (z, Tr(ι z, v))`. -/
def tangentPullbackLocal (w : (E.shift.shift.prod E.tangent) 0) :
    (E.shift.shift.prod E.tangent) 0 :=
  (w.1, R.tangentRetraction ((E.shift.toBase 1 w.1, w.2.2) : E.tangent 0))

lemma tangentPullbackLocal_eq :
    tangentPullbackLocal R = Prod.map id R.tangentRetraction ∘ tangentPullbackOp E 0 := rfl

variable {R}

lemma toBase_mem_of_mem_model {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) : E.shift.toBase 1 w.1 ∈ E.lvlSet O 1 := hw.1

lemma mem_tangentRetraction_U (hR : R.retract = O) {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) :
    ((E.shift.toBase 1 w.1, w.2.2) : E.tangent 0) ∈ R.tangentRetraction.U := by
  subst hR
  exact R.retract_subset (toBase_mem_of_mem_model hw)

lemma tangentPullbackLocal_mem (hR : R.retract = O) {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) :
    tangentPullbackLocal R w ∈ tangentPullbackModel E C O := by
  refine ⟨hw.1, ?_⟩
  have h := R.tangentRetraction.apply_mem_retract (mem_tangentRetraction_U hR hw)
  rw [R.tangentRetraction_retract, hR] at h
  exact h

lemma tangentPullbackLocal_fst (w : (E.shift.shift.prod E.tangent) 0) :
    (tangentPullbackLocal R w).1 = w.1 := rfl

lemma tangentPullbackLocal_snd_fst (hR : R.retract = O) {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) :
    (tangentPullbackLocal R w).2.1 = E.shift.toBase 1 w.1 := by
  subst hR
  exact R.levelMap_one_eq_self (toBase_mem_of_mem_model hw)

lemma tangentPullbackLocal_idem (hR : R.retract = O) {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) :
    tangentPullbackLocal R (tangentPullbackLocal R w) = tangentPullbackLocal R w := by
  have h1 : ((E.shift.toBase 1 (tangentPullbackLocal R w).1, (tangentPullbackLocal R w).2.2) :
      E.tangent 0) = (tangentPullbackLocal R w).2 :=
    Prod.ext (tangentPullbackLocal_snd_fst hR hw).symm rfl
  change ((tangentPullbackLocal R w).1, R.tangentRetraction
    ((E.shift.toBase 1 (tangentPullbackLocal R w).1, (tangentPullbackLocal R w).2.2) :
      E.tangent 0)) = _
  rw [h1]
  exact Prod.ext rfl (R.tangentRetraction.idem _ (mem_tangentRetraction_U hR hw))

lemma tangentPullbackLocal_eq_self (hR : R.retract = O) {w : (E.shift.shift.prod E.tangent) 0}
    (hw : w ∈ tangentPullbackModel E C O) (h : w.2.1 = E.shift.toBase 1 w.1) :
    tangentPullbackLocal R w = w := by
  have h1 : ((E.shift.toBase 1 w.1, w.2.2) : E.tangent 0) = w.2 := Prod.ext h.symm rfl
  have h2 : w.2 ∈ R.tangentRetraction.retract := by
    rw [R.tangentRetraction_retract, hR]; exact hw.2
  change (w.1, R.tangentRetraction ((E.shift.toBase 1 w.1, w.2.2) : E.tangent 0)) = w
  rw [h1, R.tangentRetraction.apply_eq_self_of_mem_retract h2]

/-- **The local retraction is sc-smooth** on `O² × TO`. -/
theorem isScSmoothRetractMap_tangentPullbackLocal (hR : R.retract = O) :
    IsScSmoothRetractMap (E.shift.shift.prod E.tangent)
      (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C) (tangentPullbackModel E C O)
      (E.shift.shift.prod E.tangent) (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C)
      (tangentPullbackModel E C O) (tangentPullbackLocal R) := by
  subst hR
  have hO : IsScRetract (E.shift.shift.prod E.tangent)
      (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C)
      (tangentPullbackModel E C R.retract) :=
    R.isScRetract.shift.shift.prod R.isScRetract.tangentSet
  have hmid : IsScRetract (E.shift.shift.prod E.tangent)
      (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C)
      (E.shift.lvlSet (E.lvlSet R.retract 1) 1 ×ˢ E.tangentSet R.U) :=
    R.isScRetract.shift.shift.prod R.tangentRetraction.relOpen.isScRetract
  have hH : IsScSmoothRetractMap (E.shift.shift.prod E.tangent)
      (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C) (tangentPullbackModel E C R.retract)
      (E.shift.shift.prod E.tangent)
      (E.shift.lvlSet (E.lvlSet C 1) 1 ×ˢ E.tangentSet C)
      (E.shift.lvlSet (E.lvlSet R.retract 1) 1 ×ˢ E.tangentSet R.U)
      (tangentPullbackOp E 0) :=
    (tangentPullbackOp E).isScSmoothRetractMap hO fun w hw =>
      ⟨hw.1, mem_tangentRetraction_U rfl hw⟩
  have hTR : IsScSmoothRetractMap E.tangent (E.tangentSet C) (E.tangentSet R.U) E.tangent
      (E.tangentSet C) (retractTangent E C R.retract) R.tangentRetraction :=
    { mapsTo := fun p hp => by
        have h := R.tangentRetraction.apply_mem_retract hp
        rwa [R.tangentRetraction_retract] at h
      comp_isScSmooth := fun R' hR' =>
        IsScSmooth.comp R'.isScDomain R.tangentRetraction.isScDomain
          R.tangentRetraction.isScSmooth R'.isScSmooth fun y hy => by
            have h := R'.apply_mem_retract hy
            rw [hR'] at h
            exact h }
  have hG := IsScSmoothRetractMap.prodMap R.isScRetract.shift.shift
    R.tangentRetraction.relOpen.isScRetract
    (isScSmoothRetractMap_id (E := E.shift.shift) (C := E.shift.lvlSet (E.lvlSet C 1) 1)
      (E.shift.lvlSet (E.lvlSet R.retract 1) 1)) hTR
  exact hG.comp hH hmid

end Local

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- `X² × TX` is paracompact (Theorem 2.3.10 for `X²` and `TX`). -/
instance paracompactSpace_levelTwo_prod_tangentSpace :
    ParacompactSpace (P.shift.Level 1 × P.TangentSpace) :=
  paracompactSpace_prod P.shift.shift P.tangentPolyfold

variable (P) in
/-- **The pull-back `TX|X² = {(x, α) ∈ X² × TX | p(α) = x}`** of `p : TX → X¹` by the inclusion
`X² → X¹` (Proposition 4.4.5; Definition 2.6.7 for the pull-back). -/
def tangentPullback : Set (P.shift.Level 1 × P.TangentSpace) :=
  {q | P.tangentProj q.2 = P.shift.levelVal 1 q.1}

/-- A retraction onto the model `O` of a chart. -/
def chartRetr (φ : MChart X) : ScRetraction φ.model.E φ.model.C := φ.model.isScRetract.choose

omit [T2Space X] [ParacompactSpace X] in
lemma chartRetr_retract (φ : MChart X) : (chartRetr φ).retract = φ.model.O :=
  φ.model.isScRetract.choose_spec

section Chart

variable {φ : MChart X} (hφ : P.IsChart φ) (x₁ : P.Level 1) (x₀ : P.shift.Level 1)
  (α₀ : P.TangentSpace)

/-- The product chart `(z, (y, v))` of `X² × TX` built from a chart `φ` of `X`. -/
def tangentPullbackChart : MChart (P.shift.Level 1 × P.TangentSpace) :=
  (levelChart (shift_isChart hφ x₁) x₀).prod (tangentChart hφ α₀)

lemma tangentPullbackChart_isChart :
    (P.shift.shift.prod P.tangentPolyfold).IsChart (tangentPullbackChart hφ x₁ x₀ α₀) :=
  IsChart.prod (shift_isChart (shift_isChart hφ x₁) x₀) (P.tangentPolyfold_isChart hφ α₀)

lemma tangentPullbackChart_model_O :
    (tangentPullbackChart hφ x₁ x₀ α₀).model.O =
      tangentPullbackModel φ.model.E φ.model.C φ.model.O := rfl

omit hφ in
/-- `levelLift φ 1` is injective on `V ∩ X₁`. -/
lemma levelLift_injOn (hφ : P.IsChart φ) {a b : X} (ha : a ∈ φ.source) (hb : b ∈ φ.source)
    (ha1 : a ∈ P.levelSet 1)
    (hb1 : b ∈ P.levelSet 1) (h : levelLift φ 1 a = levelLift φ 1 b) : a = b := by
  have h' := congrArg (φ.model.E.toBase 1) h
  rw [P.toBase_levelLift hφ ha ha1, P.toBase_levelLift hφ hb hb1] at h'
  exact φ.toPartialEquiv.injOn ha hb h'

/-- **The pull-back in the chart**: on the domain of the chart, `p(α) = x` iff `y = ι z`. -/
theorem mem_tangentPullback_iff {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    q ∈ P.tangentPullback ↔ (tangentPullbackChart hφ x₁ x₀ α₀ q).2.1 =
      φ.model.E.shift.toBase 1 (tangentPullbackChart hφ x₁ x₀ α₀ q).1 := by
  have h1 : (tangentPullbackChart hφ x₁ x₀ α₀ q).2.1 =
      levelLift φ 1 (P.levelVal 1 (P.tangentProj q.2)) := tangentChartMap_fst hφ hq.2
  have h2 : φ.model.E.shift.toBase 1 (tangentPullbackChart hφ x₁ x₀ α₀ q).1 =
      levelLift φ 1 (P.levelVal 1 (P.shift.levelVal 1 q.1)) :=
    P.shift.toBase_levelLift (shift_isChart hφ x₁) hq.1 (levelVal_mem _)
  rw [h1, h2]
  constructor
  · intro h
    change P.tangentProj q.2 = P.shift.levelVal 1 q.1 at h
    rw [h]
  · intro h
    exact level_ext (levelLift_injOn hφ hq.2 hq.1 (levelVal_mem _) (levelVal_mem _) h)

/-- The local retraction of `X² × TX` onto `TX|X²` in the chart: `q ↦ χ⁻¹(F(χ(q)))`. -/
def tangentPullbackRetr (q : P.shift.Level 1 × P.TangentSpace) :
    P.shift.Level 1 × P.TangentSpace :=
  (tangentPullbackChart hφ x₁ x₀ α₀).symm
    (tangentPullbackLocal (chartRetr φ) (tangentPullbackChart hφ x₁ x₀ α₀ q))

variable {hφ x₁ x₀ α₀}

lemma tangentPullbackLocal_chart_mem {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    tangentPullbackLocal (chartRetr φ) (tangentPullbackChart hφ x₁ x₀ α₀ q) ∈
      (tangentPullbackChart hφ x₁ x₀ α₀).model.O :=
  tangentPullbackLocal_mem (chartRetr_retract φ)
    ((tangentPullbackChart hφ x₁ x₀ α₀).mapsTo_model q hq)

lemma tangentPullbackRetr_mem_source {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    tangentPullbackRetr hφ x₁ x₀ α₀ q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source :=
  (tangentPullbackChart hφ x₁ x₀ α₀).symm_mapsTo (tangentPullbackLocal_chart_mem hq)

lemma chart_tangentPullbackRetr {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    tangentPullbackChart hφ x₁ x₀ α₀ (tangentPullbackRetr hφ x₁ x₀ α₀ q) =
      tangentPullbackLocal (chartRetr φ) (tangentPullbackChart hφ x₁ x₀ α₀ q) :=
  (tangentPullbackChart hφ x₁ x₀ α₀).apply_symm_apply (tangentPullbackLocal_chart_mem hq)

lemma tangentPullbackRetr_idem {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    tangentPullbackRetr hφ x₁ x₀ α₀ (tangentPullbackRetr hφ x₁ x₀ α₀ q) =
      tangentPullbackRetr hφ x₁ x₀ α₀ q := by
  have e := chart_tangentPullbackRetr hq
  have e2 := tangentPullbackLocal_idem (chartRetr_retract φ)
    ((tangentPullbackChart hφ x₁ x₀ α₀).mapsTo_model q hq)
  exact (congrArg (fun w => (tangentPullbackChart hφ x₁ x₀ α₀).symm
    (tangentPullbackLocal (chartRetr φ) w)) e).trans
    (congrArg (tangentPullbackChart hφ x₁ x₀ α₀).symm e2)

lemma tangentPullbackRetr_mem {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) :
    tangentPullbackRetr hφ x₁ x₀ α₀ q ∈ P.tangentPullback := by
  rw [mem_tangentPullback_iff hφ x₁ x₀ α₀ (tangentPullbackRetr_mem_source hq),
    chart_tangentPullbackRetr hq]
  exact tangentPullbackLocal_snd_fst (chartRetr_retract φ)
    ((tangentPullbackChart hφ x₁ x₀ α₀).mapsTo_model q hq)

lemma tangentPullbackRetr_eq_self {q : P.shift.Level 1 × P.TangentSpace}
    (hq : q ∈ (tangentPullbackChart hφ x₁ x₀ α₀).source) (hqS : q ∈ P.tangentPullback) :
    tangentPullbackRetr hφ x₁ x₀ α₀ q = q := by
  unfold tangentPullbackRetr
  rw [tangentPullbackLocal_eq_self (chartRetr_retract φ)
    ((tangentPullbackChart hφ x₁ x₀ α₀).mapsTo_model q hq)
    ((mem_tangentPullback_iff hφ x₁ x₀ α₀ hq).1 hqS)]
  exact (tangentPullbackChart hφ x₁ x₀ α₀).symm_apply_apply hq

variable (hφ x₁ x₀ α₀) in
/-- **The local retraction is sc-smooth** on the domain of the chart: in the chart it is
`(z, (y, v)) ↦ (z, Tr(ι z, v))` (`isScSmoothRetractMap_tangentPullbackLocal`). -/
theorem isScSmoothOn_tangentPullbackRetr :
    (P.shift.shift.prod P.tangentPolyfold).IsScSmoothOn (P.shift.shift.prod P.tangentPolyfold)
      (tangentPullbackRetr hφ x₁ x₀ α₀) (tangentPullbackChart hφ x₁ x₀ α₀).source := by
  have hF : IsScSmoothRetractMap (tangentPullbackChart hφ x₁ x₀ α₀).model.E
      (tangentPullbackChart hφ x₁ x₀ α₀).model.C (tangentPullbackChart hφ x₁ x₀ α₀).model.O
      (tangentPullbackChart hφ x₁ x₀ α₀).model.E (tangentPullbackChart hφ x₁ x₀ α₀).model.C
      (tangentPullbackChart hφ x₁ x₀ α₀).model.O (tangentPullbackLocal (chartRetr φ)) :=
    isScSmoothRetractMap_tangentPullbackLocal (chartRetr_retract φ)
  have hcont : ContinuousOn (tangentPullbackRetr hφ x₁ x₀ α₀)
      (tangentPullbackChart hφ x₁ x₀ α₀).source :=
    (tangentPullbackChart hφ x₁ x₀ α₀).continuousOn_invFun.comp
      ((hF.continuousOn (tangentPullbackChart hφ x₁ x₀ α₀).model.isScRetract).comp
        (tangentPullbackChart hφ x₁ x₀ α₀).continuousOn_toFun
        fun q hq => (tangentPullbackChart hφ x₁ x₀ α₀).mapsTo_model q hq)
      fun q hq => tangentPullbackLocal_chart_mem hq
  refine IsScSmoothOn.of_exists_charts (tangentPullbackChart hφ x₁ x₀ α₀).isOpen_source hcont
    fun q hq => ⟨tangentPullbackChart hφ x₁ x₀ α₀, tangentPullbackChart hφ x₁ x₀ α₀,
      (tangentPullbackChart hφ x₁ x₀ α₀).source, tangentPullbackChart_isChart hφ x₁ x₀ α₀,
      tangentPullbackChart_isChart hφ x₁ x₀ α₀, (tangentPullbackChart hφ x₁ x₀ α₀).isOpen_source,
      hq, fun y hy => ⟨hy, hy⟩, fun y hy => tangentPullbackRetr_mem_source hy, ?_⟩
  rw [(tangentPullbackChart hφ x₁ x₀ α₀).image_source]
  refine hF.congr fun w hw => ?_
  have h1 := (tangentPullbackChart hφ x₁ x₀ α₀).symm_mapsTo hw
  exact ((chart_tangentPullbackRetr h1).trans (congrArg (tangentPullbackLocal (chartRetr φ))
    ((tangentPullbackChart hφ x₁ x₀ α₀).apply_symm_apply hw))).symm

variable (hφ x₁ x₀ α₀) in
/-- The data of Definition 2.3.18 for `TX|X² ⊆ X² × TX` on the domain of a product chart. -/
def tangentPullbackSubData :
    (P.shift.shift.prod P.tangentPolyfold).SubData P.tangentPullback where
  V := (tangentPullbackChart hφ x₁ x₀ α₀).source
  r := tangentPullbackRetr hφ x₁ x₀ α₀
  isOpen := (tangentPullbackChart hφ x₁ x₀ α₀).isOpen_source
  mapsTo _ hq := tangentPullbackRetr_mem_source hq
  isScSmoothOn := isScSmoothOn_tangentPullbackRetr hφ x₁ x₀ α₀
  idem _ hq := tangentPullbackRetr_idem hq
  image := by
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨tangentPullbackRetr_mem hq', tangentPullbackRetr_mem_source hq'⟩
    · rintro ⟨hqS, hq⟩
      exact ⟨q, hq, tangentPullbackRetr_eq_self hq hqS⟩

end Chart

/-! ### The M-polyfold `TX|X²` -/

/-- **`TX|X²` is a sub-M-polyfold of `X² × TX`** (Definition 2.3.18). -/
theorem isSubMPolyfold_tangentPullback :
    (P.shift.shift.prod P.tangentPolyfold).IsSubMPolyfold P.tangentPullback := by
  intro q hq
  have hq' : P.tangentProj q.2 = P.shift.levelVal 1 q.1 := hq
  have hmem : q ∈ (tangentPullbackChart
      (P.someChart_isChart (P.levelVal 1 (P.shift.levelVal 1 q.1)))
      (P.shift.levelVal 1 q.1) q.1 q.2).source := by
    refine ⟨P.mem_someChart_source _, ?_⟩
    change P.levelVal 1 (P.tangentProj q.2) ∈
      (P.someChart (P.levelVal 1 (P.shift.levelVal 1 q.1))).source
    rw [hq']
    exact P.mem_someChart_source _
  let d := tangentPullbackSubData (P.someChart_isChart (P.levelVal 1 (P.shift.levelVal 1 q.1)))
    (P.shift.levelVal 1 q.1) q.1 q.2
  exact ⟨d.V, d.isOpen, hmem, d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

instance paracompactSpace_tangentPullback : ParacompactSpace P.tangentPullback :=
  (P.shift.shift.prod P.tangentPolyfold).paracompactSpace_subtype P.tangentPullback

variable (P) in
/-- **The M-polyfold `TX|X²`** (Proposition 2.3.19): the sub-M-polyfold
`{(x, α) | p(α) = x}` of `X² × TX`. -/
def tangentPullbackPolyfold : MPolyfold P.tangentPullback :=
  subPolyfold isSubMPolyfold_tangentPullback

/-- The projection `TX|X² → X²`, `(x, α) ↦ x`. -/
def tangentPullbackProj (q : P.tangentPullback) : P.shift.Level 1 := q.1.1

/-- The map `TX|X² → TX`, `(x, α) ↦ α`. -/
def tangentPullbackVec (q : P.tangentPullback) : P.TangentSpace := q.1.2

lemma tangentProj_tangentPullbackVec (q : P.tangentPullback) :
    P.tangentProj (tangentPullbackVec q) = P.shift.levelVal 1 (tangentPullbackProj q) := q.2

/-- The projection `TX|X² → X²` is sc-smooth. -/
theorem isScSmoothMap_tangentPullbackProj :
    P.tangentPullbackPolyfold.IsScSmoothMap P.shift.shift (tangentPullbackProj (P := P)) :=
  IsScSmoothOn.comp (isScSmoothMap_fst (P := P.shift.shift) (Q := P.tangentPolyfold))
    (subPolyfold_inclusion_isScSmooth _) (mapsTo_univ _ _)

/-- The map `TX|X² → TX` is sc-smooth. -/
theorem isScSmoothMap_tangentPullbackVec :
    P.tangentPullbackPolyfold.IsScSmoothMap P.tangentPolyfold (tangentPullbackVec (P := P)) :=
  IsScSmoothOn.comp (isScSmoothMap_snd (P := P.shift.shift) (Q := P.tangentPolyfold))
    (subPolyfold_inclusion_isScSmooth _) (mapsTo_univ _ _)

/-- The fibre of `TX|X² → X²` over `x ∈ X²` is the tangent space `T_xX`. -/
def tangentPullbackFiberEquiv (x : P.shift.Level 1) :
    {q : P.tangentPullback // tangentPullbackProj q = x} ≃
      P.tangentFiber (P.shift.levelVal 1 x) where
  toFun q := ⟨tangentPullbackVec q.1, by
    obtain ⟨⟨⟨y, α⟩, h⟩, rfl⟩ := q
    exact h⟩
  invFun α := ⟨⟨(x, α.1), α.2⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨y, α⟩, h⟩, rfl⟩ := q
    rfl
  right_inv _ := rfl

/-! ### Maps into `TX|X²` -/

section IntoPullback

universe v w

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

omit [T2Space X] [ParacompactSpace X] in
/-- Sc-smoothness on an open set is local (as `IsScSmoothOn.of_locally` of `Chapter7/Discrete`). -/
private theorem isScSmoothOn_of_locally_pb {f : Z → Y} {U : Set Z} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ U' : Set Z, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ S.IsScSmoothOn Q f U') :
    S.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨U', hU', hxU', -, hf⟩ := h x hx
    exact (hf.continuousOn.continuousAt (hU'.mem_nhds hxU')).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨U', hU', hxU', hU'U, hf⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := S.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  have hVo : IsOpen ((U' ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hU'.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hVo, ⟨⟨hxU', hxφ⟩, hfx⟩, fun y hy => ⟨hU'U hy.1.1, hy.1.2⟩,
    fun y hy => hy.2, hf.smooth φ ψ hφ hψ _ hVo (fun y hy => hy.1) fun y hy => hy.2⟩

omit [T2Space X] [ParacompactSpace X] in
/-- A map into a sub-M-polyfold is sc-smooth into it if it is sc-smooth into the ambient
M-polyfold (Proposition 2.3.19 (2), as `isScSmoothOn_subPolyfold_of_val` of `Chapter9`). -/
private theorem isScSmoothOn_subPolyfold_of_val_pb {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : Z → A} {U : Set Z}
    (hf : S.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    S.IsScSmoothOn (subPolyfold hA) f U := by
  refine isScSmoothOn_of_locally_pb hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

/-- **Maps into `TX|X²`**: `z ↦ (g(z), s(z))` with `g : Z → X²`, `s : Z → TX` sc-smooth and
`p ∘ s = g` is sc-smooth into `TX|X²`. -/
theorem isScSmoothMap_tangentPullback_mk {g : Z → P.shift.Level 1} {s : Z → P.TangentSpace}
    (hg : S.IsScSmoothMap P.shift.shift g) (hs : S.IsScSmoothMap P.tangentPolyfold s)
    (hgs : ∀ z, P.tangentProj (s z) = P.shift.levelVal 1 (g z)) :
    S.IsScSmoothMap P.tangentPullbackPolyfold
      (fun z => (⟨(g z, s z), hgs z⟩ : P.tangentPullback)) :=
  isScSmoothOn_subPolyfold_of_val_pb isSubMPolyfold_tangentPullback (IsScSmoothOn.prodMk hg hs)

end IntoPullback

/-! ### The bracket as a section of `TX|X² → X²` (Proposition 4.4.5) and Lemma 4.5.1 -/

section Bracket

variable {A B : P.Level 1 → P.TangentSpace}

/-- The section `x ↦ (x, [A, B](x))` of `TX|X² → X²`. -/
def lieBracketSection (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : P.shift.Level 1) : P.tangentPullback :=
  ⟨(x, lieBracket hA hB x), tangentProj_lieBracket hA hB x⟩

/-- **2021 Proposition 4.4.5, p. 196** (2017: Proposition 4.5), in the text's form: **`[A, B]` is an
sc-smooth section of the pull-back bundle `TX|X² → X²`**. -/
theorem _root_.Polyfold.proposition_4_4_5_section (hA : P.IsScVectorField A)
    (hB : P.IsScVectorField B) :
    P.shift.shift.IsScSmoothMap P.tangentPullbackPolyfold (lieBracketSection hA hB) ∧
      ∀ x, tangentPullbackProj (lieBracketSection hA hB x) = x :=
  ⟨isScSmoothMap_tangentPullback_mk isScSmoothMap_id (proposition_4_4_5 hA hB).1
    (tangentProj_lieBracket hA hB), fun _ => rfl⟩

universe v

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} (hf : P.IsScSmoothMap Q f)

lemma tangentProj_tangentMap_levelTwoMap {x : P.shift.Level 1} {α : P.TangentSpace}
    (hα : P.tangentProj α = P.shift.levelVal 1 x) :
    Q.tangentProj (tangentMap hf α) = Q.shift.levelVal 1 (levelTwoMap hf x) := by
  apply level_ext
  rw [levelVal_tangentProj_tangentMap, hα]
  rfl

/-- The bundle map `(f₂, Tf) : TX|X² → TY|Y²`, `(x, α) ↦ (f₂(x), Tf(α))`. -/
def tangentPullbackMap (q : P.tangentPullback) : Q.tangentPullback :=
  ⟨(levelTwoMap hf (tangentPullbackProj q), tangentMap hf (tangentPullbackVec q)),
    tangentProj_tangentMap_levelTwoMap hf (tangentProj_tangentPullbackVec q)⟩

/-- The bundle map `TX|X² → TY|Y²` is sc-smooth. -/
theorem isScSmoothMap_tangentPullbackMap :
    P.tangentPullbackPolyfold.IsScSmoothMap Q.tangentPullbackPolyfold (tangentPullbackMap hf) := by
  have h1 : P.shift.IsScSmoothMap Q.shift (liftLevelOneMap hf) :=
    IsScSmoothMap.levelOne hf fun _ => rfl
  have h2 : P.shift.shift.IsScSmoothMap Q.shift.shift (levelTwoMap hf) :=
    IsScSmoothMap.levelOne h1 fun _ => rfl
  have h3 : P.tangentPullbackPolyfold.IsScSmoothMap Q.shift.shift
      (fun q => levelTwoMap hf (tangentPullbackProj q)) :=
    IsScSmoothOn.comp h2 isScSmoothMap_tangentPullbackProj (mapsTo_univ _ _)
  have h4 : P.tangentPullbackPolyfold.IsScSmoothMap Q.tangentPolyfold
      (fun q => tangentMap hf (tangentPullbackVec q)) :=
    IsScSmoothOn.comp (tangentMap_isScSmooth hf) isScSmoothMap_tangentPullbackVec
      (mapsTo_univ _ _)
  exact isScSmoothMap_tangentPullback_mk h3 h4
    fun q => tangentProj_tangentMap_levelTwoMap hf (tangentProj_tangentPullbackVec q)

/-- The bundle map covers `f₂`. -/
lemma tangentPullbackProj_tangentPullbackMap (q : P.tangentPullback) :
    tangentPullbackProj (tangentPullbackMap hf q) = levelTwoMap hf (tangentPullbackProj q) := rfl

variable {A' B' : Q.Level 1 → Q.TangentSpace}

/-- **2021 Lemma 4.5.1, p. 201** on sections of the pull-back bundle: if
`Tf ∘ A = A' ∘ f₁` and `Tf ∘ B = B' ∘ f₁` on `X¹`, the bundle map `(f₂, Tf) : TX|X² → TY|Y²`
maps the section `[A, B]` to the section `[A', B']`: `(f₂, Tf) ∘ [A, B] = [A', B'] ∘ f₂`. -/
theorem _root_.Polyfold.lemma_4_5_1_section (hA : P.IsScVectorField A)
    (hB : P.IsScVectorField B) (hA' : Q.IsScVectorField A') (hB' : Q.IsScVectorField B')
    (hAf : ∀ x, tangentMap hf (A x) = A' (liftLevelOneMap hf x))
    (hBf : ∀ x, tangentMap hf (B x) = B' (liftLevelOneMap hf x)) (x : P.shift.Level 1) :
    tangentPullbackMap hf (lieBracketSection hA hB x) =
      lieBracketSection hA' hB' (levelTwoMap hf x) :=
  Subtype.ext (Prod.ext rfl (lemma_4_5_1 hf hA hB hA' hB' hAf hBf x))

end Bracket

end MPolyfold

end Polyfold
