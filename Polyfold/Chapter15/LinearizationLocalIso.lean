import Polyfold.Chapter15.ParametricGeneralPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 683–687) and §15.3, **Definition 15.3.5** (p. 693): the linearization `T(f, Λ)` and
general position, carried along a local strong bundle isomorphism between two strong bundles.

# `T(f, Λ)` along a local strong bundle isomorphism `W|U → W'|U'`

## The text, paraphrased

(§15.1) `T(f, Λ)(x) = ∑ σᵢ · (f − sᵢ)'(x)` for a local section structure `(sᵢ, σᵢ)` of `Λ` near
`x`.  (Definition 15.3.5) `(f, Λ)` is in general position if at every `x ∈ supp(Λ ∘ f)` every
operator of `T(f, Λ)(x)` maps the reduced tangent space `T^R_xX` onto `W_x`.  The text uses
both notions for strong bundles over ep-groupoids and passes to polyfolds through the models
(§16.6), where two models differ by a generalized strong bundle isomorphism, locally a strong
bundle isomorphism `Φ : W|U → W'|U'` covering an sc-diffeomorphism `ϕ : U → U'`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For two strong bundles over ep-groupoids `A`, `A'` and a local strong bundle isomorphism
`L : W|U → W'|U'` (Part I's `StrongBundle.LocalIso`, with `ϕ`, `Φ` and the inverses `g`, `Ψ`):

* `isoSec L s' = Ψ ∘ s' ∘ ϕ`, `isoSet L O' = U ∩ ϕ⁻¹(O')`: a local section of `W'` near `U'`
  carried to `W`; `isScPlusSectionOn_isoSec`, `isLocalRepOn_isoSec` (a local section structure of
  `Λ'` is carried to one of `Λ` if `Λ = Λ' ∘ Φ` over `U`).
* `tangentIso : T_xX ≃ T_{x'}X'` for `ϕ(x) = x'`, the identity of the chart vectors of a chart
  `c'` at `x'` and of the carried chart `c' ∘ Φ` at `x` (`coe_tangentFiberEquiv_tangentIso`);
  `mem_reducedTangentFiber_tangentIso_iff`: it maps `T^R_xX` onto `T^R_{x'}X'`.
* `fiberLin_toIntr_tangentIso`: the intrinsic operators of one chart operator through `c' ∘ Φ`
  at `x` and through `c'` at `x'` agree in the fibre coordinates;
  `surjective_toIntr_transportChart_iff`: one is onto `W_x` on `T^R_xX` iff the other is onto
  `W'_{x'}` on `T^R_{x'}X'`.
* `subDeriv_transportChart`: the chart operators `D((f̂ − ŝ) ∘ r)` of `(f, Ψ ∘ s' ∘ ϕ)` in
  `c' ∘ Φ` and of `(f', s')` in `c'` are equal, for `f = Ψ ∘ f' ∘ ϕ` on `U`.
* **`isReducedOntoAtLevel_localIso_iff`**: for sc-Fredholm section functors `f`, `f'` with
  `f = Ψ ∘ f' ∘ ϕ` on `U`, an sc⁺-multisection `Λ'` and `Λ = Λ' ∘ Φ` over `U`: the reduced
  linearization of `(f, Λ)` is onto at `x ∈ U` iff that of `(f', Λ')` is onto at `ϕ(x)`.

## Reading

The statements are at level-`1` points, where `T(f, Λ)` is defined in this project (the text
states them at smooth points).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15 StrongBundle

variable {A A' : SEP.{u}} {U : Set A.Obj} {U' : Set A'.Obj}
  (L : StrongBundle.LocalIso A.B A'.B U U')

/-! ### Local sections carried along a local strong bundle isomorphism -/

/-- A local section `s'` of `W'` carried to `W` by the local strong bundle isomorphism:
`z ↦ Ψ(s'(ϕ z))`. -/
def isoSec (s' : A'.Obj → A'.W) : A.Obj → A.W := fun z => L.Ψ (s' (L.ϕ z))

/-- The domain `U ∩ ϕ⁻¹(O')` of the carried section. -/
def isoSet (O' : Set A'.Obj) : Set A.Obj := U ∩ L.ϕ ⁻¹' O'

lemma isOpen_isoSet {O' : Set A'.Obj} (hO' : IsOpen O') : IsOpen (isoSet L O') :=
  L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage L.isOpen_U hO'

lemma P_isoSec {s' : A'.Obj → A'.W} {O' : Set A'.Obj} (hsec : ∀ y ∈ O', A'.P (s' y) = y)
    (hO's : O' ⊆ U') {z : A.Obj} (hz : z ∈ isoSet L O') : A.P (isoSec L s' z) = z := by
  have h1 : A'.P (s' (L.ϕ z)) ∈ U' := by rw [hsec _ hz.2]; exact hO's hz.2
  change A.P (L.Ψ (s' (L.ϕ z))) = z
  rw [L.covers_inv _ h1, hsec _ hz.2]
  exact L.base.left_inv z hz.1

/-- **The carried section is an sc⁺-section on `U ∩ ϕ⁻¹(O')`.** -/
theorem isScPlusSectionOn_isoSec {s' : A'.Obj → A'.W} {O' : Set A'.Obj} (hO' : IsOpen O')
    (hO's : O' ⊆ U') (hs : IsScPlusSectionOn A' s' O') :
    IsScPlusSectionOn A (isoSec L s') (isoSet L O') := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  refine ⟨fun z hz => P_isoSec L hsec hO's hz, fun z => L.Ψ₁ (G (L.ϕ z)), fun z hz => ?_, ?_⟩
  · have h1 : A'.P (A'.B.oneVal (G (L.ϕ z))) ∈ U' := by
      rw [hG _ hz.2, hsec _ hz.2]; exact hO's hz.2
    rw [L.oneVal_Ψ₁ _ h1, hG _ hz.2]
    rfl
  · have hϕ : A.X.PObj.IsScSmoothOn A'.X.PObj L.ϕ (isoSet L O') :=
      L.base.isScSmoothOn.mono (isOpen_isoSet L hO') inter_subset_left
    have hGϕ := MPolyfold.IsScSmoothOn.comp hGs hϕ fun z hz => hz.2
    refine MPolyfold.IsScSmoothOn.comp L.one.isScSmoothOn_inv hGϕ fun z hz => ?_
    change A'.P (A'.B.oneVal (G (L.ϕ z))) ∈ U'
    rw [hG _ hz.2, hsec _ hz.2]; exact hO's hz.2

open scoped Classical in
/-- **A local section structure of `Λ'` is carried to one of `Λ`**, if `Λ = Λ' ∘ Φ` over `U`:
the carried sections with the same weights represent `Λ` on `U ∩ ϕ⁻¹(O')`. -/
theorem isLocalRepOn_isoSec {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0}
    (hΛ : ∀ w, A.P w ∈ U → Λ w = Λ' (L.Φ w)) {O' : Set A'.Obj} (hO' : IsOpen O')
    (hO's : O' ⊆ U') {k : ℕ} {s' : Fin k → A'.Obj → A'.W} {σ : Fin k → ℚ≥0}
    (hs : IsLocalRepOn A' Λ' O' s' σ) :
    IsLocalRepOn A Λ (isoSet L O') (fun i => isoSec L (s' i)) σ := by
  refine ⟨hs.1, fun i => isScPlusSectionOn_isoSec L hO' hO's (hs.2.1 i), hs.2.2.1,
    fun w hw => ?_⟩
  have hwU : A.P w ∈ U := hw.1
  have hPΦ : A'.P (L.Φ w) = L.ϕ (A.P w) := L.covers w hwU
  rw [hΛ w hwU, hs.2.2.2 _ (by rw [hPΦ]; exact hw.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsec := (hs.2.1 i).1
  have hiff : L.Φ w = s' i (A'.P (L.Φ w)) ↔ w = isoSec L (s' i) (A.P w) := by
    rw [hPΦ]
    constructor
    · intro h
      change w = L.Ψ (s' i (L.ϕ (A.P w)))
      rw [← h]; exact (L.zero.left_inv w hwU).symm
    · intro h
      have h1 : s' i (L.ϕ (A.P w)) ∈ A'.P ⁻¹' U' := by
        change A'.P (s' i (L.ϕ (A.P w))) ∈ U'
        rw [hsec _ hw.2]; exact hO's hw.2
      exact (congrArg L.Φ h).trans (L.zero.right_inv _ h1)
  by_cases h : w = isoSec L (s' i) (A.P w)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

/-! ### The carried chart -/

variable {c' : StrongBundleChart A'.X.PObj A'.P} (hsub : c'.φ.source ⊆ U')

/-- The principal part of a carried local section in the carried chart is that of the section
in the original chart, on the retract `O`. -/
lemma principal_transportChart_isoSec {s' : A'.Obj → A'.W} {O' : Set A'.Obj}
    (hsec : ∀ y ∈ O', A'.P (s' y) = y) (hsubO : c'.φ.source ⊆ O') {z : c'.φ.model.E 0}
    (hz : z ∈ c'.φ.model.O) :
    (L.transportChart c' hsub).principal (isoSec L s') z = c'.principal s' z := by
  have hw : c'.φ.symm z ∈ c'.φ.source := c'.φ.symm_mapsTo hz
  have hwU' : c'.φ.symm z ∈ U' := hsub hw
  change (c' (L.Φ (L.Ψ (s' (L.ϕ (L.g (c'.φ.symm z))))))).2 = (c' (s' (c'.φ.symm z))).2
  rw [L.base.right_inv _ hwU', L.zero.right_inv _ (show A'.P (s' _) ∈ _ by
    rw [hsec _ (hsubO hw)]; exact hwU')]

variable {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1}
  (hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x')
  (hx : A.X.PObj.levelVal 1 x ∈ (L.transportChart c' hsub).φ.source)
  (hx' : A'.X.PObj.levelVal 1 x' ∈ c'.φ.source)

include hϕ in
/-- The level-`1` chart points agree. -/
lemma levelLift_transportChart :
    levelLift (L.transportChart c' hsub).φ 1 (A.X.PObj.levelVal 1 x) =
      levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x') := by
  change Function.invFun (c'.φ.model.E.toBase 1) (c'.φ (L.ϕ (A.X.PObj.levelVal 1 x))) = _
  rw [hϕ]; rfl

include hϕ in
/-- The tangent spaces of the two charts at the common chart point agree. -/
lemma mem_tangentFiberModel_transportChart_iff (v : c'.φ.model.E 0) :
    v ∈ tangentFiberModel (L.transportChart c' hsub).isChart hx ↔
      v ∈ tangentFiberModel c'.isChart hx' := by
  have hO := L.transportChart_model_O c' hsub
  have hl := levelLift_transportChart L hsub hϕ
  change ((levelLift (L.transportChart c' hsub).φ 1 (A.X.PObj.levelVal 1 x), v) :
      c'.φ.model.E.tangent 0) ∈
        retractTangent c'.φ.model.E c'.φ.model.C (L.transportChart c' hsub).φ.model.O ↔
    ((levelLift c'.φ 1 (A'.X.PObj.levelVal 1 x'), v) : c'.φ.model.E.tangent 0) ∈
        retractTangent c'.φ.model.E c'.φ.model.C c'.φ.model.O
  rw [hO, hl]

/-- **`T_xX ≃ T_{x'}X'`** for `ϕ(x) = x'`: the identity of the chart vectors of `c'` at `x'` and
of the carried chart `c' ∘ Φ` at `x` (the tangent map of `ϕ`, read in these charts). -/
def tangentIso : A.X.PObj.tangentFiber x ≃ A'.X.PObj.tangentFiber x' where
  toFun α := (tangentFiberEquiv c'.isChart hx').symm
    ⟨((tangentFiberEquiv (L.transportChart c' hsub).isChart hx α).1 : c'.φ.model.E 0),
      (mem_tangentFiberModel_transportChart_iff L hsub hϕ hx hx' _).1
        (tangentFiberEquiv (L.transportChart c' hsub).isChart hx α).2⟩
  invFun α' := (tangentFiberEquiv (L.transportChart c' hsub).isChart hx).symm
    ⟨(tangentFiberEquiv c'.isChart hx' α' : c'.φ.model.E 0),
      (mem_tangentFiberModel_transportChart_iff L hsub hϕ hx hx' _).2
        (tangentFiberEquiv c'.isChart hx' α').2⟩
  left_inv α := by
    simp only [Equiv.apply_symm_apply]
    exact (tangentFiberEquiv (L.transportChart c' hsub).isChart hx).symm_apply_apply α
  right_inv α' := by
    simp only [Equiv.apply_symm_apply]
    exact (tangentFiberEquiv c'.isChart hx').symm_apply_apply α'

lemma coe_tangentFiberEquiv_tangentIso (α : A.X.PObj.tangentFiber x) :
    (tangentFiberEquiv c'.isChart hx' (tangentIso L hsub hϕ hx hx' α) : c'.φ.model.E 0) =
      ((tangentFiberEquiv (L.transportChart c' hsub).isChart hx α).1 : c'.φ.model.E 0) := by
  change ((tangentFiberEquiv c'.isChart hx') ((tangentFiberEquiv c'.isChart hx').symm _) :
    c'.φ.model.E 0) = _
  rw [Equiv.apply_symm_apply]

lemma chartOp_tangentIso (Lop : c'.φ.model.E 0 →L[ℝ] c'.F 0) (α : A.X.PObj.tangentFiber x) :
    chartOp c' hx' Lop (tangentIso L hsub hϕ hx hx' α) =
      chartOp (L.transportChart c' hsub) hx Lop α := by
  exact congrArg Lop (coe_tangentFiberEquiv_tangentIso L hsub hϕ hx hx' α)

/-- **`T^R_xX` corresponds to `T^R_{x'}X'`** under `tangentIso`. -/
theorem mem_reducedTangentFiber_tangentIso_iff {k : ℕ} {V : ScBanach}
    (T : ScIso c'.φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V))
    (α : A.X.PObj.tangentFiber x) :
    tangentIso L hsub hϕ hx hx' α ∈ reducedTangentFiber c'.isChart hx' T ↔
      α ∈ reducedTangentFiber (L.transportChart c' hsub).isChart hx T := by
  have e : (L.transportChart c' hsub).φ (A.X.PObj.levelVal 1 x) =
      c'.φ (A'.X.PObj.levelVal 1 x') := by
    rw [L.transportChart_φ_apply, hϕ]
  unfold reducedTangentFiber
  rw [Submodule.mem_comap, Submodule.mem_comap, fiberCoord_eq_coe, fiberCoord_eq_coe,
    coe_tangentFiberEquiv_tangentIso, e]
  exact Iff.rfl

/-! ### The fibres -/

include hϕ in
/-- The fibre part of the carried chart at `x` takes values in that of `c'` at `x'`. -/
lemma exists_fiberLin_eq (v : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    ∃ w : A'.P ⁻¹' {A'.X.PObj.levelVal 1 x'},
      c'.fiberLin hx' w = (L.transportChart c' hsub).fiberLin hx v := by
  have hv : A.P v = A.X.PObj.levelVal 1 x := v.2
  have hP : A'.P (L.Φ v) = A'.X.PObj.levelVal 1 x' := by
    rw [L.covers _ (by rw [hv]; exact hx.1), hv, hϕ]
  exact ⟨⟨L.Φ v, hP⟩, rfl⟩

include hϕ in
/-- The fibre part of `c'` at `x'` takes values in that of the carried chart at `x`. -/
lemma exists_fiberLin_transportChart_eq (w : A'.P ⁻¹' {A'.X.PObj.levelVal 1 x'}) :
    ∃ v : A.P ⁻¹' {A.X.PObj.levelVal 1 x},
      (L.transportChart c' hsub).fiberLin hx v = c'.fiberLin hx' w := by
  have hw : A'.P w = A'.X.PObj.levelVal 1 x' := w.2
  have hwU : A'.P w ∈ U' := by rw [hw]; exact hsub hx'
  have hP : A.P (L.Ψ w) = A.X.PObj.levelVal 1 x := by
    rw [L.covers_inv _ hwU, hw, ← hϕ]
    exact L.base.left_inv _ hx.1
  refine ⟨⟨L.Ψ w, hP⟩, ?_⟩
  rw [StrongBundleChart.fiberLin_apply, StrongBundleChart.fiberLin_apply,
    L.transportChart_apply, L.zero.right_inv _ hwU]

/-- **The intrinsic operators of one chart operator through `c' ∘ Φ` at `x` and through `c'` at
`x'` agree in the fibre coordinates.** -/
theorem fiberLin_toIntr_tangentIso (Lop : c'.φ.model.E 0 →L[ℝ] c'.F 0)
    (α : A.X.PObj.tangentFiber x) :
    c'.fiberLin hx' (toIntr c' hx' Lop (tangentIso L hsub hϕ hx hx' α)) =
      (L.transportChart c' hsub).fiberLin hx (toIntr (L.transportChart c' hsub) hx Lop α) := by
  set c := L.transportChart c' hsub
  set τ := tangentIso L hsub hϕ hx hx'
  by_cases h : ∀ β, chartOp c hx Lop β ∈ LinearMap.range (c.fiberLin hx)
  · have h' : ∀ β', chartOp c' hx' Lop β' ∈ LinearMap.range (c'.fiberLin hx') := fun β' => by
      obtain ⟨v, hv⟩ := h (τ.symm β')
      obtain ⟨w, hw⟩ := exists_fiberLin_eq L hsub hϕ hx hx' v
      refine ⟨w, ?_⟩
      rw [hw, hv, ← chartOp_tangentIso L hsub hϕ hx hx' Lop (τ.symm β'), τ.apply_symm_apply]
    rw [fiberLin_toIntr c' hx' h', fiberLin_toIntr c hx h]
    exact chartOp_tangentIso L hsub hϕ hx hx' Lop α
  · have h' : ¬ ∀ β', chartOp c' hx' Lop β' ∈ LinearMap.range (c'.fiberLin hx') := by
      intro h'
      apply h
      intro β
      obtain ⟨w, hw⟩ := h' (τ β)
      obtain ⟨v, hv⟩ := exists_fiberLin_transportChart_eq L hsub hϕ hx hx' w
      exact ⟨v, by rw [hv, hw]; exact chartOp_tangentIso L hsub hϕ hx hx' Lop β⟩
    have h0 : toIntr c hx Lop = 0 := dif_neg h
    have h0' : toIntr c' hx' Lop = 0 := dif_neg h'
    rw [h0, h0']
    simp only [LinearMap.zero_apply, map_zero]
    rfl

include hϕ in
/-- **Onto on the reduced tangent spaces, through the carried chart and through `c'`**: the
operator `Φ_x⁻¹ ∘ Lop ∘ T(c' ∘ Φ)` maps `T^R_xX` onto `W_x` iff `Φ'_{x'}⁻¹ ∘ Lop ∘ Tc'` maps
`T^R_{x'}X'` onto `W'_{x'}`. -/
theorem surjective_toIntr_transportChart_iff (Lop : c'.φ.model.E 0 →L[ℝ] c'.F 0) {k : ℕ}
    {V : ScBanach} (T : ScIso c'.φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)) :
    Surjective ((toIntr (L.transportChart c' hsub) hx Lop).domRestrict
        (reducedTangentFiber (L.transportChart c' hsub).isChart hx T)) ↔
      Surjective ((toIntr c' hx' Lop).domRestrict (reducedTangentFiber c'.isChart hx' T)) := by
  set c := L.transportChart c' hsub
  set τ := tangentIso L hsub hϕ hx hx'
  constructor
  · intro H w
    obtain ⟨v, hv⟩ := exists_fiberLin_transportChart_eq L hsub hϕ hx hx' w
    obtain ⟨⟨α, hα⟩, hαv⟩ := H v
    refine ⟨⟨τ α, (mem_reducedTangentFiber_tangentIso_iff L hsub hϕ hx hx' T α).2 hα⟩, ?_⟩
    apply c'.fiberLin_injective hx'
    rw [LinearMap.domRestrict_apply] at hαv ⊢
    change c'.fiberLin hx' (toIntr c' hx' Lop (τ α)) = _
    rw [fiberLin_toIntr_tangentIso L hsub hϕ hx hx' Lop α, ← hv]
    exact congrArg _ hαv
  · intro H v
    obtain ⟨w, hw⟩ := exists_fiberLin_eq L hsub hϕ hx hx' v
    obtain ⟨⟨α', hα'⟩, hαw⟩ := H w
    have hα : τ.symm α' ∈ reducedTangentFiber c.isChart hx T := by
      rw [← mem_reducedTangentFiber_tangentIso_iff L hsub hϕ hx hx' T, τ.apply_symm_apply]
      exact hα'
    refine ⟨⟨τ.symm α', hα⟩, ?_⟩
    apply c.fiberLin_injective hx
    rw [LinearMap.domRestrict_apply] at hαw ⊢
    change c.fiberLin hx (toIntr c hx Lop (τ.symm α')) = _
    rw [← fiberLin_toIntr_tangentIso L hsub hϕ hx hx' Lop (τ.symm α'), τ.apply_symm_apply,
      ← hw]
    exact congrArg _ hαw

/-! ### The chart operators -/

/-- **The chart operators agree**: for `f = Ψ ∘ f' ∘ ϕ` on `U` and a carried local section,
`D((f̂ − ŝ) ∘ r)` in the carried chart is `D((f̂' − ŝ') ∘ r)` in `c'`. -/
theorem subDeriv_transportChart {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (hf' : A'.B.IsScSmoothSection f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {s' : A'.Obj → A'.W}
    {O' : Set A'.Obj} (hs' : IsScPlusSectionOn A' s' O') (hc' : A'.B.IsChart c')
    (hsubO : c'.φ.source ⊆ O') {z : c'.φ.model.E 1} (hz : c'.φ.model.E.toBase 1 z ∈ c'.U) :
    subDeriv (L.transportChart c' hsub) f (isoSec L s') z = subDeriv c' f' s' z := by
  have h1 := isSc1_sub_comp_r hf' hs' hc' hsubO
  have hEq : EqOn ((fun y => c'.principal f' y - c'.principal s' y) ∘ r c'.R)
      ((fun y => (L.transportChart c' hsub).principal f y -
        (L.transportChart c' hsub).principal (isoSec L s') y) ∘ r c'.R) c'.U := by
    intro u hu
    have huO : r c'.R u ∈ c'.φ.model.O := c'.r_mem_O hu
    change c'.principal f' (r c'.R u) - c'.principal s' (r c'.R u) =
      (L.transportChart c' hsub).principal f (r c'.R u) -
        (L.transportChart c' hsub).principal (isoSec L s') (r c'.R u)
    exact (congrArg₂ (· - ·) (L.principal_transportChart c' hsub hfL hf'.1 huO)
      (principal_transportChart_isoSec L hsub hs'.1 hsubO huO)).symm
  exact IsSc1.scDeriv_eqOn (h1.isSc1With_scDeriv.congr hEq)
    (c'.relOpen.isScDomain.uniqueDiffWithinAt 1) hz

/-! ### General position at a point -/

open scoped Classical in
/-- **General position at a point along a local strong bundle isomorphism** (Definition 15.3.5
at one point): for sc-Fredholm section functors `f` of `W` and `f'` of `W'` with
`f = Ψ ∘ f' ∘ ϕ` on `U`, an sc⁺-multisection `Λ'` of `W'` and a function `Λ` with `Λ = Λ' ∘ Φ`
over `U`, the reduced linearization of `(f, Λ)` is onto at `x ∈ U` iff that of `(f', Λ')` is
onto at `ϕ(x)`. -/
theorem isReducedOntoAtLevel_localIso_iff {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hf' : A'.E.IsScFredholmSectionFunctor f')
    {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (hΛ' : IsScPlusMultisection A' Λ')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hΛL : ∀ w, A.P w ∈ U → Λ w = Λ' (L.Φ w))
    {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1} (hxU : A.X.PObj.levelVal 1 x ∈ U)
    (hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x') :
    IsReducedOntoAtLevel f Λ x ↔ IsReducedOntoAtLevel f' Λ' x' := by
  obtain ⟨d⟩ := nonempty_localLinData hΛ' x'
  set y := A.X.PObj.levelVal 1 x with hy
  set y' := A'.X.PObj.levelVal 1 x' with hy'
  have hy'U : y' ∈ U' := hϕ ▸ L.base.mapsTo hxU
  have hso : IsOpen (d.c.φ.source ∩ U') := d.c.φ.isOpen_source.inter L.isOpen_U'
  set c' := d.c.restrict inter_subset_left hso with hc'def
  have hc' : A'.B.IsChart c' := d.isChart.restrict inter_subset_left hso
  have hsub : c'.φ.source ⊆ U' := fun z hz => hz.2
  have hx' : y' ∈ c'.φ.source := ⟨d.mem, hy'U⟩
  set O' := d.O ∩ U' with hO'def
  have hO' : IsOpen O' := d.isOpen.inter L.isOpen_U'
  have hrep' : IsLocalRepOn A' Λ' O' d.s d.σ := d.rep.mono hO' inter_subset_left
  have hsubO : c'.φ.source ⊆ O' := fun z hz => ⟨d.sub hz.1, hz.2⟩
  set c := L.transportChart c' hsub with hcdef
  have hx : y ∈ c.φ.source := ⟨hxU, by rw [mem_preimage, hϕ]; exact hx'⟩
  have hrep : IsLocalRepOn A Λ (isoSet L O') (fun i => isoSec L (d.s i)) d.σ :=
    isLocalRepOn_isoSec L hΛL hO' inter_subset_right hrep'
  have hcsub : c.φ.source ⊆ isoSet L O' := fun z hz => ⟨hz.1, hsubO hz.2⟩
  let dx' : LocalLinData A' Λ' x' := ⟨O', hO', d.k, d.s, d.σ, hrep', c', hc', hsubO, hx'⟩
  let dx : LocalLinData A Λ x :=
    ⟨isoSet L O', isOpen_isoSet L hO', d.k, fun i => isoSec L (d.s i), d.σ, hrep, c,
      L.isChart_transportChart c' hsub hc', hcsub, hx⟩
  have hsec : IsSection A.P f := hf.1.1.1
  have hsec' : IsSection A'.P f' := hf'.1.1.1
  -- the branches through `f(x)` and through `f'(x')`
  have hbr : ∀ i, isoSec L (d.s i) y = f y ↔ d.s i y' = f' y' := fun i => by
    have e1 : isoSec L (d.s i) y = L.Ψ (d.s i y') := by rw [isoSec, hϕ]
    have e2 : f y = L.Ψ (f' y') := by rw [hfL hxU]; simp only [Function.comp_apply, hϕ]
    rw [e1, e2]
    constructor
    · intro h
      have h1 : d.s i y' ∈ A'.P ⁻¹' U' := by
        change A'.P (d.s i y') ∈ U'
        rw [(hrep'.2.1 i).1 _ (hsubO hx')]; exact hy'U
      have h2 : f' y' ∈ A'.P ⁻¹' U' := by
        change A'.P (f' y') ∈ U'
        rw [hsec' y']; exact hy'U
      rw [← L.zero.right_inv _ h1, ← L.zero.right_inv _ h2, h]
    · intro h; rw [h]
  -- the chart operators
  have hl : levelLift c.φ 1 y = levelLift c'.φ 1 y' := levelLift_transportChart L hsub hϕ
  have hzU : c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y') ∈ c'.U := by
    rw [A'.X.PObj.toBase_levelLift c'.isChart hx' (levelVal_mem x')]
    exact mem_U_of_mem_O c'.isRetraction (c'.r_image ▸ c'.φ.mapsTo_model _ hx')
  have hD : ∀ i, subDeriv c f (isoSec L (d.s i)) (levelLift c.φ 1 y) =
      subDeriv c' f' (d.s i) (levelLift c'.φ 1 y') := fun i => by
    rw [hl]
    exact subDeriv_transportChart L hsub hf'.1.1 hfL (hrep'.2.1 i) hc' hsubO hzU
  obtain ⟨k, V, T, hT⟩ := c'.φ.model.isPartialQuadrant
  constructor
  · intro H L' hL' ψ hψ hyψ m V' T' hT'
    rw [linearization_eq hf' dx'] at hL'
    obtain ⟨i, hi, rfl⟩ := (mem_support_linSumIntr_iff hsec' hrep'.1
      (fun j => (hrep'.2.1 j).1) hsubO hx' _).1 hL'
    have hL : toIntr c hx (subDeriv c f (isoSec L (d.s i)) (levelLift c.φ 1 y)) ∈
        (linearization f Λ x).support := by
      rw [linearization_eq hf dx]
      exact (mem_support_linSumIntr_iff hsec hrep.1 (fun j => (hrep.2.1 j).1) hcsub hx _).2
        ⟨i, (hbr i).2 hi, rfl⟩
    have hs := H _ hL c.φ c.isChart hx k V T hT
    rw [hD i] at hs
    rw [reducedTangentFiber_eq hψ hyψ T' c'.isChart hx' T hT' hT]
    exact (surjective_toIntr_transportChart_iff L hsub hϕ hx hx' _ T).1 hs
  · intro H L₀ hL₀ ψ hψ hyψ m V' T' hT'
    rw [linearization_eq hf dx] at hL₀
    obtain ⟨i, hi, rfl⟩ := (mem_support_linSumIntr_iff hsec hrep.1
      (fun j => (hrep.2.1 j).1) hcsub hx _).1 hL₀
    have hL : toIntr c' hx' (subDeriv c' f' (d.s i) (levelLift c'.φ 1 y')) ∈
        (linearization f' Λ' x').support := by
      rw [linearization_eq hf' dx']
      exact (mem_support_linSumIntr_iff hsec' hrep'.1 (fun j => (hrep'.2.1 j).1) hsubO hx'
        _).2 ⟨i, (hbr i).1 hi, rfl⟩
    have hs := H _ hL c'.φ c'.isChart hx' k V T hT
    rw [reducedTangentFiber_eq hψ hyψ T' c.isChart hx T hT' hT, hD i]
    exact (surjective_toIntr_transportChart_iff L hsub hϕ hx hx' _ T).2 hs

end SBLocalization

end Polyfold
