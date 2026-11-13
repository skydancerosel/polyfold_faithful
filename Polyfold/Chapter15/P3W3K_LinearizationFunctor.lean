import Polyfold.Chapter15.P3T_LinearizationIntrinsic
import Polyfold.Chapter12.P3O_MorphismIso
import Polyfold.Chapter7.TangentMorphismLinear
import Polyfold.Chapter9.OrientationTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 683–684): the **functor property** in **Theorem 15.1.1** (2017: Theorem 15.1):
`T(f, Λ)` is a section functor of `GrF(X) → X_∞`.

# `T(f,Λ)(t φ) = φ_* T(f,Λ)(s φ)`

## The text, paraphrased

(p. 683) A morphism `φ : x → y` acts on `GrF(x)` by
`φ_*(∑ σ_L · L) = ∑ σ_L · μ(φ, ·) ∘ L ∘ (Tφ)⁻¹`, and a section functor of `GrF(X) → X_∞` is a
section `x ↦ T(x) ∈ GrF(x)` with `T(t φ) = φ_* T(s φ)`.  (Theorem 15.1.1) `T(f, Λ)` is such a
section functor.  The text gives no separate argument for the functor property: it follows from
the functoriality of `f` and `Λ` and the local diffeomorphism `t ∘ s⁻¹` near `φ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `muLin φ hx hy : W_x →ₗ W_y`, the linear map `μ(φ, ·)` of a morphism `φ : x → y`.
* `conjOp φ hφ hx hy L = μ(φ, ·) ∘ L ∘ (Tφ)⁻¹ : T_yX → W_y` for `L : T_xX → W_x`, with
  `Tφ = EpGroupoid.tangentMorCLE` (Chapter 7, the linear isomorphism `T_xX ≃ T_yX`), and
  `grfPush φ hφ hx hy = φ_* : GrF(x) → GrF(y)` (`Finsupp.mapDomain` of `conjOp`).
* `transSec φ s = Ψ̂ ∘ s ∘ φ̂⁻¹`: a local section near `x = s(φ)` carried to a local section near
  `y = t(φ)` by the local strong bundle isomorphism of `φ` (wave 1's `EpStrongBundle.morIso`);
  `isScPlusSectionOn_transSec`, `isLocalRepOn_transSec` (a local section structure of a functor
  `Λ` is carried to one of `Λ`).
* `chartVec_transport`: in the chart `c ∘ φ̂⁻¹` at `y` (the transported chart
  `LocalIso.transportChart`), `Tφ` is the identity of the chart vectors; `fiberLin_transport_muLin`:
  the fibre part of the transported chart at `y` composed with `μ(φ, ·)` is that of `c` at `x`.
* `toIntr_transportChart`: **the intrinsic operator read through the transported chart is
  `μ(φ, ·) ∘ (intrinsic operator through c) ∘ (Tφ)⁻¹`**, for every chart operator.
* `linSumIntr_transportChart`: the formal sum of the carried structure in the carried chart is
  `φ_*` of the formal sum at `x`.
* **`theorem_15_1_1_functor`**: for an sc-Fredholm section functor `f`, an sc⁺-multisection `Λ`,
  a morphism `φ` and level-`1` points `x = s(φ)`, `y = t(φ)`:
  `T(f, Λ)(y) = φ_* T(f, Λ)(x)` in `GrF(y)`.  This closes gap G.144.
* `grfPush_comp` and `grfPush_unit`-type statements are not needed for the theorem and are not
  formalized; `conjOp_apply` gives the action pointwise.

## Reading

The text states the functor property at smooth points.  It is proved here at every level-`1`
point (`x ∈ X₁` forces `φ ∈ 𝐗₁`, `mem_levelSet_one_of_src`), where `Tφ` is Chapter 7's bounded
linear isomorphism.  The summands are not required to be sc-Fredholm in `GrF` (as in wave 1's
`GrF`, see `linearization_summand_isScFredholm` for that property).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The action of a morphism on `GrF` -/

/-- **`μ(φ, ·) : W_x → W_y`** for a morphism `φ : x → y`, a linear map. -/
def muLin (φ : A.Mor) {x y : A.Obj} (hx : A.X.src φ = x) (hy : A.X.tgt φ = y) :
    A.P ⁻¹' {x} →ₗ[ℝ] A.P ⁻¹' {y} :=
  IsLinearMap.mk' _ (A.E.isLinearMap_sectionAct (α := fun _ => φ) (S := {x})
    (fun z hz => by rw [mem_singleton_iff.1 hz]; exact hx) (mem_singleton x) hy)

lemma muLin_apply (φ : A.Mor) {x y : A.Obj} (hx : A.X.src φ = x) (hy : A.X.tgt φ = y)
    (v : A.P ⁻¹' {x}) :
    (muLin φ hx hy v : A.W) =
      A.E.μ ⟨(φ, (v : A.W)), (show A.P v = x from v.2).trans hx.symm⟩ := by
  change A.E.sectionAct (fun _ => φ) v = _
  exact A.E.sectionAct_of_eq _ _

/-- `x ∈ X₁` and `s(φ) = x` give `φ ∈ 𝐗₁`. -/
lemma mem_levelSet_one_of_src {φ : A.Mor} {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) : φ ∈ A.X.PMor.levelSet 1 :=
  (A.X.mem_levelSet_src_iff φ 1).1 (hx ▸ levelVal_mem x)

/-- **`L ↦ μ(φ, ·) ∘ L ∘ (Tφ)⁻¹`**, `T_xX → W_x` to `T_yX → W_y` (2021 p. 683). -/
def conjOp (φ : A.Mor) (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    A.X.PObj.tangentFiber y →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 y} :=
  muLin φ hx.symm hy.symm ∘ₗ L ∘ₗ
    ((A.X.tangentMorCLE hφ hx hy).symm : A.X.PObj.tangentFiber y →L[ℝ] A.X.PObj.tangentFiber x)

lemma conjOp_apply (φ : A.Mor) (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x})
    (α : A.X.PObj.tangentFiber y) :
    conjOp φ hφ hx hy L α = muLin φ hx.symm hy.symm (L ((A.X.tangentMorCLE hφ hx hy).symm α)) :=
  rfl

/-- **`φ_* : GrF(x) → GrF(y)`** (2021 p. 683): `∑ σ_L · L ↦ ∑ σ_L · μ(φ, ·) ∘ L ∘ (Tφ)⁻¹`. -/
def grfPush (φ : A.Mor) (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) :
    GrF x → GrF y :=
  Finsupp.mapDomain (conjOp φ hφ hx hy)

/-! ### Local sections carried along a morphism -/

/-- A local section `s` near `s(φ)` carried to `t(φ)` by the local strong bundle isomorphism of
`φ`: `z ↦ Ψ̂(s(ϕ z))`, with `ϕ = s ∘ (t|sheet)⁻¹` and `Ψ̂(w) = μ((s|sheet)⁻¹(P w), w)`. -/
def transSec (φ : A.Mor) (s : A.Obj → A.W) : A.Obj → A.W := fun z =>
  (A.E.morIso φ).Ψ (s ((A.E.morIso φ).ϕ z))

/-- The domain `t(sheet) ∩ φ̂⁻¹(O)` of the carried section. -/
def transSet (φ : A.Mor) (O : Set A.Obj) : Set A.Obj :=
  (A.X.sheetAt φ).tgtSet ∩ (A.E.morIso φ).ϕ ⁻¹' O

lemma isOpen_transSet (φ : A.Mor) {O : Set A.Obj} (hO : IsOpen O) : IsOpen (transSet φ O) :=
  (A.E.morIso φ).base.isScSmoothOn.continuousOn.isOpen_inter_preimage
    (A.E.morIso φ).isOpen_U hO

lemma P_transSec {φ : A.Mor} {s : A.Obj → A.W} {O : Set A.Obj} (hsec : ∀ y ∈ O, A.P (s y) = y)
    (hOs : O ⊆ (A.X.sheetAt φ).srcSet) {z : A.Obj} (hz : z ∈ transSet φ O) :
    A.P (transSec φ s z) = z := by
  set L := A.E.morIso φ
  have h1 : A.P (s (L.ϕ z)) ∈ (A.X.sheetAt φ).srcSet := by rw [hsec _ hz.2]; exact hOs hz.2
  change A.P (L.Ψ (s (L.ϕ z))) = z
  rw [L.covers_inv _ h1, hsec _ hz.2]
  exact L.base.left_inv z hz.1

/-- **The carried section is an sc⁺-section on `t(sheet) ∩ φ̂⁻¹(O)`.** -/
theorem isScPlusSectionOn_transSec {φ : A.Mor} {s : A.Obj → A.W} {O : Set A.Obj}
    (hO : IsOpen O) (hOs : O ⊆ (A.X.sheetAt φ).srcSet) (hs : IsScPlusSectionOn A s O) :
    IsScPlusSectionOn A (transSec φ s) (transSet φ O) := by
  set L := A.E.morIso φ
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  refine ⟨fun z hz => P_transSec hsec hOs hz, fun z => L.Ψ₁ (G (L.ϕ z)), fun z hz => ?_, ?_⟩
  · have h1 : A.P (A.B.oneVal (G (L.ϕ z))) ∈ (A.X.sheetAt φ).srcSet := by
      rw [hG _ hz.2, hsec _ hz.2]; exact hOs hz.2
    rw [L.oneVal_Ψ₁ _ h1, hG _ hz.2]
    rfl
  · have hϕ : A.X.PObj.IsScSmoothOn A.X.PObj L.ϕ (transSet φ O) :=
      L.base.isScSmoothOn.mono (isOpen_transSet φ hO) inter_subset_left
    have hGϕ := MPolyfold.IsScSmoothOn.comp hGs hϕ fun z hz => hz.2
    refine MPolyfold.IsScSmoothOn.comp L.one.isScSmoothOn_inv hGϕ fun z hz => ?_
    change A.P (A.B.oneVal (G (L.ϕ z))) ∈ (A.X.sheetAt φ).srcSet
    rw [hG _ hz.2, hsec _ hz.2]; exact hOs hz.2

/-- The bundle map of the isomorphism of `φ` preserves a functor `Λ`. -/
lemma isWFunctor_morIso_Φ {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) (φ : A.Mor) {w : A.W}
    (hw : A.P w ∈ (A.X.sheetAt φ).tgtSet) : Λ ((A.E.morIso φ).Φ w) = Λ w := by
  rw [EpStrongBundle.morIso_Φ,
    A.E.sectionAct_of_eq _ (EpStrongBundle.src_morInvSec φ hw).symm]
  exact hΛ _

open scoped Classical in
/-- **A local section structure of a functor `Λ` is carried along `φ`**: the carried sections with
the same weights represent `Λ` on `t(sheet) ∩ φ̂⁻¹(O)`. -/
theorem isLocalRepOn_transSec {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) {φ : A.Mor}
    {O : Set A.Obj} (hO : IsOpen O) (hOs : O ⊆ (A.X.sheetAt φ).srcSet) {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hs : IsLocalRepOn A Λ O s σ) :
    IsLocalRepOn A Λ (transSet φ O) (fun i => transSec φ (s i)) σ := by
  set L := A.E.morIso φ
  refine ⟨hs.1, fun i => isScPlusSectionOn_transSec hO hOs (hs.2.1 i), hs.2.2.1, fun w hw => ?_⟩
  have hwU : A.P w ∈ (A.X.sheetAt φ).tgtSet := hw.1
  have hPΦ : A.P (L.Φ w) = L.ϕ (A.P w) := L.covers w hwU
  rw [← isWFunctor_morIso_Φ hΛ φ hwU, hs.2.2.2 _ (by rw [hPΦ]; exact hw.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsec := (hs.2.1 i).1
  have hiff : L.Φ w = s i (A.P (L.Φ w)) ↔ w = transSec φ (s i) (A.P w) := by
    rw [hPΦ]
    constructor
    · intro h
      change w = L.Ψ (s i (L.ϕ (A.P w)))
      rw [← h]; exact (L.zero.left_inv w hwU).symm
    · intro h
      have h1 : s i (L.ϕ (A.P w)) ∈ A.P ⁻¹' (A.X.sheetAt φ).srcSet := by
        show A.P (s i (L.ϕ (A.P w))) ∈ (A.X.sheetAt φ).srcSet
        rw [hsec _ hw.2]; exact hOs hw.2
      exact (congrArg L.Φ h).trans (L.zero.right_inv _ h1)
  by_cases h : w = transSec φ (s i) (A.P w)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

/-! ### The transported chart -/

variable {φ : A.Mor} {c : StrongBundleChart A.X.PObj A.P}

/-- The principal part of a carried local section in the transported chart is that of the
section in the original chart, on the retract `O`. -/
lemma principal_transportChart_transSec {s : A.Obj → A.W} {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hsubO : c.φ.source ⊆ O) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    ((A.E.morIso φ).transportChart c hsub).principal (transSec φ s) z = c.principal s z := by
  set L := A.E.morIso φ
  have hw : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  have hwU' : c.φ.symm z ∈ (A.X.sheetAt φ).srcSet := hsub hw
  change (c (L.Φ (L.Ψ (s (L.ϕ (L.g (c.φ.symm z))))))).2 = (c (s (c.φ.symm z))).2
  rw [L.base.right_inv _ hwU', L.zero.right_inv _ (show A.P (s _) ∈ _ by
    rw [hsec _ (hsubO hw)]; exact hwU')]

/-- **`Tφ` is the identity in the chart vectors of `c` at `x` and of the transported chart at
`y`**: `Tφ = Tφ̂`, `φ̂⁻¹ ∘ φ̂ = id` near `x`, and the chart vector of `Tg(α)` in `c` is that of `α`
in `c ∘ g` (`chartVec_tangentMapOn`, for `g = φ̂⁻¹`). -/
theorem chartVec_transport (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    (β : A.X.PObj.tangentFiber x) :
    (tangentFiberEquiv ((A.E.morIso φ).transportChart c hsub).isChart hy'
        (A.X.tangentMorCLE hφ hx hy β) : ((A.E.morIso φ).transportChart c hsub).φ.model.E 0) =
      (tangentFiberEquiv c.isChart hx' β : c.φ.model.E 0) := by
  set L := A.E.morIso φ
  have hβ : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj β.1) = A.X.src φ := by
    rw [show A.X.PObj.tangentProj β.1 = x from β.2]; exact hx
  have hβS : β.1 ∈ A.X.PObj.tangentPreimage (A.X.sheetAt φ).srcSet := by
    rw [MPolyfold.mem_tangentPreimage, hβ]; exact A.X.src_mem_sheetAt φ
  have hd := A.X.isScDiffeoOn_hat φ
  -- `Tφ(β) = Tφ̂(β)`
  have hT : (A.X.tangentMorCLE hφ hx hy β : A.X.PObj.TangentSpace) =
      tangentMapOn hd.isScSmoothOn β.1 := by
    rw [A.X.tangentMorCLE_apply, A.X.tangentMor_eq_tangentMapOn_hat hφ hβ]
  -- `T(φ̂⁻¹)(Tφ̂ β) = β`
  have hcomp := tangentMapOn_comp L.base.isScSmoothOn hd.isScSmoothOn hd.mapsTo hβS
  have hid := tangentMapOn_eqOn_id (L.base.isScSmoothOn.comp hd.isScSmoothOn hd.mapsTo)
    (fun z hz => hd.left_inv z hz) hβS
  have hback : tangentMapOn L.base.isScSmoothOn (tangentMapOn hd.isScSmoothOn β.1) = β.1 :=
    hcomp.symm.trans hid
  -- the chart vectors
  have hmem : A.X.PObj.levelVal 1 (A.X.PObj.tangentProj (tangentMapOn hd.isScSmoothOn β.1)) ∈
      (A.X.sheetAt φ).tgtSet ∩ L.ϕ ⁻¹' c.φ.source := by
    rw [levelVal_tangentProj_tangentMapOn hd.isScSmoothOn hβS, hβ, A.X.hat_src]
    refine ⟨A.X.tgt_mem_sheetAt φ, ?_⟩
    change L.ϕ (A.X.tgt φ) ∈ c.φ.source
    rw [EpStrongBundle.morIso_ϕ_tgt, ← hx]; exact hx'
  have key := chartVec_tangentMapOn L.base c.isChart hmem
  rw [hback] at key
  rw [coe_tangentFiberEquiv_apply, coe_tangentFiberEquiv_apply, hT]
  exact key.symm

/-- **`μ(φ, ·)` followed by the fibre part of the transported chart at `y` is the fibre part of `c`
at `x`**: `Φ̂ = μ(φ⁻¹, ·)` on `W_y` undoes `μ(φ, ·)` (`Ψ̂ = μ(φ, ·)` on `W_x`). -/
lemma fiberLin_transport_muLin {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    (v : A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    ((A.E.morIso φ).transportChart c hsub).fiberLin hy' (muLin φ hx.symm hy.symm v) =
      c.fiberLin hx' v := by
  set L := A.E.morIso φ
  have hv : A.P v = A.X.src φ := (show A.P v = A.X.PObj.levelVal 1 x from v.2).trans hx
  have hvS : (v : A.W) ∈ A.P ⁻¹' (A.X.sheetAt φ).srcSet := by
    show A.P v ∈ (A.X.sheetAt φ).srcSet
    rw [hv]; exact A.X.src_mem_sheetAt φ
  have hΨ : L.Ψ v = (muLin φ hx.symm hy.symm v : A.W) := by
    rw [muLin_apply, EpStrongBundle.morIso_Ψ,
      A.E.sectionAct_of_eq _ ((A.X.sheetAt φ).isScDiffeoOn_src.right_inv _
        (by rw [hv]; exact A.X.src_mem_sheetAt φ)).symm]
    refine A.E.μ_congr (Prod.ext ?_ rfl)
    change (A.X.sheetAt φ).srcInv (A.P v) = φ
    rw [hv]; exact (A.X.sheetAt φ).isScDiffeoOn_src.left_inv φ (A.X.mem_sheetAt φ)
  rw [StrongBundleChart.fiberLin_apply, StrongBundleChart.fiberLin_apply,
    StrongBundle.LocalIso.transportChart_apply, ← hΨ, L.zero.right_inv _ hvS]

/-- The fibre part of the transported chart at `y` takes values in that of `c` at `x`. -/
lemma fiberLin_transport_mem_range {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    (w : A.P ⁻¹' {A.X.PObj.levelVal 1 y}) :
    ((A.E.morIso φ).transportChart c hsub).fiberLin hy' w ∈ LinearMap.range (c.fiberLin hx') := by
  set L := A.E.morIso φ
  have hw : A.P w = A.X.tgt φ := (show A.P w = A.X.PObj.levelVal 1 y from w.2).trans hy
  have hwU : A.P w ∈ (A.X.sheetAt φ).tgtSet := by rw [hw]; exact A.X.tgt_mem_sheetAt φ
  have hP : A.P (L.Φ w) = A.X.PObj.levelVal 1 x := by
    rw [L.covers _ hwU, hw, EpStrongBundle.morIso_ϕ_tgt, hx]
  exact ⟨⟨L.Φ w, hP⟩, rfl⟩

/-- **The intrinsic operator through the transported chart**: for every chart operator `L`,
`Φ'_y⁻¹ ∘ L ∘ T(c ∘ φ̂⁻¹) = μ(φ, ·) ∘ (Φ_x⁻¹ ∘ L ∘ Tc) ∘ (Tφ)⁻¹`. -/
theorem toIntr_transportChart (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    (Lop : c.φ.model.E 0 →L[ℝ] c.F 0) :
    toIntr ((A.E.morIso φ).transportChart c hsub) hy' Lop =
      conjOp φ hφ hx hy (toIntr c hx' Lop) := by
  set c' := (A.E.morIso φ).transportChart c hsub
  set e := A.X.tangentMorCLE hφ hx hy
  have hop : ∀ α, chartOp c' hy' Lop α = chartOp c hx' Lop (e.symm α) := fun α => by
    have h := chartVec_transport hφ hx hy hsub hx' hy' (e.symm α)
    rw [e.apply_symm_apply] at h
    exact congrArg Lop h
  by_cases h : ∀ β, chartOp c hx' Lop β ∈ LinearMap.range (c.fiberLin hx')
  · have h' : ∀ α, chartOp c' hy' Lop α ∈ LinearMap.range (c'.fiberLin hy') := fun α => by
      obtain ⟨v, hv⟩ := h (e.symm α)
      exact ⟨muLin φ hx.symm hy.symm v, by
        rw [hop, fiberLin_transport_muLin hx hy hsub hx' hy', hv]⟩
    refine LinearMap.ext fun α => c'.fiberLin_injective hy' ?_
    rw [fiberLin_toIntr c' hy' h', conjOp_apply, fiberLin_transport_muLin hx hy hsub hx' hy',
      fiberLin_toIntr c hx' h, hop]
  · have h' : ¬ ∀ α, chartOp c' hy' Lop α ∈ LinearMap.range (c'.fiberLin hy') := by
      intro h'
      apply h
      intro β
      have := h' (e β)
      rw [hop, e.symm_apply_apply] at this
      obtain ⟨w, hw⟩ := this
      rw [← hw]
      exact fiberLin_transport_mem_range hx hy hsub hx' hy' w
    have h0 : toIntr c hx' Lop = 0 := dif_neg h
    have h0' : toIntr c' hy' Lop = 0 := dif_neg h'
    rw [h0, h0']
    refine LinearMap.ext fun α => ?_
    simp only [conjOp_apply, LinearMap.zero_apply, map_zero]

/-- The derivative in `U` of a map composed with `r` only depends on the map on `r(U) = O`. -/
private theorem scDeriv_congr_K {E F : ScBanach} {U : Set (E 0)} (hU : IsScDomain E U)
    {g g' : E 0 → F 0} (hg : IsSc1 U g) (h : EqOn g g' U) {z : E 1} (hz : z ∈ E.lvlSet U 1) :
    scDeriv U g' z = scDeriv U g z :=
  IsSc1.scDeriv_eqOn (hg.isSc1With_scDeriv.congr h) (hU.uniqueDiffWithinAt 1) hz

open scoped Classical in
/-- **The formal sum of the carried structure in the transported chart is `φ_*` of the formal sum
at `x`**, for a functorial sc-smooth section `f`. -/
theorem linSumIntr_transportChart {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    {O : Set A.Obj} {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hs : ∀ i, IsScPlusSectionOn A (s i) O) (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet) (hsubO : c.φ.source ⊆ O)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source) :
    linSumIntr ((A.E.morIso φ).transportChart c hsub) hy' f (fun i => transSec φ (s i)) σ =
      grfPush φ hφ hx hy (linSumIntr c hx' f s σ) := by
  set L := A.E.morIso φ
  set c' := L.transportChart c hsub
  have hsm : A.B.IsScSmoothSection f := hf.1.1
  have hfun : A.E.IsFunctorialSection hsm.1 := hf.1.2
  have hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) (A.X.sheetAt φ).tgtSet := A.E.eqOn_morIso φ hsm.1 hfun
  have hϕy : L.ϕ (A.X.PObj.levelVal 1 y) = A.X.PObj.levelVal 1 x := by
    rw [hy, EpStrongBundle.morIso_ϕ_tgt, hx]
  -- the level-`1` points agree
  have hz : levelLift c'.φ 1 (A.X.PObj.levelVal 1 y) = levelLift c.φ 1 (A.X.PObj.levelVal 1 x) := by
    change Function.invFun (c.φ.model.E.toBase 1) (c.φ (L.ϕ (A.X.PObj.levelVal 1 y))) = _
    rw [hϕy]; rfl
  set z := levelLift c.φ 1 (A.X.PObj.levelVal 1 x) with hzdef
  have ha : c.φ.model.E.toBase 1 z = c.φ (A.X.PObj.levelVal 1 x) :=
    A.X.PObj.toBase_levelLift c.isChart hx' (levelVal_mem x)
  have hyO : c.φ (A.X.PObj.levelVal 1 x) ∈ c.φ.model.O := c.φ.mapsTo_model _ hx'
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := by
    rw [ha]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ hyO)
  -- principal parts
  have hpf : ∀ w ∈ c.φ.model.O, c'.principal f w = c.principal f w := fun w hw =>
    L.principal_transportChart c hsub hfL hsm.1 hw
  have hps : ∀ i, ∀ w ∈ c.φ.model.O, c'.principal (transSec φ (s i)) w = c.principal (s i) w :=
    fun i w hw => principal_transportChart_transSec (hs i).1 hsub hsubO hw
  unfold linSumIntr linSumModelMap grfPush
  rw [Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcond : c'.principal (transSec φ (s i)) (c.φ.model.E.toBase 1 z) =
      c'.principal f (c.φ.model.E.toBase 1 z) ↔
      c.principal (s i) (c.φ.model.E.toBase 1 z) = c.principal f (c.φ.model.E.toBase 1 z) := by
    rw [hps i _ (ha ▸ hyO), hpf _ (ha ▸ hyO)]
    exact Iff.rfl
  -- the derivatives agree
  have hUd := c.relOpen.isScDomain
  have h1 : IsSc1 c.U ((fun w => c.principal f w - c.principal (s i) w) ∘ r c.R) :=
    ((isScSmooth_principal_comp_r hsm hc).sub hUd
      ((hs i).isScSmooth_principal_comp_r hc hsubO)).isSc1
  have hder : scDeriv c.U ((fun w => c'.principal f w - c'.principal (transSec φ (s i)) w) ∘
      r c.R) z = scDeriv c.U ((fun w => c.principal f w - c.principal (s i) w) ∘ r c.R) z := by
    refine scDeriv_congr_K hUd h1 (fun u hu => ?_) hzU
    have huO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu
    change c.principal f (r c.R u) - c.principal (s i) (r c.R u) =
      c'.principal f (r c.R u) - c'.principal (transSec φ (s i)) (r c.R u)
    exact (congrArg₂ (· - ·) (hpf _ huO) (hps i _ huO)).symm
  change (if c'.principal (transSec φ (s i)) (c.φ.model.E.toBase 1
      (levelLift c'.φ 1 (A.X.PObj.levelVal 1 y))) = c'.principal f (c.φ.model.E.toBase 1
      (levelLift c'.φ 1 (A.X.PObj.levelVal 1 y))) then Finsupp.single (toIntr c' hy'
      (scDeriv c.U ((fun w => c'.principal f w - c'.principal (transSec φ (s i)) w) ∘ r c.R)
        (levelLift c'.φ 1 (A.X.PObj.levelVal 1 y)))) (σ i) else 0) = _
  rw [hz]
  by_cases h : c.principal (s i) (c.φ.model.E.toBase 1 z) = c.principal f (c.φ.model.E.toBase 1 z)
  · rw [if_pos (hcond.2 h), if_pos h, Finsupp.mapDomain_single]
    congr 1
    exact (congrArg (toIntr c' hy') hder).trans (toIntr_transportChart hφ hx hy hsub hx' hy' _)
  · rw [if_neg (mt hcond.1 h), if_neg h, Finsupp.mapDomain_zero]

/-! ### Theorem 15.1.1: the functor property -/

/-- **Theorem 15.1.1 (2017: Theorem 15.1), p. 684, the functor property (gap G.144)**: for an
sc-Fredholm section functor `f`, an sc⁺-multisection `Λ` and a morphism `φ : x → y` between
level-`1` points (in particular between smooth points),
`T(f, Λ)(y) = φ_* T(f, Λ)(x)` in `GrF(y)`, where `φ_*(∑ σ_L · L) = ∑ σ_L · μ(φ, ·) ∘ L ∘ (Tφ)⁻¹`
(`grfPush`, with Chapter 7's `Tφ = tangentMorCLE`).  So `T(f, Λ)` is a section functor of
`GrF(X) → X_∞` (`X₁` here). -/
theorem theorem_15_1_1_functor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (φ : A.Mor) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) :
    linearization f Λ y = grfPush φ (mem_levelSet_one_of_src hx) hx hy (linearization f Λ x) := by
  set hφ := mem_levelSet_one_of_src hx
  obtain ⟨d⟩ := nonempty_localLinData hΛ x
  set L := A.E.morIso φ
  have hso : IsOpen (d.c.φ.source ∩ (A.X.sheetAt φ).srcSet) :=
    d.c.φ.isOpen_source.inter L.isOpen_U'
  set c := d.c.restrict inter_subset_left hso
  have hc : A.B.IsChart c := d.isChart.restrict inter_subset_left hso
  have hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet := fun z hz => hz.2
  have hsubO : c.φ.source ⊆ d.O := fun z hz => d.sub hz.1
  have hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source :=
    ⟨d.mem, by rw [hx]; exact A.X.src_mem_sheetAt φ⟩
  have hy' : A.X.PObj.levelVal 1 y ∈ (L.transportChart c hsub).φ.source := by
    refine ⟨by rw [hy]; exact A.X.tgt_mem_sheetAt φ, ?_⟩
    change L.ϕ (A.X.PObj.levelVal 1 y) ∈ c.φ.source
    rw [hy, EpStrongBundle.morIso_ϕ_tgt, ← hx]; exact hx'
  -- the structure restricted to the sheet, and its carried version
  set O := d.O ∩ (A.X.sheetAt φ).srcSet
  have hO : IsOpen O := d.isOpen.inter L.isOpen_U'
  have hrep : IsLocalRepOn A Λ O d.s d.σ := d.rep.mono hO inter_subset_left
  have hsubO' : c.φ.source ⊆ O := fun z hz => ⟨hsubO hz, hsub hz⟩
  let dx : LocalLinData A Λ x := ⟨O, hO, d.k, d.s, d.σ, hrep, c, hc, hsubO', hx'⟩
  let dy : LocalLinData A Λ y :=
    ⟨transSet φ O, isOpen_transSet φ hO, d.k, fun i => transSec φ (d.s i), d.σ,
      isLocalRepOn_transSec hΛ.1 hO inter_subset_right hrep, L.transportChart c hsub,
      L.isChart_transportChart c hsub hc, fun z hz => ⟨hz.1, hsubO' hz.2⟩, hy'⟩
  rw [linearization_eq hf dy, linearization_eq hf dx]
  exact linSumIntr_transportChart hf hφ hx hy hrep.2.1 hc hsub hsubO' hx' hy'

end SBLocalization

end Polyfold
