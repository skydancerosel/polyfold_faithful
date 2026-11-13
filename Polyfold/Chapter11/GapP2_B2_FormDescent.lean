import Polyfold.Chapter4.GapP1_OpenForms
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter2.TangentMapLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §11.2,
pp. 527–528 (the sc-smoothness argument after **Definition 11.2.3**, formula (11.4); 2017:
p. 382).  Numbers and pages are the 2021 text's.

# Sc-differential forms and surjective local sc-diffeomorphisms

## The text, paraphrased

After Definition 11.2.3 the text shows that the push-forward of an sc-form by an equivalence
is sc-smooth: near a point it is the pull-back of the form by the inverse of a local
sc-diffeomorphism (formula (11.4)).

## What is formalized

For M-polyfolds `X`, `Y` and a surjective local sc-diffeomorphism `q : X → Y`
(`MPolyfold.IsLocalScDiffeo`):
* `MPolyfold.formPullback_injective_of_isLocalScDiffeo`: **`q^*` is injective** on the families
  of alternating forms on the tangent spaces of `Y` (every point of `Y₁` is the image of a point
  of `X₁`, and `Tq` is a bijection of the tangent spaces).
* `MPolyfold.isScForm_of_formPullback`: **a family `τ` on `Y` with `q^*τ ∈ Ωᵏ(X)` is an
  sc-differential form** (`τ ∈ Ωᵏ(Y)`): on the open image `V` of a sheet of `q`, with inverse
  `g : V → X`, the restriction `τ|V` is `g^*(q^*τ)` (the text's (11.4)), and sc-smoothness of a
  form is local (`isScForm_of_cover`).

* `MPolyfold.IsLocalScDiffeo.tangentFiberEquiv` (`Tq : T_xX ≃ T_{q(x)}Y`), `MPolyfold.formDescend`
  (**the descent `τ_y = η_x ∘ (Tq(x))⁻¹`** of a family `η` on `X`, for a chosen `x` over `y`) and
  `MPolyfold.formPullback_formDescend`: `q^*τ = η` when `η` takes the same values on vectors with
  the same image under `Tq` (the content of Lemma 11.2.2 on the level of M-polyfolds).

No hypothesis is added: these are statements about arbitrary M-polyfolds.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {q : X → Y} {k : ℕ}

/-- A surjective local sc-diffeomorphism is surjective on level `1`, with the tangent spaces
mapped onto the tangent spaces: every `β₁, …, β_k ∈ T_yY` are `Tq α₁, …, Tq α_k` for some
`x ∈ X₁` over `y` and `αᵢ ∈ T_xX`. -/
theorem IsLocalScDiffeo.exists_tangentFiber_lift (hq : P.IsLocalScDiffeo Q q) (hs : Surjective q)
    (y : Q.Level 1) (β : Fin k → Q.tangentFiber y) :
    ∃ (x : P.Level 1) (_ : q (P.levelVal 1 x) = Q.levelVal 1 y) (α : Fin k → P.tangentFiber x),
      ∀ i, MPolyfold.tangentMap hq.isScSmoothMap (α i).1 = β i := by
  obtain ⟨z, hz⟩ := hs (Q.levelVal 1 y)
  have hz1 : z ∈ P.levelSet 1 := (hq.mem_levelSet_iff z 1).1 (hz ▸ levelVal_mem y)
  have hxy : q (P.levelVal 1 (P.levelMk 1 z hz1)) = Q.levelVal 1 y := by
    rw [levelVal_levelMk]; exact hz
  have h := fun i => hq.tangentFiber_subset_image (P.levelMk 1 z hz1) y hxy (β i).2
  choose a ha hab using h
  exact ⟨P.levelMk 1 z hz1, hxy, fun i => ⟨a i, ha i⟩, hab⟩

/-- **The pull-back by a surjective local sc-diffeomorphism is injective** on the families of
alternating forms. -/
theorem formPullback_injective_of_isLocalScDiffeo (hq : P.IsLocalScDiffeo Q q)
    (hs : Surjective q) (hq' : P.IsScSmoothMap Q q)
    {τ τ' : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : formPullback hq' τ = formPullback hq' τ') : τ = τ' := by
  funext y
  ext β
  obtain ⟨x, hxy, α, hα⟩ := hq.exists_tangentFiber_lift hs y β
  rw [← formPullback_eq hq' τ α hxy β hα, ← formPullback_eq hq' τ' α hxy β hα, h]

/-- The restriction of a family to an open subset `V`, read in a chart of `X` inside `V`: the
same local representative. -/
theorem isChartScSmooth_of_formRestrict {V : Set Y} (hV : IsOpen V) [Nonempty V]
    [ParacompactSpace V] {τ : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : formRestrict hV τ ∈ (Q.restrictOpen hV).scForms k) {φ : MChart Y} (hφ : Q.IsChart φ)
    (hsub : φ.source ⊆ V) : IsChartScSmooth hφ τ := by
  have hφ' : (Q.restrictOpen hV).IsChart (φ.restrictTo hsub) := isChart_restrictTo hV hφ hsub
  have hdom : TangentPre.fdom (φ.restrictTo hsub) (Subtype.val : V → Y) φ =
      (φ.restrictTo hsub).source := inter_eq_left.2 fun v hv => hv
  have himg : (φ.restrictTo hsub) '' TangentPre.fdom (φ.restrictTo hsub) (Subtype.val : V → Y) φ =
      φ.model.O := by
    rw [hdom]; exact (φ.restrictTo hsub).image_source
  have hid : EqOn (φ ∘ (Subtype.val : V → Y) ∘ (φ.restrictTo hsub).symm) id φ.model.O :=
    fun z hz => by
      simp only [Function.comp_apply, id]
      rw [MChart.restrictTo_symm_val hsub hz, φ.apply_symm_apply hz]
  refine (h hφ').congr fun p hp => ?_
  have hp' : p ∈ retractWhitney (φ.restrictTo hsub).model.E (φ.restrictTo hsub).model.C
      ((φ.restrictTo hsub) '' TangentPre.fdom (φ.restrictTo hsub) (Subtype.val : V → Y) φ) k := by
    rw [himg]; exact hp
  have e := chartForm_formPullback (isScSmoothMap_subtypeVal hV) hφ' hφ τ hp'
  rw [formRestrict, e]
  congr 1
  have e2 := retractWhitneyMap_eq_self (k := k) φ.model.isScRetract hid hp
  rw [← himg] at e2
  exact e2

/-- **A family whose pull-back by a surjective local sc-diffeomorphism is an sc-differential
form is an sc-differential form** (2021 p. 528, formula (11.4)). -/
theorem isScForm_of_formPullback (hq : P.IsLocalScDiffeo Q q) (hs : Surjective q)
    (hq' : P.IsScSmoothMap Q q) {τ : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : formPullback hq' τ ∈ P.scForms k) : τ ∈ Q.scForms k := by
  refine isScForm_of_cover τ fun y => ?_
  obtain ⟨z, hz⟩ := hs (Q.levelVal 1 y)
  obtain ⟨U, V, g, hzU, hd⟩ := hq z
  have hV : IsOpen V := hd.isOpen_target
  have hyV : Q.levelVal 1 y ∈ V := hz ▸ hd.mapsTo hzU
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  have : ParacompactSpace V := Q.paracompactSpace_subtype V
  have hg : (Q.restrictOpen hV).IsScSmoothMap P (g ∘ (Subtype.val : V → Y)) :=
    hd.isScSmoothOn_inv.comp (isScSmoothMap_subtypeVal hV) fun v _ => v.2
  have h1 : formRestrict hV τ ∈ (Q.restrictOpen hV).scForms k := by
    have h2 := formPullback_mem_scForms hg h
    rw [← formPullback_comp hq' hg τ] at h2
    rw [formRestrict, formPullback_congr (isScSmoothMap_subtypeVal hV) (hq'.comp hg)
      (fun v => (hd.right_inv v.1 v.2).symm) τ]
    exact h2
  obtain ⟨φ, hφ, hyφ⟩ := Q.exists_isChart_mem_source (Q.levelVal 1 y)
  exact ⟨φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV),
    MPolyfold.IsChart.restrict Q hφ _ _, ⟨hyφ, hyV⟩,
    isChartScSmooth_of_formRestrict hV h1 (MPolyfold.IsChart.restrict Q hφ _ _)
      inter_subset_right⟩

/-! ### The descent of a family along a surjective local sc-diffeomorphism -/

/-- **`Tq : T_xX → T_yY` as a linear isomorphism**, for a local sc-diffeomorphism `q` and
`q(x) = y`, `x ∈ X₁`. -/
def IsLocalScDiffeo.tangentFiberEquiv (hq : P.IsLocalScDiffeo Q q) {x : P.Level 1}
    {y : Q.Level 1} (hxy : q (P.levelVal 1 x) = Q.levelVal 1 y) :
    P.tangentFiber x ≃ₗ[ℝ] Q.tangentFiber y :=
  LinearEquiv.ofBijective
    (tangentMapCLM hq.isScSmoothMap hxy : P.tangentFiber x →ₗ[ℝ] Q.tangentFiber y)
    ⟨fun a b h => Subtype.ext ((hq.bijOn_tangentFiber x y hxy).injOn a.2 b.2 (by
        have h' := congrArg (Subtype.val : Q.tangentFiber y → Q.TangentSpace) h
        exact ((tangentMapCLM_apply hq.isScSmoothMap hxy a).symm.trans h').trans
          (tangentMapCLM_apply hq.isScSmoothMap hxy b))),
      fun b => by
        obtain ⟨a, ha, hab⟩ := (hq.bijOn_tangentFiber x y hxy).surjOn b.2
        exact ⟨⟨a, ha⟩, Subtype.ext ((tangentMapCLM_apply hq.isScSmoothMap hxy ⟨a, ha⟩).trans hab)⟩⟩

theorem IsLocalScDiffeo.coe_tangentFiberEquiv (hq : P.IsLocalScDiffeo Q q) {x : P.Level 1}
    {y : Q.Level 1} (hxy : q (P.levelVal 1 x) = Q.levelVal 1 y) (a : P.tangentFiber x) :
    (hq.tangentFiberEquiv hxy a : Q.TangentSpace) = MPolyfold.tangentMap hq.isScSmoothMap a.1 :=
  tangentMapCLM_apply hq.isScSmoothMap hxy a

theorem IsLocalScDiffeo.tangentMap_tangentFiberEquiv_symm (hq : P.IsLocalScDiffeo Q q)
    {x : P.Level 1} {y : Q.Level 1} (hxy : q (P.levelVal 1 x) = Q.levelVal 1 y)
    (b : Q.tangentFiber y) :
    MPolyfold.tangentMap hq.isScSmoothMap ((hq.tangentFiberEquiv hxy).symm b).1 = b := by
  rw [← hq.coe_tangentFiberEquiv hxy, LinearEquiv.apply_symm_apply]

/-- A surjective local sc-diffeomorphism is surjective on level `1`. -/
theorem IsLocalScDiffeo.exists_level_lift (hq : P.IsLocalScDiffeo Q q) (hs : Surjective q)
    (y : Q.Level 1) : ∃ x : P.Level 1, q (P.levelVal 1 x) = Q.levelVal 1 y := by
  obtain ⟨z, hz⟩ := hs (Q.levelVal 1 y)
  exact ⟨P.levelMk 1 z ((hq.mem_levelSet_iff z 1).1 (hz ▸ levelVal_mem y)), by
    rw [levelVal_levelMk]; exact hz⟩

/-- **The descent of a family `η` on `X` along a surjective local sc-diffeomorphism
`q : X → Y`**: `τ_y = η_x ∘ (Tq(x))⁻¹` for a chosen `x ∈ X₁` over `y` (the text's Definition
11.2.3 on the level of the object M-polyfolds).  See `formPullback_formDescend`. -/
def formDescend (hq : P.IsLocalScDiffeo Q q) (hs : Surjective q)
    (η : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ := fun y =>
  (η (hq.exists_level_lift hs y).choose).compLinearMap
    (hq.tangentFiberEquiv (hq.exists_level_lift hs y).choose_spec).symm.toLinearMap

/-- **`q^*(descent of η) = η`** when `η` takes the same values on vectors with the same image
under `Tq` (the content of the text's Lemma 11.2.2). -/
theorem formPullback_formDescend (hq : P.IsLocalScDiffeo Q q) (hs : Surjective q)
    (hq' : P.IsScSmoothMap Q q) {η : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : ∀ (x x' : P.Level 1), q (P.levelVal 1 x) = q (P.levelVal 1 x') →
      ∀ (α : Fin k → P.tangentFiber x) (α' : Fin k → P.tangentFiber x'),
        (∀ i, MPolyfold.tangentMap hq' (α i).1 = MPolyfold.tangentMap hq' (α' i).1) →
        η x α = η x' α') :
    formPullback hq' (formDescend hq hs η) = η := by
  funext x
  ext α
  rw [formPullback_apply]
  set y := liftLevelOneMap hq' x
  have hc := (hq.exists_level_lift hs y).choose_spec
  refine (hη _ _ hc.symm _ _ fun i => ?_).symm
  rw [eq_comm]
  exact (hq.tangentMap_tangentFiberEquiv_symm hc _).trans (coe_tangentFiberMap_apply hq' (α i))

end MPolyfold

end Polyfold
