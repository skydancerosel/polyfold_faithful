import Polyfold.Chapter17.TangentModel
import Polyfold.Chapter11.FormDescent
import Polyfold.Chapter11.EquivalenceFormsInfty
import Polyfold.Chapter11.GeneralizedForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 "Sc-Differential Forms and Stokes" (pp. 817–820): **Proposition 17.6.1** (on the fibres),
the covering-set independence of p. 819, **Definition 17.6.2**, the direct limit `Ω∞*(C)` and the
exterior derivative of p. 820 with (17.88), and **Definition 17.6.3**.  Numbers and pages are the
2021 text's.

# Sc-differential forms on a polyfold `C = (C, F, M)`

## The text, paraphrased

(p. 818) `P : TC → C¹` is the tangent bundle; (**Proposition 17.6.1**) the `k`-fold Whitney sum
`⊕ᵏ TC → C¹` is a polyfold bundle, with the uniformizers `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC`,
`(h₁, …, h_k) ↦ (TΨ(h₁), …, TΨ(h_k))`; the transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` are the `k`-fold
Whitney sums of `M(TΨ, TΨ')` over `M(Ψ¹, Ψ'¹)`.  (p. 819) A functor `ω : ⊕ᵏ TC → ℝ`,
skew-symmetric, gives `Ψ^*ω = ω_Ψ := ω ∘ ⊕ᵏ TΨ : ⊕ᵏ TO → ℝ`; if `ω_Ψ` is sc-smooth for a covering
set, then for every uniformizer of `F`.  (**Definition 17.6.2**) `ω`, skew-symmetric and linear
in each argument, is sc-smooth if `ω_Ψ` is sc-smooth for every `Ψ` of a covering set; `Ωᵏ(C)` is
the vector space of these.  (pp. 819–820) The inclusions `C^{i+1} → C^i` give
`Ωᵏ(C) → Ωᵏ(C¹) → ⋯` with direct limit `Ω∞ᵏ(C)`; `d[ω] = [dω]` with `Ψ^*dω = d(Ψ^*ω)` (17.88),
equivalently through a covering set with model `Γ : X → C`: `d[ω] = [Γ_* d(Γ^*ω)]`, independent of
the choices, and `d ∘ d = 0` since it holds for ep-groupoids.  (**Definition 17.6.3**)
`(Ω∞*(C), d)` is the de Rham complex of `C`.

## What is formalized

* Family descent on M-polyfolds (namespace `MPolyfold`): for jointly surjective local
  sc-diffeomorphisms `q_i : X_i → Y`, `formPullback_injective_of_cover`,
  `isScForm_of_formPullback_cover` (sc-smoothness descends), the gluing `formGlue` with
  `formPullback_formGlue`; on a disjoint union `sigmaForm`, `formPullback_sigmaForm`,
  `sigmaForm_mem_scForms`, `sigmaForm_ext`.
* `TObj` (objects with a tangent space), `CatAltForm k` (families of alternating `k`-linear maps
  `ω_α` on `T_αC`), `IsFunctorialForm` (`ω` a functor `⊕ᵏ TC → ℝ`).
* `unifObj`, `unifTangent` (`TΨ` on the fibre, `S_Ψ⁻¹` of Proposition 17.2.4),
  `unifTangent_transTangent` (`TΨ' ∘ Tσ_b = Tφ ∘ TΨ` for `b = (q, φ, q')`),
  `whitneyUnifTangent` and **`proposition_17_6_1`** (the fibre part).
* `unifRep` (`Ψ^*ω`), `formPullback_trSrc_unifRep` (`s^*Ψ^*ω = t^*Ψ'^*ω` on `M(Ψ, Ψ')`),
  `unifRep_mem_scForms_of_isCoveringFamily` (the independence of the covering set, p. 819).
* `catForms` (`Ωᵏ(C)`), **`definition_17_6_2`**, the witness `catConstForm_mem`.
* `modelRep` (`Γ^*ω` on `X_Ψ = ⊔ O_λ`), `modelRep_mem_epForms`, `modelFormInfty` (`[Γ^*ω]`),
  `formPullback_modelMap_modelRep`, `formsPullback_incl_modelFormInfty`, and
  `formsPullback_comparison_modelFormInfty` (`f^*[ω_{Ψ'}] = [ω_Ψ]`, used on p. 821).
* `catFormsInfty` (`Ω∞ᵏ(C)`), `catFormsInftyEquiv` (`Ω∞ᵏ(C) ≅ Ω∞ᵏ_ep(X_Ψ)`), `catFormsInftyD`,
  `catFormsInftyD_catFormsInftyD`, `catFormsToInfty` (`ω ↦ [ω]`), `catFormsInftyD_catFormsToInfty`
  ((17.88) on the models), **`definition_17_6_3`**.

## Readings

* Tangent spaces are the ones of §17.2 under the standing reading `F(α) ≠ ∅` (`HasUniformizers`),
  as in `TangentCategory.lean`; `T_αC` exists for the objects of `C¹` (`TObj`).
* "A functor `ω : ⊕ᵏ TC → ℝ`, skew-symmetric and linear in each argument" is read as a family of
  alternating `k`-linear maps `ω_α : (T_αC)ᵏ → ℝ`, constant along the morphisms of `⊕ᵏ TC`:
  `ω_{α'} ∘ ⊕ᵏ Tφ = ω_α` (`IsFunctorialForm`).
* "`ω_Ψ` is sc-smooth" is read as: `Ψ^*ω` is an sc-differential `k`-form on `O` (Definition 4.4.1),
  the reading of Part I for forms on the Whitney sum `⊕ᵏ TO`.
* `Ωᵏ(C)` is defined with the condition for every uniformizer of `F`; `definition_17_6_2` is the
  printed form (a covering set), equivalent by the sentence before it.
* `Ω∞ᵏ(C)`: the direct limit over the levels `C^i` is read through the sc-smooth models, as the
  second definition of `d` on p. 820 does: a class is a family `[ω_Ψ] ∈ Ω∞ᵏ_ep(X_Ψ)` over all
  covering families, compatible with the canonical generalized isomorphisms `f_{Ψ,Ψ'}`
  (Theorem 17.1.18).  `Γ^*` of a form on `C^i` is a form on `X_Ψ^i`, which is what the direct limit
  `Ω∞ᵏ_ep(X_Ψ)` collects; by `catFormsInftyEquiv` this is `Ω∞ᵏ_ep(X_Ψ)` for each `Ψ`.  The forms
  `Ωᵏ(C^i)` for `i ≥ 1` are not formalized separately; `Ωᵏ(C)` enters through `catFormsToInfty`.
* `d` is `d[ω] = [Γ_*d(Γ^*ω)]` (p. 820), computed on each model; (17.88) is
  `catFormsInftyD_catFormsToInfty`.
* Proposition 17.6.1 is formalized here on the fibres: the maps `⊕ᵏ TΨ` and their compatibility
  with the transition sets; the forms above use only the fibre maps.  The M-polyfold bundle
  structure on `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`, its source and target maps as local bundle isomorphisms and the
  metrics of the orbit spaces are in `WhitneySumStructure.lean` (`proposition_17_6_1_transition`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

section Cover

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {P : ∀ i, MPolyfold (X i)}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {q : ∀ i, X i → Y} {k : ℕ}

/-- Jointly surjective local sc-diffeomorphisms are jointly surjective on level `1`, with the
tangent spaces mapped onto the tangent spaces. -/
theorem exists_tangentFiber_lift_of_cover (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i))
    (hs : ∀ y, ∃ i x, q i x = y) (y : Q.Level 1) (β : Fin k → Q.tangentFiber y) :
    ∃ (i : ι) (x : (P i).Level 1) (_ : q i ((P i).levelVal 1 x) = Q.levelVal 1 y)
      (α : Fin k → (P i).tangentFiber x),
      ∀ l, MPolyfold.tangentMap (hq i).isScSmoothMap (α l).1 = β l := by
  obtain ⟨i, z, hz⟩ := hs (Q.levelVal 1 y)
  have hz1 : z ∈ (P i).levelSet 1 := ((hq i).mem_levelSet_iff z 1).1 (hz ▸ levelVal_mem y)
  have hxy : q i ((P i).levelVal 1 ((P i).levelMk 1 z hz1)) = Q.levelVal 1 y := by
    rw [levelVal_levelMk]; exact hz
  have h := fun l => (hq i).tangentFiber_subset_image ((P i).levelMk 1 z hz1) y hxy (β l).2
  choose a ha hab using h
  exact ⟨i, _, hxy, fun l => ⟨a l, ha l⟩, hab⟩

/-- **The pull-backs by jointly surjective local sc-diffeomorphisms determine a family of
alternating forms.** -/
theorem formPullback_injective_of_cover (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i))
    (hs : ∀ y, ∃ i x, q i x = y)
    {τ τ' : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : ∀ i, formPullback (hq i).isScSmoothMap τ = formPullback (hq i).isScSmoothMap τ') :
    τ = τ' := by
  funext y
  ext β
  obtain ⟨i, x, hxy, α, hα⟩ := exists_tangentFiber_lift_of_cover hq hs y β
  rw [← formPullback_eq (hq i).isScSmoothMap τ α hxy β hα,
    ← formPullback_eq (hq i).isScSmoothMap τ' α hxy β hα, h i]

/-- **A family whose pull-backs by jointly surjective local sc-diffeomorphisms are
sc-differential forms is an sc-differential form** (the proof of `isScForm_of_formPullback`,
2021 p. 528, for a family of maps). -/
theorem isScForm_of_formPullback_cover (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i))
    (hs : ∀ y, ∃ i x, q i x = y) {τ : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : ∀ i, formPullback (hq i).isScSmoothMap τ ∈ (P i).scForms k) : τ ∈ Q.scForms k := by
  refine isScForm_of_cover τ fun y => ?_
  obtain ⟨i, z, hz⟩ := hs (Q.levelVal 1 y)
  obtain ⟨U, V, g, hzU, hd⟩ := hq i z
  have hV : IsOpen V := hd.isOpen_target
  have hyV : Q.levelVal 1 y ∈ V := hz ▸ hd.mapsTo hzU
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  have : ParacompactSpace V := Q.paracompactSpace_subtype V
  have hg : (Q.restrictOpen hV).IsScSmoothMap (P i) (g ∘ (Subtype.val : V → Y)) :=
    hd.isScSmoothOn_inv.comp (isScSmoothMap_subtypeVal hV) fun v _ => v.2
  have h1 : formRestrict hV τ ∈ (Q.restrictOpen hV).scForms k := by
    have h2 := formPullback_mem_scForms hg (h i)
    rw [← formPullback_comp (hq i).isScSmoothMap hg τ] at h2
    rw [formRestrict, formPullback_congr (isScSmoothMap_subtypeVal hV)
      ((hq i).isScSmoothMap.comp hg) (fun v => (hd.right_inv v.1 v.2).symm) τ]
    exact h2
  obtain ⟨φ, hφ, hyφ⟩ := Q.exists_isChart_mem_source (Q.levelVal 1 y)
  exact ⟨φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV),
    MPolyfold.IsChart.restrict Q hφ _ _, ⟨hyφ, hyV⟩,
    isChartScSmooth_of_formRestrict hV h1 (MPolyfold.IsChart.restrict Q hφ _ _)
      inter_subset_right⟩

/-- A chosen point over `y` on level `1`, for jointly surjective local sc-diffeomorphisms. -/
theorem exists_level_lift_of_cover (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i))
    (hs : ∀ y, ∃ i x, q i x = y) (y : Q.Level 1) :
    ∃ (i : ι) (x : (P i).Level 1), q i ((P i).levelVal 1 x) = Q.levelVal 1 y := by
  obtain ⟨i, z, hz⟩ := hs (Q.levelVal 1 y)
  exact ⟨i, (P i).levelMk 1 z (((hq i).mem_levelSet_iff z 1).1 (hz ▸ levelVal_mem y)), by
    rw [levelVal_levelMk]; exact hz⟩

/-- **The gluing of a family `η_i` on the `X_i`** along jointly surjective local
sc-diffeomorphisms `q_i : X_i → Y`: `τ_y = η_{i,x} ∘ (Tq_i(x))⁻¹` for a chosen `(i, x)` over `y`
(`formDescend` for a family of maps). -/
def formGlue (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i)) (hs : ∀ y, ∃ i x, q i x = y)
    (η : ∀ i, ∀ x : (P i).Level 1, (P i).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ := fun y =>
  (η _ (exists_level_lift_of_cover hq hs y).choose_spec.choose).compLinearMap
    ((hq _).tangentFiberEquiv
      (exists_level_lift_of_cover hq hs y).choose_spec.choose_spec).symm.toLinearMap

/-- **`q_i^*(glued form) = η_i`** when the `η_i` take the same values on vectors with the same
images. -/
theorem formPullback_formGlue (hq : ∀ i, (P i).IsLocalScDiffeo Q (q i))
    (hs : ∀ y, ∃ i x, q i x = y)
    {η : ∀ i, ∀ x : (P i).Level 1, (P i).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : ∀ (i j : ι) (x : (P i).Level 1) (x' : (P j).Level 1),
      q i ((P i).levelVal 1 x) = q j ((P j).levelVal 1 x') →
      ∀ (α : Fin k → (P i).tangentFiber x) (α' : Fin k → (P j).tangentFiber x'),
        (∀ l, MPolyfold.tangentMap (hq i).isScSmoothMap (α l).1 =
          MPolyfold.tangentMap (hq j).isScSmoothMap (α' l).1) →
        η i x α = η j x' α') (i : ι) :
    formPullback (hq i).isScSmoothMap (formGlue hq hs η) = η i := by
  funext x
  ext α
  rw [formPullback_apply]
  set y := liftLevelOneMap (hq i).isScSmoothMap x
  have hc := (exists_level_lift_of_cover hq hs y).choose_spec.choose_spec
  refine (hη _ _ _ _ hc.symm _ _ fun l => ?_).symm
  rw [eq_comm]
  exact ((hq _).tangentMap_tangentFiberEquiv_symm hc _).trans
    (coe_tangentFiberMap_apply (hq i).isScSmoothMap (α l))

end Cover

section SigmaGlue

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (P : ∀ i, MPolyfold (X i)) {k : ℕ}

omit [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
theorem exists_sigmaMk_eq (y : Σ i, X i) : ∃ i x, Sigma.mk i x = y := ⟨y.1, y.2, rfl⟩

/-- **The form on `⊔ X_i` with the forms `η_i` on the summands.** -/
def sigmaForm (η : ∀ i, ∀ x : (P i).Level 1, (P i).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ y : (sigma P).Level 1, (sigma P).tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ :=
  formGlue (q := fun i => Sigma.mk i) (isLocalScDiffeo_sigmaMk P) exists_sigmaMk_eq η

/-- **`(Sigma.mk i)^*(⊔ η) = η_i`.** -/
theorem formPullback_sigmaForm
    (η : ∀ i, ∀ x : (P i).Level 1, (P i).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) (i : ι) :
    formPullback (isScSmoothMap_sigmaMk P i) (sigmaForm P η) = η i := by
  refine formPullback_formGlue (q := fun i => Sigma.mk i) (isLocalScDiffeo_sigmaMk P)
    exists_sigmaMk_eq (fun i j x x' hxx' α α' hαα' => ?_) i
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hxx'
  obtain rfl : x = x' := level_ext (eq_of_heq h)
  congr 1
  funext l
  exact Subtype.ext (eq_of_heq (sigmaTangent_mk_inj P (hαα' l)).2)

theorem sigmaForm_mem_scForms
    {η : ∀ i, ∀ x : (P i).Level 1, (P i).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : ∀ i, η i ∈ (P i).scForms k) : sigmaForm P η ∈ (sigma P).scForms k :=
  isScForm_of_formPullback_cover (q := fun i => Sigma.mk i) (isLocalScDiffeo_sigmaMk P)
    exists_sigmaMk_eq fun i => by
    rw [formPullback_sigmaForm]; exact hη i

/-- Forms on `⊔ X_i` are determined by their pull-backs to the summands. -/
theorem sigmaForm_ext {τ τ' : ∀ y : (sigma P).Level 1, (sigma P).tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : ∀ i, formPullback (isScSmoothMap_sigmaMk P i) τ =
      formPullback (isScSmoothMap_sigmaMk P i) τ') : τ = τ' :=
  formPullback_injective_of_cover (q := fun i => Sigma.mk i) (isLocalScDiffeo_sigmaMk P)
    exists_sigmaMk_eq h

end SigmaGlue

end MPolyfold

namespace GCT.PolyfoldConstruction

open MPolyfold

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {k : ℕ}

variable (S) in
/-- The objects `α` of `C¹` with a tangent space `T_αC`. -/
abbrev TObj := {α : C.Obj // S.TangentObj α}

instance TObj.fact (α : S.TObj) : Fact (S.TangentObj α.1) := ⟨α.2⟩

variable (S) in
/-- Families `ω_α : ⊕ᵏ T_αC → ℝ` of alternating `k`-linear maps. -/
abbrev CatAltForm (k : ℕ) := ∀ α : S.TObj, S.TangentSpaceAt α.1 [⋀^Fin k]→ₗ[ℝ] ℝ

/-- **`ω` is a functor `⊕ᵏ TC → ℝ`**: `ω_{α'}(Tφ v₁, …, Tφ v_k) = ω_α(v₁, …, v_k)` for every
morphism `φ : α → α'`. -/
def IsFunctorialForm (ω : S.CatAltForm k) : Prop :=
  ∀ (α α' : S.TObj) (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α.1)
    (ht : C.toGroupoidStr.tgt φ = α'.1) (v : Fin k → S.TangentSpaceAt α.1),
    ω α' (fun i => S.tangentMorCLE φ hs ht (v i)) = ω α v

variable (S) in
/-- The object `Ψ(q)`, `q ∈ O¹`, with its tangent space. -/
def unifObj (hU : S.HasUniformizers) (Ψ : S.Unif) (x : Ψ.1.P.Level 1) : S.TObj :=
  ⟨Ψ.1.obj (Ψ.1.P.levelVal 1 x),
    ⟨Ψ, _, C.toGroupoidStr.isomorphic_refl _, MPolyfold.levelVal_mem _⟩, hU _⟩

variable (S) in
/-- **`TΨ : T_qO ≃L[ℝ] T_{Ψ(q)}C`**, `h ↦ [Ψ(q), Ψ, h]` (`S_Ψ⁻¹`, Proposition 17.2.4). -/
def unifTangent (hU : S.HasUniformizers) (Ψ : S.Unif) (x : Ψ.1.P.Level 1) :
    Ψ.1.P.tangentFiber x ≃L[ℝ] S.TangentSpaceAt (S.unifObj hU Ψ x).1 :=
  (S.tangentChartCLE (S.unifObj hU Ψ x).1 Ψ x rfl).symm

/-- **`TΨ' ∘ Tσ_b = Tφ ∘ TΨ`** for `b = (q, φ, q') ∈ M(Ψ, Ψ')`. -/
theorem unifTangent_transTangent (hU : S.HasUniformizers) {Ψ Ψ' : S.Unif} (b : S.Tr Ψ Ψ')
    {x : Ψ.1.P.Level 1} {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = b.src)
    (hy : Ψ'.1.P.levelVal 1 y = b.tgt) (v : Ψ.1.P.tangentFiber x) :
    S.unifTangent hU Ψ' y (S.transTangent b hx hy v) =
      S.tangentMorCLE (α := (S.unifObj hU Ψ x).1) (α' := (S.unifObj hU Ψ' y).1) b.mor
        (b.src_mor.trans (congrArg Ψ.1.obj hx.symm)) (b.tgt_mor.trans (congrArg Ψ'.1.obj hy.symm))
        (S.unifTangent hU Ψ x v) := by
  obtain ⟨e, rfl⟩ : ∃ e, v = S.tangentChartCLE (S.unifObj hU Ψ x).1 Ψ x rfl e :=
    ⟨_, ((S.tangentChartCLE (S.unifObj hU Ψ x).1 Ψ x rfl).apply_symm_apply v).symm⟩
  have hs : C.toGroupoidStr.src b.mor = (S.unifObj hU Ψ x).1 :=
    b.src_mor.trans (congrArg Ψ.1.obj hx.symm)
  have ht : C.toGroupoidStr.tgt b.mor = (S.unifObj hU Ψ' y).1 :=
    b.tgt_mor.trans (congrArg Ψ'.1.obj hy.symm)
  set w := S.refChartCLE (S.unifObj hU Ψ x).1 e
  have hw : _ = _ := congrArg ((S.refUnif (S.unifObj hU Ψ x).2).1.P.levelVal 1) w.2
  set c := S.morTr _ b.mor (Ψ'.1.P.levelVal 1 y) (obj_refPoint (S.unifObj hU Ψ x).2) hs rfl ht
  apply (S.tangentChartCLE (S.unifObj hU Ψ' y).1 Ψ' y rfl).injective
  rw [unifTangent, unifTangent, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  apply Subtype.ext
  have L : (S.transTangent b hx hy (S.tangentChartCLE (S.unifObj hU Ψ x).1 Ψ x rfl e) :
      Ψ'.1.P.TangentSpace) = S.transMap c w.1 :=
    (transTangent_apply b hx hy _).trans ((congrArg (S.transMap b)
      (transTangent_apply (S.unitTr _ _ (obj_refPoint (S.unifObj hU Ψ x).2) rfl) rfl rfl w)).trans
      (transMap_comp' b (S.unitTr _ _ (obj_refPoint (S.unifObj hU Ψ x).2) rfl) c rfl
        (GroupoidStr.comp_unit_of_eq hs).symm hy hx.symm hw).symm)
  have R : (S.tangentChartCLE (S.unifObj hU Ψ' y).1 Ψ' y rfl
      (S.tangentMorCLE (α := (S.unifObj hU Ψ x).1) (α' := (S.unifObj hU Ψ' y).1) b.mor hs ht e) :
      Ψ'.1.P.TangentSpace) = S.transMap c w.1 := by
    have R2 : ∀ z, S.tangentChartCLE (S.unifObj hU Ψ' y).1 Ψ' y rfl
        ((S.refChartCLE (S.unifObj hU Ψ' y).1).symm z) =
        S.transTangent (S.unitTr _ _ (obj_refPoint (S.unifObj hU Ψ' y).2) rfl) rfl rfl z := by
      intro z
      exact congrArg
        (S.transTangent (S.unitTr _ _ (obj_refPoint (S.unifObj hU Ψ' y).2) rfl) rfl rfl)
        ((S.refChartCLE (S.unifObj hU Ψ' y).1).apply_symm_apply z)
    rw [tangentMorCLE, ContinuousLinearEquiv.trans_apply, R2, ContinuousLinearEquiv.trans_apply]
    exact (transTangent_apply _ rfl rfl _).trans
      ((congrArg (S.transMap _) (transTangent_apply _ rfl rfl w)).trans
      (transMap_comp' (S.unitTr _ _ (obj_refPoint (S.unifObj hU Ψ' y).2) rfl)
        (S.morTr _ b.mor _ (obj_refPoint (S.unifObj hU Ψ x).2) hs
          (obj_refPoint (S.unifObj hU Ψ' y).2) ht) c rfl (GroupoidStr.unit_comp_of_eq ht).symm
        rfl rfl hw).symm)
  exact L.trans R.symm

/-! ### Proposition 17.6.1 on the fibres -/

variable (S) in
/-- **`⊕ᵏ TΨ` on the fibre over `q ∈ O¹`** (2021 p. 818):
`(h₁, …, h_k) ↦ (TΨ(h₁), …, TΨ(h_k))`, a topological linear isomorphism
`⊕ᵏ T_qO ≃ ⊕ᵏ T_{Ψ(q)}C`. -/
def whitneyUnifTangent (hU : S.HasUniformizers) (Ψ : S.Unif) (x : Ψ.1.P.Level 1) (k : ℕ) :
    (Fin k → Ψ.1.P.tangentFiber x) ≃L[ℝ] (Fin k → S.TangentSpaceAt (S.unifObj hU Ψ x).1) :=
  ContinuousLinearEquiv.piCongrRight fun _ => S.unifTangent hU Ψ x

theorem whitneyUnifTangent_apply (hU : S.HasUniformizers) (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (v : Fin k → Ψ.1.P.tangentFiber x) (i : Fin k) :
    S.whitneyUnifTangent hU Ψ x k v i = S.unifTangent hU Ψ x (v i) := rfl

/-- **Proposition 17.6.1 on the fibres** (2021 pp. 818–819): the `⊕ᵏ TΨ` are topological linear
isomorphisms on the fibres, and on the transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`, read as the `k`-fold
Whitney sum of `M(TΨ, TΨ')` over `M(Ψ¹, Ψ'¹)`, they intertwine `⊕ᵏ Tσ_b` with `⊕ᵏ Tφ` for
`b = (q, φ, q') ∈ M(Ψ, Ψ')`. -/
theorem proposition_17_6_1 (hU : S.HasUniformizers) {Ψ Ψ' : S.Unif} (b : S.Tr Ψ Ψ')
    {x : Ψ.1.P.Level 1} {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = b.src)
    (hy : Ψ'.1.P.levelVal 1 y = b.tgt) (v : Fin k → Ψ.1.P.tangentFiber x) :
    S.whitneyUnifTangent hU Ψ' y k (fun i => S.transTangent b hx hy (v i)) = fun i =>
      S.tangentMorCLE (α := (S.unifObj hU Ψ x).1) (α' := (S.unifObj hU Ψ' y).1) b.mor
        (b.src_mor.trans (congrArg Ψ.1.obj hx.symm)) (b.tgt_mor.trans (congrArg Ψ'.1.obj hy.symm))
        (S.whitneyUnifTangent hU Ψ x k v i) :=
  funext fun i => unifTangent_transTangent hU b hx hy (v i)

variable (S) in
/-- **`Ψ^*ω = ω ∘ ⊕ᵏ TΨ`** (2021 p. 819, `ω_Ψ`): the family of alternating maps on the fibres
`T_qO`, `q ∈ O¹`. -/
def unifRep (hU : S.HasUniformizers) (ω : S.CatAltForm k) (Ψ : S.Unif) :
    ∀ x : Ψ.1.P.Level 1, Ψ.1.P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ := fun x =>
  (ω (S.unifObj hU Ψ x)).compLinearMap (S.unifTangent hU Ψ x).toLinearEquiv.toLinearMap

theorem unifRep_apply (hU : S.HasUniformizers) (ω : S.CatAltForm k) (Ψ : S.Unif)
    (x : Ψ.1.P.Level 1) (v : Fin k → Ψ.1.P.tangentFiber x) :
    S.unifRep hU ω Ψ x v = ω (S.unifObj hU Ψ x) fun i => S.unifTangent hU Ψ x (v i) := rfl

/-- `Ψ^*ω = ω ∘ ⊕ᵏ TΨ` (2021 p. 819). -/
theorem unifRep_apply_whitney (hU : S.HasUniformizers) (ω : S.CatAltForm k) (Ψ : S.Unif)
    (x : Ψ.1.P.Level 1) (v : Fin k → Ψ.1.P.tangentFiber x) :
    S.unifRep hU ω Ψ x v = ω (S.unifObj hU Ψ x) (S.whitneyUnifTangent hU Ψ x k v) := rfl

theorem unifRep_add (hU : S.HasUniformizers) (ω τ : S.CatAltForm k) (Ψ : S.Unif) :
    S.unifRep hU (ω + τ) Ψ = S.unifRep hU ω Ψ + S.unifRep hU τ Ψ := rfl

theorem unifRep_smul (hU : S.HasUniformizers) (r : ℝ) (ω : S.CatAltForm k) (Ψ : S.Unif) :
    S.unifRep hU (r • ω) Ψ = r • S.unifRep hU ω Ψ := rfl

theorem unifRep_zero (hU : S.HasUniformizers) (Ψ : S.Unif) :
    S.unifRep hU (0 : S.CatAltForm k) Ψ = 0 := rfl

/-- **`s^*(Ψ^*ω) = t^*(Ψ'^*ω)` on `M(Ψ, Ψ')`** for a functor `ω : ⊕ᵏ TC → ℝ`: on the tangent of
`b = (q, φ, q')`, `Tt = Tσ_b ∘ Ts` and `TΨ' ∘ Tσ_b = Tφ ∘ TΨ`. -/
theorem formPullback_trSrc_unifRep (hU : S.HasUniformizers) {ω : S.CatAltForm k}
    (hω : S.IsFunctorialForm ω) (Ψ Ψ' : S.Unif) :
    formPullback (S.isLocalScDiffeo_trSrc Ψ Ψ').isScSmoothMap (S.unifRep hU ω Ψ) =
      formPullback (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap (S.unifRep hU ω Ψ') := by
  funext a
  ext α
  rw [formPullback_apply, formPullback_apply]
  have hx : Ψ.1.P.levelVal 1 (liftLevelOneMap (S.isLocalScDiffeo_trSrc Ψ Ψ').isScSmoothMap a) =
      ((S.transPolyfold Ψ Ψ').levelVal 1 a).src := levelVal_levelMk _ _ _
  have hy : Ψ'.1.P.levelVal 1 (liftLevelOneMap (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap a) =
      ((S.transPolyfold Ψ Ψ').levelVal 1 a).tgt := levelVal_levelMk _ _ _
  have hT : ∀ l, tangentFiberMap (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap a (α l) =
      S.transTangent ((S.transPolyfold Ψ Ψ').levelVal 1 a) hx hy
        (tangentFiberMap (S.isLocalScDiffeo_trSrc Ψ Ψ').isScSmoothMap a (α l)) :=
    fun l => Subtype.ext ((coe_tangentFiberMap_apply _ _).trans
      ((trTTgt_eq_transMap (S := S) (α l).1).trans
        ((congrFun (transMap_congr (congrArg _ (α l).2)) _).trans
          ((transTangent_apply _ _ _ _).trans
            (congrArg _ (coe_tangentFiberMap_apply _ _))).symm)))
  rw [unifRep_apply, unifRep_apply]
  rw [show (fun l => S.unifTangent hU Ψ' _
      (tangentFiberMap (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap a (α l))) = fun l =>
      S.tangentMorCLE (α := (S.unifObj hU Ψ _).1) (α' := (S.unifObj hU Ψ' _).1) _
        (((S.transPolyfold Ψ Ψ').levelVal 1 a).src_mor.trans (congrArg Ψ.1.obj hx.symm))
        (((S.transPolyfold Ψ Ψ').levelVal 1 a).tgt_mor.trans (congrArg Ψ'.1.obj hy.symm))
        (S.unifTangent hU Ψ _
          (tangentFiberMap (S.isLocalScDiffeo_trSrc Ψ Ψ').isScSmoothMap a (α l))) from
    funext fun l => (congrArg _ (hT l)).trans (unifTangent_transTangent hU _ hx hy _)]
  exact (hω _ _ _ _ _ _).symm

/-- **Independence of the covering set** (2021 p. 819: "If `ω` is such that `ω_Ψ` is sc-smooth for
a covering set of uniformizers, then the smoothness holds for any uniformizer coming from `F`"):
the `M(Ψ, Ψ_λ)` cover `O` through `s`, and `s^*(Ψ^*ω) = t^*(Ψ_λ^*ω)`. -/
theorem unifRep_mem_scForms_of_isCoveringFamily (hU : S.HasUniformizers) {ω : S.CatAltForm k}
    (hω : S.IsFunctorialForm ω) {ι : Type u} {Φ : ι → S.Unif} (hΦ : S.IsCoveringFamily Φ)
    (h : ∀ i, S.unifRep hU ω (Φ i) ∈ (Φ i).1.P.scForms k) (Ψ : S.Unif) :
    S.unifRep hU ω Ψ ∈ Ψ.1.P.scForms k := by
  refine isScForm_of_formPullback_cover (fun i => S.isLocalScDiffeo_trSrc Ψ (Φ i))
    (fun q => ?_) fun i => ?_
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hΦ.symm ▸ mem_univ (C.toGroupoidStr.π (Ψ.1.obj q)))
    obtain ⟨q', hq'⟩ := (Φ i).1.mem_footprint_iff.1 hi
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq'.symm
    exact ⟨i, ⟨q, φ, q', hs, ht⟩, rfl⟩
  · rw [formPullback_trSrc_unifRep hU hω]
    exact formPullback_mem_scForms _ (h i)

theorem isFunctorialForm_add {ω τ : S.CatAltForm k} (hω : S.IsFunctorialForm ω)
    (hτ : S.IsFunctorialForm τ) : S.IsFunctorialForm (ω + τ) := fun α α' φ hs ht v => by
  simp only [Pi.add_apply, AlternatingMap.add_apply, hω α α' φ hs ht v, hτ α α' φ hs ht v]

theorem isFunctorialForm_smul (r : ℝ) {ω : S.CatAltForm k} (hω : S.IsFunctorialForm ω) :
    S.IsFunctorialForm (r • ω) := fun α α' φ hs ht v => by
  simp only [Pi.smul_apply, AlternatingMap.smul_apply, hω α α' φ hs ht v]

theorem isFunctorialForm_zero : S.IsFunctorialForm (0 : S.CatAltForm k) := fun _ _ _ _ _ _ => rfl

variable (S) in
/-- **`Ωᵏ(C)`** (2021 Definition 17.6.2, p. 819): the functors `ω : ⊕ᵏ TC → ℝ`, alternating and
linear in each argument, with `Ψ^*ω` sc-smooth for every uniformizer `Ψ` of `F` (by
`definition_17_6_2`, equivalently for a covering set). -/
def catForms (hU : S.HasUniformizers) (k : ℕ) : Submodule ℝ (S.CatAltForm k) where
  carrier := {ω | S.IsFunctorialForm ω ∧ ∀ Ψ : S.Unif, S.unifRep hU ω Ψ ∈ Ψ.1.P.scForms k}
  add_mem' {ω τ} hω hτ := ⟨isFunctorialForm_add hω.1 hτ.1, fun Ψ => by
    rw [unifRep_add]; exact add_mem (hω.2 Ψ) (hτ.2 Ψ)⟩
  zero_mem' := ⟨isFunctorialForm_zero, fun Ψ => by rw [unifRep_zero]; exact zero_mem _⟩
  smul_mem' r {ω} hω := ⟨isFunctorialForm_smul r hω.1, fun Ψ => by
    rw [unifRep_smul]; exact Submodule.smul_mem _ r (hω.2 Ψ)⟩

/-- **Definition 17.6.2** (2021 p. 819): `ω ∈ Ωᵏ(C)` iff `ω` is a functor `⊕ᵏ TC → ℝ` and there is
a covering set of uniformizers `Ψ` with `ω_Ψ` sc-smooth for every `Ψ ∈ Ψ`. -/
theorem definition_17_6_2 (hU : S.HasUniformizers) (ω : S.CatAltForm k) :
    ω ∈ S.catForms hU k ↔ S.IsFunctorialForm ω ∧
      ∃ c : S.CoveringFamily, ∀ i, S.unifRep hU ω (c.Ψ i) ∈ (c.Ψ i).1.P.scForms k := by
  refine ⟨fun h => ⟨h.1, S.tangentCover hU, fun i => h.2 _⟩, fun ⟨h, c, hc⟩ =>
    ⟨h, unifRep_mem_scForms_of_isCoveringFamily hU h c.cover hc⟩⟩

variable (S) in
/-- The constant `0`-form `r` on `C`. -/
def catConstForm (r : ℝ) : S.CatAltForm 0 := fun _ => AlternatingMap.constOfIsEmpty ℝ _ (Fin 0) r

/-- **Witness** for `Ωᵏ(C)`: the constant `0`-forms lie in `Ω⁰(C)`, with `Ψ^*r = r`. -/
theorem catConstForm_mem (hU : S.HasUniformizers) (r : ℝ) : S.catConstForm r ∈ S.catForms hU 0 :=
  ⟨fun _ _ _ _ _ _ => rfl, fun Ψ => by
    have : S.unifRep hU (S.catConstForm r) Ψ = Ψ.1.P.constForm r := rfl
    rw [this]; exact constForm_mem_scForms r⟩

/-! ### The pull-back `Γ^*ω` to an sc-smooth model -/

section Model

open EPLocalization CategoryTheory

variable {ι κ : Type u}

variable (S) in
/-- **`Γ^*ω = ω ∘ ⊕ᵏ TΓ`** on the model `X_Φ = ⊔ O_λ`: `Ψ_λ^*ω` on the summand `O_λ`. -/
def modelRep (hU : S.HasUniformizers) (ω : S.CatAltForm k) (Φ : ι → S.Unif) :
    ∀ y : (S.modelEpGroupoid Φ).PObj.Level 1,
      (S.modelEpGroupoid Φ).PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ :=
  MPolyfold.sigmaForm (fun i => (Φ i).1.P) fun i => S.unifRep hU ω (Φ i)

/-- `Γ^*ω` on the summand `O_λ` is `Ψ_λ^*ω`. -/
theorem formPullback_objMk_modelRep (hU : S.HasUniformizers) (ω : S.CatAltForm k)
    (Φ : ι → S.Unif) (i : ι) :
    formPullback (MPolyfold.isScSmoothMap_sigmaMk (fun i => (Φ i).1.P) i) (S.modelRep hU ω Φ) =
      S.unifRep hU ω (Φ i) :=
  MPolyfold.formPullback_sigmaForm _ _ i

theorem modelRep_add (hU : S.HasUniformizers) (ω τ : S.CatAltForm k) (Φ : ι → S.Unif) :
    S.modelRep hU (ω + τ) Φ = S.modelRep hU ω Φ + S.modelRep hU τ Φ :=
  MPolyfold.sigmaForm_ext _ fun i =>
    (formPullback_objMk_modelRep hU (ω + τ) Φ i).trans ((congrArg₂ (· + ·)
      (formPullback_objMk_modelRep hU ω Φ i).symm (formPullback_objMk_modelRep hU τ Φ i).symm).trans
      (formPullback_add _ _ _).symm)

theorem modelRep_smul (hU : S.HasUniformizers) (r : ℝ) (ω : S.CatAltForm k) (Φ : ι → S.Unif) :
    S.modelRep hU (r • ω) Φ = r • S.modelRep hU ω Φ :=
  MPolyfold.sigmaForm_ext _ fun i =>
    (formPullback_objMk_modelRep hU (r • ω) Φ i).trans ((congrArg (r • ·)
      (formPullback_objMk_modelRep hU ω Φ i).symm).trans (formPullback_smul _ _ _).symm)

/-- **`Γ^*ω` is an sc-differential form on the ep-groupoid `X_Φ`** (2021 p. 820: "`Γ^*ω` is
`sc∞`, by definition"): sc-smooth on each `O_λ`, and compatible with the morphisms since
`s^*(Ψ_λ^*ω) = t^*(Ψ_λ'^*ω)` on `M(Ψ_λ, Ψ_λ')`. -/
theorem modelRep_mem_epForms (hU : S.HasUniformizers) {ω : S.CatAltForm k}
    (hω : ω ∈ S.catForms hU k) (Φ : ι → S.Unif) :
    S.modelRep hU ω Φ ∈ (S.modelEpGroupoid Φ).epForms k := by
  refine (EpGroupoid.mem_epForms_iff_formPullback _).2
    ⟨MPolyfold.sigmaForm_mem_scForms _ fun i => hω.2 _, ?_⟩
  refine MPolyfold.sigmaForm_ext (fun p : ι × ι => S.transPolyfold (Φ p.1) (Φ p.2)) fun p => ?_
  refine (formPullback_comp _ _ _).symm.trans (Eq.trans ?_ (formPullback_comp _ _ _))
  refine (formPullback_congr _ ((MPolyfold.isScSmoothMap_sigmaMk (fun i => (Φ i).1.P) p.1).comp
    (S.isLocalScDiffeo_trSrc _ _).isScSmoothMap) (fun _ => rfl) _).trans
    (Eq.trans ?_ (formPullback_congr
      ((MPolyfold.isScSmoothMap_sigmaMk (fun i => (Φ i).1.P) p.2).comp
      (S.isLocalScDiffeo_trTgt _ _).isScSmoothMap) _ (fun _ => rfl) _))
  exact (formPullback_comp _ _ _).trans
    ((congrArg (formPullback (S.isLocalScDiffeo_trSrc (Φ p.1) (Φ p.2)).isScSmoothMap)
      (formPullback_objMk_modelRep hU ω Φ p.1)).trans
    ((formPullback_trSrc_unifRep hU hω.1 _ _).trans
    ((congrArg (formPullback (S.isLocalScDiffeo_trTgt (Φ p.1) (Φ p.2)).isScSmoothMap)
      (formPullback_objMk_modelRep hU ω Φ p.2)).symm.trans (formPullback_comp _ _ _).symm)))

variable (S) in
/-- **`[Γ^*ω] ∈ Ω∞ᵏ_ep(X_Φ)`**, the class of `Γ^*ω` (level `0`). -/
def modelFormInfty (hU : S.HasUniformizers) (ω : S.catForms hU k) (Φ : ι → S.Unif) :
    (S.modelEP Φ).epFormsInfty k :=
  (S.modelEP Φ).epFormsInftyOf k 0 ⟨S.modelRep hU ω.1 Φ, S.modelRep_mem_epForms hU ω.2 Φ⟩

/-- **`modelMap(Φ, σ)^*(Γ_Φ^*ω) = Γ_{Φ∘σ}^*ω`** on forms. -/
theorem formPullback_modelMap_modelRep (hU : S.HasUniformizers) (ω : S.CatAltForm k)
    (Φ : ι → S.Unif) (σ : κ → ι) :
    formPullback (S.modelMap Φ σ).isScSmoothMap_obj (S.modelRep hU ω Φ) =
      S.modelRep hU ω (Φ ∘ σ) :=
  MPolyfold.sigmaForm_ext _ fun j =>
    (formPullback_comp _ _ _).symm.trans ((formPullback_congr _
      (MPolyfold.isScSmoothMap_sigmaMk (fun i => (Φ i).1.P) (σ j)) (fun _ => rfl) _).trans
      ((formPullback_objMk_modelRep hU ω Φ (σ j)).trans
        (formPullback_objMk_modelRep hU ω (Φ ∘ σ) j).symm))

theorem epFormsInftyPullback_modelMap (hU : S.HasUniformizers) (ω : S.catForms hU k)
    (Φ : ι → S.Unif) (σ : κ → ι) :
    EP.epFormsInftyPullback (S.modelMap Φ σ) k (S.modelFormInfty hU ω Φ) =
      S.modelFormInfty hU ω (Φ ∘ σ) := by
  rw [modelFormInfty, EP.epFormsInftyPullback_of]
  exact congrArg _ (Subtype.ext (formPullback_modelMap_modelRep hU ω.1 Φ σ))

/-- `incl^*` maps `[Γ_Φ^*ω]` to `[Γ_Ψ^*ω]` for `Φ ∘ σ = Ψ`. -/
theorem formsPullback_incl_modelFormInfty (hU : S.HasUniformizers) (ω : S.catForms hU k)
    {Ψ : κ → S.Unif} {Φ : ι → S.Unif} {σ : κ → ι} (h : Φ ∘ σ = Ψ) :
    EPLoc.formsPullback (EPLoc.localizationFunctor.map (S.incl Ψ Φ σ h)) k
        (S.modelFormInfty hU ω Φ) =
      S.modelFormInfty hU ω Ψ := by
  subst h
  rw [incl_rfl, EPLoc.formsPullback_localizationFunctor_map]
  exact epFormsInftyPullback_modelMap hU ω Φ σ

/-- **`f^*[ω_{Ψ'}] = [ω_Ψ]`** (2021 p. 821, proof of Theorem 17.6.4) for the canonical generalized
isomorphism `f = f_{Ψ,Ψ'} : X_Ψ → X_{Ψ'}` of two covering families. -/
theorem formsPullback_comparison_modelFormInfty (hU : S.HasUniformizers) (ω : S.catForms hU k)
    (c c' : S.CoveringFamily) :
    EPLoc.formsPullback (S.comparison c c') k (S.modelFormInfty hU ω c'.Ψ) =
      S.modelFormInfty hU ω c.Ψ := by
  have e := S.comparison_comp_incl c c' (Sum.elim c.Ψ c'.Ψ) (σ := Sum.inl) (σ' := Sum.inr) rfl rfl
  exact (congrArg (EPLoc.formsPullback (S.comparison c c') k)
    (formsPullback_incl_modelFormInfty hU ω (Ψ := c'.Ψ) (Φ := Sum.elim c.Ψ c'.Ψ) (σ := Sum.inr)
      rfl).symm).trans
    ((LinearMap.congr_fun (EPLoc.formsPullback_comp (S.comparison c c')
      (EPLoc.localizationFunctor.map (S.incl c'.Ψ (Sum.elim c.Ψ c'.Ψ) Sum.inr rfl)) k).symm _).trans
    ((congrArg (fun f => EPLoc.formsPullback f k (S.modelFormInfty hU ω (Sum.elim c.Ψ c'.Ψ)))
      e).trans
      (formsPullback_incl_modelFormInfty hU ω (Ψ := c.Ψ) (σ := Sum.inl) rfl)))

end Model

/-! ### `Ω∞ᵏ(C)` and the de Rham complex -/

section DeRham

open EPLocalization CategoryTheory

theorem formsPullback_comparison_comp_apply (c c' c'' : S.CoveringFamily)
    (x : (S.modelEP c''.Ψ).epFormsInfty k) :
    EPLoc.formsPullback (S.comparison c c') k (EPLoc.formsPullback (S.comparison c' c'') k x) =
      EPLoc.formsPullback (S.comparison c c'') k x :=
  (LinearMap.congr_fun (EPLoc.formsPullback_comp (S.comparison c c') (S.comparison c' c'') k).symm
    x).trans (congrArg (fun f => EPLoc.formsPullback f k x) (S.comparison_comp c c' c''))

theorem formsPullback_comparison_self_apply (c : S.CoveringFamily)
    (x : (S.modelEP c.Ψ).epFormsInfty k) : EPLoc.formsPullback (S.comparison c c) k x = x :=
  (congrArg (fun f => EPLoc.formsPullback f k x) (S.comparison_self c)).trans
    (LinearMap.congr_fun (EPLoc.formsPullback_id _ k) x)

theorem epFormsInftyD_formsPullback_comparison (c c' : S.CoveringFamily)
    (x : (S.modelEP c'.Ψ).epFormsInfty k) :
    (S.modelEP c.Ψ).epFormsInftyD k (EPLoc.formsPullback (S.comparison c c') k x) =
      EPLoc.formsPullback (S.comparison c c') (k + 1) ((S.modelEP c'.Ψ).epFormsInftyD k x) :=
  LinearMap.congr_fun (EPLoc.theorem_11_2_1_two (S.comparison c c') k) x

variable (S) in
/-- **`Ω∞ᵏ(C)`** (2021 p. 820): the families `([ω_Ψ])_Ψ`, one class `[ω_Ψ] ∈ Ω∞ᵏ_ep(X_Ψ)` for every
covering family `Ψ`, with `f_{Ψ,Ψ'}^*[ω_{Ψ'}] = [ω_Ψ]` for the canonical generalized
isomorphisms; by `catFormsInftyEquiv` it is `Ω∞ᵏ_ep(X_Ψ)` for every single covering family. -/
def catFormsInfty (k : ℕ) :
    Submodule ℝ (∀ c : S.CoveringFamily, (S.modelEP c.Ψ).epFormsInfty k) where
  carrier := {ω | ∀ c c', EPLoc.formsPullback (S.comparison c c') k (ω c') = ω c}
  add_mem' {ω τ} hω hτ c c' := by
    simp only [Pi.add_apply, map_add, hω c c', hτ c c']
  zero_mem' c c' := by simp only [Pi.zero_apply, map_zero]
  smul_mem' r {ω} hω c c' := by
    simp only [Pi.smul_apply, map_smul, hω c c']

theorem formsPullback_comparison_catFormsInfty (ω : S.catFormsInfty k) (c c' : S.CoveringFamily) :
    EPLoc.formsPullback (S.comparison c c') k (ω.1 c') = ω.1 c :=
  ω.2 c c'

variable (S) in
/-- **`Ω∞ᵏ(C) ≅ Ω∞ᵏ_ep(X_Ψ)`** for a covering family `Ψ`, inverse `[ω] ↦ (f_{Ψ',Ψ}^*[ω])_{Ψ'}`. -/
def catFormsInftyEquiv (c₀ : S.CoveringFamily) (k : ℕ) :
    S.catFormsInfty k ≃ₗ[ℝ] (S.modelEP c₀.Ψ).epFormsInfty k where
  toFun ω := ω.1 c₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun η := ⟨fun c => EPLoc.formsPullback (S.comparison c c₀) k η, fun c c' =>
    formsPullback_comparison_comp_apply c c' c₀ η⟩
  left_inv ω := Subtype.ext (funext fun c => ω.2 c c₀)
  right_inv η := formsPullback_comparison_self_apply c₀ η

variable (S) in
/-- **`d : Ω∞ᵏ(C) → Ω∞ᵏ⁺¹(C)`** (2021 p. 820): `d[ω] = [Γ_*d(Γ^*ω)]`, i.e. `d` of each `[ω_Ψ]`;
compatible with the `f_{Ψ,Ψ'}^*` by Theorem 11.2.1 (2). -/
def catFormsInftyD (k : ℕ) : S.catFormsInfty k →ₗ[ℝ] S.catFormsInfty (k + 1) where
  toFun ω := ⟨fun c => (S.modelEP c.Ψ).epFormsInftyD k (ω.1 c), fun c c' =>
    (epFormsInftyD_formsPullback_comparison c c' (ω.1 c')).symm.trans
      (congrArg ((S.modelEP c.Ψ).epFormsInftyD k) (ω.2 c c'))⟩
  map_add' ω τ := Subtype.ext (funext fun c =>
    map_add ((S.modelEP c.Ψ).epFormsInftyD k) (ω.1 c) (τ.1 c))
  map_smul' r ω := Subtype.ext (funext fun c =>
    map_smul ((S.modelEP c.Ψ).epFormsInftyD k) r (ω.1 c))

theorem catFormsInftyD_apply (ω : S.catFormsInfty k) (c : S.CoveringFamily) :
    (S.catFormsInftyD k ω).1 c = (S.modelEP c.Ψ).epFormsInftyD k (ω.1 c) := rfl

/-- `d ∘ d = 0` on `Ω∞*(C)` ("since it holds for ep-groupoids", p. 820). -/
theorem catFormsInftyD_catFormsInftyD (ω : S.catFormsInfty k) :
    S.catFormsInftyD (k + 1) (S.catFormsInftyD k ω) = 0 :=
  Subtype.ext (funext fun _ => EP.epFormsInftyD_epFormsInftyD _ _ _)

/-- The equivalence `Ω∞*(C) ≅ Ω∞*_ep(X_Ψ)` intertwines the two `d`'s ("the definition
`d[ω] = [Γ_*d(Γ^*ω)]` is independent of the choices involved", p. 820). -/
theorem catFormsInftyEquiv_catFormsInftyD (c₀ : S.CoveringFamily) (ω : S.catFormsInfty k) :
    S.catFormsInftyEquiv c₀ (k + 1) (S.catFormsInftyD k ω) =
      (S.modelEP c₀.Ψ).epFormsInftyD k (S.catFormsInftyEquiv c₀ k ω) := rfl

variable (S) in
/-- **`Ωᵏ(C) → Ω∞ᵏ(C)`**, `ω ↦ [ω] = ([Γ_Ψ^*ω])_Ψ` (the first map of `Ωᵏ(C) → Ωᵏ(C¹) → ⋯`
followed by the passage to the limit). -/
def catFormsToInfty (hU : S.HasUniformizers) (k : ℕ) : S.catForms hU k →ₗ[ℝ] S.catFormsInfty k where
  toFun ω := ⟨fun c => S.modelFormInfty hU ω c.Ψ, fun c c' =>
    formsPullback_comparison_modelFormInfty hU ω c c'⟩
  map_add' ω τ := Subtype.ext (funext fun c => by
    change (S.modelEP c.Ψ).epFormsInftyOf k 0 _ = (S.modelEP c.Ψ).epFormsInftyOf k 0 _ +
      (S.modelEP c.Ψ).epFormsInftyOf k 0 _
    rw [← map_add]
    exact congrArg _ (Subtype.ext (modelRep_add hU ω.1 τ.1 c.Ψ)))
  map_smul' r ω := Subtype.ext (funext fun c => by
    change (S.modelEP c.Ψ).epFormsInftyOf k 0 _ = r • (S.modelEP c.Ψ).epFormsInftyOf k 0 _
    rw [← map_smul]
    exact congrArg _ (Subtype.ext (modelRep_smul hU r ω.1 c.Ψ)))

/-- **(17.88) on the models**: `d[Γ^*ω] = [d(Γ^*ω)]`, the class of `dω_Ψ` on level `1`. -/
theorem catFormsInftyD_catFormsToInfty (hU : S.HasUniformizers) (ω : S.catForms hU k)
    (c : S.CoveringFamily) :
    (S.catFormsInftyD k (S.catFormsToInfty hU k ω)).1 c =
      (S.modelEP c.Ψ).epFormsInftyOf (k + 1) 1
        ((S.modelEP c.Ψ).epFormsD k 0 ⟨S.modelRep hU ω.1 c.Ψ, S.modelRep_mem_epForms hU ω.2 c.Ψ⟩) :=
  EP.epFormsInftyD_of _ _ _ _

/-- **Definition 17.6.3** (2021 p. 820): `(Ω∞*(C), d)` is a complex, `d ∘ d = 0`, identified with
the de Rham complex `(Ω∞*_ep(X_Ψ), d)` of every sc-smooth model by `catFormsInftyEquiv`
(which commutes with `d`), and the identification is compatible with `f_{Ψ,Ψ'}^*`. -/
theorem definition_17_6_3 :
    (∀ (k : ℕ) (ω : S.catFormsInfty k), S.catFormsInftyD (k + 1) (S.catFormsInftyD k ω) = 0) ∧
      (∀ (c₀ : S.CoveringFamily) (k : ℕ) (ω : S.catFormsInfty k),
        S.catFormsInftyEquiv c₀ (k + 1) (S.catFormsInftyD k ω) =
          (S.modelEP c₀.Ψ).epFormsInftyD k (S.catFormsInftyEquiv c₀ k ω)) ∧
      ∀ (c c' : S.CoveringFamily) (k : ℕ) (ω : S.catFormsInfty k),
        EPLoc.formsPullback (S.comparison c c') k (S.catFormsInftyEquiv c' k ω) =
          S.catFormsInftyEquiv c k ω :=
  ⟨fun _ ω => catFormsInftyD_catFormsInftyD ω, fun c₀ _ ω => catFormsInftyEquiv_catFormsInftyD c₀ ω,
    fun c c' _ ω => ω.2 c c'⟩

end DeRham

end GCT.PolyfoldConstruction

end Polyfold
