import Polyfold.Chapter11.SubGroupoidModel
import Polyfold.Chapter8.EpPoincare
import Polyfold.Chapter7.NaturalRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
pp. 373–374: **Proposition 8.2.3** (2017: Proposition 8.1), the Poincaré lemma for
sc-differential forms on ep-groupoids (gap G.87).  Numbers and pages are the 2021 text's.

# The Poincaré lemma for sc-differential forms on ep-groupoids

## The text, paraphrased

(Proposition 8.2.3) For an ep-groupoid `X` and an object `x` there are saturated open
neighbourhoods `V ⊆ U` of `x` such that for every closed `[ω] ∈ Ωᵏ_{ep,∞}(U)`, `k ≥ 1`, there
is `[σ] ∈ Ωᵏ⁻¹_{ep,∞}(V)` with `d[σ] = [ω]` on `V`.  Proof: Lemma 4.4.8 for the object
M-polyfold gives a primitive `τ` on a neighbourhood invariant under the natural `G_x`-action;
its average `τ'` over `G_x` is invariant with `dτ' = ω`, and `τ'` extends to the saturation by
`σ(y) = ψ^*τ'(x')` for a morphism `ψ : x' → y`.

## What is formalized

* **`EP.proposition_8_2_3`**: the statement, with `X|U`, `X|V` the restrictions of the
  ep-groupoid to the saturated open sets (`EP.sub`, Proposition 7.1.22), `Ω*_{ep,∞}` of
  Definition 8.2.1 and the restriction `Ω*_{ep,∞}(X|U) → Ω*_{ep,∞}(X|V)` the pull-back by the
  inclusion functor `EP.subIncl`.
* **`EP.proposition_8_2_3_of_isOpen`**: the same for every saturated open neighbourhood `U` of
  `x` given in advance (the proof takes `V ⊆ U`); the text's statement is the case `U = X`.
  A saturated open set is given as an open `U` with `hU : IsEpSubgroupoid U` (Definition 7.1.21:
  a saturated sub-M-polyfold; for open sets this is saturatedness,
  `EpGroupoid.isEpSubgroupoid_of_isOpen`).
* The bridge between the forms of an ep-groupoid and Part I's forms of its object M-polyfold:
  `EP.epFormsInftyToObj_surjective_of_src_eq_tgt` (for an ep-groupoid with `s = t`, e.g. an
  M-polyfold with only the unit morphisms, every form of the object M-polyfold is a form of the
  ep-groupoid) and `EP.epFormsInftyToObj_epFormsInftyPullback` (the inclusion
  `Ω*_{ep,∞}(X) → Ω*_∞(Ob X)` commutes with the pull-backs by sc-smooth functors).

## The proof

As in the text: for `x ∈ U`, Lemma 4.4.8 for the object M-polyfold of `X|U`
(`EP.proposition_8_2_3_object`) gives an open `V₀ ∋ x`; a natural representation of `G_x` on
`U(x) ⊆ V₀` (Theorem 7.1.13) gives the translation groupoid `G_x ⋉ U(x)`; the primitive on
`U(x)` is averaged over `G_x` (`NaturalRep.exists_primitive_translation`); the average is
pushed forward along the equivalence `G_x ⋉ U(x) → X|π⁻¹(π(U(x)))`
(`EP.isEquivalence_modelFunctor`, `EP.exists_primitive_of_equivalence`), which is the text's
`σ(y) = ψ^*τ'(x')` by Definition 11.2.3.  `V = π⁻¹(π(U(x)))`.

No hypothesis is added.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u

namespace BundledMPolyfold

variable {k : ℕ}

/-- The pull-back of an sc-form by an `ScMap`, as an sc-form. -/
def pullScForm {A B : BundledMPolyfold.{u}} (g : ScMap A.P B.P) (ω : B.P.scForms k) :
    A.P.scForms k :=
  ⟨MPolyfold.formPullback g.isScSmoothMap ω.1,
    MPolyfold.formPullback_mem_scForms g.isScSmoothMap ω.2⟩

/-- Transport along equalities of bundled M-polyfolds commutes with the pull-back. -/
theorem castForms_pullScForm {A A' B B' : BundledMPolyfold.{u}} (hA : A = A') (hB : B = B')
    (g : ScMap A.P B.P) (g' : ScMap A'.P B'.P) (hg : HEq g g') (ω : B.P.scForms k) :
    castForms k hA (pullScForm g ω) = pullScForm g' (castForms k hB ω) := by
  subst hA
  subst hB
  cases eq_of_heq hg
  rfl

theorem heq_scMap_shift {A A' B B' : BundledMPolyfold.{u}} (hA : A = A') (hB : B = B')
    (g : ScMap A.P B.P) (g' : ScMap A'.P B'.P) (hg : HEq g g') : HEq g.shift g'.shift := by
  subst hA
  subst hB
  cases eq_of_heq hg
  rfl

end BundledMPolyfold

namespace EP

variable {A B : EP.{u}}

/-! ### The inclusion `Ω*_{ep,∞}(X) → Ω*_∞(Ob X)` and pull-backs -/

/-- The object map of an sc-smooth functor, as an `ScMap` of the object M-polyfolds. -/
def objScMap (F : EpFunctor A.X B.X) : ScMap A.objPolyfold.P B.objPolyfold.P :=
  ⟨F.obj, F.isScSmoothMap_obj⟩

/-- The object map of `Fⁱ` is the `i`-th index raise of the object map of `F`. -/
theorem heq_objScMap_liftFunctor (F : EpFunctor A.X B.X) :
    ∀ i : ℕ, HEq (objScMap (liftFunctor F i)) (A.objPolyfold.liftMap (objScMap F) i)
  | 0 => HEq.rfl
  | i + 1 => BundledMPolyfold.heq_scMap_shift (A.objPolyfold_lift i) (B.objPolyfold_lift i)
      (objScMap (liftFunctor F i)) _ (heq_objScMap_liftFunctor F i)

theorem epFormsToObj_epFormsPullback (F : EpFunctor A.X B.X) (k i : ℕ) (ω : B.epForms k i) :
    A.epFormsToObj k i (epFormsPullback F k i ω) =
      BundledMPolyfold.formsPullback (objScMap F) k i (B.epFormsToObj k i ω) := by
  have h := BundledMPolyfold.castForms_pullScForm (k := k) (A.objPolyfold_lift i)
    (B.objPolyfold_lift i) (objScMap (liftFunctor F i)) _ (heq_objScMap_liftFunctor F i)
    (B.epFormsToForms k i ω)
  have e1 : A.epFormsToObj k i (epFormsPullback F k i ω) =
      BundledMPolyfold.castForms k (A.objPolyfold_lift i)
        (BundledMPolyfold.pullScForm (objScMap (liftFunctor F i)) (B.epFormsToForms k i ω)) :=
    rfl
  have e2 : BundledMPolyfold.formsPullback (objScMap F) k i (B.epFormsToObj k i ω) =
      BundledMPolyfold.pullScForm (A.objPolyfold.liftMap (objScMap F) i)
        (BundledMPolyfold.castForms k (B.objPolyfold_lift i) (B.epFormsToForms k i ω)) := rfl
  exact e1.trans (h.trans e2.symm)

/-- **The inclusion `Ω*_{ep,∞}(X) → Ω*_∞(Ob X)` commutes with the pull-backs** by sc-smooth
functors. -/
theorem epFormsInftyToObj_epFormsInftyPullback (F : EpFunctor A.X B.X) (k : ℕ)
    (b : B.epFormsInfty k) :
    A.epFormsInftyToObj k (epFormsInftyPullback F k b) =
      BundledMPolyfold.formsInftyPullback (objScMap F) k (B.epFormsInftyToObj k b) := by
  obtain ⟨i, ω, rfl⟩ := B.exists_epFormsInftyOf_eq k b
  exact ((congrArg (A.epFormsInftyToObj k) (epFormsInftyPullback_of F k i ω)).trans
    ((A.epFormsInftyToObj_of k i _).trans
      (congrArg (A.objPolyfold.formsInftyOf k i) (epFormsToObj_epFormsPullback F k i ω)))).trans
    ((BundledMPolyfold.formsInftyPullback_of (objScMap F) k i _).symm.trans
      (congrArg (BundledMPolyfold.formsInftyPullback (objScMap F) k)
        (B.epFormsInftyToObj_of k i ω).symm))

/-! ### Ep-groupoids with `s = t` -/

theorem src_eq_tgt_lift (h : ∀ φ : A.Mor, A.X.src φ = A.X.tgt φ) :
    ∀ (i : ℕ) (φ : (A.lift i).Mor), (A.lift i).X.src φ = (A.lift i).X.tgt φ
  | 0, φ => h φ
  | i + 1, φ => MPolyfold.level_ext
      (src_eq_tgt_lift h i ((A.lift i).X.PMor.levelVal 1 φ))

/-- In an ep-groupoid with `s = t` every sc-form of the object M-polyfold is compatible with
the morphisms. -/
theorem epFormsToObj_surjective_of_src_eq_tgt (h : ∀ φ : A.Mor, A.X.src φ = A.X.tgt φ)
    (k i : ℕ) : Surjective (A.epFormsToObj k i) := fun ξ => by
  set ξ' := (BundledMPolyfold.castForms k (A.objPolyfold_lift i)).symm ξ with hξ'
  have hmem : ξ'.1 ∈ (A.lift i).X.epForms k :=
    ⟨ξ'.2, (A.lift i).X.isMorCompatible_iff_formPullback.2
      (formPullback_congr (A.lift i).X.isScSmoothMap_src (A.lift i).X.isScSmoothMap_tgt
        (src_eq_tgt_lift h i) ξ'.1)⟩
  refine ⟨⟨ξ'.1, hmem⟩, ?_⟩
  have e : A.epFormsToForms k i ⟨ξ'.1, hmem⟩ = ξ' := Subtype.ext rfl
  exact (congrArg (BundledMPolyfold.castForms k (A.objPolyfold_lift i)) e).trans
    (LinearEquiv.apply_symm_apply _ ξ)

/-- **For an ep-groupoid with `s = t` (an M-polyfold with only the unit morphisms), every
element of `Ω*_∞(Ob X)` is an element of `Ω*_{ep,∞}(X)`.** -/
theorem epFormsInftyToObj_surjective_of_src_eq_tgt (h : ∀ φ : A.Mor, A.X.src φ = A.X.tgt φ)
    (k : ℕ) : Surjective (A.epFormsInftyToObj k) := fun b => by
  obtain ⟨i, ξ, rfl⟩ := Module.DirectLimit.exists_of b
  obtain ⟨ω, rfl⟩ := epFormsToObj_surjective_of_src_eq_tgt h k i ξ
  exact ⟨A.epFormsInftyOf k i ω, A.epFormsInftyToObj_of k i ω⟩

/-! ### Proposition 8.2.3 -/

open scoped EpGroupoid.NaturalRep in
/-- The primitive on `U(x)` (step 1 of the proof of Proposition 8.2.3): for a natural
representation `R` of `G_x` on `U(x) ⊆ V₀` in an ep-groupoid `Z`, and a form `a` of `Z` whose
image in `Ω_∞(Ob Z)` has a primitive `b₀` on `V₀`, the pull-back of `a` to `U(x)` (as an
ep-groupoid with only the unit morphisms) has a primitive. -/
theorem exists_primitive_units {Z : EP.{u}} {xZ : Z.Obj} (R : Z.X.NaturalRep xZ)
    {V₀ : Set Z.objPolyfold.carrier} (hV₀ : IsOpen V₀) (hxV₀ : xZ ∈ V₀) (hRV₀ : R.U ⊆ V₀)
    (k : ℕ) (a : Z.epFormsInfty (k + 1))
    (b₀ : (Z.objPolyfold.openSub hV₀ ⟨xZ, hxV₀⟩).formsInfty k)
    (hb₀ : (Z.objPolyfold.openSub hV₀ ⟨xZ, hxV₀⟩).formsInftyD k b₀ =
      Z.objPolyfold.formsInftyResOpen (k + 1) hV₀ ⟨xZ, hxV₀⟩ (Z.epFormsInftyToObj (k + 1) a)) :
    ∃ β : R.unitsEP.epFormsInfty k, R.unitsEP.epFormsInftyD k β =
      epFormsInftyPullback (R.epFunctor.comp R.unitsFunctor) (k + 1) a := by
  have hne : R.U.Nonempty := ⟨xZ, R.mem_U⟩
  -- the restriction of `b₀` to `U(x)`, a form of the M-polyfold `U(x)`
  have hW : R.unitsEP.objPolyfold = Z.objPolyfold.openSub R.isOpen_U hne := rfl
  obtain ⟨β, hβ⟩ := epFormsInftyToObj_surjective_of_src_eq_tgt (A := R.unitsEP) (fun _ => rfl) k
    (Z.objPolyfold.formsInftyResOpenOpen k hV₀ ⟨xZ, hxV₀⟩ R.isOpen_U hne hRV₀ b₀)
  refine ⟨β, R.unitsEP.epFormsInftyToObj_injective (k + 1) ?_⟩
  have e1 : R.unitsEP.epFormsInftyToObj (k + 1) (R.unitsEP.epFormsInftyD k β) =
      R.unitsEP.objPolyfold.formsInftyD k (R.unitsEP.epFormsInftyToObj k β) :=
    (LinearMap.congr_fun (R.unitsEP.formsInftyD_comp_epFormsInftyToObj k) β).symm
  have e2 : (Z.objPolyfold.openSub R.isOpen_U hne).formsInftyD k
      (Z.objPolyfold.formsInftyResOpenOpen k hV₀ ⟨xZ, hxV₀⟩ R.isOpen_U hne hRV₀ b₀) =
      Z.objPolyfold.formsInftyResOpen (k + 1) R.isOpen_U hne (Z.epFormsInftyToObj (k + 1) a) :=
    (Z.objPolyfold.formsInftyD_formsInftyResOpenOpen k hV₀ ⟨xZ, hxV₀⟩ R.isOpen_U hne hRV₀
      b₀).trans ((congrArg (Z.objPolyfold.formsInftyResOpenOpen (k + 1) hV₀ ⟨xZ, hxV₀⟩
        R.isOpen_U hne hRV₀) hb₀).trans
        (Z.objPolyfold.formsInftyResOpenOpen_comp (k + 1) hV₀ ⟨xZ, hxV₀⟩ R.isOpen_U hne hRV₀ _))
  have e3 : R.unitsEP.epFormsInftyToObj (k + 1)
      (epFormsInftyPullback (R.epFunctor.comp R.unitsFunctor) (k + 1) a) =
      Z.objPolyfold.formsInftyResOpen (k + 1) R.isOpen_U hne (Z.epFormsInftyToObj (k + 1) a) :=
    epFormsInftyToObj_epFormsInftyPullback (A := R.unitsEP)
      (R.epFunctor.comp R.unitsFunctor) (k + 1) a
  exact (e1.trans ((congrArg (R.unitsEP.objPolyfold.formsInftyD k) hβ).trans e2)).trans e3.symm

open scoped EpGroupoid.NaturalRep in
/-- Steps 1 and 2 of the proof of Proposition 8.2.3: under the hypotheses of
`exists_primitive_units`, the pull-back of `a` to `G_x ⋉ U(x)` is exact. -/
theorem exists_primitive_translation_of_object {Z : EP.{u}} {xZ : Z.Obj}
    (R : Z.X.NaturalRep xZ) {V₀ : Set Z.objPolyfold.carrier} (hV₀ : IsOpen V₀) (hxV₀ : xZ ∈ V₀)
    (hRV₀ : R.U ⊆ V₀) (k : ℕ) (a : Z.epFormsInfty (k + 1))
    (b₀ : (Z.objPolyfold.openSub hV₀ ⟨xZ, hxV₀⟩).formsInfty k)
    (hb₀ : (Z.objPolyfold.openSub hV₀ ⟨xZ, hxV₀⟩).formsInftyD k b₀ =
      Z.objPolyfold.formsInftyResOpen (k + 1) hV₀ ⟨xZ, hxV₀⟩ (Z.epFormsInftyToObj (k + 1) a)) :
    ∃ τ : R.translationEP.epFormsInfty k, R.translationEP.epFormsInftyD k τ =
      epFormsInftyPullback (A := R.translationEP) R.epFunctor (k + 1) a := by
  obtain ⟨β, hβ⟩ := exists_primitive_units R hV₀ hxV₀ hRV₀ k a b₀ hb₀
  exact R.exists_primitive_translation k
    (epFormsInftyPullback (A := R.translationEP) R.epFunctor (k + 1) a) β
    (hβ.trans (LinearMap.congr_fun
      (epFormsInftyPullback_comp (A := R.unitsEP) (B := R.translationEP) R.unitsFunctor (k + 1)
        R.epFunctor) a))

open scoped EpGroupoid.NaturalRep in
/-- **2021 Proposition 8.2.3, p. 373 (2017: Proposition 8.1), with `U` given**: for every
saturated open neighbourhood `U` of an object `x` of the ep-groupoid `X` there is a saturated
open neighbourhood `V ⊆ U` of `x` such that every closed `a ∈ Ωᵏ⁺¹_{ep,∞}(X|U)` is `db` on
`V` for some `b ∈ Ωᵏ_{ep,∞}(X|V)`.  (`IsEpSubgroupoid` of an open set is: saturated,
`EpGroupoid.isEpSubgroupoid_of_isOpen`.) -/
theorem proposition_8_2_3_of_isOpen (A : EP.{u}) {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U)
    (hUo : IsOpen U) {x : A.Obj} (hx : x ∈ U) :
    ∃ (V : Set A.Obj) (hV : A.X.IsEpSubgroupoid V) (hVU : V ⊆ U), IsOpen V ∧ x ∈ V ∧
      ∀ (k : ℕ) (a : (A.sub hU).epFormsInfty (k + 1)),
        (A.sub hU).epFormsInftyD (k + 1) a = 0 →
        ∃ b : (A.sub hV).epFormsInfty k,
          (A.sub hV).epFormsInftyD k b = epFormsInftyPullback (A.subIncl hV hU hVU) (k + 1) a := by
  obtain ⟨V₀, hV₀, hxV₀, hP⟩ := (A.sub hU).proposition_8_2_3_object (show U from ⟨x, hx⟩)
  obtain ⟨R, hRV₀⟩ := (A.sub hU).X.theorem_7_1_13 (show U from ⟨x, hx⟩) hV₀ hxV₀
  refine ⟨modelSet hU R, isEpSubgroupoid_modelSet hU R hUo, modelSet_subset hU R,
    isOpen_modelSet hU R hUo, mem_modelSet hU R ⟨_, R.mem_U⟩, fun k a ha => ?_⟩
  have h1 := hP k a ha
  obtain ⟨b₀, hb₀⟩ := h1
  have h2 := exists_primitive_translation_of_object R hV₀ hxV₀ hRV₀ k a b₀ hb₀
  obtain ⟨τ, hτ⟩ := h2
  -- the push-forward to the saturation
  have hE := isEquivalence_modelFunctor hU R hUo
  have hfac : epFormsInftyPullback (A := R.translationEP) R.epFunctor (k + 1) a =
      epFormsInftyPullback (modelFunctor hU R hUo) (k + 1)
        (epFormsInftyPullback (A.subIncl (isEpSubgroupoid_modelSet hU R hUo) hU
          (modelSet_subset hU R)) (k + 1) a) :=
    (congrArg (fun F => epFormsInftyPullback F (k + 1) a)
      (subIncl_comp_modelFunctor hU R hUo).symm).trans
      (LinearMap.congr_fun (epFormsInftyPullback_comp (modelFunctor hU R hUo) (k + 1)
        (A.subIncl (isEpSubgroupoid_modelSet hU R hUo) hU (modelSet_subset hU R))) a)
  exact ⟨epFormsInftyPush hE k τ, exists_primitive_of_equivalence hE k _ τ (hτ.trans hfac)⟩

/-- **2021 Proposition 8.2.3, p. 373 (2017: Proposition 8.1), the Poincaré lemma**: for an
ep-groupoid `X` and an object `x` there are saturated open neighbourhoods `V ⊆ U` of `x` such
that for every closed `a ∈ Ωᵏ⁺¹_{ep,∞}(X|U)` (the text's `[ω] ∈ Ωᵏ_{ep,∞}(U)`, `k ≥ 1`) there is
`b ∈ Ωᵏ_{ep,∞}(X|V)` with `db = a` on `V`.  (`hU`, `hV` say that `U`, `V` are saturated; they
give the restrictions `X|U = A.sub hU`, `X|V = A.sub hV` of Proposition 7.1.22.) -/
theorem proposition_8_2_3 (A : EP.{u}) (x : A.Obj) :
    ∃ (U V : Set A.Obj) (hU : A.X.IsEpSubgroupoid U) (hV : A.X.IsEpSubgroupoid V) (hVU : V ⊆ U),
      IsOpen U ∧ A.X.IsSaturated U ∧ IsOpen V ∧ A.X.IsSaturated V ∧ x ∈ V ∧
      ∀ (k : ℕ) (a : (A.sub hU).epFormsInfty (k + 1)),
        (A.sub hU).epFormsInftyD (k + 1) a = 0 →
        ∃ b : (A.sub hV).epFormsInfty k,
          (A.sub hV).epFormsInftyD k b = epFormsInftyPullback (A.subIncl hV hU hVU) (k + 1) a := by
  obtain ⟨V, hV, hVU, hVo, hxV, h⟩ :=
    A.proposition_8_2_3_of_isOpen A.X.isEpSubgroupoid_univ isOpen_univ (mem_univ x)
  exact ⟨univ, V, A.X.isEpSubgroupoid_univ, hV, hVU, isOpen_univ, A.X.isSaturated_univ, hVo,
    hV.isSaturated, hxV, h⟩

end EP

end Polyfold
