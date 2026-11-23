import Polyfold.Chapter9.LocalFormsPush
import Polyfold.Chapter11.SubGroupoidModel

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# The forms of the restriction `X|U` with values on the tangent vectors of `X`

For a saturated open set `U` of an ep-groupoid `X` and a continuous cut-off `χ` on `X`, constant
on the orbits and with support in `U`, the classes of `Ωⁿ_{ep,∞}(X|U)` have the values
`χ(y) · a(α₁, …, αₙ)` on the tangent vectors of `X` over `y ∈ U` (and `0` off `U`).

* `EP.subRetract`, `EP.isScDiffeoOn_subRetract`: the inverse `U → X|U` of the inclusion, as an
  sc-diffeomorphism between the open sets `U ⊆ Ob X` and `Ob (X|U)`.
* `EP.subRetract_tangentMor`: it commutes with the tangent maps of the morphisms.
* **`EP.subEval`**: the evaluation `χ · a` of `Ωⁿ_{ep,∞}(X|U)` on `X` (`n ≥ 1`).
* `EP.epFormsInftyEval_epFormsInftyPullback`: `(F^*b)(α) = b(TF α)` for a functor `F` which is a
  local sc-diffeomorphism on objects.
* `EP.subEval_pullback`: where `χ = 1`, the restriction `η|U` of a class of `X` has the values of
  `η`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

open scoped Classical in
/-- **The inclusion of an open subset `A`, with its structure of a sub-M-polyfold, is an
sc-diffeomorphism onto `A`**, with inverse `x ↦ x` on `A`. -/
theorem isScDiffeoOn_val_subPolyfold_of_isOpen {A : Set X} (hA : P.IsSubMPolyfold A)
    (hAo : IsOpen A) [ParacompactSpace A] (a : A) :
    (subPolyfold hA).IsScDiffeoOn P (Subtype.val : A → X)
      (fun x => if h : x ∈ A then ⟨x, h⟩ else a) univ A :=
  { isScSmoothOn := subPolyfold_inclusion_isScSmooth hA
    isScSmoothOn_inv := isScSmoothOn_subPolyfold_of_val hA
      ((isScSmoothMap_id.mono hAo (subset_univ _)).congr fun x hx => by
        simp only [dif_pos (show x ∈ A from hx)]; rfl)
    mapsTo := fun b _ => b.2
    mapsTo_inv := fun _ _ => mem_univ _
    left_inv := fun b _ => by simp only [dif_pos b.2]
    right_inv := fun y hy => by simp only [dif_pos (show y ∈ A from hy)] }

end MPolyfold

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U)

open scoped Classical in
/-- The inverse `U → Ob (X|U)` of the inclusion, extended by a point `a` off `U`. -/
def subRetract (a : (A.sub hU).Obj) (x : A.Obj) : (A.sub hU).Obj :=
  if h : x ∈ U then (⟨x, h⟩ : U) else a

theorem subRetract_of_mem (a : (A.sub hU).Obj) {x : A.Obj} (h : x ∈ U) :
    A.subRetract hU a x = (⟨x, h⟩ : U) := dif_pos h

theorem subFunctor_obj_subRetract (a : (A.sub hU).Obj) {x : A.Obj} (h : x ∈ U) :
    (A.subFunctor hU).obj (A.subRetract hU a x) = x := by
  rw [A.subRetract_of_mem hU a h]; rfl

theorem subRetract_subFunctor_obj (a : (A.sub hU).Obj) (y : (A.sub hU).Obj) :
    A.subRetract hU a ((A.subFunctor hU).obj y) = y :=
  A.subRetract_of_mem hU a (A.subFunctor_obj_mem hU y)

/-- **The inverse of the inclusion `X|U → X` is an sc-diffeomorphism from the open set `U` of
the object space of `X` onto the object space of `X|U`.** -/
theorem isScDiffeoOn_subRetract (hUo : IsOpen U) (a : (A.sub hU).Obj) :
    A.X.PObj.IsScDiffeoOn (A.sub hU).X.PObj (A.subRetract hU a) (A.subFunctor hU).obj U univ :=
  haveI : ParacompactSpace U := A.X.PObj.paracompactSpace_subtype U
  (MPolyfold.isScDiffeoOn_val_subPolyfold_of_isOpen hU.isSubMPolyfold hUo a).symm

/-- `T(X|U → X)` is the tangent map of the inclusion as an sc-diffeomorphism. -/
theorem subFunctor_tangent_obj (hUo : IsOpen U) (a : (A.sub hU).Obj)
    (c : (A.sub hU).X.PObj.TangentSpace) :
    (A.subFunctor hU).tangent.obj c =
      tangentMapOn (A.isScDiffeoOn_subRetract hU hUo a).isScSmoothOn_inv c :=
  EpFunctor.tangent_obj_eq_tangentMapOn (A.isScDiffeoOn_subRetract hU hUo a).symm (mem_univ _)

/-- **The inverse of the inclusion commutes with the tangent maps of the morphisms**: a morphism
`ψ` of `X` starting in `U` is a morphism `ψ'` of `X|U`, and `Tψ' ∘ Tr = Tr ∘ Tψ` on
`T_{s(ψ)}X`. -/
theorem subRetract_tangentMor (hUo : IsOpen U) (a : (A.sub hU).Obj) (ψ : A.Mor)
    (hψ : A.X.src ψ ∈ U) :
    ∃ ψ' : (A.sub hU).Mor, (A.sub hU).X.src ψ' = A.subRetract hU a (A.X.src ψ) ∧
      ∀ v : A.X.PObj.TangentSpace, A.X.PObj.levelVal 1 (A.X.PObj.tangentProj v) = A.X.src ψ →
        tangentMapOn (A.isScDiffeoOn_subRetract hU hUo a).isScSmoothOn (A.X.tangentMor ψ v) =
          (A.sub hU).X.tangentMor ψ'
            (tangentMapOn (A.isScDiffeoOn_subRetract hU hUo a).isScSmoothOn v) := by
  have ht : A.X.tgt ψ ∈ U := A.X.isSaturated_iff.1 hU.isSaturated ψ hψ
  let ψ' : (A.sub hU).Mor := (⟨ψ, hψ, ht⟩ : A.X.morOn U)
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  have hsrc : (A.sub hU).X.src ψ' = A.subRetract hU a (A.X.src ψ) := by
    rw [A.subRetract_of_mem hU a hψ]; rfl
  refine ⟨ψ', hsrc, fun v hv => ?_⟩
  have hvU : v ∈ A.X.PObj.tangentPreimage U := by change _ ∈ U; rw [hv]; exact hψ
  have hb : (A.sub hU).X.PObj.levelVal 1 ((A.sub hU).X.PObj.tangentProj
      (tangentMapOn hd.isScSmoothOn v)) = (A.sub hU).X.src ψ' := by
    rw [levelVal_tangentProj_tangentMapOn hd.isScSmoothOn hvU, hv, hsrc]
  have hψ'1 : ψ' ∈ (A.sub hU).X.PMor.levelSet 1 :=
    ((A.sub hU).X.mem_levelSet_src_iff ψ' 1).1 (by
      rw [← hb]; exact (A.sub hU).X.PObj.levelVal_mem _)
  have h1 := (A.subFunctor hU).tangentMor_mor hψ'1 hb
  rw [A.subFunctor_tangent_obj hU hUo a, A.subFunctor_tangent_obj hU hUo a,
    hd.tangent.left_inv v hvU] at h1
  have hmor : (A.subFunctor hU).mor ψ' = ψ := rfl
  rw [hmor] at h1
  rw [h1]
  exact hd.tangent.right_inv _ (mem_univ _)

variable {n : ℕ} {χ : A.Obj → ℝ}

/-- **The values `χ · a` of the classes `a ∈ Ωⁿ_{ep,∞}(X|U)` on the tangent vectors of `X`**
(Remark 9.5.19, 2021 p. 451), `n ≥ 1`, for a saturated open `U` and a continuous cut-off `χ`
constant on the orbits with support in `U`. -/
def subEval (hUo : IsOpen U) (a : (A.sub hU).Obj) (hn : 0 < n) (hχ : Continuous χ)
    (hχU : tsupport χ ⊆ U) (hχinv : ∀ ψ : A.Mor, χ (A.X.src ψ) = χ (A.X.tgt ψ)) :
    A.X.FormEval n ((A.sub hU).epFormsInfty n) :=
  ((A.sub hU).epFormsInftyEval n).pushCut hn (A.isScDiffeoOn_subRetract hU hUo a) hχ hχU hχinv
    fun ψ hψ => A.subRetract_tangentMor hU hUo a ψ hψ

variable (hUo : IsOpen U) (a : (A.sub hU).Obj) (hn : 0 < n) (hχ : Continuous χ)
  (hχU : tsupport χ ⊆ U) (hχinv : ∀ ψ : A.Mor, χ (A.X.src ψ) = χ (A.X.tgt ψ))

theorem subEval_ev (ω : (A.sub hU).epFormsInfty n) {α : Fin n → A.X.PObj.TangentSpace}
    {N : Set A.Obj} {y : A.Obj} (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    (A.subEval hU hUo a hn hχ hχU hχinv).ev ω α =
      χ y * ((A.sub hU).epFormsInftyEval n).ev ω
        (fun i => tangentMapOn (A.isScDiffeoOn_subRetract hU hUo a).isScSmoothOn (α i)) :=
  FormEval.pushCut_ev _ hn _ hχ hχU hχinv _ ω hα

/-- Where `χ = 1`, the classes of `X|U` have their own values. -/
theorem evCompatOn_subEval {N : Set A.Obj} (h1 : ∀ y ∈ N, χ y = 1)
    (ω : (A.sub hU).epFormsInfty n) :
    FormEval.EvCompatOn (A.subEval hU hUo a hn hχ hχU hχinv) ((A.sub hU).epFormsInftyEval n)
      (A.isScDiffeoOn_subRetract hU hUo a) N ω ω :=
  FormEval.evCompatOn_pushCut _ hn _ hχ hχU hχinv _ h1 ω

/-- Where `χ = 1`, the classes of `X|U` have their own values (the other direction). -/
theorem evCompatOn_symm_subEval {N' : Set (A.sub hU).Obj}
    (h1 : ∀ z ∈ N', χ ((A.subFunctor hU).obj z) = 1) (ω : (A.sub hU).epFormsInfty n) :
    FormEval.EvCompatOn ((A.sub hU).epFormsInftyEval n) (A.subEval hU hUo a hn hχ hχU hχinv)
      (A.isScDiffeoOn_subRetract hU hUo a).symm N' ω ω :=
  FormEval.evCompatOn_symm_pushCut _ hn _ hχ hχU hχinv _ (subset_univ _) h1 ω

end EP

namespace EP

open MPolyfold EpGroupoid

/-- **`(F^*b)(α) = b(TF ∘ α)`** on the tangent spaces of the smooth finite-dimensional
submanifolds, for the classes of `Ωⁿ_{ep,∞}` and a functor `F` which is a local
sc-diffeomorphism on objects (as `epFormsInftyEval_isPullback`, for a functor which need not be
an equivalence). -/
theorem epFormsInftyEval_epFormsInftyPullback {A B : EP.{u}} {n : ℕ} {F : EpFunctor A.X B.X}
    (hF : A.X.PObj.IsLocalScDiffeo B.X.PObj F.obj) (b : B.epFormsInfty n)
    {α : Fin n → A.X.PObj.TangentSpace} (hα : MPolyfold.IsSubTuple A.X.PObj α) :
    (A.epFormsInftyEval n).ev (epFormsInftyPullback F n b) α =
      (B.epFormsInftyEval n).ev b (fun j => F.tangent.obj (α j)) := by
  obtain ⟨i, ω, rfl⟩ := B.exists_epFormsInftyOf_eq n b
  rw [epFormsInftyPullback_of, A.epFormsInftyEval_of, B.epFormsInftyEval_of]
  exact epFormsLevelEval_epFormsPullback hF i ω hα

variable (A : EP.{u}) {U : Set A.Obj} (hU : A.X.IsEpSubgroupoid U) {n : ℕ} {χ : A.Obj → ℝ}
  (hUo : IsOpen U) (a : (A.sub hU).Obj) (hn : 0 < n) (hχ : Continuous χ)
  (hχU : tsupport χ ⊆ U) (hχinv : ∀ ψ : A.Mor, χ (A.X.src ψ) = χ (A.X.tgt ψ))

/-- **Where `χ = 1`, the restriction `η|U` of a class `η ∈ Ωⁿ_{ep,∞}(X)` has the values of
`η`.** -/
theorem subEval_pullback (η : A.epFormsInfty n) {N : Set A.Obj}
    (hN : A.X.PObj.IsSmoothSubmanifold N) {y : A.Obj} (hy : y ∈ N) (h1 : χ y = 1)
    (α : Fin n → A.X.PObj.TangentSpace) (hα : ∀ i, α i ∈ A.X.PObj.submanifoldTangent N y) :
    (A.subEval hU hUo a hn hχ hχU hχinv).ev (epFormsInftyPullback (A.subFunctor hU) n η) α =
      (A.epFormsInftyEval n).ev η α := by
  have hd := A.isScDiffeoOn_subRetract hU hUo a
  have hyU : y ∈ U := hχU (subset_tsupport _ (by
    change χ y ≠ 0; rw [h1]; exact one_ne_zero))
  rw [A.subEval_ev hU hUo a hn hχ hχU hχinv _ hα, h1, one_mul,
    epFormsInftyEval_epFormsInftyPullback (A.isLocalScDiffeo_subFunctor_obj hU hUo) η
      ⟨A.subRetract hU a '' (N ∩ U), A.subRetract hU a y,
        (hN.inter_isOpen hUo).image_of_isScDiffeoOn hd inter_subset_right, ⟨y, ⟨hy, hyU⟩, rfl⟩,
        fun i => tangentMapOn_mem_submanifoldTangent_image hd hN hyU (hα i)⟩]
  congr 1
  funext i
  rw [A.subFunctor_tangent_obj hU hUo a]
  exact hd.tangent.left_inv _ (by
    change _ ∈ U; rw [levelVal_tangentProj_of_mem (hα i)]; exact hyU)

end EP

end Polyfold
