import Polyfold.Chapter8.GapP2_B_EpForms
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
pp. 372–373: the forms `Ω*_{ep,∞}(X)` of an ep-groupoid inside the forms `Ω*_∞(X)` of its object
M-polyfold (§4.4), and **Definition 8.2.2** as a cochain complex (gap G.74).

# `Ω*_{ep,∞}(X) ⊆ Ω*_∞(X)` and the sc-de Rham complex

## The text, paraphrased

(p. 373) `d[ω] := [dω]`, "where `dω` is the exterior derivative of an sc-differential form on the
object M-polyfold"; (Definition 8.2.2) `(Ω*_{ep,∞}(X), d)` is the sc-de Rham complex.

## What is formalized (namespace `Polyfold.EP`)

* `objPolyfold A`: the object M-polyfold of the ep-groupoid, bundled; `objPolyfold_lift`: the
  object M-polyfold of the index lift `Xⁱ` is the lift `(Ob X)ⁱ` of Part I (2021 p. 37).
* `epFormsToObj A k i : Ωᵏ_ep(Xⁱ) → Ωᵏ((Ob X)ⁱ)` (injective), commuting with the directed
  systems and with `d`; **`epFormsInftyToObj A k : Ωᵏ_{ep,∞}(X) → Ωᵏ_∞(Ob X)`**, injective
  (`epFormsInftyToObj_injective`) and a chain map
  (`formsInftyD_comp_epFormsInftyToObj`): the complex of the ep-groupoid is a subcomplex of
  Part I's `(Ω*_∞(Ob X), d)`, and its `d` is the `d` of the object M-polyfold.
* **`epDeRhamComplex A`**: Definition 8.2.2 as a cochain complex of real vector spaces
  (Mathlib's `CochainComplex (ModuleCat ℝ) ℕ`), with `epDeRhamComplex_X`, `epDeRhamComplex_d`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u

namespace BundledMPolyfold

variable (k : ℕ)

/-- Transport of sc-forms along an equality of bundled M-polyfolds. -/
def castForms {B B' : BundledMPolyfold.{u}} (h : B = B') : B.P.scForms k ≃ₗ[ℝ] B'.P.scForms k := by
  subst h
  exact LinearEquiv.refl ℝ _

/-- The step `Ωᵏ(X) → Ωᵏ(X¹)` for a bundled M-polyfold. -/
def lowerStep (B : BundledMPolyfold.{u}) : B.P.scForms k →ₗ[ℝ] B.shift.P.scForms k :=
  LinearMap.codRestrict (B.shift.P.scForms k)
    ((MPolyfold.formLowerₗ B.P k).domRestrict (B.P.scForms k))
    fun ω => MPolyfold.formLower_mem_scForms ω.2

theorem castForms_lowerStep {B B' : BundledMPolyfold.{u}} (h : B = B') (ω : B.P.scForms k) :
    castForms k (congrArg BundledMPolyfold.shift h) (lowerStep k B ω) =
      lowerStep k B' (castForms k h ω) := by
  subst h
  rfl

theorem castForms_extD {B B' : BundledMPolyfold.{u}} (h : B = B') (ω : B.P.scForms k) :
    castForms (k + 1) (congrArg BundledMPolyfold.shift h) (MPolyfold.extDₗ B.P k ω) =
      MPolyfold.extDₗ B'.P k (castForms k h ω) := by
  subst h
  rfl

end BundledMPolyfold

namespace EP

variable (A : EP.{u}) (k : ℕ)

/-- The object M-polyfold of an ep-groupoid, bundled. -/
def objPolyfold : BundledMPolyfold.{u} := BundledMPolyfold.of A.X.PObj

/-- **The object M-polyfold of `Xⁱ` is the lift `(Ob X)ⁱ`** of the object M-polyfold. -/
theorem objPolyfold_lift : ∀ i : ℕ, (A.lift i).objPolyfold = A.objPolyfold.lift i
  | 0 => rfl
  | i + 1 => congrArg BundledMPolyfold.shift (objPolyfold_lift i)

/-- **The inclusion `Ωᵏ_ep(Xⁱ) → Ωᵏ((Ob X)ⁱ)`** into Part I's forms on the lifts of the object
M-polyfold. -/
def epFormsToObj (i : ℕ) : A.epForms k i →ₗ[ℝ] A.objPolyfold.forms k i :=
  (BundledMPolyfold.castForms k (A.objPolyfold_lift i)).toLinearMap ∘ₗ A.epFormsToForms k i

theorem epFormsToObj_injective (i : ℕ) : Injective (A.epFormsToObj k i) :=
  (BundledMPolyfold.castForms k (A.objPolyfold_lift i)).injective.comp
    (A.epFormsToForms_injective k i)

theorem epFormsToObj_epFormsStep (i : ℕ) (ω : A.epForms k i) :
    A.epFormsToObj k (i + 1) (A.epFormsStep k i ω) =
      A.objPolyfold.formsStep k i (A.epFormsToObj k i ω) :=
  BundledMPolyfold.castForms_lowerStep k (A.objPolyfold_lift i) (A.epFormsToForms k i ω)

theorem epFormsToObj_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : A.epForms k i) :
    A.epFormsToObj k j (A.epFormsMap k i j h ω) =
      A.objPolyfold.formsMap k i j h (A.epFormsToObj k i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self, BundledMPolyfold.formsMap_self]; rfl
  | succ j hij ih =>
    rw [epFormsMap_succ A k hij, LinearMap.comp_apply, epFormsToObj_epFormsStep, ih,
      BundledMPolyfold.formsMap_succ _ k hij, LinearMap.comp_apply]

theorem epFormsToObj_epFormsD (i : ℕ) (ω : A.epForms k i) :
    A.epFormsToObj (k + 1) (i + 1) (A.epFormsD k i ω) =
      A.objPolyfold.formsD k i (A.epFormsToObj k i ω) :=
  BundledMPolyfold.castForms_extD k (A.objPolyfold_lift i) (A.epFormsToForms k i ω)

/-- **`Ωᵏ_{ep,∞}(X) → Ωᵏ_∞(Ob X)`**: a form on the ep-groupoid as a form on the object
M-polyfold (Definition 4.4.2). -/
def epFormsInftyToObj : A.epFormsInfty k →ₗ[ℝ] A.objPolyfold.formsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms k i)) (A.epFormsMap k)
    (fun i => (A.objPolyfold.formsInftyOf k i).comp (A.epFormsToObj k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [epFormsToObj_epFormsMap, BundledMPolyfold.formsInftyOf_formsMap]

theorem epFormsInftyToObj_of (i : ℕ) (ω : A.epForms k i) :
    A.epFormsInftyToObj k (A.epFormsInftyOf k i ω) =
      A.objPolyfold.formsInftyOf k i (A.epFormsToObj k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- **2021 p. 373: `d` on `Ω*_{ep,∞}(X)` is the exterior derivative of the object M-polyfold**:
the inclusion `Ω*_{ep,∞}(X) → Ω*_∞(Ob X)` is a chain map. -/
theorem formsInftyD_comp_epFormsInftyToObj :
    (A.objPolyfold.formsInftyD k).comp (A.epFormsInftyToObj k) =
      (A.epFormsInftyToObj (k + 1)).comp (A.epFormsInftyD k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [epFormsInftyToObj_of, BundledMPolyfold.formsInftyD_of, epFormsInftyD_of,
    epFormsInftyToObj_of, epFormsToObj_epFormsD]

/-- **`Ωᵏ_{ep,∞}(X) → Ωᵏ_∞(Ob X)` is injective.** -/
theorem epFormsInftyToObj_injective : Injective (A.epFormsInftyToObj k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq k a
  rw [LinearMap.mem_ker, epFormsInftyToObj_of] at ha
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact ha
  have h0 : A.epFormsToObj k j (A.epFormsMap k i j hij ω) = 0 := by
    rw [epFormsToObj_epFormsMap]; exact hj
  have h1 : A.epFormsMap k i j hij ω = 0 :=
    A.epFormsToObj_injective k j (h0.trans (map_zero _).symm)
  rw [← A.epFormsInftyOf_epFormsMap k hij ω, h1, map_zero]

/-! ### Definition 8.2.2 as a cochain complex -/

open CategoryTheory in
/-- **2021 Definition 8.2.2 (2017: 8.3): the sc-de Rham complex `(Ω*_{ep,∞}(X), d)` of the
ep-groupoid `X`**, as a cochain complex of real vector spaces. -/
def epDeRhamComplex : CochainComplex (ModuleCat.{max u 1} ℝ) ℕ :=
  CochainComplex.of (fun k => ModuleCat.of ℝ (A.epFormsInfty k))
    (fun k => ModuleCat.ofHom (A.epFormsInftyD k)) fun k => by
      rw [← ModuleCat.ofHom_comp, A.epFormsInftyD_comp_epFormsInftyD k]
      rfl

theorem epDeRhamComplex_X : (A.epDeRhamComplex.X k : Type _) = A.epFormsInfty k := rfl

theorem epDeRhamComplex_d :
    A.epDeRhamComplex.d k (k + 1) = ModuleCat.ofHom (A.epFormsInftyD k) := by
  unfold epDeRhamComplex
  exact CochainComplex.of_d (fun k => ModuleCat.of ℝ (A.epFormsInfty k))
    (fun k => ModuleCat.ofHom (A.epFormsInftyD k)) k

end EP

end Polyfold
