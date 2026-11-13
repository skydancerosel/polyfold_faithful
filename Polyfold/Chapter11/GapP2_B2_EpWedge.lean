import Polyfold.Chapter8.GapP2_B_EpFormsObj
import Polyfold.Chapter4.ScFormsWedge2021b

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2, p. 372
(Definitions 8.2.1, 8.2.2) with Part I's §4.4 (the wedge product of sc-differential forms).
Numbers and pages are the 2021 text's.

# The wedge product on `Ω*_{ep,∞}(X)`

## What is formalized

Part I's `(Ω*_∞(Ob X), ∧, d)` is a differential graded algebra (`formsInftyWedge`,
`formsInftyGAlgebra`, `formsInftyGradedD_of_mul_of`), and `Ω*_{ep,∞}(X) → Ω*_∞(Ob X)`
(`EP.epFormsInftyToObj`) is an injective chain map (Chapter 8).  Here:
* `EP.epFormsRange A k`: the image of `Ωᵏ_{ep,∞}(X)` in `Ωᵏ_∞(Ob X)`.
* `EP.formsInftyOne_mem_epFormsRange`: it contains the unit `1 ∈ Ω⁰_∞(Ob X)`.
* **`EP.formsInftyWedge_mem_epFormsRange`**: it is closed under the wedge product.
* `EP.formsInftyD_mem_epFormsRange`: it is closed under `d`.

So **`Ω*_{ep,∞}(X)` is a differential graded subalgebra of `Ω*_∞(Ob X)`**;
`EP.exists_epFormsInfty_wedge` gives for `a ∈ Ωᵏ_{ep,∞}(X)`, `b ∈ Ωˡ_{ep,∞}(X)` the unique
`c ∈ Ωᵏ⁺ˡ_{ep,∞}(X)` with image `a ∧ b`.  (The graded-algebra instances on the type
`Ω*_{ep,∞}(X)` itself are not defined here.)
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u

namespace BundledMPolyfold

/-- Transport along an equality of bundled M-polyfolds commutes with the wedge product. -/
theorem castForms_formWedge {k l : ℕ} {B B' : BundledMPolyfold.{u}} (h : B = B')
    (ω : B.P.scForms k) (τ : B.P.scForms l) :
    castForms (k + l) h ⟨formWedge ω.1 τ.1, formWedge_mem_scForms ω.2 τ.2⟩ =
      ⟨formWedge (castForms k h ω).1 (castForms l h τ).1,
        formWedge_mem_scForms (castForms k h ω).2 (castForms l h τ).2⟩ := by
  subst h
  rfl

theorem castForms_formOne {B B' : BundledMPolyfold.{u}} (h : B = B') :
    castForms 0 h ⟨formOne B.P, formOne_mem_scForms⟩ = ⟨formOne B'.P, formOne_mem_scForms⟩ := by
  subst h
  rfl

end BundledMPolyfold

namespace EP

variable (A : EP.{u})

/-- The image of `Ωᵏ_{ep,∞}(X)` in Part I's `Ωᵏ_∞(Ob X)`. -/
def epFormsRange (k : ℕ) : Submodule ℝ (A.objPolyfold.formsInfty k) :=
  LinearMap.range (A.epFormsInftyToObj k)

variable {A}

theorem epFormsToObj_formWedge {k l : ℕ} (i : ℕ) (ω : A.epForms k i) (τ : A.epForms l i) :
    A.epFormsToObj (k + l) i
        ⟨formWedge ω.1 τ.1, (A.lift i).X.formWedge_mem_epForms ω.2 τ.2⟩ =
      A.objPolyfold.formsWedge k l i (A.epFormsToObj k i ω) (A.epFormsToObj l i τ) :=
  BundledMPolyfold.castForms_formWedge (A.objPolyfold_lift i) (A.epFormsToForms k i ω)
    (A.epFormsToForms l i τ)

theorem epFormsInftyToObj_of_formWedge {k l : ℕ} (n : ℕ) (ω : A.epForms k n)
    (τ : A.epForms l n) :
    A.epFormsInftyToObj (k + l) (A.epFormsInftyOf (k + l) n
        ⟨formWedge ω.1 τ.1, (A.lift n).X.formWedge_mem_epForms ω.2 τ.2⟩) =
      A.objPolyfold.formsInftyWedge k l (A.epFormsInftyToObj k (A.epFormsInftyOf k n ω))
        (A.epFormsInftyToObj l (A.epFormsInftyOf l n τ)) :=
  (A.epFormsInftyToObj_of (k + l) n _).trans
    ((congrArg (A.objPolyfold.formsInftyOf (k + l) n) (epFormsToObj_formWedge n ω τ)).trans
      ((A.objPolyfold.formsInftyWedge_of_of n _ _).symm.trans
        (congrArg₂ (fun x y => A.objPolyfold.formsInftyWedge k l x y)
          (A.epFormsInftyToObj_of k n ω).symm (A.epFormsInftyToObj_of l n τ).symm)))

/-- **The wedge product of two forms of the ep-groupoid is a form of the ep-groupoid**: for
`a ∈ Ωᵏ_{ep,∞}(X)`, `b ∈ Ωˡ_{ep,∞}(X)` there is `c ∈ Ωᵏ⁺ˡ_{ep,∞}(X)` whose image in
`Ω*_∞(Ob X)` is the wedge product of the images (unique, the map being injective). -/
theorem exists_epFormsInfty_wedge {k l : ℕ} (a : A.epFormsInfty k) (b : A.epFormsInfty l) :
    ∃ c : A.epFormsInfty (k + l), A.epFormsInftyToObj (k + l) c =
      A.objPolyfold.formsInftyWedge k l (A.epFormsInftyToObj k a) (A.epFormsInftyToObj l b) := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq k a
  obtain ⟨j, τ, rfl⟩ := A.exists_epFormsInftyOf_eq l b
  exact ⟨_, (epFormsInftyToObj_of_formWedge (max i j) (A.epFormsMap k i _ (le_max_left i j) ω)
    (A.epFormsMap l j _ (le_max_right i j) τ)).trans
    (congrArg₂ (fun x y => A.objPolyfold.formsInftyWedge k l (A.epFormsInftyToObj k x)
      (A.epFormsInftyToObj l y)) (A.epFormsInftyOf_epFormsMap k (le_max_left i j) ω)
      (A.epFormsInftyOf_epFormsMap l (le_max_right i j) τ))⟩

/-- `Ω*_{ep,∞}(X)` is closed under the wedge product of `Ω*_∞(Ob X)`. -/
theorem formsInftyWedge_mem_epFormsRange {k l : ℕ} {a : A.objPolyfold.formsInfty k}
    {b : A.objPolyfold.formsInfty l} (ha : a ∈ A.epFormsRange k) (hb : b ∈ A.epFormsRange l) :
    A.objPolyfold.formsInftyWedge k l a b ∈ A.epFormsRange (k + l) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c, hc⟩ := exists_epFormsInfty_wedge a' b'
  exact ⟨c, hc⟩

/-- `Ω*_{ep,∞}(X)` contains the unit of `Ω*_∞(Ob X)`. -/
theorem formsInftyOne_mem_epFormsRange : A.objPolyfold.formsInftyOne ∈ A.epFormsRange 0 := by
  have hmem : formOne A.X.PObj ∈ (A.lift 0).X.epForms 0 :=
    ⟨formOne_mem_scForms, fun _ _ _ _ _ _ => by ext a; rfl⟩
  refine ⟨A.epFormsInftyOf 0 0 ⟨formOne A.X.PObj, hmem⟩, ?_⟩
  rw [epFormsInftyToObj_of]
  rfl

/-- `Ω*_{ep,∞}(X)` is closed under `d` of `Ω*_∞(Ob X)`. -/
theorem formsInftyD_mem_epFormsRange {k : ℕ} {a : A.objPolyfold.formsInfty k}
    (ha : a ∈ A.epFormsRange k) : A.objPolyfold.formsInftyD k a ∈ A.epFormsRange (k + 1) := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨A.epFormsInftyD k a',
    (LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj k) a').symm⟩

end EP

end Polyfold
