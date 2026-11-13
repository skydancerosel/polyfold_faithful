import Polyfold.Chapter11.FormAveraging
import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
pp. 373–374: the averaging step of the proof of **Proposition 8.2.3** (2017: Proposition 8.1)
for the translation groupoid `G_x ⋉ U(x)` of a natural representation (gap G.87).  Numbers and
pages are the 2021 text's.

# Averaging on the translation groupoid `G_x ⋉ U(x)`

## The text, paraphrased

A primitive `τ` on the `G_x`-invariant neighbourhood is averaged, `τ' = (1/#G_x) Σ_g g^*τ`; then
`τ'` is `G_x`-invariant and `dτ' = ω`.

## What is formalized

For a natural representation `R` of `G_x` on `U = U(x)` (Theorem 7.1.13) in an ep-groupoid:
* `NaturalRep.translationEP R`: the ep-groupoid `G_x ⋉ U(x)` (Chapter 7's
  `translationEpGroupoid`) as an object of `EP`; `NaturalRep.unitsEP R`: the M-polyfold `U(x)`
  as an ep-groupoid with only the unit morphisms (`EpGroupoid.trivial`).
* `unitsFunctor R : U(x) → G_x ⋉ U(x)` (the identity on objects), `smulFunctor R g : U(x) → U(x)`
  (`y ↦ g ∗ y`), `smulNatTrans R g : unitsFunctor → unitsFunctor ∘ smulFunctor g` (`y ↦ (g, y)`).
* **`NaturalRep.exists_primitive_translation`**: if `c ∈ Ωᵏ⁺¹_{ep,∞}(G_x ⋉ U(x))` and
  `β ∈ Ωᵏ_{ep,∞}(U(x))` (a form of the M-polyfold `U(x)`, not necessarily invariant) satisfy
  `dβ = c` on `U(x)`, then `c = dτ` for some `τ ∈ Ωᵏ_{ep,∞}(G_x ⋉ U(x))`: the average of `β`
  (`EP.exists_primitive_of_average`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid.NaturalRep

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {x : Obj} (R : X.NaturalRep x)

/-- **`G_x ⋉ U(x)` as an object of `EP`.** -/
abbrev translationEP : EP.{u} := EP.mk R.U (X.Isotropy x × R.U) R.translationEpGroupoid

/-- **The M-polyfold `U(x)` as an ep-groupoid with only the unit morphisms.** -/
abbrev unitsEP : EP.{u} := EP.mk R.U R.U (EpGroupoid.trivial R.objPolyfold)

/-- The functor `U(x) → G_x ⋉ U(x)`, the identity on objects and `y ↦ 1_y = (1, y)` on
morphisms. -/
def unitsFunctor : EpFunctor R.unitsEP.X R.translationEP.X where
  obj := id
  mor := fun y : R.U => ((1 : X.Isotropy x), y)
  src_mor _ := rfl
  tgt_mor := fun y : R.U => one_smul (X.Isotropy x) y
  mor_comp φ ψ h := by
    have h' : φ = ψ := h
    subst h'
    change ((1 : X.Isotropy x), φ) = (1 * 1, φ)
    rw [mul_one]
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothMap_sheet 1

/-- The functor `U(x) → U(x)`, `y ↦ g ∗ y`. -/
def smulFunctor (g : X.Isotropy x) : EpFunctor R.unitsEP.X R.unitsEP.X where
  obj := fun y : R.U => g • y
  mor := fun y : R.U => g • y
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := R.isScSmoothMap_smul g
  isScSmoothMap_mor := R.isScSmoothMap_smul g

/-- The natural transformation `y ↦ (g, y) : y → g ∗ y` from `unitsFunctor` to
`unitsFunctor ∘ smulFunctor g`. -/
def smulNatTrans (g : X.Isotropy x) :
    EpNatTrans R.unitsFunctor (R.unitsFunctor.comp (R.smulFunctor g)) where
  app := fun y : R.U => (g, y)
  isScSmoothMap_app := isScSmoothMap_sheet g
  src_app _ := rfl
  tgt_app _ := rfl
  naturality m := by
    change ((g * 1, m) : X.Isotropy x × R.U) = (1 * g, m)
    rw [mul_one, one_mul]

/-- **2021 Proposition 8.2.3, the averaging step (p. 374), for `G_x ⋉ U(x)`**: a form
`c ∈ Ωᵏ⁺¹_{ep,∞}(G_x ⋉ U(x))` which has a primitive `β` among the forms of the M-polyfold
`U(x)` has a primitive `τ ∈ Ωᵏ_{ep,∞}(G_x ⋉ U(x))` (the average of `β` over `G_x`). -/
theorem exists_primitive_translation (k : ℕ) (c : R.translationEP.epFormsInfty (k + 1))
    (β : R.unitsEP.epFormsInfty k)
    (hβ : R.unitsEP.epFormsInftyD k β = EP.epFormsInftyPullback R.unitsFunctor (k + 1) c) :
    ∃ τ : R.translationEP.epFormsInfty k, R.translationEP.epFormsInftyD k τ = c := by
  have := Fintype.ofFinite (X.Isotropy x)
  exact EP.exists_primitive_of_average R.unitsFunctor R.smulFunctor R.smulNatTrans
    (MPolyfold.isLocalScDiffeo_id) injective_id surjective_id (fun m => ⟨m.1, m.2, rfl⟩)
    (fun g => Equiv.mulRight g)
    (fun g h => EpFunctor.ext (funext fun y : R.U => (mul_smul h g y).symm)
      (funext fun y : R.U => (mul_smul h g y).symm)) k c β hβ

end EpGroupoid.NaturalRep

end Polyfold
