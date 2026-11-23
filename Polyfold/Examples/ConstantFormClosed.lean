import Polyfold.Chapter16.IndexZeroAllAdmissible
import Polyfold.Chapter6.IntervalEndInclusion

/-!
# The constant `0`-forms are closed

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4 (p. 197) and §9.2:
the exterior derivative of a constant `0`-form is zero.

## What is formalized

* `MPolyfold.extD_constForm`: `d c = 0` for the constant `0`-form `c` of an M-polyfold: `c` is
  the pull-back of the constant `0`-form of the point `ℝ⁰` along the constant map, `d` commutes
  with pull-backs (`extD_formPullback`), and every `1`-form on `ℝ⁰` is zero.
* `EP.constFormInfty c`, `EP.epFormsInftyD_constFormInfty`, `EP.zeroFormEval_constFormInfty`:
  the class of the constant `0`-form in `Ω⁰_{ep,∞}(X)` is closed and has the value `c` at the
  smooth points.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The constant `0`-form is the pull-back of the constant `0`-form of the point. -/
theorem constForm_eq_formPullback (c : ℝ)
    (hf : P.IsScSmoothMap (rnPolyfold 0) fun _ : X => (0 : Fin 0 → ℝ)) :
    P.constForm c = formPullback hf ((rnPolyfold 0).constForm c) := by
  funext x
  ext α
  rfl

/-- Every `1`-form on the point `ℝ⁰` is zero; in particular `dω = 0` there. -/
theorem extD_eq_zero_of_point
    (ω : ∀ y : (rnPolyfold 0).Level 1, (rnPolyfold 0).tangentFiber y [⋀^Fin 0]→ₗ[ℝ] ℝ) :
    extD ω = 0 := by
  funext x
  ext α
  have hsub : Subsingleton ((rnPolyfold 0).shift.tangentFiber x) := by
    let y₀ : (rnPolyfold 0).Level 1 := (rnPolyfold 0).shift.levelVal 1 x
    have hφ := (rnPolyfold 0).shift_isChart (isChart_rnChart (0 : Fin 0 → ℝ)) y₀
    have hx : (rnPolyfold 0).shift.levelVal 1 x ∈
        (levelChart (isChart_rnChart (0 : Fin 0 → ℝ)) y₀).source := mem_univ _
    have e := tangentFiberLinearEquiv hφ hx
    have hE : Subsingleton ((levelChart (isChart_rnChart (0 : Fin 0 → ℝ)) y₀).model.E 0) :=
      (inferInstance : Subsingleton (Fin 0 → ℝ))
    exact ⟨fun a b => e.injective (Subtype.ext (Subsingleton.elim _ _))⟩
  have hα : α = fun _ => 0 := funext fun i => Subsingleton.elim _ _
  rw [hα]
  exact (extD ω x).map_coord_zero 0 rfl

/-- **The constant `0`-forms are closed**: `d c = 0`. -/
theorem extD_constForm (c : ℝ) : extD (P.constForm c) = 0 := by
  have h0 : (0 : Fin 0 → ℝ) ∈ (rnPolyfold 0).smoothSet := by
    refine mem_iInter.2 fun m => ?_
    rw [rnPolyfold_levelSet]
    exact mem_univ _
  have hf : P.IsScSmoothMap (rnPolyfold 0) fun _ : X => (0 : Fin 0 → ℝ) :=
    isScSmoothMap_const h0
  rw [constForm_eq_formPullback c hf, extD_formPullback hf (constForm_mem_scForms c),
    extD_eq_zero_of_point]
  rfl

end MPolyfold

namespace EP

variable (A : EP.{u})

/-- The class of the constant `0`-form `c` in `Ω⁰_{ep,∞}(X)`. -/
def constFormInfty (c : ℝ) : A.epFormsInfty 0 :=
  A.epFormsInftyOf 0 0 ⟨_, (A.lift 0).X.constForm_mem_epForms c⟩

/-- **The constant `0`-form is closed** in `Ω*_{ep,∞}(X)`. -/
theorem epFormsInftyD_constFormInfty (c : ℝ) : A.epFormsInftyD 0 (A.constFormInfty c) = 0 := by
  rw [constFormInfty, epFormsInftyD_of]
  have h : A.epFormsD 0 0 ⟨_, (A.lift 0).X.constForm_mem_epForms c⟩ = 0 :=
    Subtype.ext (MPolyfold.extD_constForm c)
  rw [h, map_zero]

/-- The value of the constant `0`-form `c` at a smooth point is `c`. -/
theorem zeroFormEval_constFormInfty (c : ℝ) {p : A.Obj} (hp : p ∈ A.X.PObj.smoothSet) :
    A.zeroFormEval (A.constFormInfty c) p = c := by
  rw [constFormInfty, EP.zeroFormEval_of, A.zeroLevelEval_eq 0 _ hp (fun j => Fin.elim0 j)]
  rfl

end EP

end Polyfold
