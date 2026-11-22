import Polyfold.Chapter18.Orientations
import Polyfold.Chapter18.FredholmSectionFunctorsExamples
import Polyfold.Chapter18.MultisectionFunctorsExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.5, pp. 856–859: **witnesses for the hypotheses of §18.5** (`Orientations.lean`) on the
reflection bundle of Chapter 17.  Numbers and pages are the 2021 text's.

# The diagonal section of the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, and `f(x) = (x, x)`
(`reflDiag`).

* `reflection_isSmoothObj`: every object of `ℤ/2 ⋉ ℝ` is smooth.
* **`reflDiag_orientation_hyp`**: the hypotheses of §18.5 not in the text hold for `f`
  (tameness, bump functions, the tame form of Definition 18.1.1, `F̄(x) ≠ ∅`), together with the
  sc-Fredholm property, and the isotropy `−1` of `0` acts non-trivially on the fibre `μ(0) = ℝ`.
* `reflDiag_orPush_isotropy`: over `0` the fibre of `σ : O_f → C_∞` is a two-point set and the
  isotropy `g = (−1, 0)` acts on it by a bijection `g_*` (p. 857).
* `reflDiag_two_orientations`: an orientation of `f` comes with a second one, different at `0`
  (`exists_two_orientations`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction

/-- **Every object of `ℤ/2 ⋉ ℝ` is smooth** (Definition 17.1.31). -/
theorem reflection_isSmoothObj (x : Fin 1 → ℝ) : reflectionConstruction.IsSmoothObj x :=
  (isSmoothObj_obj_iff (reflQ.baseUnif reflΨ) x).2 (by
    change x ∈ (rnPolyfold 1).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]
    exact mem_univ x)

/-- **The hypotheses of §18.5 hold for the diagonal section** `f(x) = (x, x)`: the polyfold
structure is tame and admits bump functions (Definition 18.4.1), `f` is an sc-Fredholm section
functor in the plain and the tame form (Definition 18.1.1), and `F̄(x) ≠ ∅`.  The witness is not
degenerate: `f` is not the zero section and the isotropy `−1` of `0` acts on the fibre
`μ(0) = ℝ` by `v ↦ −v`. -/
theorem reflDiag_orientation_hyp :
    reflectionConstruction.IsTame ∧ reflectionConstruction.AdmitsModelBumpFunctions ∧
      reflQ.IsScFredholmSectionFunctor reflDiag ∧ reflQ.IsScFredholmSectionFunctorTame reflDiag ∧
      reflQ.HasStrongBundleUniformizers ∧
      (∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) :=
  ⟨reflectionConstruction_isTame, reflection_admitsModelBumpFunctions,
    isScFredholmSectionFunctor_reflDiag, isScFredholmSectionFunctorTame_reflDiag,
    reflQ_hasStrongBundleUniformizers, reflDiag_nondegenerate.1, reflDiag_nondegenerate.2.1⟩

/-- **The isotropy `g = (−1, 0)` of `0` in the orientation category of `f`** (p. 857): the fibre
of `σ : O_f → C_∞` over `0` has exactly two points, and `g_*` is a bijection of it. -/
theorem reflDiag_orPush_isotropy :
    (∃ o₁ o₂ : reflQ.DetOr isScFredholmSectionFunctor_reflDiag reflQ_hasStrongBundleUniformizers
        0 (reflection_isSmoothObj 0), o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂) ∧
      Bijective (reflQ.orPush isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers
        (((-1 : ℤˣ), (0 : Fin 1 → ℝ)) : GCT.reflection.Mor) rfl (smul_zero _)
        (reflection_isSmoothObj 0) (reflection_isSmoothObj 0)) :=
  have h := reflQ.orPush_bijective_two isScFredholmSectionFunctor_reflDiag
    reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers
    (φ := (((-1 : ℤˣ), (0 : Fin 1 → ℝ)) : GCT.reflection.Mor)) (α := 0) (α' := 0) rfl
    (smul_zero _) (reflection_isSmoothObj 0) (reflection_isSmoothObj 0)
  ⟨h.1, h.2.2⟩

/-- **An orientation of `f` comes with a second one** (p. 857, `o` and `−o`), different over `0`. -/
theorem reflDiag_two_orientations
    (h : reflQ.IsOrientable isScFredholmSectionFunctor_reflDiag
      reflection_admitsModelBumpFunctions reflectionConstruction_isTame
      isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers) :
    ∃ o₁ o₂, reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflectionConstruction_isTame
        isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o₁ ∧
      reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflectionConstruction_isTame
        isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o₂ ∧
      o₁ 0 (reflection_isSmoothObj 0) ≠ o₂ 0 (reflection_isSmoothObj 0) :=
  reflQ.exists_two_orientations _ _ _ _ _ h (reflection_isSmoothObj 0)

end GCT.VectorBundle.ReflectionBundle

end Polyfold
