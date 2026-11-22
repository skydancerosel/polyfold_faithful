import Polyfold.Chapter18.ImplicitFunctionSubcategory
import Polyfold.Chapter18.ImplicitFunctionTheoremExamples
import Polyfold.Chapter18.ModelSectionPushforward

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 844–846: **non-degenerate witnesses** for the polyfold `C_U` (p. 845), Theorem 18.1.5
on `C_U`, and `[f̄]_* f^c = f^{c'}` (Remark 18.1.2 (a)), on the reflection bundle
(`FredholmSectionFunctorsExamples.lean`).

# Witnesses on the reflection bundle

`C = ℤ/2 ⋉ ℝ` (the generator `−1` acting by `x ↦ −x`, isotropy `ℤ/2` at `0`), `μ(x) = ℝ` with
`−1` acting by `v ↦ −v`, and the section functor `f(x) = (x, x)` (`reflDiag`, vanishing exactly
at `0`).

* `openSubConstruction_reflection`: for every open `U ⊆ |C|`, `C_U` is a tame polyfold with
  uniformizers at all objects.
* `theorem_18_1_5_subcategory_hyp_applies`: Theorem 18.1.5 on `C_U` applies at `0`: there is an
  open neighbourhood `U` of `|0|` on which `Θ|C_U` is a tame orbifold-type branched
  ep⁺-subcategory of `C_U`, with `Θ|C_U(0) = 1` at the object `0`, whose isotropy `−1` acts by
  `v ↦ −v` on the fibre.
* `pushforward_reflSingle_reflPair`: `[f̄]_* f^c = f^{c'}` for the two covering families `c` (one
  copy of `Ψ̄`) and `c'` (two copies), and the non-zero section `f`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongPolyfoldBundleConstruction
  PolyfoldConstruction SBLocalization

/-- **`C_U` is a tame polyfold with uniformizers** for every open `U` of `|ℤ/2 ⋉ ℝ|`. -/
theorem openSubConstruction_reflection {U : Set GCT.reflection.toGroupoidStr.OrbitSpace}
    (hU : IsOpen U) :
    (reflectionConstruction.openSubConstruction hU).HasUniformizers ∧
      (reflectionConstruction.openSubConstruction hU).IsTame :=
  ⟨hasUniformizers_openSubConstruction hU reflectionConstruction_hasUniformizers,
    isTame_openSubConstruction hU reflectionConstruction_isTame⟩

/-- **Theorem 18.1.5 on `C_U` applies** to the witness at the solution object `0` (isotropy
`ℤ/2`, acting by `v ↦ −v` on the fibre): there is an open neighbourhood `U` of `|0|` such that
`Θ|C_U` is a branched ep⁺-subcategory of the polyfold `C_U`, of orbifold-type and tame, with
`Θ|C_U(0) = 1`, and `C_U` is a tame polyfold with uniformizers. -/
theorem theorem_18_1_5_subcategory_hyp_applies :
    ∃ U : Set GCT.reflection.toGroupoidStr.OrbitSpace, ∃ hU : IsOpen U,
      GCT.reflection.toGroupoidStr.π
          ((reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj
            ⟨true, reflPoint⟩) ∈ U ∧
      (reflectionConstruction.openSubConstruction hU).IsBranchedSubcategory
        (restrictTheta U reflDiag.zeroIndicator) ∧
      (GCT.reflection.openSub U).IsOrbifoldTypeBranched (restrictTheta U reflDiag.zeroIndicator) ∧
      (reflectionConstruction.openSubConstruction hU).IsTameSubcategory
        (restrictTheta U reflDiag.zeroIndicator) ∧
      (reflectionConstruction.openSubConstruction hU).HasUniformizers ∧
      (reflectionConstruction.openSubConstruction hU).IsTame ∧
      ∃ β : (GCT.reflection.openSub U).Obj, restrictTheta U reflDiag.zeroIndicator β = 1 := by
  obtain ⟨-, U, hU, -, hmem, h1, h2, h3, hiff, -⟩ := reflQ.theorem_18_1_5_subcategory
    isScFredholmSectionFunctor_reflDiag isScFredholmSectionFunctorTame_reflDiag
    reflDiag_zero_mem reflDiag_isGoodPositionGermTame
  exact ⟨U, hU, hmem, h1, h2, h3, (openSubConstruction_reflection hU).1,
    (openSubConstruction_reflection hU).2,
    (show GCT.reflection.objOver U from ⟨_, hmem⟩), (hiff _).2 reflDiag_zero_mem⟩

/-- **`[f̄]_* f^c = f^{c'}` on the witness**: the model sections of the non-zero section functor
`f(x) = (x, x)` for one copy (`reflSingle`) and two copies (`reflPair`) of `Ψ̄` correspond under
the push-forward along `f̄_{c,c'}`. -/
theorem pushforward_reflSingle_reflPair :
    GenSBMap.pushforward (reflQ.isGeneralizedIso_bundleComparison reflSingle reflPair)
        (reflQ.modelSection reflSingle.Ψ reflDiag) = reflQ.modelSection reflPair.Ψ reflDiag ∧
      GenSBMap.pullback (reflQ.isGeneralizedIso_bundleComparison reflSingle reflPair)
        (reflQ.modelSection reflPair.Ψ reflDiag) = reflQ.modelSection reflSingle.Ψ reflDiag ∧
      ∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0 :=
  ⟨reflQ.pushforward_bundleComparison_modelSection reflSingle reflPair reflDiag_germs.1,
    reflQ.pullback_bundleComparison_modelSection reflSingle reflPair reflDiag_germs.1,
    reflDiag_nondegenerate.1⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
