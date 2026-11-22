import Polyfold.Chapter18.LinearizationSetLocal
import Polyfold.Chapter18.LinearizationSetExamples
import Polyfold.Chapter18.GoodPositionIntrinsicExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, Definition 18.1.4, p. 845: **non-degenerate witnesses for `Lin(f, α)` with local
sc⁺-sections** (`LinearizationSetLocal.lean`), whose claims hold with no hypothesis.

* `definition_18_1_4_local_reflDiag`: on the reflection bundle of Chapter 17 with `f(x) = (x, x)`
  (`reflDiag`), at the zero `0`, whose isotropy `ℤ/2` acts on the fibre by `v ↦ −v`:
  `Lin(f, 0)` with local sc⁺-sections contains `f'(0)`, is the set read through `Ψ̄` and its point
  `0`, has one index, and `φ_*` maps it into itself for every `φ : 0 → 0`;
  `linPush_reflDiag_neg_local` is the case `φ = (−1, 0)`.
* `definition_18_1_4_local_halfF`: on `ℤ/2 ⋉ H`, `H = [0, ∞) × ℝ`, with
  `f(a, y) = a² + y² − 1` (`halfF`), at the zero `(0, 1) ∈ ∂C`: the same claims.

## Reading

Both constructions have global transitions `k ↦ g ∗ k`, as do the other strong polyfold bundle
constructions with sections in this development; on them `HasTransportedScPlusSections` holds as
well (for `reflQ`, `reflQ_hasTransportedScPlusSections`).  The claims of
`definition_18_1_4_local` are proved for every strong polyfold bundle construction, with
transitions that need not be global: the local sc⁺-section `t̄ ∘ s̄⁻¹ ∘ s ∘ s ∘ t⁻¹` is defined
near `t(a)` only (`exists_linZeroLoc_transAct`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor TrivialBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction

/-- **Definition 18.1.4 with local sc⁺-sections on the reflection bundle**: at the zero `0` of
`f(x) = (x, x)`, `Lin(f, 0)` with local sc⁺-sections contains `f'(0)`, is the set read through
`Ψ̄` and its point `0`, has one index, and `φ_*` maps it into itself for every `φ : 0 → 0`. -/
theorem definition_18_1_4_local_reflDiag :
    reflQ.linearization reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0
        reflDiag_toFun_zero ⟨reflUnif, rfl⟩ ∈
      reflQ.linSetLoc reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 ∧
    reflQ.linSetLoc reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 =
      reflQ.linSetLocAt reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0
        (Ψ := reflΨ) rfl linSetPoint obj_linSetPoint ∧
    (∃ i : ℤ, ∀ L ∈ reflQ.linSetLoc reflDiag
        isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0,
      HasFiniteIndex L ∧ linIndex L = i) ∧
    ∀ (φ : GCT.reflection.Mor) (hs : GCT.reflection.toGroupoidStr.src φ = 0)
      (ht : GCT.reflection.toGroupoidStr.tgt φ = 0),
      ∀ L ∈ reflQ.linSetLoc reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor
          0,
        linPush φ hs ht L ∈
          reflQ.linSetLoc reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor
            0 := by
  obtain ⟨h1, h2, h3, h4⟩ := reflQ.definition_18_1_4_local isScFredholmSectionFunctor_reflDiag 0
  exact ⟨h1 (reflQ.linearization_mem_linSet _ 0 reflDiag_toFun_zero ⟨reflUnif, rfl⟩),
    h2 reflΨ rfl linSetPoint obj_linSetPoint, h3,
    fun φ hs ht => h4 0 φ hs ht ⟨reflUnif, rfl⟩⟩

/-- **`φ_* f'(0)` lies in `Lin(f, 0)` with local sc⁺-sections for `φ = (−1, 0)`**, whose fibre
map `μ(φ)` is `v ↦ −v`. -/
theorem linPush_reflDiag_neg_local :
    linPush (V := reflV) (S := reflectionConstruction) (α := 0) (α' := 0)
        ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl
        (show ((-1 : ℤˣ) • (0 : Fin 1 → ℝ)) = 0 from smul_zero _)
        (reflQ.linearization reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor
          0 reflDiag_toFun_zero ⟨reflUnif, rfl⟩) ∈
      reflQ.linSetLoc reflDiag isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 ∧
    ∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v :=
  ⟨definition_18_1_4_local_reflDiag.2.2.2 _ _ _ _ definition_18_1_4_local_reflDiag.1,
    fun _ hv => reflV_map_ne 0 hv⟩

end GCT.VectorBundle.ReflectionBundle

namespace GCT.VectorBundle.HalfSpaceReflection

open PolyfoldConstruction HalfSpaceBundle MPolyfold StrongPolyfoldBundleConstruction

/-- **Definition 18.1.4 with local sc⁺-sections on `ℤ/2 ⋉ H`**: at the boundary zero `(0, 1)` of
`f(a, y) = a² + y² − 1`, `Lin(f, α)` with local sc⁺-sections contains `f'(α)`, is the set read
through `Ψ̄` and its point `(0, 1)`, has one index, and `φ_*` maps it into itself for every
`φ : α → α`. -/
theorem definition_18_1_4_local_halfF :
    halfQ.linearization halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint
        halfF_zero_topPoint (halfQ_F_nonempty topPoint) ∈
      halfQ.linSetLoc halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint ∧
    halfQ.linSetLoc halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint =
      halfQ.linSetLocAt halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint
        (Ψ := halfΨ) rfl (halfPt topPoint) (obj_halfPt topPoint) ∧
    (∃ i : ℤ, ∀ L ∈ halfQ.linSetLoc halfF
        isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor topPoint,
      HasFiniteIndex L ∧ linIndex L = i) ∧
    ∀ (φ : halfC.Mor) (hs : halfC.toGroupoidStr.src φ = topPoint)
      (ht : halfC.toGroupoidStr.tgt φ = topPoint),
      ∀ L ∈ halfQ.linSetLoc halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor
          topPoint,
        linPush φ hs ht L ∈
          halfQ.linSetLoc halfF isScFredholmSectionFunctor_halfF.isScSmoothSectionFunctor
            topPoint := by
  obtain ⟨h1, h2, h3, h4⟩ := halfQ.definition_18_1_4_local isScFredholmSectionFunctor_halfF
    topPoint
  exact ⟨h1 (halfQ.linearization_mem_linSet _ topPoint halfF_zero_topPoint
      (halfQ_F_nonempty topPoint)),
    h2 halfΨ rfl (halfPt topPoint) (obj_halfPt topPoint), h3,
    fun φ hs ht => h4 topPoint φ hs ht (halfQ_F_nonempty topPoint)⟩

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
