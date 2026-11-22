import Polyfold.Chapter18.ImplicitFunctionTheorem
import Polyfold.Chapter18.FredholmSectionFunctorsExamples
import Polyfold.Chapter4.NonVacuityG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 845–846: **a non-degenerate witness for Theorem 18.1.5 and Remark 18.1.6** on the
reflection bundle (`FredholmSectionFunctorsExamples.lean`).

# The implicit function theorem for the diagonal section of the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `μ(x) = ℝ`, the generator `−1` acting by `x ↦ −x` and `v ↦ −v`, and the section
functor `f(x) = (x, x)` (`reflDiag`), whose representative in `Ψ̄` is the graph section of the
identity.  At the solution object `0` (whose isotropy `ℤ/2` acts by `v ↦ −v` on the fibre):

* `theorem_18_1_5_hyp_witness`: all hypotheses of `theorem_18_1_5_model` hold, in the model with
  two copies of `Ψ̄` (`reflPair`), at the point `0` of the copy `true`;
* `theorem_18_1_5_hyp_applies`: its conclusions hold, with a natural representation `U(0)` whose
  image is an open neighbourhood of `|0|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor TrivialBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction SBLocalization

/-- The point `0` of the copy `true` of `Ψ̄` in the model with two copies. -/
abbrev reflPoint : (reflPair.Ψ true).1.base.O := (0 : Fin 1 → ℝ)

/-- The representative `q ↦ (q, q)` is in good position at `0` (Part I's Definition 3.6.6 in a
tame chart). -/
theorem reflDiag_isGoodPositionGermTame :
    (reflPair.Ψ true).1.B.IsGoodPositionGermTame ((reflPair.Ψ true).1.localRep reflDiag)
      reflPoint := by
  change reflUnifData.B.IsGoodPositionGermTame (reflUnifData.localRep reflDiag) (0 : Fin 1 → ℝ)
  rw [localRep_reflDiag]
  refine TrivialBundle.isGoodPositionGermTame_graphSection contDiff_id ?_
  rw [fderiv_id]
  exact fun v => ⟨v, rfl⟩

/-- `f(Γ(true, 0)) = f(0) = 0`. -/
theorem reflDiag_zero_mem :
    (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj ⟨true, reflPoint⟩ ∈
      reflDiag.zeroSet := by
  rw [reflDiag_zeroSet]
  rfl

/-- **The hypotheses of Theorem 18.1.5 (`theorem_18_1_5_model`) are satisfiable**, at a solution
object with non-trivial isotropy: `f` is an sc-Fredholm section functor with tame germ data,
`f(0) = 0`, and the representative is in good position at `0`; `f` is not the zero section and
`−1` acts non-trivially on the fibre over `0` (`reflDiag_nondegenerate`). -/
theorem theorem_18_1_5_hyp_witness :
    reflQ.IsScFredholmSectionFunctor reflDiag ∧ reflQ.IsScFredholmSectionFunctorTame reflDiag ∧
      (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj ⟨true, reflPoint⟩ ∈
        reflDiag.zeroSet ∧
      (reflPair.Ψ true).1.B.IsGoodPositionGermTame ((reflPair.Ψ true).1.localRep reflDiag)
        reflPoint ∧
      (∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) :=
  ⟨isScFredholmSectionFunctor_reflDiag, isScFredholmSectionFunctorTame_reflDiag,
    reflDiag_zero_mem, reflDiag_isGoodPositionGermTame, reflDiag_nondegenerate.1,
    reflDiag_nondegenerate.2.1⟩

/-- **Theorem 18.1.5 applies** to the witness: there is a natural representation `U(0)` in the
model with two copies of `Ψ̄` whose image is an open neighbourhood of `|0|`, on which `Θ ∘ Γ` has
tame local branching structures at the zeros of `f`, `(f^Ψ̄, Λ₀)` is in good position there, and
the zero set is a smooth submanifold. -/
theorem theorem_18_1_5_hyp_applies :
    ∃ R : (reflQ.modelSEP reflPair.Ψ).X.NaturalRep ⟨true, reflPoint⟩,
      IsOpen ((reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).orbitMap ''
        ((reflectionConstruction.modelEP (reflQ.modelBase reflPair.Ψ)).X.π '' R.U)) ∧
      (∀ y ∈ R.U, (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj y ∈
          reflDiag.zeroSet →
        Nonempty ((reflQ.modelSEP reflPair.Ψ).X.TameBranchingStructure (fun z =>
          reflDiag.zeroIndicator
            ((reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj z)) y) ∧
        SBLocalization.IsGoodPositionAt (A := reflQ.modelSEP reflPair.Ψ)
          (reflQ.modelSection reflPair.Ψ reflDiag) (zeroMultisection (reflQ.modelSEP reflPair.Ψ))
          y) ∧
      (reflQ.modelSEP reflPair.Ψ).X.PObj.IsSmoothSubmanifold
        {y ∈ R.U | (reflectionConstruction.modelFunctor (reflQ.modelBase reflPair.Ψ)).obj y ∈
          reflDiag.zeroSet} := by
  obtain ⟨R, hU, -, -, -, h1, h2, hS, -⟩ := reflQ.theorem_18_1_5_model
    isScFredholmSectionFunctor_reflDiag isScFredholmSectionFunctorTame_reflDiag
    reflDiag_zero_mem reflDiag_isGoodPositionGermTame
  exact ⟨R, hU, fun y hy hz => ⟨h1 y hy hz, h2 y hy hz⟩, hS⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
