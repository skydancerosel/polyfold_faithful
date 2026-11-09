import Polyfold.Chapter8.TangentZhouLevels
import Polyfold.Chapter2.TangentProjOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §8.1 "Regularity Properties and Tangents": **Proposition 8.1.17** (p. 371, new in the
2021 edition), parts (1) and (2), without the hypothesis that `p : T𝐗 → 𝐗¹` is open.  Numbers
and pages are the 2021 text's.

# Proposition 8.1.17 without the openness hypothesis on `p`

## The text, paraphrased

(Proposition 8.1.17, p. 371) (1) If `X¹` has (LUC), so has `TX`.  (2) If `X` has (SLUC), so has
`TX`.  The proof of (1) passes from an open set of `TU(x)` to its image in `V(x) = U(x) ∩ X₁`,
which needs the projection `p : TX → X¹` to be open (Part I, 2021 Proposition 2.3.15 (2)).

## What is formalized

* `EpGroupoid.nonEffectivePart_tangent_eq_of_levelOneReps` (`(T𝐗)^T = p⁻¹((𝐗¹)^T)`),
  **`EpGroupoid.proposition_8_1_17_2021_one_of_levelOneReps`** (Proposition 8.1.17 (1)),
  `EpGroupoid.proposition_8_1_17_2021_two_of_levelOneReps` (Proposition 8.1.17 (2) for `(TX)⁰`),
  `EP.isLUC_tangent_lift_of_levelOneReps` (every `T(X^i)` has (LUC); rows V8.45, V8.52) and
  **`EP.proposition_8_1_17_two_all_2021_of_levelOneReps`** (Proposition 8.1.17 (2) for every
  `(TX)^i`).

Each one is the corresponding theorem of `TangentZhou.lean` or `TangentZhouLevels.lean`, with the
hypothesis `IsOpenMap tangentProj` (gap G.8) discharged by `MPolyfold.isOpenMap_tangentProj`
(`Chapter2/TangentProjOpen.lean`).  The remaining hypotheses are those of the text's proof:
(LUC) for `X¹` or (SLUC) for `X`, and `HasConnectedDenseLevelOneReps` (the text's
`V(x) = U(x) ∩ X₁` connected and dense; satisfiable: `hasConnectedDenseLevelOneReps_point`,
`EpGroupoid.hasConnectedDenseLevelOneReps_of_subsingleton`).  The suffix `_of_levelOneReps` names
that remaining hypothesis.  Where `HasConnectedDenseLevelOneReps` is also available as a theorem
(`Chapter7/SmoothConnectedReps.lean`), the forms without it are the `_of_isLUC` / `_of_isSLUC`
theorems of `Chapter7/SmoothRegularAssembly.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `(T𝐗)^T = p⁻¹((𝐗¹)^T)` under (LUC) for `X¹` (the step of the proof of 2021 Proposition
8.1.17 (1)), without the hypothesis that `p : T𝐗 → 𝐗¹` is open. -/
theorem nonEffectivePart_tangent_eq_of_levelOneReps (h : X.liftOne.IsLUC)
    (hR : X.HasConnectedDenseLevelOneReps) :
    X.tangentEpGroupoid.nonEffectivePart = X.PMor.tangentProj ⁻¹' X.liftOne.nonEffectivePart :=
  X.nonEffectivePart_tangent_eq h hR X.PMor.isOpenMap_tangentProj

/-- **2021 Proposition 8.1.17 (1), p. 371**: if `X¹` has (LUC), so has `TX`.  The hypothesis
"`p : T𝐗 → 𝐗¹` open" of `proposition_8_1_17_2021_one` is discharged. -/
theorem proposition_8_1_17_2021_one_of_levelOneReps (h : X.liftOne.IsLUC)
    (hR : X.HasConnectedDenseLevelOneReps) : X.tangentEpGroupoid.IsLUC :=
  X.proposition_8_1_17_2021_one h hR X.PMor.isOpenMap_tangentProj

/-- **2021 Proposition 8.1.17 (2), p. 371, for `(TX)⁰`**: (SLUC) for `X` gives (LUC) for `TX`,
without the openness hypothesis on `p`. -/
theorem proposition_8_1_17_2021_two_of_levelOneReps (A : EP.{u}) (h : A.IsSLUC)
    (hR : A.X.HasConnectedDenseLevelOneReps) : A.X.tangentEpGroupoid.IsLUC :=
  proposition_8_1_17_2021_two A h hR A.X.PMor.isOpenMap_tangentProj

end EpGroupoid

namespace EP

/-- Under (SLUC) every `T(X^i)` has (LUC) (2021 Proposition 8.1.17 (1) for `X^i`), without the
openness hypothesis on `p` (rows V8.45, V8.52). -/
theorem isLUC_tangent_lift_of_levelOneReps (A : EP.{u}) (h : A.IsSLUC)
    (hR : ∀ i, (A.lift i).X.HasConnectedDenseLevelOneReps) (i : ℕ) :
    (A.lift i).X.tangentEpGroupoid.IsLUC :=
  A.isLUC_tangent_lift h hR (fun j => (A.lift j).X.PMor.isOpenMap_tangentProj) i

/-- **2021 Proposition 8.1.17 (2), p. 371**: if `X` has (SLUC), so has `TX`: every `(TX)^i` has
(LUC).  The hypothesis "`p` open for every `X^i`" of `proposition_8_1_17_two_all_2021` is
discharged. -/
theorem proposition_8_1_17_two_all_2021_of_levelOneReps (A : EP.{u}) (h : A.IsSLUC)
    (hR : ∀ i, (A.lift i).X.HasConnectedDenseLevelOneReps) : A.tangentEP.IsSLUC :=
  A.proposition_8_1_17_two_all_2021 h hR fun j => (A.lift j).X.PMor.isOpenMap_tangentProj

end EP

end Polyfold
