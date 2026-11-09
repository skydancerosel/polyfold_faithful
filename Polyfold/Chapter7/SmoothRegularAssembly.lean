import Polyfold.Chapter2.TangentProjOpen
import Polyfold.Chapter7.ZhouFacts
import Polyfold.Chapter7.SmoothConnectedReps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.4 (pp. 331–340), the
Part I facts used there (p. 289, Proposition 2.3.15 (2) on p. 39), Corollary 7.6.8 (p. 351) and
Proposition 8.1.17 (p. 371).

# The Part I facts of §7.4 are theorems; §7.4 without hypotheses

## The text, paraphrased

(§7.4, pp. 331–340) The proofs of Propositions 7.4.8, 7.4.10 and 7.4.22 use four facts from
Part I about an M-polyfold `X`: `X_∞` is dense in every `X_m` (p. 289); `U ∩ X_∞` is connected for
a connected open `U`; `p : TX → X¹` is open (Proposition 2.3.15 (2)); two sc-smooth maps agreeing
near a smooth point in `X_∞` have the same tangent there.  Chapter 7 bundles them as the hypothesis
`MPolyfold.SmoothRegular` (gap G.85).

## What is formalized

* **`MPolyfold.smoothRegular`**: every M-polyfold satisfies `SmoothRegular` (gap G.85 closed), from
  `MPolyfold.denseSmooth` (`Chapter7/SmoothPointsDense.lean`), `MPolyfold.smoothConnected`
  (`Chapter7/SmoothConnectedReps.lean`), `MPolyfold.isOpenMap_tangentProj`
  (`Chapter2/TangentProjOpen.lean`, gap G.8) and `MPolyfold.tangentDeterminedSmooth`
  (`Chapter7/ZhouFacts.lean`).
* **§7.4 with (ZHOU) as the only hypothesis** (rows V7.90, V7.91, V7.94, V7.102 lose
  `SmoothRegular` and `DenseSmoothTangent`): `proposition_7_4_8_unconditional`
  ((ZHOU) ⇔ (ZHOU')), `proposition_7_4_10_of_isZhou` ((ZHOU) ⇒ (LUC)),
  `isSmoothUC_of_isZhou'`, `isVSLUC_of_isZhou'`, `corollary_7_4_11_of_isZhou`,
  `proposition_7_4_22_of_isZhou` ((ZHOU) ⇒ (LR)), `corollary_7_6_8_of_isZhou'`
  (Corollary 7.6.8 under (ZHOU) alone, row V7.83); for every `X^i`:
  `EP.proposition_7_4_9_of_isZhou`, `EP.corollary_7_4_11_all_of_isZhou`,
  `EP.theorem_7_4_13_all_of_isZhou` ((ZHOU) ⇒ (SLUC)),
  `EP.theorem_7_4_24_all_of_isZhou` ((ZHOU) ⇒ (SLR)).
* **Proposition 8.1.17 with no hypothesis beyond LUC/SLUC** (rows V8.45, V8.52):
  `nonEffectivePart_tangent_eq_of_isLUC`, `proposition_8_1_17_one_of_isLUC`,
  `EP.proposition_8_1_17_two_of_isSLUC`, `EP.isLUC_tangent_lift_of_isSLUC`,
  `EP.proposition_8_1_17_two_all_of_isSLUC`.
* **`EpGroupoid.Examples.JumpingRetract.not_isZhou_unconditional`**: the example of Appendix 7.6.3
  fails (ZHOU), with no hypothesis (row V7.95; 2021 p. 331).

## What the text leaves implicit, and the choices made

* The text takes the four Part I facts for granted; here each is a theorem, proved in the files
  named above, and `SmoothRegular` is kept as the bundle for the proofs of §7.4.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The Part I facts of 2021 §7.4 (gap G.85)**: every M-polyfold satisfies `SmoothRegular`:
`X_∞` is dense in every `X_m`, `U ∩ X_∞` is connected for connected open `U`, `p : TX → X¹` is
open, and sc-smooth maps agreeing near a smooth point have the same tangent there. -/
theorem smoothRegular : P.SmoothRegular :=
  ⟨P.denseSmooth, P.smoothConnected, P.isOpenMap_tangentProj, P.tangentDeterminedSmooth⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### §7.4 with (ZHOU) as the only hypothesis -/

/-- **2021 Proposition 7.4.8, p. 332 (new in the 2021 edition)**: (ZHOU) ⇔ (ZHOU'), with no
hypothesis (row V7.90). -/
theorem proposition_7_4_8_unconditional : X.IsZhou ↔ X.IsZhou' :=
  X.proposition_7_4_8 X.PObj.smoothRegular X.PObj.denseSmoothTangent

/-- **2021 Proposition 7.4.10, p. 333 (new in the 2021 edition)**: (ZHOU) ⇒ (LUC), with no
Part I hypothesis (row V7.90). -/
theorem proposition_7_4_10_of_isZhou (hZ : X.IsZhou) : X.IsLUC :=
  X.proposition_7_4_10 X.PObj.smoothRegular hZ

/-- (ZHOU) gives unique continuation through `X_∞`, with no Part I hypothesis. -/
theorem isSmoothUC_of_isZhou' (hZ : X.IsZhou) : X.IsSmoothUC :=
  X.isSmoothUC_of_isZhou X.PObj.smoothRegular hZ

/-- (ZHOU) ⇒ (VSLUC), with no Part I hypothesis. -/
theorem isVSLUC_of_isZhou' (hZ : X.IsZhou) : X.IsVSLUC :=
  X.isVSLUC_of_isZhou X.PObj.smoothRegular hZ

/-- **2021 Corollary 7.4.11, p. 334 (new in the 2021 edition), for `X⁰` and `X¹`**: (ZHOU)
gives (LUC) for `X` and for `X¹`, with no Part I hypothesis (row V7.90). -/
theorem corollary_7_4_11_of_isZhou (hZ : X.IsZhou) : X.IsLUC ∧ X.liftOne.IsLUC :=
  X.corollary_7_4_11 X.PObj.smoothRegular hZ

/-- **2021 Proposition 7.4.22, p. 338 (new in the 2021 edition)**: (ZHOU) ⇒ (LR), with no
Part I hypothesis (row V7.94). -/
theorem proposition_7_4_22_of_isZhou (hZ : X.IsZhou) : X.IsLR :=
  X.proposition_7_4_22 X.PObj.smoothRegular hZ

/-- **2021 Corollary 7.6.8, p. 351, for `i = 1` and as sets**, under (ZHOU) alone (row V7.83). -/
theorem corollary_7_6_8_of_isZhou' (hZ : X.IsZhou) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 :=
  X.corollary_7_6_8_of_isZhou hZ X.PObj.smoothRegular X.hasConnectedDenseLevelOneReps

/-! ### Proposition 8.1.17 without added hypotheses -/

/-- `(T𝐗)^T = p⁻¹((𝐗¹)^T)` under (LUC) for `X¹`, with no further hypothesis. -/
theorem nonEffectivePart_tangent_eq_of_isLUC (h : X.liftOne.IsLUC) :
    X.tangentEpGroupoid.nonEffectivePart = X.PMor.tangentProj ⁻¹' X.liftOne.nonEffectivePart :=
  X.nonEffectivePart_tangent_eq h X.hasConnectedDenseLevelOneReps X.PMor.isOpenMap_tangentProj

/-- **2021 Proposition 8.1.17 (1), p. 371 (new in the 2021 edition)**: if `X¹` has (LUC), so has
`TX`; with no further hypothesis (row V8.45). -/
theorem proposition_8_1_17_one_of_isLUC (h : X.liftOne.IsLUC) :
    X.tangentEpGroupoid.IsLUC :=
  X.proposition_8_1_17_one h X.hasConnectedDenseLevelOneReps X.PMor.isOpenMap_tangentProj

end EpGroupoid

namespace EP

open EpGroupoid

/-- **2021 Proposition 7.4.9, p. 333 (new in the 2021 edition)**: (ZHOU) for `X` gives (ZHOU) for
every `X^i`, with no Part I hypothesis (row V7.102). -/
theorem proposition_7_4_9_of_isZhou (A : EP.{u}) (hZ : A.X.IsZhou) (i : ℕ) :
    (A.lift i).X.IsZhou :=
  A.proposition_7_4_9 hZ A.X.PObj.denseSmoothTangent
    (fun i => (A.lift i).X.PObj.smoothRegular) i

/-- **2021 Corollary 7.4.11, p. 334 (new in the 2021 edition)**: under (ZHOU) every `X^i` has
(LUC), with no Part I hypothesis (row V7.102). -/
theorem corollary_7_4_11_all_of_isZhou (A : EP.{u}) (hZ : A.X.IsZhou) (i : ℕ) :
    (A.lift i).X.IsLUC :=
  A.corollary_7_4_11_all hZ A.X.PObj.denseSmoothTangent
    (fun i => (A.lift i).X.PObj.smoothRegular) i

/-- **2021 Theorem 7.4.13, p. 334 (new in the 2021 edition)**: (ZHOU) ⇒ (SLUC), with no Part I
hypothesis (rows V7.91, V7.102). -/
theorem theorem_7_4_13_all_of_isZhou (A : EP.{u}) (hZ : A.X.IsZhou) : A.IsSLUC :=
  A.theorem_7_4_13_all hZ A.X.PObj.denseSmoothTangent fun i => (A.lift i).X.PObj.smoothRegular

/-- **2021 Theorem 7.4.24, p. 340 (new in the 2021 edition)**: (ZHOU) ⇒ (SLR), with no Part I
hypothesis (rows V7.94, V7.102). -/
theorem theorem_7_4_24_all_of_isZhou (A : EP.{u}) (hZ : A.X.IsZhou) : A.IsSLR :=
  A.theorem_7_4_24_all hZ A.X.PObj.denseSmoothTangent fun i => (A.lift i).X.PObj.smoothRegular

/-- **2021 Proposition 8.1.17 (2), p. 371, for `(TX)⁰`**: (SLUC) for `X` gives (LUC) for `TX`,
with no further hypothesis (row V8.45). -/
theorem proposition_8_1_17_two_of_isSLUC (A : EP.{u}) (h : A.IsSLUC) :
    A.X.tangentEpGroupoid.IsLUC :=
  A.X.proposition_8_1_17_one_of_isLUC (h 1)

/-- Under (SLUC) every `T(X^i)` has (LUC), with no further hypothesis (row V8.52). -/
theorem isLUC_tangent_lift_of_isSLUC (A : EP.{u}) (h : A.IsSLUC) (i : ℕ) :
    (A.lift i).X.tangentEpGroupoid.IsLUC :=
  A.isLUC_tangent_lift h (fun i => (A.lift i).X.hasConnectedDenseLevelOneReps)
    (fun i => (A.lift i).X.PMor.isOpenMap_tangentProj) i

/-- **2021 Proposition 8.1.17 (2), p. 371 (new in the 2021 edition)**: if `X` has (SLUC), so
has `TX`; with no further hypothesis (row V8.52). -/
theorem proposition_8_1_17_two_all_of_isSLUC (A : EP.{u}) (h : A.IsSLUC) :
    A.tangentEP.IsSLUC :=
  A.proposition_8_1_17_two_all h (fun i => (A.lift i).X.hasConnectedDenseLevelOneReps)
    fun i => (A.lift i).X.PMor.isOpenMap_tangentProj

end EP

namespace EpGroupoid.Examples.JumpingRetract

/-- **2021 p. 331**: the ep-groupoid of Appendix 7.6.3 (our `JumpingRetract.X`) does not satisfy
(ZHOU), with no hypothesis: it does not have (LUC) (`JumpingRetract.not_isLUC`), and (ZHOU) ⇒
(LUC) (row V7.95). -/
theorem not_isZhou_unconditional : ¬ X.IsZhou :=
  not_isZhou X.PObj.smoothRegular

end EpGroupoid.Examples.JumpingRetract

end Polyfold
