import Polyfold.Chapter10.EquivalenceLR
import Polyfold.Chapter10.LocalizationProperties

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.3 (pp. 492–495): **Proposition 10.3.16** (p. 492) and **Theorem
10.3.21** (p. 495) in full, both new in the 2021 edition.  Numbers and pages are the 2021 text's.
The parts of Theorem 10.3.21 for (LUC), (SLUC), (ZHOU) are `EPLoc.theorem_10_3_21` in
`LocalizationProperties.lean`; Theorem 10.3.19 is treated in `LocalizationLRCounterexample.lean`.

# (LR) and (SLR) under generalized isomorphisms

## The text, paraphrased

(Proposition 10.3.16) If `f : X → Y` is a generalized isomorphism and one of `X`, `Y` has the
local regularity property, so has the other.  *Proof* (text): `f` is represented by
`X ←F A →G Y` with `F`, `G` equivalences; apply Proposition 10.1.9 to `F` and to `G`.

(Theorem 10.3.21) The same holds for each of (LR), (LUC), (SLR), (SLUC), (ZHOU), by Propositions
10.1.9, 10.1.16, 10.1.17, 10.1.18 and 10.1.19.

## What is formalized (namespace `Polyfold.EPLocalization.EPLoc`)

* `proposition_10_3_16` (**Proposition 10.3.16**), from `EpFunctor.proposition_10_1_9`.
* `theorem_10_3_21_all` (**Theorem 10.3.21**, all five properties), with (SLR) from
  `EP.proposition_10_1_19`.

## What the text leaves implicit, and the choices made

* As in `LocalizationProperties.lean`, a representative `X ←F A →Φ Y` of a generalized
  isomorphism has `Φ` an equivalence by Theorem 10.3.10, and the invariance under equivalences is
  applied to `F` and `Φ` (`iff_of_isGeneralizedIso`).  The hypotheses are satisfiable: `𝟙` of any
  object is a generalized isomorphism, and the point ep-groupoid has (LR)
  (`Examples.pointLocReg`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization

namespace EPLoc

variable {X Y : EP.{u}}

/-- **2021 Proposition 10.3.16, p. 492 (new in the 2021 edition)**: if `f : X → Y` is a
generalized isomorphism, `X` has the local regularity property iff `Y` has it (Proposition
10.1.9). -/
theorem proposition_10_3_16 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    X.X.IsLR ↔ Y.X.IsLR :=
  iff_of_isGeneralizedIso (fun A => A.X.IsLR) (fun _ hF => EpFunctor.proposition_10_1_9 hF) hf

/-- **2021 Theorem 10.3.21, p. 495 (new in the 2021 edition)**, all five properties: if
`f : X → Y` is a generalized isomorphism, each of (LR), (LUC), (SLR), (SLUC), (ZHOU) holds for
`X` iff it holds for `Y` (Propositions 10.1.9, 10.1.16, 10.1.19, 10.1.18, 10.1.17). -/
theorem theorem_10_3_21_all {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    (X.X.IsLR ↔ Y.X.IsLR) ∧ (X.X.IsLUC ↔ Y.X.IsLUC) ∧ (X.IsSLR ↔ Y.IsSLR) ∧
      (X.IsSLUC ↔ Y.IsSLUC) ∧ (X.X.IsZhou ↔ Y.X.IsZhou) :=
  ⟨proposition_10_3_16 hf, (theorem_10_3_21 hf).1,
    iff_of_isGeneralizedIso EP.IsSLR (fun _ hF => EP.proposition_10_1_19 hF) hf,
    (theorem_10_3_21 hf).2.1, (theorem_10_3_21 hf).2.2⟩

end EPLoc

end EPLocalization

end Polyfold
