import Polyfold.Chapter11.GapP2_B2_OrbitForms
import Polyfold.Chapter10.LocalizationLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2, p. 720 (before Definition 16.2.5): the push-forward `h_*ω` of an sc-form along a
generalized isomorphism `h` with `α' ∘ |h| = α` "does not depend on `h`".  Numbers and pages are
the 2021 text's.

# Push-forwards of forms depend only on the orbit map

## The text, paraphrased

(p. 720) For polyfold structures `(X, α)`, `(X', α')` of `(Z, c)` there is a generalized
isomorphism `h : X → X'` with `α' ∘ |h| = α` (16.6); `h_*ω` does not depend on `h` provided (16.6)
holds; the same for pull-backs.

## What is formalized

This is Proposition 11.2.9 (`EPLoc.formsPush_eq_of_orbitMap_eq`, `formsPullback_eq_of_orbitMap_eq`,
`GapP2_B2_OrbitForms.lean`, (LR) for the target).  Here only the form used in Chapter 16:
**`EPLoc.formsPush_eq_of_orbitMap_eq_or`**, with (LR) for source or target (Proposition 10.3.16
moves it), and the pull-back analogue.  For polyfold structures (ZHOU) gives (LR), so no hypothesis
is added; `h = h'` itself may fail (`not_theorem_10_3_19`, `not_lemma_16_2_1`).
-/

set_option maxSynthPendingDepth 3

open CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}}

/-- **2021 p. 720 (Proposition 11.2.9)**: generalized isomorphisms `h, h' : X → Y` with
`|h| = |h'|` have `h_* = h'_*` on `Ωᵏ_{ep,∞}`, if `X` or `Y` has (LR). -/
theorem formsPush_eq_of_orbitMap_eq_or (hLR : X.X.IsLR ∨ Y.X.IsLR) {h h' : of X ⟶ of Y}
    (hh : IsGeneralizedIso h) (hh' : IsGeneralizedIso h') (heq : orbitMap h = orbitMap h')
    (k : ℕ) : formsPush h hh k = formsPush h' hh' k :=
  formsPush_eq_of_orbitMap_eq h h' hh hh' heq (hLR.elim (proposition_10_3_16 hh).1 id) k

/-- The pull-back analogue of `formsPush_eq_of_orbitMap_eq_or`. -/
theorem formsPullback_eq_of_orbitMap_eq_or (hLR : X.X.IsLR ∨ Y.X.IsLR) {h h' : of X ⟶ of Y}
    (hh : IsGeneralizedIso h) (hh' : IsGeneralizedIso h') (heq : orbitMap h = orbitMap h')
    (k : ℕ) : formsPullback h k = formsPullback h' k :=
  formsPullback_eq_of_orbitMap_eq h h' hh hh' heq (hLR.elim (proposition_10_3_16 hh).1 id) k

end EPLocalization.EPLoc

end Polyfold
