import Polyfold.Chapter2.Retracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 2, the statement
of Chapter 2 that the 2021 edition changes in substance: **Proposition 2.1.13** (p. 27; 2017:
Proposition 2.3; preprint: Proposition 2.6).

# Proposition 2.1.13 in the 2021 edition

## The text, paraphrased

(Proposition 2.1.13, p. 27) Let `(O, C, E)`, `(O', C', E')` be sc-smooth retracts, `f : O → O'` a
map, and `r : U → U`, `s : V → V` sc-smooth retractions onto `O`.  (1) If `f ∘ r : U → E'` is
sc-smooth, so is `f ∘ s`, and conversely.  (2) If `f ∘ r` is sc-smooth, then
`T(f ∘ r)|TO = T(f ∘ s)|TO`.  (3) **If `f ∘ r` is sc-smooth**, then `T(f ∘ r)|TO` maps `TO` into
`TO'`.  The 2017 and preprint statements of (3) have no hypothesis; the tangent map `T(f ∘ r)` is
only defined when `f ∘ r` is at least sc¹, and the proof of (3) (`ρ ∘ f ∘ r = f ∘ r` and the chain
rule, for a retraction `ρ` onto `O'`) uses it.

## What is formalized

* `Polyfold.proposition_2_1_13`: the three parts together, (3) under the 2021 hypothesis.
  The Lean statements of the preprint item, `proposition_2_1_13_one`, `proposition_2_1_13_two`,
  `proposition_2_1_13_three` (`Retracts.lean`), already carry the hypothesis "`f ∘ r` sc-smooth" in (3):
  the formalization had read (3) in the 2021 form from the start, and the 2021 change confirms
  that reading.  The proof is the conjunction of these three theorems.

## What the text leaves implicit, and the choices made

* `f : O → O'` is a total map `E₀ → E'₀` with `f(O) ⊆ O'` (the hypothesis `MapsTo f O O'`), as in
  `Retracts.lean`; the tangent `TO` of the retract is `Tr(TU)`, the tangent map is computed with
  the chosen sc-derivative (`tangentMap`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {f : E 0 → E' 0}

/-- **Proposition 2.1.13, p. 27** (2017: Proposition 2.3; preprint: Proposition 2.6), in the 2021
form: for sc-smooth retractions `r` (`R`), `s` (`S`) onto the same retract `O` and a retraction `ρ`
(`R'`) onto `O'`, with `f(O) ⊆ O'`:
(1) if `f ∘ r` is sc-smooth then `f ∘ s` is sc-smooth (and, exchanging the roles, conversely);
(2) if `f ∘ r` is sc-smooth then `T(f ∘ r) = T(f ∘ s)` on `TO`;
(3) **if `f ∘ r` is sc-smooth** then `T(f ∘ r)` maps `TO` into `TO'`. -/
theorem proposition_2_1_13 (R S : ScRetraction E C) (hRS : R.retract = S.retract)
    (R' : ScRetraction E' C') (hfO : MapsTo f R.retract R'.retract) :
    (IsScSmooth R.U (f ∘ R) ↔ IsScSmooth S.U (f ∘ S)) ∧
    (IsScSmooth R.U (f ∘ R) →
      EqOn (tangentMap R.U (f ∘ R)) (tangentMap S.U (f ∘ S)) R.tangent) ∧
    (IsScSmooth R.U (f ∘ R) → MapsTo (tangentMap R.U (f ∘ R)) R.tangent R'.tangent) :=
  ⟨⟨proposition_2_1_13_one R S hRS, proposition_2_1_13_one S R hRS.symm⟩,
    proposition_2_1_13_two R S hRS, fun hf => proposition_2_1_13_three R R' hf hfO⟩

end Polyfold
