import Polyfold
/-! Blind formalization of V3_25 (the text's §3.3, Definition 3.28, p. 85). Choices:
- This item is a definition.  Setting: the text's `ℝⁿ` is read as an arbitrary finite-dimensional
  real normed space `P : Type` (with its unique, constant sc-structure `ScBanach.const P`; all
  norms on `P` are equivalent, so "sufficiently close" does not depend on the norm), `C̃ ⊆ P` a
  partial quadrant (`IsPartialQuadrant (ScBanach.const P) C̃`, Definition 1.11), `W` an arbitrary
  sc-Banach space, and `C̃ ⊕ W` is `ScBanach.paramProd P W` (levels `P × W_m`) with the set
  `C̃ × W`.  No universe choices arise (`P : Type`, sc-Banach spaces in `Type 1`).
- "an sc⁰-germ `f : O(C̃ ⊕ W, 0) → (W, 0)`": a germ of neighbourhoods
  `G : ScNbhdGerm (C̃ ⊕ W) (C̃ × W)` (Definition 3.1) and `f = w − B(a, w)` (`contractionMap B`)
  an sc⁰-germ on `G` (`IsSc0Germ`, Definition 3.2) with `f(0, 0) = 0` (the target `(W, 0)`).
- "for every `ε > 0`, `m ≥ 0`, `|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` for `(a, w), (a, w')` on
  level `m` sufficiently close to `(0, 0)`": for all `ε > 0` and `m` there is `r > 0` such that
  for `(a, w), (a, w')` in the level-`m` set `U_m` of the germ (the domain of `f` on level `m`)
  with `|a| < r`, `|w|_m < r`, `|w'|_m < r`, the level-`m` values satisfy the estimate.  The
  level-`m` values `B(a, w), B(a, w') ∈ W_m` are written without junk: for any `y, y' ∈ W_m`
  whose images in `W₀` are `B(a, w)`, `B(a, w')` (they exist because `f` is sc⁰, and are unique).
- B states the definition as a characterization of the project's `IsSc0ContractionGerm`
  (for partial quadrants `C̃`, as in the text).  The project definitions used inside the text's
  notion are `ScNbhdGerm`, `IsSc0Germ` (Definitions 3.1/3.2) and `contractionMap`.
- The title mentions the project's "working form" (`ContractionGerm`); the quoted statement only
  defines sc⁰-contraction germs and asserts no property, so nothing about the working form is
  claimed.
-/
namespace RoundTrip.V3_25
open Polyfold

/-- **Definition 3.28** (text): `f(a, w) = w − B(a, w)` is an sc⁰-contraction germ on the germ of
neighbourhoods `G` of `0` in `C̃ ⊕ W`: `f` is an sc⁰-germ with `f(0, 0) = 0`, and for every
`ε > 0` and level `m`, `|B(a, w) − B(a, w')|_m ≤ ε |w − w'|_m` for `(a, w), (a, w')` in `U_m`
close enough to `(0, 0)` on level `m`. -/
def IsSc0ContractionGermText {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {W : ScBanach} (Ct : Set P)
    (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0) : Prop :=
  IsSc0Germ (F := W) G (contractionMap Bm) ∧ contractionMap Bm (0, 0) = 0 ∧
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ r : ℝ, 0 < r ∧
    ∀ (a : P) (w w' : W.lvl m),
      ((a, w) : P × W.lvl m) ∈ G.U m → ((a, w') : P × W.lvl m) ∈ G.U m →
      ‖a‖ < r → ‖w‖ < r → ‖w'‖ < r →
      ∀ y y' : W.lvl m, W.toBase m y = Bm (a, W.toBase m w) →
        W.toBase m y' = Bm (a, W.toBase m w') →
        ‖y - y'‖ ≤ ε * ‖w - w'‖

/-- Definition 3.28: the project's `IsSc0ContractionGerm` is the text's sc⁰-contraction germ
(for a partial quadrant `C̃` in a finite-dimensional `P`). -/
def B : Prop :=
  ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0),
    IsPartialQuadrant (ScBanach.const P) Ct →
      (IsSc0ContractionGerm Ct G Bm ↔ IsSc0ContractionGermText Ct G Bm)

end RoundTrip.V3_25
