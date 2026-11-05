import Polyfold
/-! Blind formalization of V3_33 (the text's §3.4, Definition 3.37, p. 90). Choices:
- This item is a definition.  Setting: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant
  sc-structures), the parameter set is literally the text's `[0, ∞)^k ⊕ ℝ^{n−k}` (`stdQuadrant n k`,
  the first `k` coordinates nonnegative, with `k ≤ n`), `W` an arbitrary sc-Banach space; the
  domain space `[0,∞)^k ⊕ ℝ^{n−k} ⊕ W` is the set `stdQuadrant n k × W` in
  `ScBanach.paramProd (Fin n → ℝ) W`, the target `ℝᴺ ⊕ W` is `ScBanach.paramProd (Fin N → ℝ) W`.
  No universe choices arise.
- "a germ `f : O(…, 0) → (ℝᴺ ⊕ W, 0)`": a germ of neighbourhoods `G` (Definition 3.1, project
  `ScNbhdGerm`) and a map `f` with `f(0) = 0`; "sc-smooth germ": `IsScSmoothGerm G f`
  (Definition 3.2).
- "`P_W ∘ f` is an sc⁰-contraction germ" (`P_W : ℝᴺ ⊕ W → W` the projection): the text's
  Definition 3.28, restated here as in my blind V3_25 (`IsSc0ContractionGermText`, not the
  project's definition), applied to `B(a, w) = w − P_W f(a, w)`, so that `P_W ∘ f = w − B(a, w)`:
  `P_W ∘ f` an sc⁰-germ vanishing at `0`, and for all `ε > 0`, `m`, the estimate
  `|B(a, w) − B(a, w')|_m ≤ ε|w − w'|_m` for `(a, w), (a, w')` in `U_m` near `(0, 0)` on level `m`
  (level-`m` values written without junk).
- "`𝔠_basic` is the class of basic germs": the class of all `(G, f)` (for all `n, k, N, W`)
  satisfying `IsBasicGermText`; `B` characterizes membership.
- B states the definition as a characterization of the project's `IsBasicGerm` (Definition 3.7,
  which carries the contraction map `B` as an extra argument, hence `∃ B`), on the text's parameter
  sets `[0, ∞)^k ⊕ ℝ^{n−k}`.  The definition asserts no further property.
-/
namespace RoundTrip.V3_33
open Polyfold

/-- The standard partial quadrant `[0, ∞)^k ⊕ ℝ^{n−k} ⊆ ℝⁿ`. -/
def stdQuadrant (n k : ℕ) : Set (Fin n → ℝ) := {a | ∀ i : Fin n, (i : ℕ) < k → 0 ≤ a i}

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

/-- **Definition 3.37** (text): `f : O([0,∞)^k ⊕ ℝ^{n−k} ⊕ W, 0) → (ℝᴺ ⊕ W, 0)` is a basic germ:
an sc-smooth germ with `f(0) = 0` such that `P_W ∘ f` is an sc⁰-contraction germ. -/
def IsBasicGermText {n k N : ℕ} {W : ScBanach}
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (stdQuadrant n k ×ˢ Set.univ))
    (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0) : Prop :=
  IsScSmoothGerm (F := ScBanach.paramProd (Fin N → ℝ) W) G f ∧ f 0 = 0 ∧
    IsSc0ContractionGermText (stdQuadrant n k) G (fun x => x.2 - (f x).2)

/-- Definition 3.37: on the parameter sets `[0, ∞)^k ⊕ ℝ^{n−k}`, the project's basic germs
(`IsBasicGerm` for some contraction map) are exactly the text's basic germs (the class
`𝔠_basic`). -/
def B : Prop :=
  ∀ (n k N : ℕ) (W : ScBanach)
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (stdQuadrant n k ×ˢ Set.univ))
    (f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0),
    k ≤ n →
      ((∃ Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0, IsBasicGerm (stdQuadrant n k) G f Bm) ↔
        IsBasicGermText G f)

end RoundTrip.V3_33
