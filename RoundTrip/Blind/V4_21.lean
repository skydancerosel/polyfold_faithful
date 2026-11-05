import Polyfold
/-! Blind formalization of V4_21 (the text's §4.1, Lemma 4.11, p. 154, in the proof of
Proposition 4.9).

Text: let `f(a + y) = 0` with `|a|_0, |y|_0 < ε`; if `ε` is small, `y = δ(a)`.

Choices:
- The item does not define `f` and `δ`; they come from the proof of Proposition 4.9.  The setting
  (Proposition 4.9, cf. V4_20): `E : ScBanach` (levels in `Type`), `C ⊆ E₀`, `t : U → U` an
  sc-smooth retraction (`ScRetraction E C`, Definition 2.1) which is an sc⁺-retraction
  (`IsScPlusRetractionB`, Definition 4.4, copied from my V4_9) onto `O = t(U) ∋ 0`;
  `N = T_0O = Dt(0)E` (the range of `scDeriv t.U t.toFun 0`, as in V4_20), in good position to
  `C` (Definition 3.21): `N ∩ C` has nonempty interior in `N`, and `Y` is a good complement (an
  sc-complement, `E.IsScSplitting N Y`, with `ε > 0` such that `|y|₀ ≤ ε|n|₀` implies
  `n ∈ C ↔ n + y ∈ C`); `p : E₀ → E₀` the (continuous) projection onto `N` along `Y`.  All this is
  `IsSetting49B`.  READING of "the sc-projection `p`": the projection along `Y` (so that
  `E = T_0O ⊕ Y` and `a + y` match `p`); the item V4_20 writes `p = Dt(0)`, which differs unless
  `Y = ker Dt(0)`.  I chose the projection along `Y` because the lemmas decompose points as
  `a + y`, `a ∈ T_0O`, `y ∈ Y`.
- `f` (READING, reconstructed from item V4_19, which describes the contraction
  `y ↦ (1 − p)t(a + y)` used in these proofs): `f(x) = (1 − p)(x − t(x))` for `x ∈ U` (`fB`); so
  `f(a + y) = y − (1 − p)t(a + y)` for `a ∈ T_0O`, `y ∈ Y`, and `f = 0` on `O`.  This is what
  makes Lemma 4.12 (`f(a + δ(a)) = 0` implies `a + δ(a) ∈ O`) non-trivial.
- `δ`: the solution germ of `f(a + δ(a)) = 0` over `V = T_0O ∩ C` near `0` (from Chapter 3,
  Corollary 3.47 per item V4_24).  I do not reconstruct its construction; B quantifies over EVERY
  map `δ` with the properties the text's `δ` has (`IsSolutionB`): `δ(a) → 0` as `a → 0` in
  `T_0O ∩ C` (with `δ(0) = 0`), and for `a ∈ T_0O ∩ C` with `|a|₀ < ε₀`: `δ(a) ∈ Y`,
  `a + δ(a) ∈ U`, `f(a + δ(a)) = 0`.  (Any two such maps agree near `0`, so this is the text's
  `δ` near `0`.)
- The claim: there is `ε > 0` such that for all `a ∈ T_0O`, `y ∈ Y` with `|a|₀, |y|₀ < ε`,
  `a + y ∈ U` (the domain of `f`) and `f(a + y) = 0`, we have `y = δ(a)`.  I did NOT add
  `a ∈ C` (the text does not state it; it follows from `a + y ∈ C` and the good-complement
  estimate once `y` is small compared with `a`).  "If `ε` is small" is `∃ ε > 0` (the property
  is inherited by smaller `ε`).
- Nothing looks false to me under these readings.
-/
namespace RoundTrip.V4_21
open Polyfold

/-- Definition 4.4: the sc-smooth retraction `r : U → U` is an sc⁺-retraction: `r(U_m) ⊆ U_{m+1}`
for every `m`, and a lift `U → E¹` of `r` is sc-smooth. -/
def IsScPlusRetractionB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  (∀ (m : ℕ) (x : E.lvl m), E.toBase m x ∈ R.U →
      ∃ y : E.lvl (m + 1), E.toBase (m + 1) y = R.toFun (E.toBase m x)) ∧
  ∃ g : E.lvl 0 → E.shift.lvl 0,
    (∀ x ∈ R.U, E.toBase 1 (g x) = R.toFun x) ∧ IsScSmooth (E := E) (F := E.shift) R.U g

/-- `T_0O = Dt(0)E`, the range of the derivative of the retraction at `0`. -/
noncomputable def tangentAtZero {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C) :
    Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv t.U t.toFun 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- The setting of Proposition 4.9: `t` an sc⁺-retraction onto `O ∋ 0`, `T_0O` in good position
to `C` with good complement `Y` (an sc-complement), and `p` the projection onto `T_0O` along
`Y`. -/
def IsSetting49B {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C)
    (Y : Submodule ℝ (E.lvl 0)) (p : E.lvl 0 →L[ℝ] E.lvl 0) : Prop :=
  IsScPlusRetractionB t ∧ (0 : E.lvl 0) ∈ t.retract ∧
  (interior ((Subtype.val : tangentAtZero t → E.lvl 0) ⁻¹' C)).Nonempty ∧
  E.IsScSplitting (tangentAtZero t) Y ∧
  (∃ ε > (0 : ℝ), ∀ n ∈ tangentAtZero t, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + y ∈ C)) ∧
  (∀ n ∈ tangentAtZero t, p n = n) ∧ (∀ y ∈ Y, p y = 0)

/-- The map `f(x) = (1 − p)(x − t(x))` of the proof of Proposition 4.9. -/
def fB {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C) (p : E.lvl 0 →L[ℝ] E.lvl 0)
    (x : E.lvl 0) : E.lvl 0 :=
  (x - t.toFun x) - p (x - t.toFun x)

/-- `δ` is a solution germ of `f(a + δ(a)) = 0` over `T_0O ∩ C`: continuous at `0` with
`δ(0) = 0`, and near `0` in `T_0O ∩ C`, `δ(a) ∈ Y`, `a + δ(a) ∈ U` and `f(a + δ(a)) = 0`. -/
def IsSolutionB {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C)
    (Y : Submodule ℝ (E.lvl 0)) (p : E.lvl 0 →L[ℝ] E.lvl 0) (δ : E.lvl 0 → E.lvl 0) : Prop :=
  δ 0 = 0 ∧
  Filter.Tendsto δ (nhdsWithin 0 {a | a ∈ tangentAtZero t ∧ a ∈ C}) (nhds 0) ∧
  ∃ ε₀ > (0 : ℝ), ∀ a ∈ tangentAtZero t, a ∈ C → ‖a‖ < ε₀ →
    δ a ∈ Y ∧ a + δ a ∈ t.U ∧ fB t p (a + δ a) = 0

/-- Lemma 4.11 (uniqueness): small zeros `a + y` of `f` (`a ∈ T_0O`, `y ∈ Y`) lie on the graph
of `δ`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (t : ScRetraction E C) (Y : Submodule ℝ (E.lvl 0))
    (p : E.lvl 0 →L[ℝ] E.lvl 0) (δ : E.lvl 0 → E.lvl 0),
    IsSetting49B t Y p → IsSolutionB t Y p δ →
      ∃ ε > (0 : ℝ), ∀ a ∈ tangentAtZero t, ∀ y ∈ Y, ‖a‖ < ε → ‖y‖ < ε →
        a + y ∈ t.U → fB t p (a + y) = 0 → y = δ a

end RoundTrip.V4_21
