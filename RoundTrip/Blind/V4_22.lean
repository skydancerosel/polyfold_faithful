import Polyfold
/-! Blind formalization of V4_22 (the text's §4.1, Lemma 4.12, pp. 154–155, in the proof of
Proposition 4.9).

Text: let `f(a + δ(a)) = 0` and `|a|_0 < ε`; if `ε` is small, `a + δ(a) ∈ O`.

Choices:
- The item does not define `f` and `δ`; they come from the proof of Proposition 4.9.  Setting,
  `f` and `δ` exactly as in my V4_21 (same prelude): `E : ScBanach` (levels in `Type`), `C ⊆ E₀`,
  `t : U → U` an sc-smooth retraction (`ScRetraction E C`) which is an sc⁺-retraction
  (`IsScPlusRetractionB`, Definition 4.4, copied from my V4_9) onto `O = t(U) ∋ 0`;
  `N = T_0O = Dt(0)E` (range of `scDeriv t.U t.toFun 0`), in good position to `C` (Definition
  3.21) with good complement `Y` (an sc-complement with the `ε`-cone condition); `p` the continuous
  projection onto `N` along `Y` (READING of "the sc-projection"; the item V4_20 writes
  `p = Dt(0)`, which differs unless `Y = ker Dt(0)`).
- `f(x) = (1 − p)(x − t(x))` on `U` (`fB`; READING reconstructed from item V4_19's contraction
  `y ↦ (1 − p)t(a + y)`); `f = 0` on `O`, and the lemma says the zeros `a + δ(a)` are in `O`.
- `δ`: B quantifies over EVERY map with the properties of the text's solution germ
  (`IsSolutionB`): `δ(a) → 0` as `a → 0` in `T_0O ∩ C`, `δ(0) = 0`, and for `a ∈ T_0O ∩ C` near
  `0`: `δ(a) ∈ Y`, `a + δ(a) ∈ U`, `f(a + δ(a)) = 0`.
- The claim: there is `ε > 0` such that for `a ∈ T_0O ∩ C` (the domain `V` of `δ`; needed since
  `δ(a)` is only specified there) with `|a|₀ < ε`, `a + δ(a) ∈ U` and `f(a + δ(a)) = 0` (both
  automatic for small `a`, kept as in the text), `a + δ(a) ∈ O = t(U)` (`t.retract`).
- Nothing looks false to me under these readings.
-/
namespace RoundTrip.V4_22
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

/-- Lemma 4.12 (existence): for small `a ∈ T_0O ∩ C`, the zero `a + δ(a)` of `f` lies in `O`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (t : ScRetraction E C) (Y : Submodule ℝ (E.lvl 0))
    (p : E.lvl 0 →L[ℝ] E.lvl 0) (δ : E.lvl 0 → E.lvl 0),
    IsSetting49B t Y p → IsSolutionB t Y p δ →
      ∃ ε > (0 : ℝ), ∀ a ∈ tangentAtZero t, a ∈ C → ‖a‖ < ε →
        a + δ a ∈ t.U → fB t p (a + δ a) = 0 → a + δ a ∈ t.retract

end RoundTrip.V4_22
