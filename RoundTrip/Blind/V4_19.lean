import Polyfold
/-! Blind formalization of V4_19 (the text's §4.1, proofs of Lemmas 4.11, 4.12, (76)–(77),
pp. 154–155).

Text: since `t` is sc⁺, `u ↦ (1 − p)t(u)` is `C^1` between the `1`-levels;
`‖(1 − p)Dt(u)‖_{L(E_1)} ≤ 1/2` for `|u|_1 < ε_1`, and the differences of `t` are written as
integrals of `Dt` along segments.

Choices:
- Setting (Proposition 4.9 and the proofs of Lemmas 4.11, 4.12; same prelude as my V4_21):
  `E : ScBanach` (levels in `Type`), `C ⊆ E₀`, `t : U → U` an sc-smooth retraction
  (`ScRetraction E C`) which is an sc⁺-retraction (`IsScPlusRetractionB`, Definition 4.4, copied
  from my V4_9) onto `O = t(U) ∋ 0`; `N = T_0O = Dt(0)E` (range of `scDeriv t.U t.toFun 0`) in
  good position to `C` (Definition 3.21) with good complement `Y` (an sc-complement with the
  `ε`-cone condition); `p` the continuous projection onto `N` along `Y` (READING of "the
  sc-projection"; the item V4_20 writes `p = Dt(0)`, which differs unless `Y = ker Dt(0)`; for the
  present claims both readings work, since `(1 − p)Dt(0) = 0` either way).  The good-position
  hypotheses are not needed for these claims; they are the setting of the proofs and are kept.
- "Between the `1`-levels": `U₁ = U ∩ E₁` as a subset of `E₁` (`E.lvlSet t.U 1`, relatively open
  in the partial quadrant `C ∩ E₁` of `E₁`), maps `E₁ → E₁` given on `U₁` by `t` and by
  `(1 − p) ∘ t` (`g`, `h`; values off `U₁` irrelevant; they exist since `t(U) ⊆ E₁` and `p` maps
  into `N ⊆ E₁`).  "`C^1`": Mathlib's `ContDiffOn ℝ 1 · U₁` (derivatives within `U₁`; unique
  there, `U₁` being relatively open in a convex set with nonempty interior).
- `Dt(u)`, `u ∈ U₁`: the derivative of `t : U₁ → E₁` within `U₁`, `fderivWithin ℝ g U₁ u`, an
  element of `L(E₁)`; `(1 − p)Dt(u)` is the derivative of `h`, `fderivWithin ℝ h U₁ u` (chain rule,
  `1 − p` linear on `E₁`).  "`|u|₁ < ε₁`": `‖u‖ < ε₁` in `E₁`; B asserts `∃ ε₁ > 0`.
- "Differences of `t` are integrals of `Dt` along segments": for `u, v ∈ E₁` whose segment lies in
  `U₁`, `t(v) − t(u) = ∫₀¹ Dt(u + s(v − u))(v − u) ds` in `E₁` (interval integral).  Read on level
  `1`, where the estimate is used; applying `ι₁` gives the level-`0` version.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_19
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

/-- Proofs of Lemmas 4.11, 4.12: on level `1`, `t` and `u ↦ (1 − p)t(u)` are `C¹` on `U₁`;
`‖(1 − p)Dt(u)‖_{L(E₁)} ≤ 1/2` for `|u|₁ < ε₁`; and differences of `t` along segments in `U₁` are
integrals of `Dt`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (t : ScRetraction E C) (Y : Submodule ℝ (E.lvl 0))
    (p : E.lvl 0 →L[ℝ] E.lvl 0), IsSetting49B t Y p →
      ∃ g h : E.lvl 1 → E.lvl 1,
        -- `g = t` and `h = (1 − p) ∘ t` on `U₁`, as maps between the `1`-levels
        (∀ u ∈ E.lvlSet t.U 1, E.toBase 1 (g u) = t.toFun (E.toBase 1 u)) ∧
        (∀ u ∈ E.lvlSet t.U 1,
          E.toBase 1 (h u) = t.toFun (E.toBase 1 u) - p (t.toFun (E.toBase 1 u))) ∧
        -- both are `C¹` between the `1`-levels
        ContDiffOn ℝ 1 g (E.lvlSet t.U 1) ∧ ContDiffOn ℝ 1 h (E.lvlSet t.U 1) ∧
        -- `‖(1 − p)Dt(u)‖_{L(E₁)} ≤ 1/2` for `|u|₁ < ε₁`
        (∃ ε₁ > (0 : ℝ), ∀ u ∈ E.lvlSet t.U 1, ‖u‖ < ε₁ →
          ‖fderivWithin ℝ h (E.lvlSet t.U 1) u‖ ≤ 1 / 2) ∧
        -- differences of `t` are integrals of `Dt` along segments
        (∀ u v : E.lvl 1, segment ℝ u v ⊆ E.lvlSet t.U 1 →
          g v - g u =
            ∫ s in (0 : ℝ)..1, fderivWithin ℝ g (E.lvlSet t.U 1) (u + s • (v - u)) (v - u))

end RoundTrip.V4_19
