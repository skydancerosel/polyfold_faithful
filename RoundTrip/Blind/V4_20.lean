import Polyfold
/-! Blind formalization of V4_20 (the text's §4.1, Proposition 4.9, p. 150).

Text: let `t : U → U` be an sc⁺-retraction onto `O ∋ 0` with `T_0O` in good position to `C`, `Y`
a good complement, `E = T_0O ⊕ Y`, and `p = Dt(0) : E → T_0O` "the sc-projection".  There are
open neighbourhoods `U` of `0` in `O` and `V` of `0` in `T_0O ∩ C` such that `p : U → V` is an
sc-diffeomorphism; `(V, T_0O ∩ C, T_0O)` is a local model.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`, and
  `t : ScRetraction E C` (checked with `#print`: `U` relatively open in the partial quadrant `C`,
  `t` sc-smooth on `U`, `t ∘ t = t` on `U`).  "sc⁺-retraction" (Definition 4.4): `t.IsScPlus`
  (checked: `t(U) ⊆ E₁` and the lift `U → E¹` is sc-smooth).  `O = t(U)` (`t.retract`), `0 ∈ O`.
- `T_0O = Dt(0)E`: the range of `scDeriv t.U t.toFun 0` (the derivative of `t` at the level-1
  point `0`, from the definition of sc¹; unique there).  It is the fibre over `0` of `Tt(TU)`
  (Definition 2.17), since `Dt(y) = Dt(0) Dt(y)` when `t(y) = 0`.
- "the sc-projection `p`": I follow the item literally, `p = Dt(0)`, viewed as a map
  `E₀ → T_0O`.  AMBIGUITY: the phrase "`Y` a good complement, `E = T_0O ⊕ Y`, … the
  sc-projection" could also mean the projection onto `T_0O` along `Y`, which differs from `Dt(0)`
  unless `ker Dt(0) = Y`.  I chose `Dt(0)` because the item says `p = Dt(0)` explicitly; then `Y`
  enters only through the hypothesis that a good complement exists.
- "in good position" (Definition 3.21): my own `IsGoodPositionB` — `N ∩ C` has nonempty interior
  in `N`, and `N` has a good complement `Y` which is an sc-complement (`E.IsScSplitting N Y`,
  checked: both sc-subspaces and complementary on every level) with an `ε > 0` such that
  `|y|₀ ≤ ε|n|₀` implies `n ∈ C ↔ n + y ∈ C`.  I did not use the project's `IsInGoodPosition`,
  whose complement is only algebraic (a weaker hypothesis than the text's, hence a stronger B).
- `T_0O` as an sc-space: the sc-structure induced from `E` (`E.ofSubspace hN`, levels
  `T_0O ∩ E_m`), for `hN : E.IsScSubspace T_0O` which B asserts (it is presupposed by "the local
  model `(V, T_0O ∩ C, T_0O)`"; `T_0O` is in fact finite-dimensional).  `T_0O ∩ C` is the set
  `NC` of its points lying in `C`.
- "open neighbourhood `U` of `0` in `O`": `O ∩ W` with `W` open in `E₀`, `0 ∈ W`.  "open
  neighbourhood `V` of `0` in `T_0O ∩ C`" and "`(V, T_0O ∩ C, T_0O)` is a local model": `0 ∈ V`,
  `IsRelOpenInQuadrant (E.ofSubspace hN) NC V` (checked: `NC` is a partial quadrant of `T_0O` and
  `V` is relatively open in it) and `IsScRetract` of `(V, NC, T_0O)`.
- "`p : U → V` is an sc-diffeomorphism": a map `p' : E₀ → (T_0O)₀` with underlying values
  `Dt(0)x`, and `q : (T_0O)₀ → E₀`, mutually inverse on `O ∩ W` and `V`, both sc-smooth maps
  between the retracts `(O ∩ W, C, E)` and `(V, NC, T_0O)` (Definition 2.7): the project's
  `IsScSmoothRetractMap` (checked: `f(O) ⊆ O'` and `f ∘ r` sc-smooth for EVERY retraction `r`
  onto the source; as a conclusion this is the strong form), with `(O ∩ W, C, E)` asserted to be a
  retract so that this is not vacuous.
- Nothing looks false to me (with `p = Dt(0)`: `Dt(0)` maps `C` into `C`, so it maps `O` into
  `T_0O ∩ C`; whether it is onto a neighbourhood relies on the good-position hypothesis).
-/
namespace RoundTrip.V4_20
open Polyfold

/-- `T_0O = Dt(0)E`, the range of the derivative of the retraction at `0`. -/
noncomputable def tangentAtZero {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C) :
    Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv t.U t.toFun 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Definition 3.21 with an sc-complement: `N ∩ C` has nonempty interior in `N`, and `N` has an
sc-complement `Y` with `n ∈ C ↔ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodPositionB (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior ((Subtype.val : N → E.lvl 0) ⁻¹' C)).Nonempty ∧
    ∃ Y : Submodule ℝ (E.lvl 0), E.IsScSplitting N Y ∧
      ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + y ∈ C)

/-- Proposition 4.9: near `0`, `Dt(0)` is an sc-diffeomorphism from the sc⁺-retract `O` onto a
relatively open neighbourhood of `0` in the partial quadrant `T_0O ∩ C` of `T_0O`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (t : ScRetraction E C),
    t.IsScPlus → (0 : E.lvl 0) ∈ t.retract → IsGoodPositionB E C (tangentAtZero t) →
      ∃ hN : E.IsScSubspace (tangentAtZero t),
        ∃ W : Set (E.lvl 0), IsOpen W ∧ (0 : E.lvl 0) ∈ W ∧
        ∃ V : Set ((E.ofSubspace hN).lvl 0), (0 : (E.ofSubspace hN).lvl 0) ∈ V ∧
          -- `(V, T_0O ∩ C, T_0O)` is a local model, `V` relatively open in `T_0O ∩ C`
          IsRelOpenInQuadrant (E.ofSubspace hN) {v | Subtype.val v ∈ C} V ∧
          IsScRetract (E.ofSubspace hN) {v | Subtype.val v ∈ C} V ∧
          -- `p = Dt(0) : O ∩ W → V` is an sc-diffeomorphism
          ∃ (p : E.lvl 0 → (E.ofSubspace hN).lvl 0) (q : (E.ofSubspace hN).lvl 0 → E.lvl 0),
            (∀ x, Subtype.val (p x) = scDeriv t.U t.toFun 0 x) ∧
            IsScRetract E C (t.retract ∩ W) ∧
            IsScSmoothRetractMap E C (t.retract ∩ W)
              (E.ofSubspace hN) {v | Subtype.val v ∈ C} V p ∧
            IsScSmoothRetractMap (E.ofSubspace hN) {v | Subtype.val v ∈ C} V
              E C (t.retract ∩ W) q ∧
            (∀ x ∈ t.retract ∩ W, q (p x) = x) ∧ (∀ v ∈ V, p (q v) = v)

end RoundTrip.V4_20
