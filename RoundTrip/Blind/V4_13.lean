import Polyfold
/-! Blind formalization of V4_13 (the text's §4.1, Proposition 4.8, p. 149).

Text: an sc-smooth retract `(O, C, E)` is an sc⁺-retract iff `O_0 = O_∞` and
`1_0^1 : O → O^1` is sc-smooth.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C O ⊆ E₀`.  "sc-smooth
  retract `(O, C, E)`" is the project's `IsScRetract E C O` (Definition 2.3, checked with
  `#print`: `∃ R : ScRetraction E C, R.retract = O`; `ScRetraction` carries `U` relatively open in
  the partial quadrant `C`).  It is a hypothesis; B is `IsScRetract E C O → (… ↔ …)`.
- "sc⁺-retract" (Definition 4.6): my own `IsScPlusRetractB` (copied from my V4_11): some
  sc-smooth retraction `t : U → U` onto `O` is an sc⁺-retraction in the sense of Definition 4.4
  (`IsScPlusRetractionB`, copied from V4_9: `t(U_m) ⊆ U_{m+1}` for all `m`, and a lift
  `g : E₀ → E₁` of `t` on `U` is sc-smooth on `U` into the shifted space `E¹`).
- "`O_0 = O_∞`": every `o ∈ O` lies on every level (`o` lifts along `E_m → E₀` for every `m`).
- `O^1` is the retract `(O_1, C_1, E^1)`, `O_1 = O ∩ E_1` and `C_1 = C ∩ E_1` as subsets of
  `(E¹)₀ = E₁` (`E.lvlSet O 1`, `E.lvlSet C 1`; `E.shift.lvl 0` is `E.lvl 1` by `rfl`).
  `1_0^1 : O → O^1` is the map `x ↦ x`, as a function `g : E₀ → E₁` with `ι₁ (g x) = x` on `O`
  (values off `O` irrelevant).  B asks the sc-smoothness for EVERY such lift `g`; when
  `O ⊆ E₁` lifts exist, and all agree on `O`, so this is the same as asking it for one.
- "sc-smooth" for a map between retracts (Definition 2.7): the project's `IsScSmoothRetractMap`
  (checked with `#print`: `g(O) ⊆ O'` and `g ∘ R` sc-smooth on `R.U` for EVERY sc-smooth
  retraction `R` onto `O`; by the text's Proposition 2.6 this is the same as for one `R`, and a
  retraction onto `O` exists since `(O, C, E)` is a retract).  The argument `C'` is unused by it.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_13
open Polyfold

/-- Definition 4.4: the sc-smooth retraction `r : U → U` is an sc⁺-retraction: `r(U_m) ⊆ U_{m+1}`
for every `m`, and a lift `U → E¹` of `r` is sc-smooth. -/
def IsScPlusRetractionB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  (∀ (m : ℕ) (x : E.lvl m), E.toBase m x ∈ R.U →
      ∃ y : E.lvl (m + 1), E.toBase (m + 1) y = R.toFun (E.toBase m x)) ∧
  ∃ g : E.lvl 0 → E.shift.lvl 0,
    (∀ x ∈ R.U, E.toBase 1 (g x) = R.toFun x) ∧ IsScSmooth (E := E) (F := E.shift) R.U g

/-- Definition 4.6: `(O, C, E)` is an **sc⁺-retract** if some sc⁺-retraction `t : U → U` of a
relatively open `U ⊆ C` has image `O`. -/
def IsScPlusRetractB (E : ScBanach) (C O : Set (E.lvl 0)) : Prop :=
  ∃ t : ScRetraction E C, t.retract = O ∧ IsScPlusRetractionB t

/-- Proposition 4.8: an sc-smooth retract `(O, C, E)` is an sc⁺-retract iff `O_0 = O_∞` and
`1_0^1 : O → O^1` is sc-smooth. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    (IsScPlusRetractB E C O ↔
      -- `O_0 = O_∞`
      ((∀ o ∈ O, ∀ m : ℕ, ∃ y : E.lvl m, E.toBase m y = o) ∧
      -- `1_0^1 : O → O^1` is sc-smooth
      ∀ g : E.lvl 0 → E.shift.lvl 0, (∀ x ∈ O, E.toBase 1 (g x) = x) →
        IsScSmoothRetractMap E C O E.shift (E.lvlSet C 1) (E.lvlSet O 1) g))

end RoundTrip.V4_13
