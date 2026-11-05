import Polyfold
/-! Blind formalization of V4_11 (the text's §4.1, Definition 4.6 and the remark after it,
pp. 148–149).

Text: `(O, C, E)` is an sc⁺-retract if there are a relatively open `U ⊆ C` and an
sc⁺-retraction `t : U → U` onto `O`; by Lemma 4.5 this is intrinsic.

Choices:
- This item is a definition plus a property.  B is the conjunction of: the project's
  `IsScPlusRetract E C O` agrees with my `IsScPlusRetractB E C O`; and "intrinsic": if `(O, C, E)`
  is an sc⁺-retract then EVERY sc-smooth retraction (of a relatively open subset of `C`) onto `O`
  is an sc⁺-retraction (the content of Lemma 4.5 that the remark invokes).
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C O ⊆ E₀`.  "A relatively
  open `U ⊆ C` and a retraction `t : U → U`": an sc-smooth retraction `t : ScRetraction E C`
  (Definition 2.1, audited in V2_1; the structure carries `U` relatively open in the partial
  quadrant `C`); "onto `O`": `t(U) = O` (`ScRetraction.retract`).  The text presupposes that
  `(O, C, E)` is an sc-smooth retract; this follows from the existence of `t`.
- "sc⁺-retraction" (Definition 4.4): my own `IsScPlusRetractionB` (copied from my V4_9):
  `t(U_m) ⊆ U_{m+1}` for all `m`, and a lift `g : E₀ → E₁` of `t` on `U` is sc-smooth on `U` as
  a map into the shifted space `E¹` (`IsScSmooth` with target `E.shift`).
- Compared with the project's `IsScPlusRetract` (checked with `#print`: `∃ R, R.retract = O ∧
  R.IsScPlus`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_11
open Polyfold

/-- Definition 4.4: the sc-smooth retraction `r : U → U` is an sc⁺-retraction: `r(U_m) ⊆ U_{m+1}`
for every `m`, and a lift `U → E¹` of `r` is sc-smooth. -/
def IsScPlusRetractionB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  (∀ (m : ℕ) (x : E.lvl m), E.toBase m x ∈ R.U →
      ∃ y : E.lvl (m + 1), E.toBase (m + 1) y = R.toFun (E.toBase m x)) ∧
  ∃ g : E.lvl 0 → E.shift.lvl 0,
    (∀ x ∈ R.U, E.toBase 1 (g x) = R.toFun x) ∧ IsScSmooth (E := E) (F := E.shift) R.U g

/-- **Definition 4.6**: `(O, C, E)` is an **sc⁺-retract** if there is an sc⁺-retraction
`t : U → U` of a relatively open `U ⊆ C` onto `O`. -/
def IsScPlusRetractB (E : ScBanach) (C O : Set (E.lvl 0)) : Prop :=
  ∃ t : ScRetraction E C, t.retract = O ∧ IsScPlusRetractionB t

/-- Definition 4.6 (the project's `IsScPlusRetract` is the text's notion), and it is intrinsic:
on an sc⁺-retract every sc-smooth retraction onto `O` is an sc⁺-retraction. -/
def B : Prop :=
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScPlusRetract E C O ↔ IsScPlusRetractB E C O) ∧
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScPlusRetractB E C O →
    ∀ s : ScRetraction E C, s.retract = O → IsScPlusRetractionB s)

end RoundTrip.V4_11
