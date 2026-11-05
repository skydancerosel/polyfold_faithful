import Polyfold
/-! Blind formalization of V1_9 (the text's §1.1, Proposition 1.10, p. 10).

Text: let `E` and `F` be sc-Banach spaces.  If `T : E → F` is sc-Fredholm and `S : E → F` is an
sc⁺-operator, then `T + S` is sc-Fredholm.

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`).
- sc-Fredholm (Definition 1.8) is written out by hand (`IsScFredholmB`, the same prelude as in
  `RoundTrip/Blind/V1_7.lean`): there are sc-splittings `E = K ⊕ X`, `F = C ⊕ Y`
  (`ScBanach.IsScSplitting`) with `K = ker T₀` finite-dimensional, `C` finite-dimensional,
  `Y = T₀(E₀)`, and `T : X_m → Y_m` bijective for every `m` (the sc-isomorphism `X → Y`; the
  continuity of the inverse on each level is automatic by the open mapping theorem).  I did not
  use the project's `IsScFredholm`, although its `#print` shows the same fields.
- sc⁺-operator (Definition 1.4: `S(E_m) ⊆ F_{m+1}` continuously): the project's
  `ScPlus E F = ScOperator E F.shift`; as an operator `E → F` it is `ScPlus.toScOperator S`
  (`F.shiftIncl ∘ S`, checked with `#print`).
- `T + S` is the level-wise sum `ScOperator.add T S.toScOperator` (checked with `#print`).
-/
namespace RoundTrip.V1_9
open Polyfold

/-- Conditions (1)–(3) of Definition 1.8 for the data `E = K ⊕ X`, `F = C ⊕ Y`. -/
def IsFredholmData {E F : ScBanach} (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)) : Prop :=
  E.IsScSplitting K X ∧ F.IsScSplitting C Y ∧
  K = LinearMap.ker (T.lvl 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0) ∧ FiniteDimensional ℝ K ∧
  FiniteDimensional ℝ C ∧ Y = LinearMap.range (T.lvl 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0) ∧
  ∀ m : ℕ, Set.BijOn (T.lvl m) (E.levelSub X m) (F.levelSub Y m)

/-- `T` is sc-Fredholm (Definition 1.8). -/
def IsScFredholmB {E F : ScBanach} (T : ScOperator E F) : Prop :=
  ∃ (K X : Submodule ℝ (E.lvl 0)) (C Y : Submodule ℝ (F.lvl 0)), IsFredholmData T K X C Y

/-- An sc-Fredholm operator plus an sc⁺-operator is sc-Fredholm. -/
def B : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (S : ScPlus E F),
    IsScFredholmB T → IsScFredholmB (T.add S.toScOperator)

end RoundTrip.V1_9
