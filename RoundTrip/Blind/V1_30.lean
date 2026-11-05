import Polyfold
/-! Blind formalization of V1_30 (the text's §1.1, Proposition 1.10, p. 10).

Text: if `T : E → F` is sc-Fredholm and `S : E → F` is an sc⁺-operator, then `T + S` is
sc-Fredholm.  The index of `T + S` is not mentioned, so B says nothing about it (the item's title
"preserves the index" is not part of the quoted claim).

Choices:
- Setting: `E F : ScBanach` (the project's sc-Banach spaces, levels in `Type`; forced by
  `ScBanach`, and checked with `#print` to be a scale of real Banach spaces with injective compact
  inclusions and `E_∞` dense in every level, i.e. Definition 1.1).  `T : ScOperator E F`; the
  text's `T : E → F` is the level-0 map `T.lvl 0` (an `ScOperator` is a family of continuous
  linear level maps compatible with the inclusions, Definition 1.3).
- sc-Fredholm (Definition 1.8) is written out by hand (`IsScFredholmB`, the same prelude as in
  `RoundTrip/Blind/V1_9.lean`): there are sc-splittings `E = K ⊕ X`, `F = C ⊕ Y`
  (`ScBanach.IsScSplitting`, checked with `#print`: both summands sc-subspaces and
  `E_m = K_m ⊕ X_m` algebraically on every level, which is automatically topological) with
  `K = ker T₀` finite-dimensional, `C` finite-dimensional, `Y = T₀(E₀)`, and `T : X_m → Y_m`
  bijective for every `m` (the linear sc-isomorphism `X → Y` of (3); continuity of the level
  inverses is automatic by the open mapping theorem, `X_m`, `Y_m` being closed in `E_m`, `F_m`).
  The project's `IsScFredholm` was not used (its `#print` shows the same fields).
- sc⁺-operator (Definition 1.4: `S(E_m) ⊆ F_{m+1}`, continuously): the project's
  `ScPlus E F = ScOperator E F.shift`; as an operator `E → F` it is `S.toScOperator`
  (`F.shiftIncl ∘ S`).  `T + S` is the level-wise sum `T.add S.toScOperator`.
- This is the same claim as item V1_9 (also Proposition 1.10); B is stated identically.
  Nothing looks false.
-/
namespace RoundTrip.V1_30
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

/-- Proposition 1.10: an sc-Fredholm operator plus an sc⁺-operator is sc-Fredholm. -/
def B : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (S : ScPlus E F),
    IsScFredholmB T → IsScFredholmB (T.add S.toScOperator)

end RoundTrip.V1_30
