import Polyfold
/-! Blind formalization of V1_8 (the text's §1.1, Proposition 1.9, p. 9). Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`) and an
  sc-operator `T : ScOperator E F`; the text's `T : E → F` is the level-0 map `T.lvl 0`.
- sc-Fredholm (Definition 1.8) is written out by hand (`IsScFredholmB`, the same prelude as in
  `RoundTrip/Blind/V1_7.lean` and `V1_9.lean`): there are sc-splittings `E = K ⊕ X`, `F = C ⊕ Y`
  (`ScBanach.IsScSplitting`) with `K = ker T₀` finite-dimensional, `C` finite-dimensional,
  `Y = T₀(E₀)`, and `T : X_m → Y_m` bijective for every `m` (the sc-isomorphism `X → Y`; the
  continuity of the inverse on each level is automatic by the open mapping theorem).  I did not
  use the project's `IsScFredholm`.
- "`e ∈ E` and `T(e) ∈ F_m`": `e : E.lvl 0` with `T₀ e` in the range of the inclusion
  `F.toBase m : F_m → F₀`; "`e ∈ E_m`": `e` in the range of `E.toBase m`.  All `m : ℕ`.
-/
namespace RoundTrip.V1_8
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

/-- An sc-Fredholm operator is regularizing: `T(e) ∈ F_m` implies `e ∈ E_m`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F), IsScFredholmB T →
    ∀ (m : ℕ) (e : E.lvl 0), T.lvl 0 e ∈ Set.range (F.toBase m) →
      e ∈ Set.range (E.toBase m)

end RoundTrip.V1_8
