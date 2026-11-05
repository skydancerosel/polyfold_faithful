import Polyfold
/-! Blind formalization of V1_29 (the text's §1.1, Definition 1.8 and the sentences after it,
p. 9).

Text: after the definition of an sc-Fredholm operator `T : E → F` (sc-splittings `E = K ⊕ X`,
`F = C ⊕ Y` with (1) `K = ker T` finite-dimensional, (2) `C` finite-dimensional and `Y = T(E)`,
(3) `T : X → Y` an sc-isomorphism): "`K ⊂ E_∞`, `T(X_m) = Y_m`, `E_m = K ⊕ X_m` and
`F = C ⊕ T(E_m)`" for all `m`; the index is `dim K − dim C`.  (The item notes that the text does
NOT state that `T : E_m → F_m` is Fredholm with this index on every level; so that is not in B.)

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`),
  `T : ScOperator E F` (checked with `#print`: continuous linear `T_m : E_m → F_m` commuting with
  the inclusions); the text's `T : E → F` is `T_0`.
- The data `(K, X, C, Y)` of Definition 1.8 (`IsFredholmData`, the same prelude as
  `RoundTrip/Blind/V1_7.lean`, re-checked): `K X ⊆ E₀`, `C Y ⊆ F₀` subspaces;
  `E.IsScSplitting K X`, `F.IsScSplitting C Y` (checked with `#print`: both summands sc-subspaces
  — closed, with `A ∩ E_∞` dense in every `A_m` — and `E_m = K_m ⊕ X_m` for all `m`, where
  `A_m = E.levelSub A m = ι_m⁻¹(A)`); `K = ker T₀` finite-dimensional; `C` finite-dimensional;
  `Y = T₀(E₀)`; and "`T : X → Y` is an sc-isomorphism" as: for every `m`, `T_m` maps `X_m`
  bijectively onto `Y_m` (continuity of `T_m` is built in; continuity of the inverse
  `Y_m → X_m` is automatic by the open mapping theorem, `X_m`, `Y_m` being closed subspaces of
  Banach spaces).
- B is the conjunction, for every such data and every `m`, of:
  * `K ⊂ E_∞`: `K ≤ E.smooth` (`E.smooth = ⋂ₘ ι_m(E_m)`, checked);
  * `T(X_m) = Y_m`: the image of `X_m` under `T_m` is `Y_m`, inside `F_m`;
  * `E_m = K ⊕ X_m`: `IsCompl K_m X_m` in `E_m` (with `K ⊂ E_∞`, `K_m` is `K` seen in `E_m`);
  * `F = C ⊕ T(E_m)`: formalized LITERALLY, in `F = F₀`: `C` and the image `T(E_m) ⊆ F₀` of
    `E_m` are complementary subspaces of `F₀`.  I believe this is a misprint for
    `F_m = C ⊕ T(E_m)` (inside `F_m`): read literally it is false for `m ≥ 1` as soon as `F₀` is
    infinite-dimensional (e.g. `T = id`, `K = C = 0`: then `T(E_m) = E_m` would have to be all of
    `F₀ = E₀`, but `E_m ≠ E₀` since the inclusion is compact).  So B is FALSE as written; the
    intended reading is `B_intended` (same, with `IsCompl C_m (T_m(E_m))` in `F_m`).
  * "the index is `dim K − dim C`": formalized as the well-definedness the text presupposes when
    it calls this number *the* index: any two data satisfying (1)–(3) for the same `T` give the
    same integer `dim K − dim C` (`Module.finrank`, which is the dimension here since `K`, `C` are
    finite-dimensional).
- I did not use the project's `ScFredholmSplitting`/`IsScFredholm`/`scIndex`.
-/
namespace RoundTrip.V1_29
open Polyfold

/-- Conditions (1)–(3) of Definition 1.8 for the data `E = K ⊕ X`, `F = C ⊕ Y`. -/
def IsFredholmData {E F : ScBanach} (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)) : Prop :=
  E.IsScSplitting K X ∧ F.IsScSplitting C Y ∧
  -- (1)
  K = LinearMap.ker (T.lvl 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0) ∧ FiniteDimensional ℝ K ∧
  -- (2)
  FiniteDimensional ℝ C ∧ Y = LinearMap.range (T.lvl 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0) ∧
  -- (3) `T : X → Y` is an sc-isomorphism: a bijection `X_m → Y_m` on every level
  ∀ m : ℕ, Set.BijOn (T.lvl m) (E.levelSub X m) (F.levelSub Y m)

/-- The image `T(E_m)` of the level `E_m`, as a subspace of `F₀`. -/
def imageLevelBase {E F : ScBanach} (T : ScOperator E F) (m : ℕ) : Submodule ℝ (F.lvl 0) :=
  LinearMap.range ((T.lvl 0).comp (E.toBase m) : E.lvl m →ₗ[ℝ] F.lvl 0)

/-- The image `T(E_m)` of the level `E_m`, as a subspace of `F_m`. -/
def imageLevel {E F : ScBanach} (T : ScOperator E F) (m : ℕ) : Submodule ℝ (F.lvl m) :=
  LinearMap.range (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m)

/-- The well-definedness of the index `dim K − dim C`. -/
def IndexWellDefined {E F : ScBanach} (T : ScOperator E F) (K : Submodule ℝ (E.lvl 0))
    (C : Submodule ℝ (F.lvl 0)) : Prop :=
  ∀ (K' X' : Submodule ℝ (E.lvl 0)) (C' Y' : Submodule ℝ (F.lvl 0)),
    IsFredholmData T K' X' C' Y' →
      (Module.finrank ℝ K : ℤ) - Module.finrank ℝ C =
        (Module.finrank ℝ K' : ℤ) - Module.finrank ℝ C'

/-- The level statements after Definition 1.8 (literal reading of `F = C ⊕ T(E_m)`, in `F₀`)
and the well-definedness of the index `dim K − dim C`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)), IsFredholmData T K X C Y →
      K ≤ E.smooth ∧
      (∀ m : ℕ,
        Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub X m) = F.levelSub Y m ∧
        IsCompl (E.levelSub K m) (E.levelSub X m) ∧
        IsCompl C (imageLevelBase T m)) ∧
      IndexWellDefined T K C

/-- The intended reading (`F_m = C ⊕ T(E_m)` inside `F_m`); see the header. -/
def B_intended : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)), IsFredholmData T K X C Y →
      K ≤ E.smooth ∧
      (∀ m : ℕ,
        Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub X m) = F.levelSub Y m ∧
        IsCompl (E.levelSub K m) (E.levelSub X m) ∧
        IsCompl (F.levelSub C m) (imageLevel T m)) ∧
      IndexWellDefined T K C

end RoundTrip.V1_29
