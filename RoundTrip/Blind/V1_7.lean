import Polyfold
/-! Blind formalization of V1_7 (the text's §1.1, Definition 1.8 and the remarks after it, p. 9).

Text: an sc-operator `T : E → F` is sc-Fredholm if there are sc-splittings `E = K ⊕ X`,
`F = C ⊕ Y` with (1) `K = ker T` finite-dimensional, (2) `C` finite-dimensional and `Y = T(E)`,
(3) `T : X → Y` an sc-isomorphism.  "Then `K ⊂ E_∞`, `T(X_m) = Y_m`, `E_m = K ⊕ X_m` and
`F = C ⊕ T(E_m)`.  The index is `ind(T) = dim K − dim C`."

Choices:
- Setting: `E F : ScBanach` (the project's sc-Banach spaces, whose levels live in `Type`; this is
  forced by `ScBanach`, and the text's spaces are real Banach spaces so nothing is lost).
  `T : ScOperator E F`; the text's `T : E → F` is the level-0 map `T.lvl 0`.
- The definition itself is not a claim.  B is the conjunction of the claims made about any data
  `(K, X, C, Y)` satisfying (1)–(3) (`IsFredholmData`, written out by hand here, not the project's
  `ScFredholmSplitting`), for every `m : ℕ`:
  * `K ⊂ E_∞`: `K ≤ E.smooth`;
  * `T(X_m) = Y_m`: the image of `X_m = X ∩ E_m` under `T : E_m → F_m` is `Y_m = Y ∩ F_m`;
  * `E_m = K ⊕ X_m`: `IsCompl (K ∩ E_m) (X ∩ E_m)` in `E_m` (together with `K ⊂ E_∞` this says
    that `K` itself, viewed in `E_m`, is a complement of `X_m`);
  * `F = C ⊕ T(E_m)`: formalized LITERALLY as a statement in `F = F₀`: `C` and the image
    `T(E_m) ⊆ F₀` of `E_m` are complementary subspaces of `F₀`.  I believe this is a misprint for
    `F_m = C ⊕ T(E_m)` (inside `F_m`): read literally it is false for `m ≥ 1` as soon as `F` is
    infinite-dimensional (e.g. `T = id`, `K = C = 0`: then `F₀ = E_m` would be needed).  So B as
    written is FALSE; the intended reading is recorded as `B_intended` below (same B with the
    last level statement replaced by `IsCompl (C ∩ F_m) (T(E_m))` in `F_m`).
  * "The index is `ind(T) = dim K − dim C`": formalized as the well-definedness that the text
    presupposes when it calls this number *the* index of `T`: any two choices of data satisfying
    (1)–(3) give the same `dim K − dim C` (as integers).
- (3) "`T : X → Y` is an sc-isomorphism" (with the induced structures `X_m = X ∩ E_m`,
  `Y_m = Y ∩ F_m`) is formalized as: for every `m`, `T : E_m → F_m` maps `X_m` bijectively onto
  `Y_m`.  Continuity of `T` on each level is part of `ScOperator`; continuity of the inverse
  `Y_m → X_m` is automatic (open mapping theorem: `X_m`, `Y_m` are closed subspaces of Banach
  spaces), so it is not stated.
- Project definitions used (checked with `#print`): `ScBanach`, `ScOperator`, `ScBanach.levelSub`
  (`A_m = A ∩ E_m` as a subspace of `E_m`), `ScBanach.IsScSplitting` (both summands
  sc-subspaces and `E_m = F_m ⊕ G_m` on every level, Definition 1.5), `ScScale.smooth`
  (`E_∞ = ⋂ E_m`), `ScScale.toBase`.
-/
namespace RoundTrip.V1_7
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

/-- The consequences of Definition 1.8 (literal reading of `F = C ⊕ T(E_m)`, in `F₀`) and the
well-definedness of the index `dim K − dim C`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)), IsFredholmData T K X C Y →
      K ≤ E.smooth ∧
      (∀ m : ℕ,
        Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub X m) = F.levelSub Y m ∧
        IsCompl (E.levelSub K m) (E.levelSub X m) ∧
        IsCompl C (imageLevelBase T m)) ∧
      (∀ (K' X' : Submodule ℝ (E.lvl 0)) (C' Y' : Submodule ℝ (F.lvl 0)),
        IsFredholmData T K' X' C' Y' →
          (Module.finrank ℝ K : ℤ) - Module.finrank ℝ C =
            (Module.finrank ℝ K' : ℤ) - Module.finrank ℝ C')

/-- The intended reading (`F_m = C ⊕ T(E_m)` inside `F_m`); see the header. -/
def B_intended : Prop :=
  ∀ (E F : ScBanach) (T : ScOperator E F) (K X : Submodule ℝ (E.lvl 0))
    (C Y : Submodule ℝ (F.lvl 0)), IsFredholmData T K X C Y →
      K ≤ E.smooth ∧
      (∀ m : ℕ,
        Submodule.map (T.lvl m : E.lvl m →ₗ[ℝ] F.lvl m) (E.levelSub X m) = F.levelSub Y m ∧
        IsCompl (E.levelSub K m) (E.levelSub X m) ∧
        IsCompl (F.levelSub C m) (imageLevel T m)) ∧
      (∀ (K' X' : Submodule ℝ (E.lvl 0)) (C' Y' : Submodule ℝ (F.lvl 0)),
        IsFredholmData T K' X' C' Y' →
          (Module.finrank ℝ K : ℤ) - Module.finrank ℝ C =
            (Module.finrank ℝ K' : ℤ) - Module.finrank ℝ C')

end RoundTrip.V1_7
