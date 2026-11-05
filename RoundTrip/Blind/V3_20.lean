import Polyfold
/-! Blind formalization of V3_20 (the text's §3.1, Definition 3.21, pp. 76–77). Choices:
- This item is a definition.  `B` states that the project's notions `IsInGoodPosition` ("`N` in good
  position to `C`") and `IsGoodComplement` ("`P` a good complement of `N`"), the declarations whose
  docstrings are "Definition 3.21", are the text's notions, written here as `IsInGoodPositionB` and
  `IsGoodComplementB`.
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀` a partial quadrant
  (`IsPartialQuadrant`, Definition 1.11; a hypothesis, since the definition is made for partial
  quadrants), `N ⊆ E₀` a finite-dimensional subspace (`Submodule`, `[FiniteDimensional ℝ N]`).
- "`N ∩ C` has nonempty interior in `N`": the interior, in `N` with its subspace topology, of
  `{n ∈ N | n ∈ C}` is nonempty.
- Good complement `P` (`IsGoodComplementB`): the kind of complement depends on `N`, as the text's
  remark says.  If `N` is smooth (`N ⊆ E_∞ = E.smooth`; a finite-dimensional sc-subspace is exactly
  such an `N`), `P` must be an sc-complement: `E = N ⊕ P` is an sc-splitting
  (`ScBanach.IsScSplitting`, Definition 1.5).  If `N` is not smooth, "a merely topological
  complement is allowed": `E₀ = N ⊕ P` algebraically with `P` closed (for finite-dimensional `N`
  this is a topological direct sum).  In both cases: there is `ε > 0` such that for `n ∈ N`,
  `p ∈ P` with `|p|₀ ≤ ε|n|₀`, `n ∈ C ↔ n + p ∈ C` (`|·|₀` the norm of `E₀`).
- `IsInGoodPositionB`: nonempty interior and some good complement.
- Doubt: the project's `IsGoodComplement` is documented to require only an algebraic complement;
  if so, the second conjunct of `B` (good complements) fails for non-closed `P`, while the first
  (good position, an existential over `P`) may still hold.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_20
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.21**: `N` is in good position to `C`: `N ∩ C` has nonempty interior in `N` and
`N` has a good complement. -/
def IsInGoodPositionB (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior ((Subtype.val : N → E.lvl 0) ⁻¹' C)).Nonempty ∧ ∃ P, IsGoodComplementB E C N P

/-- Definition 3.21: the project's good position and good complements are the text's. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N],
    IsPartialQuadrant E C →
      (IsInGoodPosition E C N ↔ IsInGoodPositionB E C N) ∧
      (∀ P : Submodule ℝ (E.lvl 0), IsGoodComplement E C N P ↔ IsGoodComplementB E C N P)

end RoundTrip.V3_20
