import Polyfold
/-! Blind formalization of V3_21 (the text's §3.1, Proposition 3.22, p. 77). Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀` a partial quadrant
  (`IsPartialQuadrant`, Definition 1.11), `N ⊆ E₀` a finite-dimensional sc-subspace (`Submodule`
  with `[FiniteDimensional ℝ N]` and `ScBanach.IsScSubspace`, Definition 1.5; for finite dimension
  this forces `N ⊆ E_∞`).
- "In good position" (Definition 3.21): as written in my blind file V3_20 (`IsInGoodPositionB`,
  copied below): `N ∩ C` has nonempty interior in `N`, and `N` has a good complement `P` — an
  sc-complement (`E = N ⊕ P` an sc-splitting; a topological complement if `N` were not smooth) with
  `ε > 0` such that `|p|₀ ≤ ε|n|₀` implies `n ∈ C ↔ n + p ∈ C`.  This is the text's notion; I did
  not use the project's `IsInGoodPosition`, documented as using a merely algebraic complement.
- "`N ∩ C` is a partial quadrant in `N`": `{n : N | n ∈ C}` is a partial quadrant
  (`IsPartialQuadrant`, Definition 1.11) of `N` with the constant sc-structure
  (`ScBanach.const N`); for a finite-dimensional sc-subspace the induced sc-structure is the
  constant one up to the identity sc-isomorphism, and being a partial quadrant only depends on the
  sc-isomorphism class.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_21
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

/-- Proposition 3.22: if the finite-dimensional sc-subspace `N` is in good position to the partial
quadrant `C`, then `N ∩ C` is a partial quadrant in `N`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N],
    IsPartialQuadrant E C → E.IsScSubspace N → IsInGoodPositionB E C N →
      IsPartialQuadrant (ScBanach.const N) ((Subtype.val : N → E.lvl 0) ⁻¹' C)

end RoundTrip.V3_21
