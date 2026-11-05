import Polyfold
/-! Blind formalization of V1_5 (the text's §1.1, Proposition 1.6, p. 7). Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by the project's `ScBanach`), and a
  finite-dimensional subspace `F ⊆ E = E₀` (`Submodule ℝ (E.lvl 0)` with `FiniteDimensional`).
- "sc-subspace": the project's `ScBanach.IsScSubspace` (checked with `#print`: `F` closed and
  `F_m ⊆ closure (F_m ∩ E_∞)` in `E_m` for every `m`, i.e. `F ∩ E_∞` dense in `F_m`; the text's
  remaining sc-structure conditions on `F_m = F ∩ E_m` are automatic).  Item V1_4 states that this
  is the text's Definition 1.5.
- `E_∞`: the project's `ScScale.smooth` (checked: `⨅ m, range (toBase m)` in `E₀`).
- "has an sc-complement": there is `G` with `E = F ⊕ G` an sc-splitting, the project's
  `ScBanach.IsScSplitting F G` (checked: `F`, `G` sc-subspaces and `E_m = F_m ⊕ G_m` on every
  level; topological automatically, `F_m`, `G_m` being closed).
- B is the conjunction of the two sentences, for every finite-dimensional `F`.
-/
namespace RoundTrip.V1_5
open Polyfold

/-- A finite-dimensional subspace is an sc-subspace iff it consists of smooth points, and a
finite-dimensional sc-subspace has an sc-complement. -/
def B : Prop :=
  ∀ (E : ScBanach) (F : Submodule ℝ (E.lvl 0)), FiniteDimensional ℝ F →
    (E.IsScSubspace F ↔ F ≤ E.smooth) ∧
    (E.IsScSubspace F → ∃ G : Submodule ℝ (E.lvl 0), E.IsScSplitting F G)

end RoundTrip.V1_5
