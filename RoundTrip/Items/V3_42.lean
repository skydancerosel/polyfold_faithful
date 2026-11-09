import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_42

/-! Round trip for V3_42 (Corollary 3.47, local germ-solvability for `f + s`).

`A` is the conjunction of the types of `Polyfold.theorem_3_5_11_sc_smooth`, `Polyfold.theorem_3_5_11`
and `Polyfold.StabilityData.scDerivGerm_pushMap₀` (no universe parameters: everything is in
`Type`).

Neither direction is proved.

`A → B` fails on the conclusion.  The setting of `B` is reachable from `A` by glue (take
`P = Fin n → ℝ`, `Q = Fin N → ℝ`; absorb the `ℝᴺ`-component of `B`'s `s` into the basic germ, since
`A`'s `StabilityData.s` only perturbs the `W`-component; choose the splitting of `1 + D₂s(0)` with
`proposition_1_1_11_preprint`; identify `D 0` with `Dfs` by uniqueness of the derivative at the smooth point
`0`; `B`'s `IsInGoodPositionSc` gives `A`'s `IsInGoodPosition`, `isInGoodPosition_of_sc` below).
But `A` only produces an *algebraic* good complement `Y` (`IsGoodComplement`: `IsCompl K Y` on
level `0`), while `B` (Definition 3.21 of the text) requires `Y` to be an *sc-complement*
(`E.IsScSplitting K Y`), with `σ` taking values in that `Y`.  Replacing `A`'s `Y` by the
sc-complement `Y₀` that `B`'s hypothesis provides needs a reparametrization `v ↦ v + π_K σ(v)` of
`K ∩ C` near `0` and its inverse (an inverse function theorem on a partial quadrant), i.e. new
mathematics.  Secondarily, `B` wants `σ` to be `C¹` into `E₁` on all of `V` and an sc-smooth germ
into `E¹`, whereas `A` gives `C^k`-lifts `σ_k` into `E_k` on shrinking neighbourhoods `V_k`.

`B → A` fails: `A` is stated for an arbitrary finite-dimensional `P` (transport of basic germs,
sc⁺-germs and germs of neighbourhoods along `P ≅ ℝⁿ` would be needed); `A`'s hypothesis `hpos`
is the algebraic good position, weaker than `B`'s `IsInGoodPositionSc` (so `B` cannot be
applied); and the conjunct `scDerivGerm_pushMap₀` (a chain-rule identity for the coordinate change
of Theorem 3.38) has no counterpart in `B`. -/

open Set

noncomputable section

namespace RoundTrip.V3_42
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.theorem_3_5_11_sc_smooth) ∧ (type_of% @Polyfold.theorem_3_5_11) ∧
    (type_of% @Polyfold.StabilityData.scDerivGerm_pushMap₀)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_5_11_sc_smooth, @Polyfold.theorem_3_5_11,
    @Polyfold.StabilityData.scDerivGerm_pushMap₀⟩

/-- Glue (hypothesis side of `A → B`): the blind good position (sc-complement) gives the project's
(algebraic complement). -/
theorem isInGoodPosition_of_sc {E : ScBanach} {C : Set (E.lvl 0)} {N : Submodule ℝ (E.lvl 0)}
    (h : IsInGoodPositionSc E C N) : IsInGoodPosition E C N := by
  obtain ⟨hint, Y, hsplit, ε, hε, hgood⟩ := h
  refine ⟨hint, Y, ?_, ε, hε, hgood⟩
  have := hsplit.2.2 0
  simpa using this

end RoundTrip.V3_42

end
