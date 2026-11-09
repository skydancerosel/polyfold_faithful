import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_38

/-! Round trip for V3_38 (Theorem 3.43, local germ-solvability I).

`A` is the conjunction of the types of `Polyfold.theorem_3_5_6_sc_smooth`, `Polyfold.theorem_3_5_6`,
`Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level`, `Polyfold.ShiftedBasicData.H_contDiffOn`,
`Polyfold.ShiftedBasicData.Sol.exists_eq_add_τ` and `Polyfold.exists_proj_mem_of_eq_zero` (no
universe parameters: everything is in `Type`).

Neither direction is proved; the two statements are set up differently.

* `A` (germ form) is about an arbitrary sc-smooth germ `g` with `g(0) = 0` whose index-raised germ
  `g¹` is basic (`ShiftedBasicData`), and it **assumes** (i) `K' = ker Dg(0)` in good position
  (`hpos`) and (ii) the regularity of the zeros of `g` (`hreg`: zeros near `0` lie on level `1`
  and are small there, the content of Lemma 3.42).  It concludes a good complement `Y` of `K'`
  in the *algebraic* sense, `τ` with `C¹` on `V` into level `0` plus `C^k`-lifts `τ_k` on
  shrinking `V_k`, and the zero set of `g` near `0` equal to the graph (`g(y + τ y) = 0` and every
  zero in `U''` is on the graph).
* `B` (the text) starts from `f = h + s` (basic `h`, sc⁺ `s`, `K = ker Df(0)` in good position)
  and an arbitrary strong bundle isomorphism `Φ` with `g = Φ_*(f)`, `g¹` basic, and **concludes**
  that `K'` is in good position, with an *sc-complement* `Y'`, `τ` an sc-smooth germ into `E'¹`
  that is `C¹` into `E'₁` on `V`, and `φ({f = 0}) = {g = 0} = graph` after shrinking `U`.

`A → B` fails: from `B`'s hypotheses one must (a) produce `hpos` for `K'` (transport of the good
position of `K` along `Dφ(0)`, which maps `C` onto `C'`), (b) produce `hreg` (Lemma 3.42, from
Theorem 3.40 for `f + s` and the level-`1` continuity of `φ`) — both are proofs the project does
only for its own coordinate change (`StabilityData.lemma_3_5_5`), not for an arbitrary `Φ` — and
(c) `A`'s complement is only algebraic while `B` demands an sc-complement (`IsScSplitting`),
which cannot be obtained without re-choosing the complement (a reparametrization of `K' ∩ C'`, an
inverse function theorem on a partial quadrant).  (c) is a genuine difference in the conclusion.

`B → A` fails: an arbitrary `ShiftedBasicData` `g` is not of the form `Φ_*(h + s)` with `h` basic
on level `0` (only `g¹` is basic), so `B` cannot be instantiated; `A`'s `hpos` is algebraic, `B`
needs `ker Df(0)` in sc-good position; and the helper conjuncts (`H_contDiffOn`,
`exists_proj_mem_of_eq_zero`, …) are independent lemmas with no counterpart in `B`. -/

open Set

noncomputable section

namespace RoundTrip.V3_38
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.theorem_3_5_6_sc_smooth) ∧ (type_of% @Polyfold.theorem_3_5_6) ∧
    (type_of% @Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level) ∧
    (type_of% @Polyfold.ShiftedBasicData.H_contDiffOn) ∧
    (type_of% @Polyfold.ShiftedBasicData.Sol.exists_eq_add_τ) ∧
    (type_of% @Polyfold.exists_proj_mem_of_eq_zero)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_5_6_sc_smooth, @Polyfold.theorem_3_5_6,
    @Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level, @Polyfold.ShiftedBasicData.H_contDiffOn,
    @Polyfold.ShiftedBasicData.Sol.exists_eq_add_τ, @Polyfold.exists_proj_mem_of_eq_zero⟩

/-- Glue: the blind good position (sc-complement) gives the project's (algebraic complement); the
converse is what `A → B` would need for the output complement and is not available. -/
theorem isInGoodPosition_of_sc {E : ScBanach} {C : Set (E.lvl 0)} {N : Submodule ℝ (E.lvl 0)}
    (h : IsInGoodPositionSc E C N) : IsInGoodPosition E C N := by
  obtain ⟨hint, Y, hsplit, ε, hε, hgood⟩ := h
  refine ⟨hint, Y, ?_, ε, hε, hgood⟩
  have := hsplit.2.2 0
  simpa using this

end RoundTrip.V3_38

end
