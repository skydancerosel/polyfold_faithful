import Polyfold
/-! Blind formalization of V4_46 (the text's §4.2, proof of Theorem 4.22, pp. 162–163: linear
algebra at the corner of a centred chart).

Text: "`E = T_0O ⊕ Z = T_0A ⊕ Ã ⊕ Z`, so `T_0A` has an sc-complement `Y ⊆ W`; with
`T_0A = N ⊕ (T_0A ∩ W)`, `E = N ⊕ W`, `C = (T_0A ∩ C) ⊕ Y`, and `T_0A ∩ C` is a partial quadrant
(Proposition 3.22)."

Choices:
- What is formalized: the linear algebra of this step, as an implication from the decompositions
  the text starts from to the four conclusions.  The item gives only this sentence; its context
  (a tame chart centred at `0`, `E = ℝⁿ ⊕ W` with `C = [0,∞)ⁿ ⊕ W`, a finite-dimensional
  submanifold `A` in general position) enters only through the relations listed below, so B
  quantifies over ALL subspaces `T_0O`, `Z`, `T_0A`, `Ã` with these relations (they need not be
  actual tangent spaces).  This is more general than the in-context statement; I chose it because
  the in-context objects are not described by the item.
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`) with a presentation
  `T : E ≅ ℝⁿ ⊕ W'` of the partial quadrant, `C = T⁻¹([0,∞)ⁿ ⊕ W')` (Definition 1.11).  The text's
  `W ⊆ E` (it identifies `W'` with `{0} ⊕ W'`) is `T⁻¹({0} ⊕ W')`, the vectors all of whose
  half-line coordinates vanish: the project's `minimalSubspaceWith T 0` (checked with `#print`:
  the kernel of `v ↦ ((Tv)_i)_{i ∈ I(0)}`, and `I(0)` is every index), i.e. `E_0` of Definition
  2.27.
- Hypotheses (the text's "`E = T_0O ⊕ Z = T_0A ⊕ Ã ⊕ Z`" with what the context supplies):
  `E = T_0O ⊕ Z` is an sc-splitting (`E.IsScSplitting`, checked: both sc-subspaces, complementary
  on every level `E_m`); `Z ⊆ W` (tameness at `0`: `T_0O` has an sc-complement in `E_0 = W`);
  `T_0O = T_0A ⊕ Ã` is an sc-splitting of `T_0O`: `T_0A`, `Ã` are sc-subspaces of `E`
  (`IsScSubspace`, checked: closed, smooth points dense in every level) whose levels are
  complementary in the levels of `T_0O` (the form the project uses for Definition 4.21);
  `Ã ⊆ W` (general position: `Ã ⊆ T^R_0O = T_0O ∩ E_0`); `T_0A` is finite-dimensional (`A` is
  a finite-dimensional submanifold; clearly presupposed).
- Conclusions: (1) some `Y ⊆ W` is an sc-complement of `T_0A` (`E.IsScSplitting T_0A Y`) and, for
  that `Y`, `C = (T_0A ∩ C) ⊕ Y`, read as `C = {a + y | a ∈ T_0A ∩ C, y ∈ Y}` (the sum is direct
  since `T_0A ∩ Y = 0`); (2) for EVERY subspace `N` with `T_0A = N ⊕ (T_0A ∩ W)` (algebraic:
  `N ⊓ (T_0A ⊓ W) = ⊥`, `N ⊔ (T_0A ⊓ W) = T_0A`), `E = N ⊕ W` as an sc-splitting; (3)
  `T_0A ∩ C` is a partial quadrant in `T_0A`, with `T_0A` carrying the sc-structure induced from
  `E` (`E.ofSubspace`; for a finite-dimensional sc-subspace this is the constant structure up to
  sc-isomorphism) and `IsPartialQuadrant` (checked: the preimage of `[0,∞)^k ⊕ W''` under an
  sc-isomorphism).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_46
open Polyfold

/-- The linear algebra at the corner of a centred chart in the proof of Theorem 4.22. -/
def B : Prop :=
  ∀ (E : ScBanach) (n : ℕ) (W' : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W'))
    (C : Set (E.lvl 0)), C = T.lvl 0 ⁻¹' quadrant n W' 0 →
    ∀ (TO Z TA At : Submodule ℝ (E.lvl 0)),
      -- `E = T_0O ⊕ Z`, `Z ⊆ W`
      E.IsScSplitting TO Z → Z ≤ minimalSubspaceWith T 0 →
      -- `T_0O = T_0A ⊕ Ã`, `Ã ⊆ W`, `T_0A` finite-dimensional
      ∀ (hTA : E.IsScSubspace TA), E.IsScSubspace At →
      (∀ m : ℕ, E.levelSub TA m ⊓ E.levelSub At m = ⊥ ∧
        E.levelSub TA m ⊔ E.levelSub At m = E.levelSub TO m) →
      At ≤ minimalSubspaceWith T 0 → FiniteDimensional ℝ TA →
        -- `T_0A` has an sc-complement `Y ⊆ W`, and `C = (T_0A ∩ C) ⊕ Y`
        (∃ Y : Submodule ℝ (E.lvl 0), E.IsScSplitting TA Y ∧ Y ≤ minimalSubspaceWith T 0 ∧
          C = {c | ∃ a ∈ TA, a ∈ C ∧ ∃ y ∈ Y, c = a + y}) ∧
        -- `T_0A = N ⊕ (T_0A ∩ W)` gives `E = N ⊕ W`
        (∀ N : Submodule ℝ (E.lvl 0), N ⊓ (TA ⊓ minimalSubspaceWith T 0) = ⊥ →
          N ⊔ (TA ⊓ minimalSubspaceWith T 0) = TA → E.IsScSplitting N (minimalSubspaceWith T 0)) ∧
        -- `T_0A ∩ C` is a partial quadrant in `T_0A`
        IsPartialQuadrant (E.ofSubspace hTA) {v | Subtype.val v ∈ C}

end RoundTrip.V4_46
