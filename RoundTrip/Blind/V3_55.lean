import Polyfold
/-! Blind formalization of V3_55 (the text's §3.8.1, Lemma 3.65, p. 123). Choices:
- Setting (the standing assumptions of §3.8.1, the proof of Proposition 3.22): `E = ℝⁿ ⊕ W` with
  `W` an arbitrary sc-Banach space (`(ScBanach.const (Fin n → ℝ)).prod W`, level `0` is
  `ℝⁿ × W₀`), `C = [0, ∞)ⁿ ⊕ W` (`quadC`, defined here: all `ℝⁿ`-coordinates `≥ 0`), `N ⊆ E₀` a
  finite-dimensional smooth subspace (`[FiniteDimensional ℝ N]`, `N ⊆ E_∞ = E.smooth`) in good
  position to `C` (Definition 3.21: `N ∩ C` has nonempty interior in `N`, and `N` has a good
  complement).  No universe choices arise (`ScBanach` forces levels in `Type`).
- "`N^⊥`" is the text's name for a good complement of `N` (Definition 3.21 for smooth `N`: an
  sc-complement, `E = N ⊕ N^⊥` an sc-splitting, with `ε > 0` such that `n ∈ C ⟺ n + p ∈ C` for
  `n ∈ N`, `p ∈ N^⊥`, `|p|₀ ≤ ε|n|₀`; `IsGoodComplementSc`, as in the earlier blind file V3_41).
  The claim is made for every good complement.  I did not use the project's `IsGoodComplement`,
  documented as asking only for an algebraic complement (a weaker hypothesis would make `B`
  stronger than the text).
- `Σ = {i | some nonzero a ∈ N ∩ C has a_i = 0}` (`sigmaIdx`, defined here; the project's
  `vanIdx` has the same docstring but I wrote it out).
- The claim `N^⊥ ⊆ ℝ^Σ ⊕ W` is read as stated in the quote's gloss: every `p ∈ N^⊥` has `p_i = 0`
  for all `i ∈ Σ`.  Doubt about the notation: if `ℝ^Σ ⊕ W` were the vectors whose coordinates
  *outside* `Σ` vanish, the claim would be false (e.g. `N` the diagonal of `ℝ²`, `W = 0`: `Σ = ∅`,
  but `N^⊥ ≠ 0`); I formalize the gloss ("vanishing coordinates `i ∈ Σ`"), which is true.
-/
namespace RoundTrip.V3_55
open Polyfold

/-- The sc-Banach space `E = ℝⁿ ⊕ W`. -/
noncomputable abbrev Emod (n : ℕ) (W : ScBanach) : ScBanach := (ScBanach.const (Fin n → ℝ)).prod W

/-- The quadrant `C = [0, ∞)ⁿ ⊕ W ⊆ E₀`. -/
def quadC (n : ℕ) (W : ScBanach) : Set ((Emod n W).lvl 0) := {x | ∀ i : Fin n, 0 ≤ x.1 i}

/-- Definition 3.21 (complement, smooth `N`): `Y` is a good complement of `N` with respect to `C`:
an sc-complement with `n ∈ C ⟺ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- The set `Σ` of indices `i` such that some nonzero `a ∈ N ∩ C` has `a_i = 0`. -/
def sigmaIdx (n : ℕ) (W : ScBanach) (N : Submodule ℝ ((Emod n W).lvl 0)) : Set (Fin n) :=
  {i | ∃ a ∈ N, a ∈ quadC n W ∧ a ≠ 0 ∧ a.1 i = 0}

/-- Lemma 3.65: for `N` (finite-dimensional, smooth) in good position to `C = [0,∞)ⁿ ⊕ W`, every
good complement `N^⊥` of `N` has vanishing coordinates `p_i = 0` for all `i ∈ Σ`. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (N : Submodule ℝ ((Emod n W).lvl 0)) [FiniteDimensional ℝ N],
    N ≤ (Emod n W).smooth →
    (interior (Subtype.val ⁻¹' quadC n W : Set N)).Nonempty →
    ∀ Nperp : Submodule ℝ ((Emod n W).lvl 0),
      IsGoodComplementSc (Emod n W) (quadC n W) N Nperp →
      ∀ p ∈ Nperp, ∀ i ∈ sigmaIdx n W N, p.1 i = 0

end RoundTrip.V3_55
