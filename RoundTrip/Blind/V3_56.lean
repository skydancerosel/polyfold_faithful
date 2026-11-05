import Polyfold
/-! Blind formalization of V3_56 (the text's §3.8.1, Proposition 3.69, p. 126). `B` is the
conjunction of (1) and (2).  Choices:
- Setting (§3.8.1, as in my blind file V3_55): `E = ℝⁿ ⊕ W` with `W` an arbitrary sc-Banach space
  (`(ScBanach.const (Fin n → ℝ)).prod W`, level `0` is `ℝⁿ × W₀`), `C = [0, ∞)ⁿ ⊕ W` (`quadC`),
  `N ⊆ E₀` a finite-dimensional (`[FiniteDimensional ℝ N]`) smooth (`N ⊆ E_∞ = E.smooth`)
  subspace in good position to `C` (Definition 3.21: `N ∩ C` has nonempty interior in `N` and `N`
  has a good complement, an sc-complement with the `ε`-property, `IsInGoodPositionSc` as in the
  earlier blind file V3_41; not the project's `IsInGoodPosition`, documented as using an
  algebraic complement).  No universe choices arise.
- `d_C(x)` for the standard quadrant `C = [0, ∞)ⁿ ⊕ W`: the number of `i` with `x_i = 0`
  (Definition 1.23 with the identity presentation; `dC`, written out here).
- `d_{N ∩ C}(x)`: `N ∩ C` is a partial quadrant in `N` (Proposition 3.22), and its degeneracy
  index is Definition 1.23 for the finite-dimensional space `N` with its constant sc-structure:
  the project's `degIndex (ScBanach.const N) (N ∩ C)` (computed with any presentation; junk `0`
  only if `N ∩ C` were not a partial quadrant, which does not happen under the hypotheses).
- `N ∩ W`: `W` is identified with `{0} ⊕ W` (`Wsub`, the vectors with all `ℝⁿ`-coordinates `0`);
  `dim N − dim(N ∩ W)` is a difference of `finrank`s in `ℕ` (no truncation, `N ∩ W ⊆ N`).
- The quantifier "`x ∈ N ∩ C`" covers both cases; the case split is on `x ∈ N ∩ W`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_56
open Polyfold

/-- The sc-Banach space `E = ℝⁿ ⊕ W`. -/
noncomputable abbrev Emod (n : ℕ) (W : ScBanach) : ScBanach := (ScBanach.const (Fin n → ℝ)).prod W

/-- The quadrant `C = [0, ∞)ⁿ ⊕ W ⊆ E₀`. -/
def quadC (n : ℕ) (W : ScBanach) : Set ((Emod n W).lvl 0) := {x | ∀ i : Fin n, 0 ≤ x.1 i}

/-- `W ≅ {0} ⊕ W ⊆ E₀`, the vectors with vanishing `ℝⁿ`-coordinates. -/
def Wsub (n : ℕ) (W : ScBanach) : Submodule ℝ ((Emod n W).lvl 0) where
  carrier := {x | ∀ i : Fin n, x.1 i = 0}
  add_mem' := fun ha hb i => by simp [ha i, hb i]
  zero_mem' := fun _ => rfl
  smul_mem' := fun _ _ ha i => by simp [ha i]

/-- The degeneracy index `d_C(x)` of the standard quadrant: the number of vanishing coordinates. -/
noncomputable def dC (n : ℕ) (W : ScBanach) (x : (Emod n W).lvl 0) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x.1 i = 0)).card

/-- Definition 3.21 (complement, smooth `N`): `Y` is a good complement of `N` with respect to `C`:
an sc-complement with `n ∈ C ⟺ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- Definition 3.21: the (finite-dimensional) subspace `N` is in good position to `C`: `N ∩ C` has
nonempty interior in `N` and `N` has a good complement. -/
def IsInGoodPositionSc (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧ ∃ Y, IsGoodComplementSc E C N Y

/-- Proposition 3.69: for `N` (smooth, finite-dimensional) in good position to
`C = [0,∞)ⁿ ⊕ W` and `x ∈ N ∩ C`: (1) `d_{N∩C}(x) = d_C(x)` if `x ∉ N ∩ W`;
(2) `d_{N∩C}(x) = dim N − dim(N ∩ W)` if `x ∈ N ∩ W`. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (N : Submodule ℝ ((Emod n W).lvl 0)) [FiniteDimensional ℝ N],
    N ≤ (Emod n W).smooth →
    IsInGoodPositionSc (Emod n W) (quadC n W) N →
    ∀ x : N, (x : (Emod n W).lvl 0) ∈ quadC n W →
      ((x : (Emod n W).lvl 0) ∉ Wsub n W →
          degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadC n W) x = dC n W x) ∧
      ((x : (Emod n W).lvl 0) ∈ Wsub n W →
          degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadC n W) x =
            Module.finrank ℝ N - Module.finrank ℝ (N ⊓ Wsub n W : Submodule ℝ _))

end RoundTrip.V3_56
