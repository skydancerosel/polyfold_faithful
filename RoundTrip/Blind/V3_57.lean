import Polyfold
/-! Blind formalization of V3_57 (the text's §3.8.1, Lemma 3.70, p. 127). Choices:
- Setting (§3.8.1, as in my blind files V3_55, V3_56): `E = ℝⁿ ⊕ W` with `W` an arbitrary
  sc-Banach space (`(ScBanach.const (Fin n → ℝ)).prod W`; level `0` is `ℝⁿ × W₀`, level `1` is
  `ℝⁿ × W₁`), `C = [0, ∞)ⁿ ⊕ W` (`quadC`), `N ⊆ E₀` finite-dimensional and smooth (`N ⊆ E_∞`,
  the standing assumption of §3.8.1) with `N ∩ C` of nonempty interior in `N`, and `Y` a good
  complement of `N` (Definition 3.21 for smooth `N`: sc-complement with the `ε`-property,
  `IsGoodComplementSc` as in V3_41/V3_55; not the project's `IsGoodComplement`, documented as
  algebraic only).  "In good position with good complement `Y`" = nonempty interior and `Y`
  a good complement.  No universe choices arise.
- "`τ : N ∩ C → Y₁` of class `C¹`": `Y₁ = Y ∩ E₁` with the level-`1` norm, so `τ : N → E₁` (values
  off `N ∩ C` are junk and unused) with `ι₁ τ(v) ∈ Y` for `v ∈ N ∩ C` (`ι₁ = E.toBase 1`), and
  `ContDiffOn ℝ 1 τ (N ∩ C)` into `E₁` (Mathlib's `C¹` within the set; `N ∩ C` is a convex subset
  of `N` with nonempty interior, so derivatives within it are unique).  `τ(0) = 0` and
  `Dτ(0) = 0` (`HasFDerivWithinAt τ 0 (N ∩ C) 0`).
- `d_C`: the number of vanishing `ℝⁿ`-coordinates (`dC`; Definition 1.23 for the standard
  quadrant), evaluated at `v + τ(v) = v + ι₁ τ(v) ∈ E₀`.  `d_{N ∩ C}`: the project's `degIndex`
  (Definition 1.23) for the partial quadrant `N ∩ C` of `N` with the constant sc-structure (as in
  V3_56).
- "`v ∈ N ∩ C \ N ∩ W` close to `0`": there is `δ > 0` such that the equality holds for every
  `v ∈ N ∩ C` with `v ∉ W` (`W ≅ {0} ⊕ W`, `Wsub`) and `|v|₀ < δ`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_57
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

/-- Lemma 3.70: for `N` in good position to `C = [0,∞)ⁿ ⊕ W` with good complement `Y` and a
`C¹` map `τ : N ∩ C → Y₁` with `τ(0) = 0`, `Dτ(0) = 0`, `d_{N∩C}(v) = d_C(v + τ(v))` for all
`v ∈ N ∩ C \ N ∩ W` close to `0`. -/
def B : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (N : Submodule ℝ ((Emod n W).lvl 0)) [FiniteDimensional ℝ N],
    N ≤ (Emod n W).smooth →
    (interior (Subtype.val ⁻¹' quadC n W : Set N)).Nonempty →
    ∀ Y : Submodule ℝ ((Emod n W).lvl 0), IsGoodComplementSc (Emod n W) (quadC n W) N Y →
    ∀ τ : N → (Emod n W).lvl 1,
      (∀ v : N, (v : (Emod n W).lvl 0) ∈ quadC n W → (Emod n W).toBase 1 (τ v) ∈ Y) →
      ContDiffOn ℝ 1 τ (Subtype.val ⁻¹' quadC n W : Set N) →
      τ 0 = 0 →
      HasFDerivWithinAt τ (0 : N →L[ℝ] (Emod n W).lvl 1) (Subtype.val ⁻¹' quadC n W : Set N) 0 →
      ∃ δ > (0 : ℝ), ∀ v : N, (v : (Emod n W).lvl 0) ∈ quadC n W →
        (v : (Emod n W).lvl 0) ∉ Wsub n W → ‖v‖ < δ →
          degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadC n W) v =
            dC n W ((v : (Emod n W).lvl 0) + (Emod n W).toBase 1 (τ v))

end RoundTrip.V3_57
