import Polyfold
/-! Blind formalization of V1_19 (the text's §1.2, Corollary 1.20, p. 13).

Text: let `U` be relatively open in a partial quadrant of an sc-Banach space and `f : U → ℝᴺ`.
If for some `k` and all `0 ≤ l ≤ k` the map `f : U_l → ℝᴺ` is `C^{l+1}`, then `f` is `sc^{k+1}`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by the project's `ScBanach`); `C, U ⊆ E₀`
  with `IsRelOpenInQuadrant E C U` (checked with `#print`: `C` a partial quadrant, `U = O ∩ C`,
  `O` open).  `N k : ℕ`.
- `ℝᴺ` is `Fin N → ℝ` (sup norm; `C^{l+1}` does not depend on the norm), with its constant
  sc-structure `ScBanach.const (Fin N → ℝ)` (checked with `#print`: every level is `Fin N → ℝ`,
  inclusions the identity; level 0 is `Fin N → ℝ` by `rfl`).  `f : E₀ → ℝᴺ` is a total function;
  only its values on `U` matter.
- "`f : U_l → ℝᴺ`" is `f ∘ ι_l` on `U_l = E.lvlSet U l = ι_l⁻¹(U) ⊆ E_l`; "`C^{l+1}`" is
  Mathlib's `ContDiffOn ℝ (l+1)` on `U_l` (derivatives within the set).
- `sc^{k+1}` is the project's `IsSck (k+1)` (checked with `#print` and by `rfl`: `IsSck 0 = IsSc0`,
  `IsSck (j+1) = IsSc1 ∧ IsSck j` of the tangent map on `TU`; Definitions 1.12, 1.14, 1.15).
- "for some `k`": B quantifies over every `k` (the hypothesis is assumed for that `k`).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_19
open Polyfold

/-- If `f : U_l → ℝᴺ` is `C^{l+1}` for all `l ≤ k`, then `f : U → ℝᴺ` is `sc^{k+1}`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C U : Set (E.lvl 0)) (N : ℕ) (f : E.lvl 0 → (Fin N → ℝ)) (k : ℕ),
    IsRelOpenInQuadrant E C U →
    (∀ l : ℕ, l ≤ k → ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) →
      IsSck (k + 1) E (ScBanach.const (Fin N → ℝ)) U f

end RoundTrip.V1_19
