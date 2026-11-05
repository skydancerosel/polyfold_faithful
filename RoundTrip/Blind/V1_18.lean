import Polyfold
/-! Blind formalization of V1_18 (the text's §1.2, Proposition 1.19, p. 13).

Text: let `U` be relatively open in a partial quadrant of `E` and `F` an sc-Banach space.  Assume
that for every `m ≥ 0` and `0 ≤ l ≤ k` the map `f : U → F` induces a map `f : U_{m+l} → F_m` of
class `C^{l+1}`.  Then `f` is `sc^{k+1}`.

Choices:
- Setting: `E F : ScBanach` (levels in `Type`, forced by the project's `ScBanach`); `C, U ⊆ E₀`
  with `IsRelOpenInQuadrant E C U` (checked with `#print`: `C` a partial quadrant, `U = O ∩ C`,
  `O` open).  `f : E₀ → F₀` is a total function; only its values on `U` matter.  `k : ℕ`.
- "`f` induces a map `f : U_{m+l} → F_m`" is the hypothesis that `f(x) ∈ F_m` for every
  `x ∈ U_{m+l}` (`f (ι x) ∈ range (ι_m : F_m → F₀)`), and the induced map is
  `levelTo f (m+l) m : E_{m+l} → F_m` (`x ↦` the point of `F_m` over `f(x)`, via
  `Function.invFun`).  `U_{m+l}` is `E.lvlSet U (m+l) = ι⁻¹(U) ⊆ E_{m+l}`.
- "of class `C^{l+1}`" is Mathlib's `ContDiffOn ℝ (l+1)` on `U_{m+l}` (derivatives within the
  set; it is locally a convex set with nonempty interior, so this is the usual notion with
  one-sided derivatives at the boundary).
- `sc^{k+1}` is the project's `IsSck (k+1) E F U f` (checked with `#print` and by `rfl`:
  `IsSck 0 = IsSc0`, `IsSck (j+1) = IsSc1 ∧ IsSck j` of the tangent map on `TU`; this is
  Definitions 1.12, 1.14, 1.15).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_18
open Polyfold

/-- The map `E_a → F_b` induced by `f : E₀ → F₀`: the point of `F_b` over `f(x)` (junk if none). -/
noncomputable def levelTo {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (a b : ℕ) :
    E.lvl a → F.lvl b :=
  fun x => Function.invFun (F.toBase b) (f (E.toBase a x))

/-- If `f : U_{m+l} → F_m` is `C^{l+1}` for all `m` and `l ≤ k`, then `f` is `sc^{k+1}`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) (k : ℕ),
    IsRelOpenInQuadrant E C U →
    (∀ m l : ℕ, l ≤ k →
      (∀ x ∈ E.lvlSet U (m + l), f (E.toBase (m + l) x) ∈ Set.range (F.toBase m)) ∧
      ContDiffOn ℝ (l + 1) (levelTo f (m + l) m) (E.lvlSet U (m + l))) →
      IsSck (k + 1) E F U f

end RoundTrip.V1_18
