import Polyfold
/-! Blind formalization of V2_37 (the text's §2.3, Theorem 2.31, first statement, p. 35).

Text: for a retract `(O, C, E)` and a smooth `x ∈ O`, `dim(T_xO / T^R_xO) ≤ d_O(x)`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C O ⊆ E₀` with `(O, C, E)` an
  sc-smooth retract (`IsScRetract`, checked with `#print`: `O = r(U)` for an sc-smooth retraction
  `r : U → U`, `U` relatively open in the partial quadrant `C`).
- "smooth `x ∈ O`": `x ∈ O ∩ E_∞` (`E.smooth = ⋂ E_m`).  `x₁ ∈ E₁` is its (unique) lift to level 1,
  needed because the project's tangent data are indexed by points of `E₁`.
- `T_xO` (Definition 2.17, the fibre over `x` of `TO = Tr(TU)`) is the image `Dr(x)(E₀)` of the
  derivative of a retraction `r` onto `O` at `x` (`LinearMap.range (scDeriv r.U r x₁)`, `scDeriv`
  being the derivative family of `r` from the definition of `sc¹`, unique on `U₁`).  The fibre of
  `Tr(TU)` over `x ∈ O₁` equals `Dr(x)(E₀)` because `Dr(y) = Dr(r(y)) ∘ Dr(y)`.  Since the text's
  `T_xO` does not depend on `r`, B asserts the inequality for EVERY retraction `r` onto `O`.
- `E_x` and `T^R_xO = T_xO ∩ E_x` (Definition 2.27): for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`
  (`C = T₀⁻¹([0,∞)ⁿ ⊕ W)`), `E_x` is the subspace of `v` with `(Tv)_i = 0` for every `i` with
  `(Tx)_i = 0` (the project's `minimalSubspaceWith T x`, checked with `#print`: the kernel of
  `v ↦ ((Tv)_i)_{i ∈ I(x)}`).  `E_x` does not depend on `T` (it is the largest linear subspace of
  the tangent cone of `C` at `x`), so B asserts the inequality for EVERY presentation `T`.
- `dim(T_xO / T^R_xO)` is `quotDim (T_xO) (E_x) = finrank (T_xO / (T_xO ∩ E_x))` (checked; the
  junk value `0` for infinite dimension never occurs, the quotient embeds in `ℝ^{I(x)}`).
- `d_O(x)`: the text, just before Theorem 2.31, regards the retract `O` as an M-polyfold, and
  `d_O` is the degeneracy index of that M-polyfold (Definition 2.22: the minimum of `d_{C'}(φ(x))`
  over the charts `φ` around `x`).  This is the project's `MPolyfold.degIndex` of
  `LocalModel.toMPolyfold` (checked with `#print`: the M-polyfold on the subtype `↥O` with the
  single chart `id : O → O`, and `degIndex` = `sInf` of `d_{C'}(φ(x))` over all charts `φ`
  compatible with that atlas whose domain contains `x`).  I used it rather than `d_C(x)` (which
  would give a weaker statement, `d_O ≤ d_C`).
-/
namespace RoundTrip.V2_37
open Polyfold

/-- `dim(T_xO / T^R_xO) ≤ d_O(x)` at smooth points of a retract. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O) (x : E.lvl 0) (hx : x ∈ O),
    x ∈ E.smooth →
    ∀ (x₁ : E.lvl 1), E.toBase 1 x₁ = x →
    ∀ (R : ScRetraction E C), R.retract = O →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      C = T.lvl 0 ⁻¹' quadrant n W 0 →
        quotDim (LinearMap.range (scDeriv R.U R.toFun x₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0))
            (minimalSubspaceWith T x) ≤
          ((LocalModel.mk E C O hO).toMPolyfold ⟨x, hx⟩).degIndex ⟨x, hx⟩

end RoundTrip.V2_37
