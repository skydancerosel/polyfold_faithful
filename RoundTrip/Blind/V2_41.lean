import Polyfold
/-! Blind formalization of V2_41 (the text's §2.4, Proposition 2.35, p. 41; discussion pp. 40–41).

Text: for a tame retraction and a smooth `x ∈ O`, `(1 − Dr(x))E ⊆ E_x`, so in condition (2) one
can take `A = (1 − Dr(x))E`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`, `R : ScRetraction E C`
  an sc-smooth retraction `r : U → U` (checked with `#print`), `O = r(U)`.
- "Tame retraction": the project's `ScRetraction.IsTame` (Definition 2.34, checked with `#print`:
  for EVERY presentation `T` of `C`, (1) `d_C(r(x)) = d_C(x)` on `U` and (2) at every smooth
  `x ∈ O₁` some `A ≤ E_x` with `E = Dr(x)E ⊕ A` an sc-splitting; my `RoundTrip/Blind/V2_40.lean`
  states this is the text's notion).
- "smooth `x ∈ O`": `x ∈ O ∩ E_∞`, `x₁ ∈ E₁` its lift (the project indexes derivatives by points
  of `E₁`).  `Dr(x)` is `scDeriv R.U R.toFun x₁` (the derivative family of the sc¹ map `r`,
  unique on `U₁`); `(1 − Dr(x))E` is the range of `1 − Dr(x)`; `T_xO = Dr(x)E` its range.
- `E_x = {v | (Tv)_i = 0 for i ∈ I(x)}`, `I(x) = {i | (Tx)_i = 0}`, for a presentation
  `T : E ≅ ℝⁿ ⊕ W` of `C` (the project's `minimalSubspaceWith T x`, checked with `#print`: the
  kernel of `v ↦ ((Tv)_i)_{i ∈ I(x)}`); presentation-independent, so B is stated for EVERY `T`.
- "In condition (2) one can take `A = (1 − Dr(x))E`": `A` is an sc-subspace, `A ⊆ E_x`, and
  `E = T_xO ⊕ A` is an sc-splitting (`IsScSplitting`, checked: both sc-subspaces and a direct sum
  on every level).  B is the conjunction of the inclusion and this.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_41
open Polyfold

/-- The tangent space `T_xO = Dr(x)E` computed with the retraction `R`, at the level-1 point
`x₁`. -/
noncomputable def tangentAt {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (x₁ : E.lvl 1) : Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv R.U R.toFun x₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- `(1 − Dr(x))E`. -/
noncomputable def complB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (x₁ : E.lvl 1) : Submodule ℝ (E.lvl 0) :=
  LinearMap.range ((1 - scDeriv R.U R.toFun x₁ : E.lvl 0 →L[ℝ] E.lvl 0) : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Proposition 2.35: for a tame retraction and smooth `x ∈ O`, `(1 − Dr(x))E ⊆ E_x`, and
`A = (1 − Dr(x))E` is an sc-complement of `T_xO` inside `E_x`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (R : ScRetraction E C), R.IsTame →
    ∀ x ∈ R.retract, x ∈ E.smooth →
    ∀ (x₁ : E.lvl 1), E.toBase 1 x₁ = x →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      C = T.lvl 0 ⁻¹' quadrant n W 0 →
        -- `(1 − Dr(x))E ⊆ E_x`
        complB R x₁ ≤ minimalSubspaceWith T x ∧
        -- `A = (1 − Dr(x))E` satisfies condition (2)
        (E.IsScSubspace (complB R x₁) ∧ complB R x₁ ≤ minimalSubspaceWith T x ∧
          E.IsScSplitting (tangentAt R x₁) (complB R x₁))

end RoundTrip.V2_41
