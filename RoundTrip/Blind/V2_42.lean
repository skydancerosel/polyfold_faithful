import Polyfold
/-! Blind formalization of V2_42 (the text's §2.4, Proposition 2.36, p. 41).

Text: for a tame retract `(O, C, E)` and a smooth `x ∈ O`: `T^R_xO` (an sc-subspace, per the
item's title) has codimension `d_O(x)` in `T_xO`, `dim(T_xO / T^R_xO) = d_O(x)` (13), and the
partial cone `C_xO` is a partial quadrant in `T_xO`; for every `x ∈ O`, `d_O(x) = d_C(x)` (14).

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C, O ⊆ E₀` with `(O, C, E)`
  a tame sc-smooth retract: `IsTameRetract E C O` (Definition 2.34, checked with `#print`:
  `O = r(U)` for an `ScRetraction` `r` with `r.IsTame`, i.e. for every presentation `T` of `C`,
  `d_C(r(x)) = d_C(x)` on `U` and at every smooth `x ∈ O` the space `Dr(x)E` has an sc-complement
  inside `E_x`).  `hO : IsScRetract E C O` is the (redundant) retract proof needed to build the
  M-polyfold `O`.
- "smooth `x ∈ O`": `x ∈ O ∩ E_∞` (`E.smooth = ⋂ E_m`); `x₁ ∈ E₁` is its lift to level 1 (the
  project indexes tangent data by points of `E₁`).
- `T_xO` (Definition 2.17) is `Dr(x)E` = range of `scDeriv R.U R.toFun x₁` for a retraction `R`
  onto `O` (the fibre over `x` of `Tr(TU)`; `Dr(y) = Dr(r(y)) Dr(y)` gives equality).  The text's
  `T_xO` does not depend on `R`, so the claims are asserted for EVERY retraction `R` onto `O`.
- `E_x`, `C_x` (Definitions 2.27, 2.33), for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W)`): `E_x = {v | (Tv)_i = 0 for i ∈ I(x)}`, `C_x = {v | (Tv)_i ≥ 0 for
  i ∈ I(x)}`, `I(x) = {i | (Tx)_i = 0}`.  `T^R_xO = T_xO ∩ E_x` is the project's
  `reducedTangentSpaceWith R T x₁` and `C_xO = T_xO ∩ C_x` is `partialConeWith R T x₁` (both
  checked with `#print`, via `minimalSubspaceWith` and `partialQuadrantAtWith`, which are exactly
  the sets above).  They do not depend on `T`; B asserts the claims for EVERY presentation `T`.
- "`T^R_xO` is an sc-subspace": `E.IsScSubspace (T^R_xO)` (checked: closed, and smooth points
  dense in every level `T^R_xO ∩ E_m`).  Being an sc-subspace of `E` contained in `T_xO` is the
  same as being an sc-subspace of `T_xO` with its induced filtration.
- Codimension: `rank (T_xO / T^R_xO) = d_O(x)` as cardinals (`Module.rank`, so an infinite
  codimension is not mistaken for `0`).
- "`C_xO` is a partial quadrant in `T_xO`": `T_xO` with the sc-structure induced from `E`
  (`E.ofSubspace h` for `h : E.IsScSubspace T_xO`, asserted to exist), and the preimage of `C_xO`
  in it satisfies `IsPartialQuadrant` (Definition 1.11, checked: the preimage of `[0,∞)^k ⊕ W'`
  under an sc-isomorphism).
- `d_O(x)`: the text regards the retract `O` as an M-polyfold; `d_O` is its degeneracy index
  (Definition 2.22).  This is `MPolyfold.degIndex` of `LocalModel.toMPolyfold` (checked: the
  M-polyfold on `↥O` with the single chart `id : O → O`; `degIndex` = minimum of
  `d_{C'}(φ(x))` over all charts compatible with that atlas around `x`), as in
  `RoundTrip/Blind/V2_37.lean`.  `d_C(x)` is the project's `degIndex E C x` (Definition 1.23,
  checked: the number of vanishing half-line coordinates of `x`, for a chosen presentation).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_42
open Polyfold

/-- The tangent space `T_xO = Dr(x)E` computed with the retraction `R`, at the level-1 point
`x₁`. -/
noncomputable def tangentAt {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (x₁ : E.lvl 1) : Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv R.U R.toFun x₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Proposition 2.36: at a smooth point of a tame retract, `T^R_xO` is an sc-subspace of
codimension `d_O(x)` in `T_xO` and `C_xO` is a partial quadrant in `T_xO`; and `d_O = d_C` on
`O`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O), IsTameRetract E C O →
    (∀ (x : E.lvl 0) (hx : x ∈ O), x ∈ E.smooth →
      ∀ (x₁ : E.lvl 1), E.toBase 1 x₁ = x →
      ∀ (R : ScRetraction E C), R.retract = O →
      ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
        C = T.lvl 0 ⁻¹' quadrant n W 0 →
          -- `T^R_xO` is an sc-subspace
          E.IsScSubspace (reducedTangentSpaceWith R T x₁) ∧
          -- (13): `dim(T_xO / T^R_xO) = d_O(x)`
          Module.rank ℝ (tangentAt R x₁ ⧸
              Submodule.comap (tangentAt R x₁).subtype (reducedTangentSpaceWith R T x₁)) =
            (((LocalModel.mk E C O hO).toMPolyfold ⟨x, hx⟩).degIndex ⟨x, hx⟩ : Cardinal) ∧
          -- `C_xO` is a partial quadrant in `T_xO`
          ∃ h : E.IsScSubspace (tangentAt R x₁),
            IsPartialQuadrant (E.ofSubspace h) {v | Subtype.val v ∈ partialConeWith R T x₁}) ∧
    -- (14): `d_O = d_C` on `O`
    (∀ (x : E.lvl 0) (hx : x ∈ O),
      ((LocalModel.mk E C O hO).toMPolyfold ⟨x, hx⟩).degIndex ⟨x, hx⟩ = degIndex E C x)

end RoundTrip.V2_42
