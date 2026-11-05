import Polyfold
/-! Blind formalization of V2_33 (the text's §2.3, Remark 2.28, p. 33).

Text: `T^R_xO ⊂ C_xO ⊂ T_xO`; naively one might expect `C_xO` to be a partial quadrant in `T_xO`,
which in general is not the case.

Choices:
- Setting (as in `RoundTrip/Blind/V2_37.lean`, `V2_42.lean`): `E : ScBanach` (levels in `Type`,
  forced by `ScBanach`), `C, O ⊆ E₀` with `(O, C, E)` an sc-smooth retract (`IsScRetract`,
  checked with `#print`: `O = r(U)` for an `ScRetraction` `r`).  The remark refers to
  Definition 2.27, which is made at smooth points: "`x ∈ O_∞`" is `x ∈ O ∩ E_∞`
  (`E.smooth = ⋂ E_m`), with `x₁ ∈ E₁` its lift to level 1 (the project indexes tangent data by
  points of `E₁`).
- `T_xO = Dr(x)E` (Definition 2.17) is `tangentAt R x₁`, the range of `scDeriv R.U R.toFun x₁`
  for a retraction `R` onto `O` (independent of `R`, so all claims are made for EVERY such `R`).
- `E_x = {v | (Tv)_i = 0 for i ∈ I(x)}`, `C_x = {v | (Tv)_i ≥ 0 for i ∈ I(x)}`,
  `I(x) = {i | (Tx)_i = 0}`, for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W)`); they do not depend on `T`, so all claims are made for EVERY `T`.
  `T^R_xO = T_xO ∩ E_x` is the project's `reducedTangentSpaceWith R T x₁` and
  `C_xO = T_xO ∩ C_x` is `partialConeWith R T x₁` (both checked with `#print`: `range Dr(x) ⊓
  ker((T·)_i)_{i ∈ I(x)}` and `range Dr(x) ∩ {v | ∀ i, (Tx)_i = 0 → 0 ≤ (Tv)_i}`).
- First claim: the two set inclusions.
- Second claim, "in general is not the case": there EXIST a retract `(O, C, E)`, a smooth
  `x ∈ O` (with retraction `R` and presentation `T`) such that `C_xO` is not a partial quadrant in
  `T_xO`.  `T_xO` carries the sc-structure induced from `E` (`E.ofSubspace h`, `h` a proof that
  `T_xO` is an sc-subspace, which I require to exist so that the negation is not vacuous), and
  "partial quadrant" is `IsPartialQuadrant` (Definition 1.11, checked: `T'⁻¹([0,∞)^k ⊕ W')` for
  an sc-isomorphism `T'`), applied to the preimage of `C_xO` in the subtype.
- DOUBT: I believe the second claim is FALSE with these definitions of `C_x`, `C_xO`.  Sketch:
  since `r(C) ⊆ C` and `r(x) = x`, `P = Dr(x)` maps `C_x` into `C_x`, so `C_xO = P(C_x)
  = T^R_xO + cone(Pe_i)`; modulo `T^R_xO` this is the cone spanned by the columns of the
  `k × k` matrix `M_ij = λ_i(Pe_j)` (`k = d_C(x)`, `λ_i(e_j) = δ_ij`), which is nonnegative and
  idempotent; by Flor's theorem on nonnegative idempotent matrices its column cone is simplicial,
  so `C_xO ≅ [0,∞)^{rank M} ⊕ T^R_xO` would be a partial quadrant.  I formalized the claim
  literally anyway.
-/
namespace RoundTrip.V2_33
open Polyfold

/-- The tangent space `T_xO = Dr(x)E` computed with the retraction `R`, at the level-1 point
`x₁`. -/
noncomputable def tangentAt {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (x₁ : E.lvl 1) : Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv R.U R.toFun x₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Remark 2.28: `T^R_xO ⊆ C_xO ⊆ T_xO` at smooth points of a retract; and `C_xO` is not always a
partial quadrant in `T_xO`. -/
def B : Prop :=
  -- `T^R_xO ⊂ C_xO ⊂ T_xO`
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    ∀ x ∈ O, x ∈ E.smooth →
    ∀ (x₁ : E.lvl 1), E.toBase 1 x₁ = x →
    ∀ (R : ScRetraction E C), R.retract = O →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      C = T.lvl 0 ⁻¹' quadrant n W 0 →
        (↑(reducedTangentSpaceWith R T x₁) : Set (E.lvl 0)) ⊆ partialConeWith R T x₁ ∧
        partialConeWith R T x₁ ⊆ (↑(tangentAt R x₁) : Set (E.lvl 0))) ∧
  -- in general `C_xO` is not a partial quadrant in `T_xO`
  (∃ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O ∧
    ∃ x ∈ O, x ∈ E.smooth ∧
    ∃ (x₁ : E.lvl 1), E.toBase 1 x₁ = x ∧
    ∃ (R : ScRetraction E C), R.retract = O ∧
    ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      C = T.lvl 0 ⁻¹' quadrant n W 0 ∧
      ∃ h : E.IsScSubspace (tangentAt R x₁),
        ¬ IsPartialQuadrant (E.ofSubspace h) {v | Subtype.val v ∈ partialConeWith R T x₁})

end RoundTrip.V2_33
