import Polyfold
/-! Blind formalization of V2_32 (the text's §2.3, Definition 2.27, p. 33).

Text: for a retract `(O, C, E)` and a smooth `x ∈ O`: `C_xO := T_xO ∩ C_x` (the partial cone) and
`T^R_xO := T_xO ∩ E_x` (the reduced tangent space).

Choices:
- This item is a definition; it asserts no further property.  Setting: `E : ScBanach` (levels in
  `Type`, forced by `ScBanach`), `C, O ⊆ E₀`, and an sc-smooth retraction `R : ScRetraction E C`
  with `R.retract = O` (checked with `#print`: `R.U` relatively open in the partial quadrant `C`,
  `R.toFun` sc-smooth on `U`, `r(U) ⊆ U`, `r ∘ r = r` on `U`, `R.retract = r(U)`), so `(O, C, E)`
  is a retract (Definition 2.3).
- "smooth `x ∈ O`": `x ∈ O ∩ E_∞` (`E.smooth = ⋂_m E_m`); the point is given as `x₁ ∈ E₁` with
  `x = E.toBase 1 x₁` (the project's notions take the level-1 point).
- `T_xO` (Definition 2.17): the fibre over `x₁` of `TO = Tr(TU)` (Definition 2.5), computed with
  `R` (`TO` does not depend on the retraction, Proposition 2.4): `TxOB R x₁ = {h | (x₁, h) ∈
  Tr(TU)}`, with `Tr` the project's Chapter-1 `tangentMap R.U R.toFun` (`(x, h) ↦ (r(x),
  Dr(x)h)`) and `TU = E.tangentSet R.U` (`U₁ × E₀`).  I did not use `tangentSpace`/
  `retractTangent`, which pick a retraction by choice.
- `E_x` and `C_x` (§2.3, p. 32) are defined for `C = [0,∞)^n ⊕ W` (my definitions `ExB`, `CxB`,
  copied from `RoundTrip/Blind/V2_31.lean`); a general partial quadrant `C` is presented by an
  sc-isomorphism `T : E ≅ ℝⁿ ⊕ W` with `C = T⁻¹([0,∞)ⁿ ⊕ W)` (Definition 1.11), and
  `E_x = T⁻¹(E_{Tx})`, `C_x = T⁻¹(C_{Tx})`.  These do not depend on `T` (`E_x`, `C_x` are the
  lineality space and the tangent cone of `C` at `x`), so B quantifies over EVERY presentation.
- B: the project's `partialConeWith R T x₁` and `reducedTangentSpaceWith R T x₁` (Definitions 2.27,
  2.38 per their docstrings) are `T_xO ∩ C_x` and `T_xO ∩ E_x`.
-/
namespace RoundTrip.V2_32
open Polyfold

/-- The standard sc-Banach space `ℝ^k ⊕ W`. -/
noncomputable abbrev EB (k : ℕ) (W : ScBanach) : ScBanach := (ScBanach.const (Fin k → ℝ)).prod W

section
variable {k : ℕ} {W : ScBanach}

/-- The coordinate `a ↦ a_i` on `(ℝ^k ⊕ W)₀`. -/
noncomputable def coordB (i : Fin k) : (EB k W).lvl 0 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i ∘L ContinuousLinearMap.fst ℝ (Fin k → ℝ) (W.lvl 0)

/-- `E_i = {a | a_i = 0}`. -/
noncomputable def EiB (i : Fin k) : Submodule ℝ ((EB k W).lvl 0) :=
  LinearMap.ker (coordB (W := W) i : (EB k W).lvl 0 →ₗ[ℝ] ℝ)

/-- `I(x) = {i | x ∈ E_i}`. -/
def IxB (x : (EB k W).lvl 0) : Set (Fin k) :=
  {i | x ∈ EiB (W := W) i}

/-- `E_x = ⋂_{i ∈ I(x)} E_i`. -/
noncomputable def ExB (x : (EB k W).lvl 0) : Submodule ℝ ((EB k W).lvl 0) :=
  ⨅ i ∈ IxB x, EiB (W := W) i

/-- `C_x = ⋂_{i ∈ I(x)} H_i`, `H_i = {a | a_i ≥ 0}`. -/
def CxB (x : (EB k W).lvl 0) : Set ((EB k W).lvl 0) :=
  ⋂ i ∈ IxB x, {a | 0 ≤ coordB (W := W) i a}
end

/-- `T_xO`: the fibre over `x₁` of `TO = Tr(TU)`. -/
def TxOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) (x₁ : E.lvl 1) :
    Set (E.lvl 0) :=
  {h | (x₁, h) ∈ Polyfold.tangentMap R.U R.toFun '' E.tangentSet R.U}

/-- Definition 2.27: the project's partial cone and reduced tangent space are `T_xO ∩ C_x` and
`T_xO ∩ E_x`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (R : ScRetraction E C), R.retract = O →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso E (EB n W)), C = T.lvl 0 ⁻¹' quadrant n W 0 →
    ∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ O → E.toBase 1 x₁ ∈ E.smooth →
      partialConeWith R T x₁ = TxOB R x₁ ∩ T.lvl 0 ⁻¹' CxB (T.lvl 0 (E.toBase 1 x₁)) ∧
      (reducedTangentSpaceWith R T x₁ : Set (E.lvl 0)) =
        TxOB R x₁ ∩ T.lvl 0 ⁻¹' (ExB (T.lvl 0 (E.toBase 1 x₁)) : Set _)

end RoundTrip.V2_32
