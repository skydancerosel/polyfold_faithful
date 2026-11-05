import Polyfold
/-! Blind formalization of V1_3 (the text's §1.1, Definition 1.4 and the remark after it, p. 7).
Choices:
- This item is a definition with an asserted property.  Setting: `E F : ScBanach` (levels in
  `Type`); `E_m ⊆ E₀` is presented by the composite inclusion `E.toBase m` (as in
  `RoundTrip/Blind/V1_2.lean`, whose `IsScOperatorText` prelude is copied here).
- `IsScPlusText S` (Definition 1.4), for a linear `S : E₀ → F₀`: `S` is an sc-operator `E → F`,
  and `S : E → F¹` is an sc-operator, i.e. for every `m` there is a continuous
  `S_m : E_m → F_{m+1} = (F¹)_m` with `ι_{m+1} ∘ S_m = S ∘ ι_m` (this contains `S(E_m) ⊆ F_{m+1}`).
- "sc-compact: `S : E_m → F_m` is compact for every `m`": `IsScCompactText S`, for every `m` the
  induced map `S_m : E_m → F_m` (the unique `S_m` with `ι_m ∘ S_m = S ∘ ι_m`) is a compact
  operator (Mathlib's `IsCompactOperator`: some neighbourhood of `0` is mapped into a compact set).
- B is the conjunction of (1) the definition, as a characterization of the project's `ScPlus E F`
  (`= ScOperator E F.shift`, read with `#print`; its operator `E → F` is `ScPlus.toScOperator`,
  `F.shiftIncl ∘ S`): a linear map is an sc⁺-operator iff it is the level-0 map of an
  `ScPlus E F`; and (2) the asserted property: every sc⁺-operator is sc-compact.
-/
namespace RoundTrip.V1_3
open Polyfold

/-- `T : E → F` is an sc-operator (Definition 1.3). -/
def IsScOperatorText {E F : ScBanach} (T : E.lvl 0 →ₗ[ℝ] F.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ Tm : E.lvl m → F.lvl m,
    (∀ x, F.toBase m (Tm x) = T (E.toBase m x)) ∧ Continuous Tm

/-- **Definition 1.4**: `S` is an sc⁺-operator: an sc-operator `E → F` which is also an
sc-operator `E → F¹` (it maps `E_m` continuously into `F_{m+1}`). -/
def IsScPlusText {E F : ScBanach} (S : E.lvl 0 →ₗ[ℝ] F.lvl 0) : Prop :=
  IsScOperatorText S ∧
    ∀ m : ℕ, ∃ Sm : E.lvl m → F.lvl (m + 1),
      (∀ x, F.toBase (m + 1) (Sm x) = S (E.toBase m x)) ∧ Continuous Sm

/-- `S` is sc-compact: every induced map `S : E_m → F_m` is a compact operator. -/
def IsScCompactText {E F : ScBanach} (S : E.lvl 0 →ₗ[ℝ] F.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ Sm : E.lvl m → F.lvl m,
    (∀ x, F.toBase m (Sm x) = S (E.toBase m x)) ∧ IsCompactOperator Sm

/-- Definition 1.4: the project's `ScPlus` are the text's sc⁺-operators, and every sc⁺-operator
is sc-compact. -/
def B : Prop :=
  (∀ (E F : ScBanach) (S : E.lvl 0 →ₗ[ℝ] F.lvl 0),
    (∃ S' : ScPlus E F, ∀ x, S'.toScOperator.lvl 0 x = S x) ↔ IsScPlusText S) ∧
  (∀ (E F : ScBanach) (S : E.lvl 0 →ₗ[ℝ] F.lvl 0), IsScPlusText S → IsScCompactText S)

end RoundTrip.V1_3
