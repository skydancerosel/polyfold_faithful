import Polyfold
/-! Blind formalization of V4_8 (the text's §4.1, proof of Lemma 4.7 (ii), p. 149).

Text: "`Dr(o)` is a sc⁺-operator, since `r` is a sc⁺-map.  Consequently `Dr(o)` is a compact
operator between every level," and the image of the projection `Dr(o)` must be
finite-dimensional.

Choices:
- Setting (that of Lemma 4.7): `E : ScBanach` (levels in `Type`, forced by `ScBanach`),
  `C ⊆ E₀`, `r : ScRetraction E C` an sc⁺-retraction (the project's `r.IsScPlus`, checked with
  `#print`: `r(U) ⊆ E₁` and the lift `U → E¹` is sc-smooth; agreement with Definition 4.4 is item
  V4_9), `O = r(U)` and `o ∈ O`.  I state the three claims for this `r` and every `o ∈ O`, as the
  text does, not for general sc⁺-maps (the item's title states the general principle; the quoted
  text applies it to `r` at `o ∈ O`, which is a smooth point by Lemma 4.7 (i)).
- `o ∈ O` enters as a level-1 point `o₁` with `ι₁ o₁ ∈ O` (every point of `O` lies in `E₁`
  since `r(U) ⊆ E₁`); `Dr(o)` is `scDeriv r.U r.toFun o₁` (the project's chosen derivative
  family; unique at points of `U₁`).
- "sc⁺-operator" (Definition 1.4): my own `IsScPlusOperatorB`: for every `m`, `Dr(o)` maps `E_m`
  into `E_{m+1}`, by a continuous linear map `E_m → E_{m+1}` (intertwined with the inclusions into
  `E₀`).
- "compact operator between every level": my own `IsCompactOnLevelsB`: for every `m`, the map
  induced by `Dr(o)` on `E_m` is a continuous linear `E_m → E_m` which is a compact operator
  (Mathlib's `IsCompactOperator`).
- "the image of the projection `Dr(o)` is finite-dimensional": `FiniteDimensional ℝ` of the range
  of `Dr(o) : E₀ → E₀`.  That `Dr(o)` is a projection (Definition 2.3 remark, item V2_1) is
  presupposed, not asserted.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_8
open Polyfold

/-- `T : E₀ → E₀` is an **sc⁺-operator** `E → E` (Definition 1.4): for every `m` it maps `E_m`
into `E_{m+1}` by a continuous linear map `E_m → E_{m+1}`. -/
def IsScPlusOperatorB (E : ScBanach) (T : E.lvl 0 →L[ℝ] E.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ S : E.lvl m →L[ℝ] E.lvl (m + 1),
    ∀ x : E.lvl m, E.toBase (m + 1) (S x) = T (E.toBase m x)

/-- `T : E₀ → E₀` induces a compact operator `E_m → E_m` on every level `m`. -/
def IsCompactOnLevelsB (E : ScBanach) (T : E.lvl 0 →L[ℝ] E.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ S : E.lvl m →L[ℝ] E.lvl m,
    (∀ x : E.lvl m, E.toBase m (S x) = T (E.toBase m x)) ∧ IsCompactOperator S

/-- Proof of Lemma 4.7 (ii): for an sc⁺-retraction `r` and `o ∈ O`, `Dr(o)` is an sc⁺-operator,
hence compact on every level, and its image is finite-dimensional. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (r : ScRetraction E C), r.IsScPlus →
    ∀ o₁ : E.lvl 1, E.toBase 1 o₁ ∈ r.retract →
      IsScPlusOperatorB E (scDeriv r.U r.toFun o₁) ∧
      IsCompactOnLevelsB E (scDeriv r.U r.toFun o₁) ∧
      FiniteDimensional ℝ
        (LinearMap.range (scDeriv r.U r.toFun o₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0))

end RoundTrip.V4_8
