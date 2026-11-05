import Polyfold
/-! Blind formalization of V4_12 (the text's §4.1, Lemma 4.7, p. 149).

Text: if `r` is an sc⁺-retraction onto `O`: (i) `O = O_∞`; (ii) at every `o ∈ O`,
`T_oO = Dr(o)E` is finite-dimensional.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`,
  `r : ScRetraction E C` (Definition 2.1, audited in V2_1: `r : U → U` sc-smooth and idempotent on
  `U` relatively open in the partial quadrant `C`).  "sc⁺-retraction" (Definition 4.4): the
  project's `r.IsScPlus` (checked with `#print`: `r(U) ⊆ E₁` and the lift `U → E¹` is sc-smooth;
  its agreement with the text is item V4_9).  `O = r(U)` (`r.retract`).
- (i) `O_∞ = O ∩ E_∞`, so `O = O_∞` says every `o ∈ O` is a smooth point; "smooth point" is my
  own `IsSmoothPointB` (`o` lifts to every level `E_m` along the composite inclusion
  `E_m → E₀`).
- (ii) `Dr(o)` needs `o ∈ U₁`; every `o ∈ O` is in `E₁` (by (i), or directly from
  `r(U) ⊆ E₁`), so I quantify over level-1 points `o₁` with `ι₁ o₁ ∈ O`; this covers all `o ∈ O`.
  `Dr(o)` is `scDeriv r.U r.toFun o₁` (the project's chosen derivative family of the `sc¹` map
  `r`; for `o ∈ U₁` the derivative `E₀ → E₀` is unique, `U₁` being relatively open in a partial
  quadrant of the dense subspace `E₁`).
- "`T_oO = Dr(o)E`": the text identifies the tangent space with `Dr(o)E`; I assert both the
  identification with the project's `tangentSpace E C O o₁` (Definition 2.17, checked with
  `#print`: the fibre over `o₁` of `TO = Tr'(TU')` for a chosen retraction `r'` onto `O`) and
  "finite-dimensional" as `FiniteDimensional ℝ` of the range of `Dr(o)` (a subspace of `E₀`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_12
open Polyfold

/-- `x ∈ E₀` is a smooth point: `x ∈ E_m` for every `m`. -/
def IsSmoothPointB (E : ScBanach) (x : E.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ y : E.lvl m, E.toBase m y = x

/-- Lemma 4.7: the retract `O` of an sc⁺-retraction `r` consists of smooth points, and at every
`o ∈ O` the tangent space `T_oO = Dr(o)E` is finite-dimensional. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (r : ScRetraction E C), r.IsScPlus →
    -- (i) `O = O_∞`
    (∀ o ∈ r.retract, IsSmoothPointB E o) ∧
    -- (ii) `T_oO = Dr(o)E` is finite-dimensional
    ∀ o₁ : E.lvl 1, E.toBase 1 o₁ ∈ r.retract →
      tangentSpace E C r.retract o₁ = Set.range (scDeriv r.U r.toFun o₁) ∧
      FiniteDimensional ℝ
        (LinearMap.range (scDeriv r.U r.toFun o₁ : E.lvl 0 →ₗ[ℝ] E.lvl 0))

end RoundTrip.V4_12
