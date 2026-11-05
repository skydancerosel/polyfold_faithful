import Polyfold
/-! Blind formalization of V2_1 (the text's §2.1, Definition 2.1, p. 18, and the remark after
Definition 2.3).

Text: for a tuple `(U, C, E)`, `U` relatively open in the partial quadrant `C` of `E`, an
sc-smooth map `r : U → U` with `r ∘ r = r` is an *sc-smooth retraction* on `U`.  After
Definition 2.3: for `x ∈ U₁` the chain rule gives `Dr(r(x)) ∘ Dr(x) = Dr(x)`, so for `x ∈ O₁`
(`O = r(U)`), `Dr(x)` is a projection.

Choices:
- This item is a definition plus a property.  Setting: `E : ScBanach` (levels in `Type`, forced by
  `ScBanach`), `C U ⊆ E₀`, and a total map `r : E₀ → E₀` (only its values on `U` matter; `r : U → U`
  is `Set.MapsTo r U U`).
- The tuple `(U, C, E)` ("`U` relatively open in the partial quadrant `C`") is the project's
  `IsRelOpenInQuadrant E C U` (checked with `#print`: `C` is a partial quadrant
  (`IsPartialQuadrant`, Definition 1.11) and `U = W ∩ C` for an open `W ⊆ E₀`).
- "sc-smooth map `r : U → U`" is `IsScSmooth U r` (Definition 1.15, the project's `∀ k, IsSck k`,
  checked: `IsSck (k+1)` is `sc¹` plus `IsSck k` of the tangent map) together with `r(U) ⊆ U`;
  "`r ∘ r = r`" is asserted on `U`.  My definition is `IsScRetractionB`.
- Definition part of B: `IsScRetractionB E C U r` holds iff `(U, r)` is (the domain and map of) a
  project `ScRetraction E C` (checked with `#print`: fields `U`, `toFun`, `relOpen`, `mapsTo`,
  `isScSmooth`, `idem`).
- `Dr(x)` for `x ∈ U₁` is `scDeriv U r x₁` (the project's chosen derivative family of the `sc¹` map
  `r`, at the level-1 point `x₁` over `x`).  I accept this choice: for `x ∈ U₁` the derivative
  `Dr(x) : E₀ → E₀` is unique (`U₁` is relatively open in a partial quadrant of `E₁`, a set of
  unique differentiability, and `E₁` is dense in `E₀`).
- `r(x)` for `x ∈ U₁` is in `U₁` (`r` is `sc⁰`); it enters as a level-1 point `y₁` with
  `ι₁ y₁ = r(ι₁ x₁)` (unique by injectivity of `ι₁ : E₁ → E₀`).
- `O₁ = O ∩ E₁` with `O = r(U)` (Definition 2.3); "projection" = idempotent bounded linear
  operator, `Dr(x) ∘ Dr(x) = Dr(x)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_1
open Polyfold

/-- **Definition 2.1**: `r : U → U` is an sc-smooth retraction on the relatively open subset `U`
of the partial quadrant `C ⊆ E`: sc-smooth, `r(U) ⊆ U`, and `r ∘ r = r` on `U`. -/
def IsScRetractionB (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0) : Prop :=
  IsRelOpenInQuadrant E C U ∧ Set.MapsTo r U U ∧ IsScSmooth U r ∧ ∀ x ∈ U, r (r x) = r x

/-- Definition 2.1 (the project's `ScRetraction` is the text's notion), and: `Dr(r(x)) ∘ Dr(x) =
Dr(x)` for `x ∈ U₁`, so `Dr(x)` is a projection for `x ∈ O₁`. -/
def B : Prop :=
  (∀ (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0),
    (∃ R : ScRetraction E C, R.U = U ∧ R.toFun = r) ↔ IsScRetractionB E C U r) ∧
  (∀ (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0),
    IsScRetractionB E C U r →
      -- `Dr(r(x)) ∘ Dr(x) = Dr(x)` for `x ∈ U₁`
      (∀ x₁ y₁ : E.lvl 1, E.toBase 1 x₁ ∈ U → E.toBase 1 y₁ = r (E.toBase 1 x₁) →
        (scDeriv U r y₁).comp (scDeriv U r x₁) = scDeriv U r x₁) ∧
      -- `Dr(x)` is a projection for `x ∈ O₁`, `O = r(U)`
      (∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ r '' U →
        (scDeriv U r x₁).comp (scDeriv U r x₁) = scDeriv U r x₁))

end RoundTrip.V2_1
