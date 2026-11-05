import Polyfold
/-! Blind formalization of V1_31 (the text's §1.1, after Definition 1.1, p. 6).

Text: a finite-dimensional Banach space has precisely one sc-structure, the constant one
`E_m = E`; on an infinite-dimensional space the constant structure is not an sc-structure,
because property (1) fails.

Choices:
- Setting: no project definition is used.  The text's notion of an sc-structure is written from
  Mathlib alone, with the prelude of `RoundTrip/Blind/V1_1.lean`: the levels are normed spaces
  `X m` (`X 0` is the text's `E = E₀`) with continuous linear maps `ι m : X (m+1) → X m`
  presenting the inclusions `E_{m+1} ⊂ E_m`; `IsScStructure X ι` says: every `X m` complete,
  every `ι m` injective and a compact operator (`IsCompactOperator`; this is property (1) — the
  text's (1) for `m < n` follows by composing), and `E_∞ = ⋂ₘ E_m` (`smoothPts`, via the
  composite inclusions `inclTo0 m : X m → X 0`) dense in every `E_m` (property (2)).
  Spaces live in `Type` (as the project's levels do; nothing depends on the universe).
- "precisely one sc-structure, the constant one" is read as the conjunction of
  (a) existence: the constant structure `X m = V`, `ι m = id` on a finite-dimensional `V` is an
      sc-structure (completeness is automatic in finite dimension, so `V` is only a normed space);
  (b) uniqueness: every sc-structure on a finite-dimensional `E₀` has `E_m = E₀` for all `m`,
      with the same topology: the composite inclusion `E_m → E₀` is (the underlying map of) a
      continuous linear equivalence.  The norms on `E_m` are part of the data of an
      sc-structure, so "the constant one" can only mean this (up to equivalent norms, which in
      finite dimension is no restriction).
- "on an infinite-dimensional space the constant structure is not an sc-structure, because
  property (1) fails": for every infinite-dimensional Banach space `V`, the identity `V → V` (the
  inclusion `E_{m+1} → E_m` of the constant structure) is not a compact operator, and the constant
  structure is not an sc-structure.  Both conjuncts are stated.
- Nothing looks false.
-/
namespace RoundTrip.V1_31

section
variable (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]

/-- The composite inclusion `E_m → E₀` of the sequence presented by `ι m : E_{m+1} → E_m`. -/
def inclTo0 (ι : ∀ m, X (m + 1) →L[ℝ] X m) : ∀ m, X m →L[ℝ] X 0
  | 0 => ContinuousLinearMap.id ℝ (X 0)
  | m + 1 => (inclTo0 ι m).comp (ι m)

/-- The smooth points `E_∞ = ⋂ₘ E_m ⊆ E₀`. -/
def smoothPts (ι : ∀ m, X (m + 1) →L[ℝ] X m) : Set (X 0) :=
  ⋂ m, Set.range (inclTo0 X ι m)

/-- **Definition 1.1**: `E₀ ⊇ E₁ ⊇ ⋯` (presented by `X`, `ι`) is an sc-structure on `E = X 0`:
Banach levels, injective compact inclusions (property (1)), `E_∞` dense in every `E_m`
(property (2)). -/
def IsScStructure (ι : ∀ m, X (m + 1) →L[ℝ] X m) : Prop :=
  (∀ m, CompleteSpace (X m)) ∧
  (∀ m, Function.Injective (ι m)) ∧
  (∀ m, IsCompactOperator (ι m)) ∧
  (∀ m, Dense (inclTo0 X ι m ⁻¹' smoothPts X ι))

end

/-- A finite-dimensional space has exactly one sc-structure, the constant one; on an
infinite-dimensional Banach space the constant structure violates (1). -/
def B : Prop :=
  -- existence: the constant structure on a finite-dimensional space is an sc-structure
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
      IsScStructure (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V)) ∧
  -- uniqueness: every sc-structure on a finite-dimensional `E₀` has `E_m = E₀` (topologically)
  (∀ (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
      (ι : ∀ m, X (m + 1) →L[ℝ] X m), IsScStructure X ι → FiniteDimensional ℝ (X 0) →
      ∀ m, ∃ φ : X m ≃L[ℝ] X 0, ⇑φ = ⇑(inclTo0 X ι m)) ∧
  -- infinite dimension: property (1) fails for the constant structure, which is therefore not
  -- an sc-structure
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V],
      ¬ FiniteDimensional ℝ V →
      ¬ IsCompactOperator (ContinuousLinearMap.id ℝ V) ∧
      ¬ IsScStructure (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V))

end RoundTrip.V1_31
