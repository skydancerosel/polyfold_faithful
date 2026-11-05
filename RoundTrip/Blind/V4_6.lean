import Polyfold
/-! Blind formalization of V4_6 (the text's §4.1, Remark 4.3, p. 148).

Text: if `X₀ = X_∞`, `1₀¹ : X → X¹` has the inverse `1₁⁰`, which is always sc-smooth; so if
`1₀¹` is sc-smooth it is an sc-diffeomorphism.  It is possible that `X¹ ≠ X` as M-polyfolds
although the underlying sets agree.  A finite-dimensional space with the constant structure has
`X = X¹`.

Choices:
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X`.  `X_m` is the
  project's `P.levelSet m` (checked: points mapped into `E_m` by some chart of `P`), `X_∞` is
  `P.smoothSet = ⋂ X_m`, and `X¹` is the project's `P.shift` (the level `X₁` with the charts
  `(V₁, φ, (O₁, C₁, E¹))`, an M-polyfold on the type `P.Level 1 = X₁`; its paracompactness is a
  project instance found by instance search).
- `1₁⁰ : X¹ → X` is the inclusion `P.levelVal 1` (checked: `Subtype.val`).  `1₀¹ : X → X¹` is
  `P.toLevelOne x₀` (checked: `x ↦ x` on `X₁`, the junk value `x₀` off `X₁`); under `X₀ = X_∞`
  (or `X₀ = X₁`) the junk is never used, and every claim is made for every junk value `x₀`
  (except in the existence claim, see below).
- "`1₁⁰` is always sc-smooth": for EVERY M-polyfold (not only when `X₀ = X_∞`), the inclusion
  `X¹ → X` is sc-smooth (`IsScSmoothMap`, Definition 2.14).
- "has the inverse `1₁⁰`": the two maps are mutually inverse.  "sc-diffeomorphism": my own
  `IsScDiffeoB` — sc-smooth, with an sc-smooth two-sided inverse.
- "It is possible that `X¹ ≠ X` as M-polyfolds although the underlying sets agree": there is an
  M-polyfold `X` for which `1₀¹ : X → X¹` (the identity of the common underlying set) is NOT an
  sc-diffeomorphism.  READING: I took the hypothesis "the underlying sets agree" in the context
  of the remark, i.e. `X₀ = X_∞` (which gives `X₀ = X₁`); the weaker literal reading `X₀ = X₁`
  would give a weaker existence claim.  Since `X` must be nonempty for the claim to say
  anything, the junk value is existentially quantified (`∃ x₀`), which forces `X₁ ≠ ∅`.
  "`X¹ ≠ X` as M-polyfolds" is read as "the identification is not an sc-diffeomorphism" (not "no
  sc-diffeomorphism at all").
- "A finite-dimensional space with the constant structure has `X = X¹`": for every
  finite-dimensional normed space `V`, the M-polyfold of `V` with the constant sc-structure
  (`ScBanach.const V`; the M-polyfold is the project's `IsRelOpenInQuadrant.toMPolyfold` of the
  relatively open subset `V` of the partial quadrant `V`, on the subtype `↥(univ : Set V)`;
  checked: the local model `(U, C, E)` with the identity retraction as its one chart), has
  `X₁ = X` and `1₀¹` is an sc-diffeomorphism.  The hypothesis `IsRelOpenInQuadrant … univ univ`
  is needed to build the M-polyfold; it is true (`C = V` is the partial quadrant with `n = 0`).
- Nothing looks false to me, but I have not seen the example behind "it is possible".
-/
namespace RoundTrip.V4_6
open Polyfold

/-- `f : X → X¹` is an sc-diffeomorphism with inverse `g : X¹ → X`. -/
def IsScDiffeoB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (f : X → P.Level 1) (g : P.Level 1 → X) : Prop :=
  P.IsScSmoothMap P.shift f ∧ P.shift.IsScSmoothMap P g ∧
    (∀ x : X, g (f x) = x) ∧ (∀ y : P.Level 1, f (g y) = y)

/-- Remark 4.3: `1₁⁰ : X¹ → X` is always sc-smooth; if `X₀ = X_∞`, `1₀¹` and `1₁⁰` are inverse,
so `1₀¹` is an sc-diffeomorphism as soon as it is sc-smooth; this can fail although the
underlying sets agree; for a finite-dimensional space with the constant structure `X = X¹`. -/
def B : Prop :=
  -- `1₁⁰ : X¹ → X` is always sc-smooth
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.shift.IsScSmoothMap P (P.levelVal 1)) ∧
  -- if `X₀ = X_∞`: `1₁⁰` inverts `1₀¹`, and if `1₀¹` is sc-smooth it is an sc-diffeomorphism
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.smoothSet = Set.univ → ∀ x₀ : P.Level 1,
      (∀ x : X, P.levelVal 1 (P.toLevelOne x₀ x) = x) ∧
      (∀ y : P.Level 1, P.toLevelOne x₀ (P.levelVal 1 y) = y) ∧
      (P.IsScSmoothMap P.shift (P.toLevelOne x₀) →
        IsScDiffeoB P (P.toLevelOne x₀) (P.levelVal 1))) ∧
  -- possibly `X¹ ≠ X` as M-polyfolds although the underlying sets agree
  (∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : ParacompactSpace X)
    (P : MPolyfold X), P.smoothSet = Set.univ ∧
      ∃ x₀ : P.Level 1, ¬ IsScDiffeoB P (P.toLevelOne x₀) (P.levelVal 1)) ∧
  -- a finite-dimensional space with the constant structure has `X = X¹`
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hV : IsRelOpenInQuadrant (ScBanach.const V) Set.univ Set.univ),
    (hV.toMPolyfold ⟨0, Set.mem_univ _⟩).levelSet 1 = Set.univ ∧
    ∀ x₀ : (hV.toMPolyfold ⟨0, Set.mem_univ _⟩).Level 1,
      IsScDiffeoB (hV.toMPolyfold ⟨0, Set.mem_univ _⟩)
        ((hV.toMPolyfold ⟨0, Set.mem_univ _⟩).toLevelOne x₀)
        ((hV.toMPolyfold ⟨0, Set.mem_univ _⟩).levelVal 1))

end RoundTrip.V4_6
