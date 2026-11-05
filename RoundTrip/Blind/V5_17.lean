import Polyfold
/-! Blind formalization of V5_17 (the text's §5.3, Proposition 5.10, p. 173, and §5.4.2,
Proposition 5.30, p. 193).

Text: with sc-smooth bump functions, for every `x` and `U(x)` there is an sc-smooth
`f : X → [0, 1]` with `f(x) = 1`, `supp(f) ⊆ U(x)`, and `f ≡ 1` near `x`.

Choices:
- Setting: `X : Type` (universe 0, as asked) with `PX : MPolyfold X` (Definition 2.13).  No
  tameness.
- "with sc-smooth bump functions": `X` admits sc-smooth bump functions in the sense of Definitions
  5.9 / 5.29 read literally (`f` NOT IDENTICALLY ZERO, see `RoundTrip/Blind/V5_16.lean`): the
  project's `PX.AdmitsBumpFunctionsWeak` (checked with `#print`).  I did not use the project's
  `AdmitsBumpFunctions` (`f(x) ≠ 0`), a stronger hypothesis; `BStrong` below (not the item) is the
  claim under it.
- "`U(x)`": an open `U ⊆ X` containing `x`; every `x` and every such `U`.
- "sc-smooth `f : X → [0, 1]`": `f : X → ℝ` sc-smooth (`PX.IsScSmoothMap realPolyfold f`, `ℝ` with
  the identity chart and constant sc-structure, checked) with all values in `[0, 1]`.
- "`supp(f)`": closure of `{f ≠ 0}` (`tsupport f`).  "`f ≡ 1` near `x`": `f = 1` on a neighbourhood
  of `x` (`∀ᶠ y in 𝓝 x, f y = 1`); it implies `f(x) = 1`, which is stated anyway.
- DOUBT: with the literal ("not identically zero") hypothesis the bump given for `x` need not be
  non-zero AT `x`, so I am not sure the proposition follows from it in general; the project's
  docstring of `AdmitsBumpFunctions` says the proof of Proposition 5.30 uses the reading
  `f(x) ≠ 0`.  Formalized literally anyway.
-/
namespace RoundTrip.V5_17
open Polyfold Filter Topology

/-- Propositions 5.10 / 5.30: with sc-smooth bump functions, every point has, inside any given
neighbourhood, an sc-smooth cut-off function `X → [0, 1]` equal to `1` near the point. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctionsWeak →
      ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
        ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ (∀ y, f y ∈ Set.Icc (0 : ℝ) 1) ∧
          f x = 1 ∧ tsupport f ⊆ U ∧ ∀ᶠ y in 𝓝 x, f y = 1

/-- Not the item: the same claim under the pointwise reading `f(x) ≠ 0` of the hypothesis. -/
def BStrong : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctions →
      ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
        ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ (∀ y, f y ∈ Set.Icc (0 : ℝ) 1) ∧
          f x = 1 ∧ tsupport f ⊆ U ∧ ∀ᶠ y in 𝓝 x, f y = 1

end RoundTrip.V5_17
