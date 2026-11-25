import Polyfold
/-! Blind formalization of V16_76 (the text's Part II, §16.6, Theorem 16.6.4, p. 737 of the
Springer 2021 book; 2017: Theorem 16.7).

Text: for an sc-Fredholm section: compact solution set ⇔ proper ⇔ proper`<∞`.

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`, an
  sc-Fredholm section `f : c.FredholmSection` (Definition 16.6.1), used as an sc-smooth section
  `(f : c.ScSection)`.  No further hypothesis (none is quoted).
- "compact solution set": `HasCompactSolutionSet` (Definition 16.6.2; `#print`ed:
  `IsCompact S(f)`).
- "proper", "proper`<∞`": the project's `ScSection.IsProper` and `ScSection.IsProperLtInfty`
  (Definition 16.6.3 (1), (2)).  `#print`ed: `IsProper` is "`S(f)` compact and for every auxiliary
  norm `n` there is an open `U ⊇ S(f)` with `cl{z ∈ U | f(z) ∈ Y_{0,1}, n(f(z)) ≤ 1}` compact";
  `IsProperLtInfty` the same with "for every `C > 0`, `cl{… ≤ C}` compact" for one `U`.  I could
  not check these against the text of Definition 16.6.3 (not quoted); the conjunct "`S(f)`
  compact" in both makes the implications "proper ⇒ compact solution set" immediate.
- B is the chain of two `↔`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_76
open Polyfold

/-- Theorem 16.6.4: for an sc-Fredholm section, compact solution set, proper and proper`<∞` are
equivalent. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p) (f : c.FredholmSection),
      ((f : c.ScSection).HasCompactSolutionSet ↔ (f : c.ScSection).IsProper) ∧
      ((f : c.ScSection).IsProper ↔ (f : c.ScSection).IsProperLtInfty)

end RoundTrip.V16_76
