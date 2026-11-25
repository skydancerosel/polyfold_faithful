import Polyfold
/-! Blind formalization of V18_24 (the text's Part II, §18.2, Theorem 18.2.2, p. 850 of the
Springer 2021 book; 2017: Theorem 18.3).

Text: for an sc-Fredholm section functor the three conditions of Definition 18.2.1 are equivalent
(from Theorem 12.4.2).

Choices:
- Setting: universe `0`; `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT `V`
  with a strong polyfold bundle construction `Q`, and a section functor `f`.  "sc-Fredholm":
  `Q.IsScFredholmSectionFunctor f` (Definition 18.1.1).  No other hypothesis: Theorem 12.4.2
  assumes `|X|` paracompact, which here is part of the setting (`|C|` is metrizable).
- The three conditions of Definition 18.2.1: (1) compact moduli space
  `f.HasCompactModuliSpace` (`|S_f|` compact), (2) proper `Q.IsProper f`, (3) proper`<∞`
  `Q.IsProperLtInfty f` (docstrings: `|S_f|` compact and, for every auxiliary norm `N`, an open
  neighbourhood `U` of `|S_f|` with `cl{x ∈ U | |N| ∘ |f|(x) ≤ 1}` (resp. `≤ C` for every
  `0 < C < ∞`) compact).  Taken from the vocabulary; they match my reading.
- B: `(1) ↔ (2)` and `(1) ↔ (3)`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_24
open Polyfold

/-- Theorem 18.2.2: for an sc-Fredholm section functor, compact moduli space ⇔ proper ⇔
proper`<∞`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    Q.IsScFredholmSectionFunctor f →
      (f.HasCompactModuliSpace ↔ Q.IsProper f) ∧ (f.HasCompactModuliSpace ↔ Q.IsProperLtInfty f)

end RoundTrip.V18_24
