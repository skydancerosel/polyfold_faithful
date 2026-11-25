import Polyfold
/-! Blind formalization of V16_77 (the text's Part II, §16.6, Definition 16.6.5, p. 739 of the
Springer 2021 book; 2017: Definition 16.42).

Text: an orientation of `f` is the choice of an orientation of a representative `(W, F)`
(transported by Theorem 12.5.7).

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`, an
  sc-Fredholm section `f : c.FredholmSection` (Definition 16.6.1; `#print`ed: a class of
  representatives `(f, Γ, W, F)`, `c.SectionRep`, with the Fredholm property).
- "an orientation of a representative `(W, F)`": the project's `OrientationRep f` (`#print`ed: a
  representative `a` with `⟦a⟧ = f`, `F` an sc-Fredholm section functor, sc⁺-sections through
  every point of `W` (Part I's standing hypothesis for orientation transport), a topology on
  `O_F` as in Theorem 12.5.3 and an orientation `o` of Definition 12.5.4).
- "transported by Theorem 12.5.7": the project's `OrientationRep.Correspondence o o'` (a diagram
  `W ← W'' → W'` of strong bundle equivalences between the two models compatible with the maps
  to `Y`, with `F'' = Φ^*F = Ψ^*F'` and `Φ^*o = Ψ^*o'`).  I take it as the text's transport.
- A definition carries no theorem; what it presupposes, and what B states, is that the choice on
  one representative determines the orientation on every representative:
  (0) `f` is orientable iff it has an orientation of a representative (pins the project's
      `FredholmSection.IsOrientable`);
  (1) existence of the transport: given an orientation `o` and any representative `a'` of `f`
      satisfying the standing hypothesis (sc⁺-sections through every point of `W'`), there is an
      orientation `o'` on `a'` corresponding to `o`.  The Fredholm property of `F'` is not
      assumed: it is part of the conclusion (it holds by invariance of sc-Fredholm functors);
  (2) uniqueness of the transport: two orientations on the same representative that both
      correspond to `o` have the same orientation `x ↦ o_x` (stated with `HEq`, since the types
      of the orientation functions depend on the representative through the record).  This
      presupposes that the transport does not depend on the diagram chosen.
- Nothing looks doubtful to me, with the caveat that (2) is my reading of "transported".
-/
namespace RoundTrip.V16_77
open Polyfold

/-- Definition 16.6.5: an orientation of one representative determines, by transport, a unique
corresponding orientation of every representative. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p) (f : c.FredholmSection),
    -- (0) orientable = an orientation of a representative exists
    (f.IsOrientable ↔ Nonempty (StrongPolyfoldBundle.OrientationRep f)) ∧
    -- (1) the transport to any representative exists
    (∀ (o : StrongPolyfoldBundle.OrientationRep f) (a' : c.SectionRep),
      (⟦a'⟧ : c.ScSection) = (f : c.ScSection) → a'.S.A.B.HasScPlusSectionsThrough →
      ∃ o' : StrongPolyfoldBundle.OrientationRep f, o'.a = a' ∧ Nonempty (o.Correspondence o')) ∧
    -- (2) the transport is unique
    (∀ (o o₁ o₂ : StrongPolyfoldBundle.OrientationRep f), o₁.a = o₂.a →
      Nonempty (o.Correspondence o₁) → Nonempty (o.Correspondence o₂) → HEq o₁.o o₂.o)

end RoundTrip.V16_77
