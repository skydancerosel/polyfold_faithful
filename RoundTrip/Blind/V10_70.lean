import Polyfold
/-! Blind formalization of V10_70 (the Springer 2021 book, Part II, §10.5, the composition behind
Definition 10.5.1, p. 506 (2017: Definition 10.14, p. 366); Theorem 10.3.8, p. 488 (2017:
Theorem 10.3, p. 352), Appendix §10.6.1): composition of generalized strong bundle maps.

Text: Definition 10.5.1 calls the generalized strong bundle maps the morphisms of a category; the
composition, its independence of the representatives and the category laws are not spelled out.
What is meant is the strong bundle analogue of Theorem 10.3.8: the class of the composite diagram
depends only on the classes, the composition is associative, with units `[1_W]`.

Choices:
- Setting: universe 0, strong bundles over ep-groupoids `SEP.{0}`, diagrams the project's
  `SDiagram` and classes `D.cls` in the project's `GenSBMap` (see `RoundTrip/Blind/V10_69.lean`).
- The composite of `D : W ←Φ W'' →Ψ W'` and `E : W' ←Φ' V'' →Ψ' W'''` (the text's
  "following our earlier construction", the analogue of `X ← A ×_Y B → Z`): the project's
  `SDiagram.comp D E` (read with `#print`: middle the pull-back of `W''` along
  `πX : X'' ×_{X'} Y'' → X''`, the project's model of `W'' ×_{W'} V''`, with legs
  `Φ ∘ Π_{W''}` and `Ψ' ∘ Π_{V''}`), trusted as that construction; its middle is the strong bundle
  weak fibred product of V10_68.  The unit `1_W = W ←1 W →1 W`: the project's `SDiagram.id`
  (read with `#print`).
- "Independence of the representatives": equal classes of the factors give equal classes of the
  composites (stated with classes, as Theorem 10.3.8 states it, so it does not depend on whether
  "having a common refinement" is transitive).  Category laws: associativity and both unit laws,
  up to equality of classes.  The `D.comp E` order is diagrammatic (`[E] ∘ [D]` in the text).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_70
open Polyfold Polyfold.SBLocalization

/-- **Theorem 10.3.8, strong bundle case**: composition of classes of diagrams of strong bundles
is well defined, associative and unital. -/
def B : Prop :=
  (∀ (A A' A'' : SEP.{0}) (D₁ D₂ : SDiagram A A') (E₁ E₂ : SDiagram A' A''),
      D₁.cls = D₂.cls → E₁.cls = E₂.cls → (D₁.comp E₁).cls = (D₂.comp E₂).cls) ∧
  (∀ (A A' A'' A''' : SEP.{0}) (D : SDiagram A A') (E : SDiagram A' A'')
      (G : SDiagram A'' A'''),
      ((D.comp E).comp G).cls = (D.comp (E.comp G)).cls) ∧
  (∀ (A A' : SEP.{0}) (D : SDiagram A A'),
      ((SDiagram.id A).comp D).cls = D.cls ∧ (D.comp (SDiagram.id A')).cls = D.cls)

end RoundTrip.V10_70
