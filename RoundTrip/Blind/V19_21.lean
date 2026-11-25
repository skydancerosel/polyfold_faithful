import Polyfold
/-! Blind formalization of V19_21 (the text's §19.3, Proposition 19.3.7, p. 877 of the Springer
2021 book; new in the 2021 edition).

Text: `Ψ̄ : G × O → M(Ψ, Ψ)` is a homeomorphism.

Choices:
- Setting: universe `0`: a groupoidal category `C`, a uniformizer construction `F`
  (`C.UniformizerConstruction`, Definition 19.1.3) and arbitrary transition data `F` for it
  (`U.TransitionData`, properties (A)–(F) of (19.3)), all from the vocabulary.  `M(Ψ, Ψ)` carries
  the topology `T^F_{Ψ,Ψ}` of Lemma 19.3.1 (the vocabulary's `F.Tr Ψ Ψ`, open sets `IsOpenTr`);
  stating it for every transition data covers `T_{Ψ,Ψ}` of every transition construction
  (Definition 19.3.2: `T_{Ψ,Ψ}` is `T^F_{Ψ,Ψ}` of any representative).  `Ψ` ranges over the
  uniformizers occurring in `F` (`U.Unif`).
- `Ψ̄(g, o) = (o, Ψ(g, o), g ∗ o)` = the vocabulary's `Uniformizer.hat` (Lemma 17.1.9).  `G`
  carries the discrete topology (the uniformizer's `discG` instance), `O` the topology of its
  M-polyfold structure, `G × O` the product topology.
- "homeomorphism" = a `≃ₜ` whose underlying map is `Ψ̄`.  I did not use `hatHomeomorph`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_21
open Polyfold

/-- Proposition 19.3.7: `Ψ̄ : G × O → M(Ψ, Ψ)` is a homeomorphism. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (U : C.UniformizerConstruction) (F : U.TransitionData)
    (Ψ : U.Unif),
    ∃ e : (Ψ : C.Uniformizer).G × (Ψ : C.Uniformizer).O ≃ₜ F.Tr Ψ Ψ,
      ∀ p, e p = F.toTr ((Ψ : C.Uniformizer).hat p)

end RoundTrip.V19_21
