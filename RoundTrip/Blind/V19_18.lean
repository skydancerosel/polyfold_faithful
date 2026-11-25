import Polyfold
/-! Blind formalization of V19_18 (the text's §19.3, Proposition 19.3.4, p. 874 of the Springer
2021 book; 2017: Proposition 19.1).

Text: the germs `F_h` map open sets to open sets and are homeomorphisms onto open subsets;
`T_{Ψ,Ψ'}` is Hausdorff.

Choices:
- Setting: universe `0`: a groupoidal category `C`, a uniformizer construction `F`
  (`C.UniformizerConstruction`, Definition 19.1.3) and transition data `F` for it
  (`U.TransitionData`, the properties (A)–(F) of (19.3), from the vocabulary), arbitrary.  The
  proposition is about the topology `T^F_{Ψ,Ψ'}` of Lemma 19.3.1 defined by transition data; a
  statement for every transition data covers every representative of every transition
  construction (Definition 19.3.2 defines `T_{Ψ,Ψ'}` as `T^F_{Ψ,Ψ'}` of a representative).
- `M(Ψ, Ψ')` with `T^F_{Ψ,Ψ'}` = the vocabulary's `F.Tr Ψ Ψ'` (the transition set with the
  topology whose open sets are the vocabulary's `IsOpenTr`: `W` such that every `h ∈ W` has an
  open `V ∋ s(h)` in `V(s(h))` with `F_h(V) ⊂ W`; this is exactly the text's collection of
  Lemma 19.3.1 as the vocabulary states it).
- `Ψ, Ψ'` range over the uniformizers occurring in `F` (`U.Unif`), `h` over all of `M(Ψ, Ψ')`.
  The germ `F_h` is the map `F.map Ψ Ψ' h` on its domain `V(o) = F.dom Ψ Ψ' h`, `o = s(h)`.
- "maps open sets to open sets": every open `W ⊂ V(o)` has `T^F`-open image.  "homeomorphism onto
  an open subset": `F_h` restricted to `V(o)` is an open embedding.
- Hausdorff = `T2Space`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_18
open Polyfold

/-- Proposition 19.3.4: the germs `F_h` are open embeddings and `T^F_{Ψ,Ψ'}` is Hausdorff. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (U : C.UniformizerConstruction) (F : U.TransitionData)
    (Ψ Ψ' : U.Unif),
    (∀ (h : (Ψ : C.Uniformizer).Trans Ψ') (W : Set (Ψ : C.Uniformizer).O),
        W ⊆ F.dom Ψ Ψ' h → IsOpen W →
          IsOpen ((fun q => F.toTr (F.map Ψ Ψ' h q)) '' W)) ∧
    (∀ h : (Ψ : C.Uniformizer).Trans Ψ',
        Topology.IsOpenEmbedding
          (fun q : F.dom Ψ Ψ' h => F.toTr (F.map Ψ Ψ' h (q : (Ψ : C.Uniformizer).O)))) ∧
    T2Space (F.Tr Ψ Ψ')

end RoundTrip.V19_18
