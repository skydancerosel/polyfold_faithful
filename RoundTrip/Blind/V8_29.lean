import Polyfold
/-! Blind formalization of V8_29 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Proposition 8.2,
pp. 276–277; 2021: Proposition 8.5.2, pp. 384–386).

Text: if `F : Y → X` and `H : Z → Y` are proper covering functors between ep-groupoids, then the
composition `F ∘ H : Z → X` is a proper covering functor.

Choices:
- Setting: the six object/morphism spaces in `Type` (universe 0, as in the Chapter 7 blind
  files), Hausdorff paracompact (required by the project's `MPolyfold`), ep-groupoids
  `X`, `Y`, `Z` the project's `EpGroupoid` (characterized in `RoundTrip/Blind/V7_3.lean`), functors
  the project's `EpFunctor` (characterized in `RoundTrip/Blind/V7_9.lean`).
- "Proper covering functor": the project's `EpFunctor.IsProperCovering`, read with `#print`; its
  fields are exactly the text's Definition 8.5.1 (V8.27): (1) `F` surjective and a local
  sc-diffeomorphism on objects; (2) finite fibres, an open `U(x) ∋ x` and mutually disjoint
  `U(y) ∋ y` (`y ∈ F⁻¹(x)`) with `F : U(y) → U(x)` sc-diffeomorphisms and
  `F⁻¹(U(x)) = ⋃ U(y)`; (3) `φ ↦ (F(φ), s(φ))` an sc-diffeomorphism from `𝐘` onto
  `𝐗 ₛ×_F Y` with its sub-M-polyfold structure in `𝐗 × Y`.
- The composite: the project's `EpFunctor.comp F H` (`(comp F H).obj = F.obj ∘ H.obj`,
  `(comp F H).mor = F.mor ∘ H.mor`, see `RoundTrip/Blind/V7_9.lean`).
- The parenthetical proof (`L_{F∘H} = K̃ ∘ L_H`) is not formalized: it is a proof sketch, the claim
  is the proposition.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_29
open Polyfold

/-- Proposition 8.5.2: the composite of two proper covering functors is a proper covering
functor. -/
def B : Prop :=
  ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
    [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
    (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
    (F : EpFunctor Y X) (H : EpFunctor Z Y),
    F.IsProperCovering → H.IsProperCovering → (EpFunctor.comp F H).IsProperCovering

end RoundTrip.V8_29
