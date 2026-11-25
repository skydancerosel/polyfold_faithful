import Polyfold
/-! Blind formalization of V19_37 (the text's §19.5, Proposition 19.5.7, p. 889 of the Springer
2021 book; new in the 2021 edition).

Text: for `T` metrizable, (ZHOU) of the basic construction gives (ZHOU) of the polyfold
`(S, F, M)`.

Choices:
- Setting: universe `0`: a groupoidal category `C : GroupoidalCategory.{0}` (the text's `S`) with
  a basic construction `B = (F, 𝓕)` (`C.BasicConstruction`, Definition 19.1.7), with
  `B.U.HasClassUniformizers` (every class contains an object with a uniformizer; needed for the
  natural topology `T` of Definition 19.2.1 to be a topology on `|S|`), and `T` (the vocabulary's
  `B.natTop hB`, open sets = `NatOpen` of Definition 19.2.1) metrizable.
- "the polyfold `(S, F, M)`": the natural polyfold structure of Theorem 19.5.3 (2) on the GCT
  `(S, T)` (vocabulary `B.toGCTOfMetrizable hB hm`, i.e. `C` with `T`).  I state the claim for
  EVERY polyfold structure `P` (Definition 17.1.8) which is natural in the sense of
  `IsNaturalStructure` (copied from the blind V19_33): the uniformizer sets of `P` are those of
  `F`, and each `M(Ψ, Ψ')` carries the natural topology `T_{Ψ,Ψ'}` (Definition 19.3.2, the
  `T^F_{Ψ,Ψ'}` of every representative `F` of `𝓕`).  Since `s : M(Ψ, Ψ') → O` is a local
  sc-diffeomorphism in any polyfold structure, these data determine `P` up to the choice of
  equivalent atlases.  I did not use the project's `toPolyfoldConstruction`.
- (ZHOU) of the basic construction: the vocabulary's `B.IsZhou` (Definition 19.5.6: for every
  smooth class `z ∈ |S|` there are `α_z` with `|α_z| = z`, `Ψ ∈ F(α_z)` and a smooth `ō` with
  `Ψ(ō) = α_z` such that every `g` fixing `ō` with `Tg = id` on `T_ōO` is the identity near `ō`;
  checked by `#print` of `IsZhou`, `IsZhouAt`, `IsSmoothClass`).
- (ZHOU) of the polyfold: the vocabulary's `GCT.PolyfoldConstruction.IsZhou` (Definition 17.1.22:
  the ep-groupoid `X_Ψ` of some covering set `Ψ` satisfies Chapter 7's (ZHOU)).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_37
open Polyfold

/-- `P` is the natural polyfold structure `(F, M)` of the basic construction `B` on `(S, T)`: its
uniformizers are those of `F`, and `M(Ψ, Ψ')` carries the natural topology `T_{Ψ,Ψ'}`. -/
def IsNaturalStructure {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction) : Prop :=
  (∀ (α : C.Obj) (Ψ : (B.toGCTOfMetrizable hB hm).LocalUniformizer),
      Ψ ∈ P.F α ↔ Ψ.toUniformizer ∈ B.U.F α) ∧
  (∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α,
      ∃ Ψl : (B.toGCTOfMetrizable hB hm).LocalUniformizer, Ψl ∈ P.F α ∧ Ψl.toUniformizer = Ψ) ∧
  (∀ (Ψ Ψ' : GCT.Unif P.F) (hΨ : ∃ α, Ψ.1.toUniformizer ∈ B.U.F α)
      (hΨ' : ∃ α, Ψ'.1.toUniformizer ∈ B.U.F α) (F : B.U.TransitionData),
      Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
        P.topM Ψ Ψ' = F.topology ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ'.1.toUniformizer, hΨ'⟩)

/-- Proposition 19.5.7: (ZHOU) of the basic construction passes to the polyfold. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction),
    IsNaturalStructure B hB hm P → B.IsZhou → P.IsZhou

end RoundTrip.V19_37
