import Polyfold
/-! Blind formalization of V19_39 (the text's §19.5, Proposition 19.5.9, p. 890 of the Springer
2021 book; new in the 2021 edition).

Text: for `T` metrizable, (LUC), resp. (SLUC), of the basic construction gives (LUC), resp.
(SLUC), of the polyfold.

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
- (LUC), (SLUC) of the basic construction: the vocabulary's `B.IsLUC` (Definition 19.5.8: for every
  `z ∈ |S|` an `α_z` with `|α_z| = z`, `Ψ ∈ F(α_z)`, `ō` with `Ψ(ō) = α_z` and an open
  `G_ō`-invariant `U ∋ ō` such that every `g ∈ G_ō` which is the identity on a nonempty open
  subset of `U` is the identity on `U`) and `B.IsSLUC` ((LUC) for every level `(Fⁱ, 𝓕ⁱ)`, the
  vocabulary's `IsLUCLevel i`, read with Chapter 7's (LUC) of `(G ⋉ O)ⁱ` at the point over `ō`).
- (LUC), (SLUC) of the polyfold: the vocabulary's `GCT.PolyfoldConstruction.IsLUC`, `IsSLUC`
  (Definition 17.1.22: some `X_Ψ` has Chapter 7's (LUC), resp. (SLUC)).
- "resp." = the conjunction of the two implications.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_39
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

/-- Proposition 19.5.9: (LUC) and (SLUC) of the basic construction pass to the polyfold. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))
    (P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction),
    IsNaturalStructure B hB hm P →
      (B.IsLUC → P.IsLUC) ∧ (B.IsSLUC → P.IsSLUC)

end RoundTrip.V19_39
