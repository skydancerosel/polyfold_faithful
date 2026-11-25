import Polyfold
/-! Blind formalization of V19_33 (the text's §19.5, Theorem 19.5.3, p. 888 of the Springer 2021
book; 2017: Theorem 19.5).

Text: (1) properness and second countable or paracompact give `T` metrizable, so `(S, T)` is a
GCT.  (2) If `T` is metrizable there is a natural polyfold structure `(F, M)`, tame when the
domains are tame.

Choices:
- Setting: universe `0`: a groupoidal category `C : GroupoidalCategory.{0}` (the text's `S`) with
  a basic construction `B = (F, 𝓕)` (`C.BasicConstruction`, Definition 19.1.7).
- Hypothesis added (as in the blind V19_12): `B.U.HasClassUniformizers` (every class of `|S|`
  contains an object `α` with `F(α) ≠ ∅`); without it the natural topology `T` of Definition
  19.2.1 is not a topology on `|S|`, and the theorem speaks of `T`.
- `T` = the vocabulary's `B.natTop hB`, whose open sets are exactly the vocabulary's `NatOpen`
  (the collection of Definition 19.2.1; checked by `#print`).
- "properness": the properness condition of Definition 19.4.1, read as its version (v1), the
  vocabulary's `B.PropernessV1` (for every `Ψ` of `F` and `o ∈ O` an open `U(o) ∋ o` such that
  sequences `h_k ∈ M(Ψ, Ψ')` with `s(h_k) ∈ U(o)` and `t(h_k)` convergent have convergent
  subsequences).  I take (v1) because it does not depend on `T`; if the text intends (v2) or (v3)
  this is a different hypothesis.
- (1): `(second countable ∨ paracompact) → metrizable` for `T`.  "so `(S, T)` is a GCT" adds
  nothing: a GCT (Definition 17.1.1, `Polyfold.GCT`) is a groupoidal category with a metrizable
  topology on its orbit space.
- (2): no properness hypothesis (the quoted statement attaches properness to (1) only).  For
  metrizable `T` the GCT `(S, T)` is the vocabulary's `B.toGCTOfMetrizable hB hm` (checked by
  `#print`: it is `C` with the topology `B.natTop hB`).  "there is a natural polyfold structure
  `(F, M)`" = there is a polyfold structure `P` (Definition 17.1.8, `GCT.PolyfoldConstruction`)
  which is natural in the sense of `IsNaturalStructure` below:
  * its uniformizer sets are `F`: the members of `P.F α` are exactly the local uniformizers whose
    underlying uniformizer lies in `F(α)`, and every member of `F(α)` occurs;
  * each `M(Ψ, Ψ')` carries the natural topology `T_{Ψ,Ψ'}` of Definition 19.3.2, i.e. the
    topology `T^F_{Ψ,Ψ'}` of every representative `F` of `𝓕` (vocabulary
    `TransitionData.topology`).
  I do not pin the M-polyfold atlas of `M(Ψ, Ψ')` separately: a polyfold structure requires `s` to
  be a local sc-diffeomorphism onto the M-polyfold `O`, which determines the M-polyfold structure
  of `M(Ψ, Ψ')` from its topology (it is that of Theorem 19.5.1).  I did not use the project's
  `toPolyfoldConstruction`, `gctF`, `transPolyfold` or `B.M`.
- "tame when the domains are tame": if the M-polyfolds `O` of all `Ψ ∈ F(α)`, all `α`, are tame
  (`MPolyfold.IsTame`), then `P.IsTame` (Definition 17.1.8: all its local uniformizers tame).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_33
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

/-- Theorem 19.5.3: metrizability of `T` and the natural (tame) polyfold structure. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers),
    -- (1) properness and second countable or paracompact give `T` metrizable
    (B.PropernessV1 →
      (@SecondCountableTopology C.OrbitSpace (B.natTop hB) ∨
        @ParacompactSpace C.OrbitSpace (B.natTop hB)) →
      @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)) ∧
    -- (2) for metrizable `T`, a natural polyfold structure, tame when the domains are tame
    (∀ hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB),
      ∃ P : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction,
        IsNaturalStructure B hB hm P ∧
        ((∀ (α : C.Obj), ∀ Ψ ∈ B.U.F α, Ψ.P.IsTame) → P.IsTame))

end RoundTrip.V19_33
