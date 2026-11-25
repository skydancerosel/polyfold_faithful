import Polyfold
/-! Blind formalization of V19_26 (the text's §19.4, Proposition 19.4.4, p. 883 of the Springer
2021 book; 2017: Proposition 19.3).

Text: under properness every `T_{Ψ,Ψ'}` is metrizable.

Choices:
- Setting: universe `0`: a groupoidal category `C` with a basic construction `B = (F, 𝓕)`
  (`C.BasicConstruction`, Definition 19.1.7, from the vocabulary).  `T_{Ψ,Ψ'}` (Definition
  19.3.2) = `T^F_{Ψ,Ψ'}` of a representative `F` of `𝓕` (the vocabulary's `F.Tr Ψ Ψ'`, open sets
  `IsOpenTr`); B is stated for EVERY representative `F` (`⟦F⟧ = 𝓕`).  `Ψ, Ψ'` range over the
  uniformizers occurring in `F` (`B.U.Unif`).
- "properness" = the properness condition (v1) of Definition 19.4.1 (Proposition 19.4.2 says
  (v1), (v2), (v3) are equivalent; (v1) is the one that does not involve the topology `T` of
  `|S|`, so no hypothesis on `|S|` is needed).  (v1), written out myself from the vocabulary's
  description (I do not have Definition 19.4.1 itself; I did not use `PropernessV1` or
  `TransitionV1`): for every `Ψ` and `o ∈ O` there is an open `U(o) ∋ o` such that for every
  `Ψ'` every sequence `h_k ∈ M(Ψ, Ψ')` with `s(h_k) ∈ U(o)` and `t(h_k)` convergent in `O'` has
  a subsequence convergent in `T_{Ψ,Ψ'}`.
- "metrizable" = Mathlib's `TopologicalSpace.MetrizableSpace`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_26
open Polyfold Filter Topology

/-- The properness condition (v1), for the topologies `T^F_{Ψ,Ψ'}`. -/
def V1 {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData) :
    Prop :=
  ∀ (Ψ : U.Unif) (o : (Ψ : C.Uniformizer).O),
    ∃ W : Set (Ψ : C.Uniformizer).O, IsOpen W ∧ o ∈ W ∧
      ∀ (Ψ' : U.Unif) (h : ℕ → F.Tr Ψ Ψ'),
        (∀ k, GroupoidStr.TransitionSet.src (h k : (Ψ : C.Uniformizer).Trans Ψ') ∈ W) →
        (∃ y : (Ψ' : C.Uniformizer).O,
          Tendsto (fun k => GroupoidStr.TransitionSet.tgt
            (h k : (Ψ : C.Uniformizer).Trans Ψ')) atTop (𝓝 y)) →
        ∃ (φ : ℕ → ℕ) (x : F.Tr Ψ Ψ'), StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 x)

/-- Proposition 19.4.4: under properness every `T_{Ψ,Ψ'}` is metrizable. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    V1 F → ∀ Ψ Ψ' : B.U.Unif, TopologicalSpace.MetrizableSpace (F.Tr Ψ Ψ')

end RoundTrip.V19_26
