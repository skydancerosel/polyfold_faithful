import Polyfold
/-! Blind formalization of V19_30 (the text's §19.4, Corollary 19.4.8, p. 885 of the Springer
2021 book; new in the 2021 edition).

Text: if `T` is metrizable, every `T_{Ψ,Ψ'}` is metrizable.

Choices:
- Setting: universe `0`: a groupoidal category `C` with a basic construction `B = (F, 𝓕)`
  (`C.BasicConstruction`, Definition 19.1.7, from the vocabulary).  Hypothesis added:
  `B.U.HasClassUniformizers` (every class `z ∈ |S|` contains an object `α` with `F(α) ≠ ∅`):
  the text's `T` is a topology on `|S|` only then (Theorem 19.2.2 (1)), and §19.4 presupposes
  that.
- `T` (Definition 19.2.1) is written out as `natOpen` (the existential reading, as in my
  V19_12) and `|S|` is topologized by `TopologicalSpace.generateFrom natOpen` (`natT`); under the
  hypothesis above its open sets are exactly the members of `T` (Theorem 19.2.2 (1)).  I did not
  use the project's `natTop`.
- `T_{Ψ,Ψ'}` (Definition 19.3.2) = `T^F_{Ψ,Ψ'}` of a representative `F` of `𝓕` (the
  vocabulary's `F.Tr Ψ Ψ'`, open sets `IsOpenTr`); B is stated for EVERY representative `F`
  (`⟦F⟧ = 𝓕`).  `Ψ, Ψ'` range over the uniformizers occurring in `F` (`B.U.Unif`).
- "metrizable" = `TopologicalSpace.MetrizableSpace`, for `natT` and for `F.Tr Ψ Ψ'`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_30
open Polyfold

/-- The collection `T` of Definition 19.2.1. -/
def natOpen {C : GroupoidalCategory.{0}} (U : C.UniformizerConstruction)
    (W : Set C.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ α : C.Obj, C.π α = z ∧ ∃ Ψ ∈ U.F α, ∃ o : Ψ.O, Ψ.obj o = α ∧
    ∃ V : Set Ψ.O, IsOpen V ∧ o ∈ V ∧ (fun q => C.π (Ψ.obj q)) '' V ⊆ W

/-- The topology `T` on `|S|`. -/
@[instance_reducible] def natT {C : GroupoidalCategory.{0}} (U : C.UniformizerConstruction) :
    TopologicalSpace C.OrbitSpace :=
  TopologicalSpace.generateFrom {W | natOpen U W}

/-- `q ↦ |Ψ(q)|`. -/
def orb {C : GroupoidalCategory.{0}} (Ψ : C.Uniformizer) (q : Ψ.O) : C.OrbitSpace :=
  C.π (Ψ.obj q)

/-- Corollary 19.4.8: if `T` is metrizable, every `T_{Ψ,Ψ'}` is metrizable. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    @TopologicalSpace.MetrizableSpace C.OrbitSpace (natT B.U) →
    ∀ Ψ Ψ' : B.U.Unif, TopologicalSpace.MetrizableSpace (F.Tr Ψ Ψ')

end RoundTrip.V19_30
