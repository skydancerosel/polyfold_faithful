import Polyfold
/-! Blind formalization of V19_29 (the text's §19.4, Proposition 19.4.7, p. 885 of the Springer
2021 book; 2017: Proposition 19.6).

Text: `T` is metrizable if and only if properness holds and `T` is paracompact.

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
- "properness" = the properness condition (v1) of Definition 19.4.1 (Proposition 19.4.2 says
  (v1), (v2), (v3) are equivalent; I take the first).  (v1), written out myself from the
  vocabulary's description (I do not have Definition 19.4.1 itself; I did not use
  `PropernessV1` or `TransitionV1`): for every `Ψ` and `o ∈ O` there is an open `U(o) ∋ o` such
  that for every `Ψ'` every sequence `h_k ∈ M(Ψ, Ψ')` with `s(h_k) ∈ U(o)` and `t(h_k)`
  convergent in `O'` has a subsequence convergent in `T_{Ψ,Ψ'}`.
- "paracompact" = Mathlib's `ParacompactSpace`, "metrizable" =
  `TopologicalSpace.MetrizableSpace`, both for `natT`.
- Doubtful only in the choice of (v1) for "properness": the "only if" direction asserts (v1)
  from metrizability; with (v2) or (v3) instead the claim would differ unless Proposition 19.4.2
  holds as stated.
-/
namespace RoundTrip.V19_29
open Polyfold Filter Topology

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

/-- Proposition 19.4.7: `T` is metrizable iff properness holds and `T` is paracompact. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    (@TopologicalSpace.MetrizableSpace C.OrbitSpace (natT B.U) ↔
      V1 F ∧ @ParacompactSpace C.OrbitSpace (natT B.U))

end RoundTrip.V19_29
