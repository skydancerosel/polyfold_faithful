import Polyfold
/-! Blind formalization of V19_24 (the text's §19.4, Proposition 19.4.2, p. 880 of the Springer
2021 book; 2017: Proposition 19.4).

Text: the three properness conditions (v1), (v2), (v3) of Definition 19.4.1 are equivalent.

Choices:
- Setting: universe `0`: a groupoidal category `C` with a basic construction `B = (F, 𝓕)`
  (`C.BasicConstruction`, Definition 19.1.7, from the vocabulary).  Hypothesis added:
  `B.U.HasClassUniformizers` (every class `z ∈ |S|` contains an object `α` with `F(α) ≠ ∅`):
  the text's `T` on `|S|`, used in (v2) and (v3), is a topology only then (Theorem 19.2.2 (1)),
  and §19.4 presupposes that.
- `T` (Definition 19.2.1) is written out as `natOpen` (the existential reading, as in my
  V19_12) and `|S|` is topologized by `TopologicalSpace.generateFrom natOpen`; under the
  hypothesis above its open sets are exactly the members of `T` (Theorem 19.2.2 (1)).  I did not
  use the project's `natTop`.
- `T_{Ψ,Ψ'}` on `M(Ψ, Ψ')` (Definition 19.3.2) = `T^F_{Ψ,Ψ'}` of a representative `F` of `𝓕`
  (the vocabulary's `F.Tr Ψ Ψ'`, open sets `IsOpenTr`, Lemma 19.3.1); B is stated for EVERY
  representative `F` (`⟦F⟧ = 𝓕`).  `Ψ, Ψ'` range over the uniformizers occurring in `F`
  (`B.U.Unif`); `O`, `O'` carry the topologies of their M-polyfold structures.
- I do not have the text of Definition 19.4.1 in my input; I wrote the three conditions as the
  vocabulary's docstrings describe them (I did not use `PropernessV1/V2/V3/V3Lim`,
  `TransitionV1`, `OrbitChartV2/V3`):
  (v1) for every `Ψ` and `o ∈ O` there is an open `U(o) ∋ o` such that for every `Ψ'` every
       sequence `h_k ∈ M(Ψ, Ψ')` with `s(h_k) ∈ U(o)` and `t(h_k)` convergent in `O'` has a
       subsequence convergent in `T_{Ψ,Ψ'}`;
  (v2) for every `Ψ` and `o ∈ O` there is an open `U(o) ∋ o` with
       `cl_T |Ψ(U(o))| ⊂ |Ψ(O)|`;
  (v3) for every `Ψ` and `o ∈ O` there is an open `U(o) ∋ o` such that for every sequence
       `q_k ∈ U(o)` for which `|Ψ(q_k)|` converges in `T` (to some `z`), a subsequence of `q_k`
       converges in `O` to a point of `cl_O(U(o))`.
  `|Ψ(V)|` is the image of `V` under `q ↦ |Ψ(q)|`.  "Subsequence" = composition with a strictly
  monotone `ℕ → ℕ`.
- Doubtful: (v3) as printed (per the vocabulary) does not ask that the limit `p` of the
  subsequence satisfy `|Ψ(p)| = z`; I formalize it literally.  Since `T` is not yet known to be
  Hausdorff, this printed (v3) might be weaker than (v1), (v2).
- B is `(v1 ↔ v2) ∧ (v2 ↔ v3)`.
-/
namespace RoundTrip.V19_24
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

/-- The properness condition (v2), for the topology `T` on `|S|`. -/
def V2 {C : GroupoidalCategory.{0}} (U : C.UniformizerConstruction) : Prop :=
  ∀ (Ψ : U.Unif) (o : (Ψ : C.Uniformizer).O),
    ∃ W : Set (Ψ : C.Uniformizer).O, IsOpen W ∧ o ∈ W ∧
      @closure C.OrbitSpace (natT U) (orb (Ψ : C.Uniformizer) '' W) ⊆
        Set.range (orb (Ψ : C.Uniformizer))

/-- The properness condition (v3) as printed, for the topology `T` on `|S|`. -/
def V3 {C : GroupoidalCategory.{0}} (U : C.UniformizerConstruction) : Prop :=
  ∀ (Ψ : U.Unif) (o : (Ψ : C.Uniformizer).O),
    ∃ W : Set (Ψ : C.Uniformizer).O, IsOpen W ∧ o ∈ W ∧
      ∀ q : ℕ → (Ψ : C.Uniformizer).O, (∀ k, q k ∈ W) →
        (∃ z : C.OrbitSpace,
          @Tendsto ℕ C.OrbitSpace (fun k => orb (Ψ : C.Uniformizer) (q k)) atTop
            (@nhds C.OrbitSpace (natT U) z)) →
        ∃ (φ : ℕ → ℕ) (p : (Ψ : C.Uniformizer).O), StrictMono φ ∧ p ∈ closure W ∧
          Tendsto (q ∘ φ) atTop (𝓝 p)

/-- Proposition 19.4.2: the three properness conditions are equivalent. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    (V1 F ↔ V2 B.U) ∧ (V2 B.U ↔ V3 B.U)

end RoundTrip.V19_24
