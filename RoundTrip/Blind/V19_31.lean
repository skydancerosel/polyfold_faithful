import Polyfold
/-! Blind formalization of V19_31 (the text's §19.5, Theorem 19.5.1, p. 886 of the Springer 2021
book; 2017: Theorem 19.4).

Text: if `T` is metrizable, the metrizable space `M(Ψ, Ψ')` has a natural M-polyfold structure
for which `s` and `t` are local sc-diffeomorphisms.

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
- Claims: for all `Ψ, Ψ'`: (i) `(M(Ψ, Ψ'), T_{Ψ,Ψ'})` is metrizable (the text's "the metrizable
  space", i.e. Corollary 19.4.8, read as part of the claim); (ii) there is an M-polyfold
  structure `P` on it (`MPolyfold`; the `T2Space`/`ParacompactSpace` instances it needs are
  existentially quantified, they are Props) which is natural and for which `s : M(Ψ, Ψ') → O`
  and `t : M(Ψ, Ψ') → O'` are local sc-diffeomorphisms (`MPolyfold.IsLocalScDiffeo`, into the
  uniformizers' M-polyfolds `O`, `O'`).
- "natural" (my reading; the statement does not spell it out): every map
  `F_h : V(o) → M(Ψ, Ψ')`, `h ∈ M(Ψ, Ψ')`, of the transition data is an sc-diffeomorphism from
  the open subset `V(o)` of `O` onto an open subset of `M(Ψ, Ψ')` (`MPolyfold.IsScDiffeoOn` with
  some inverse `g`), i.e. the inverses `s|F_h(V(o))` are charts.  These sets cover `M(Ψ, Ψ')`
  (`h = F_h(o)`), so this determines `P`.  I did not use the project's `transPolyfold`,
  `sheetPolyfold`, `sheet` or `sheetMap`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_31
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

/-- `s(o, φ, o') = o` on `M(Ψ, Ψ')`. -/
def src {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData)
    (Ψ Ψ' : U.Unif) (h : F.Tr Ψ Ψ') : (Ψ : C.Uniformizer).O :=
  GroupoidStr.TransitionSet.src (h : (Ψ : C.Uniformizer).Trans Ψ')

/-- `t(o, φ, o') = o'` on `M(Ψ, Ψ')`. -/
def tgt {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData)
    (Ψ Ψ' : U.Unif) (h : F.Tr Ψ Ψ') : (Ψ' : C.Uniformizer).O :=
  GroupoidStr.TransitionSet.tgt (h : (Ψ : C.Uniformizer).Trans Ψ')

/-- The map `F_h : V(o) → M(Ψ, Ψ')` (its values off `V(o) = F.dom Ψ Ψ' h` are irrelevant). -/
def germ {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData)
    (Ψ Ψ' : U.Unif) (h : (Ψ : C.Uniformizer).Trans Ψ') (q : (Ψ : C.Uniformizer).O) :
    F.Tr Ψ Ψ' :=
  F.toTr (F.map Ψ Ψ' h q)

/-- The M-polyfold structure `P` on `(M(Ψ, Ψ'), T_{Ψ,Ψ'})` is the natural one: every `F_h` is an
sc-diffeomorphism from the open set `V(o) ⊂ O` onto an open subset of `M(Ψ, Ψ')` (i.e. the
maps `s|F_h(V(o))` are charts). -/
def IsNatural {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} (F : U.TransitionData)
    (Ψ Ψ' : U.Unif) [T2Space (F.Tr Ψ Ψ')] [ParacompactSpace (F.Tr Ψ Ψ')]
    (P : MPolyfold (F.Tr Ψ Ψ')) : Prop :=
  ∀ h : (Ψ : C.Uniformizer).Trans Ψ',
    IsOpen (germ F Ψ Ψ' h '' F.dom Ψ Ψ' h) ∧
    ∃ g : F.Tr Ψ Ψ' → (Ψ : C.Uniformizer).O,
      (Ψ : C.Uniformizer).P.IsScDiffeoOn P (germ F Ψ Ψ' h) g (F.dom Ψ Ψ' h)
        (germ F Ψ Ψ' h '' F.dom Ψ Ψ' h)

/-- Theorem 19.5.1: if `T` is metrizable, `M(Ψ, Ψ')` is metrizable and carries a natural
M-polyfold structure for which `s` and `t` are local sc-diffeomorphisms. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    @TopologicalSpace.MetrizableSpace C.OrbitSpace (natT B.U) →
    ∀ Ψ Ψ' : B.U.Unif,
      TopologicalSpace.MetrizableSpace (F.Tr Ψ Ψ') ∧
      ∃ (_ : T2Space (F.Tr Ψ Ψ')) (_ : ParacompactSpace (F.Tr Ψ Ψ')) (P : MPolyfold (F.Tr Ψ Ψ')),
        IsNatural F Ψ Ψ' P ∧
        P.IsLocalScDiffeo (Ψ : C.Uniformizer).P (src F Ψ Ψ') ∧
        P.IsLocalScDiffeo (Ψ' : C.Uniformizer).P (tgt F Ψ Ψ')

end RoundTrip.V19_31
