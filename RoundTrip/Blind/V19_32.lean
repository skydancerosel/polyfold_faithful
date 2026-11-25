import Polyfold
/-! Blind formalization of V19_32 (the text's §19.5, Corollary 19.5.2, p. 887 of the Springer
2021 book; 2017: Corollary 19.1).

Text: with their natural M-polyfold structures (Theorem 19.5.1) all structure maps of the
transition sets are sc-smooth.

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
- Hypothesis of Theorem 19.5.1 kept: `T` metrizable (the natural structures are defined only
  then).
- "their natural M-polyfold structures": B quantifies over EVERY family `N` of M-polyfold
  structures `N.M Ψ Ψ'` on the `(M(Ψ, Ψ'), T_{Ψ,Ψ'})` (with the needed `T2Space` /
  `ParacompactSpace` instances, Props) which are natural in the sense of my V19_31: every
  `F_h : V(o) → M(Ψ, Ψ')` is an sc-diffeomorphism from the open `V(o) ⊂ O` onto an open subset
  (`MPolyfold.IsScDiffeoOn`).  Such a structure is unique (the sets `F_h(V(o))` cover), so `∀`
  is the reading of "the natural structure"; existence is Theorem 19.5.1 (V19_31), not repeated.
- Structure maps (Definition 17.1.5, p. 746): `s : M(Ψ, Ψ') → O`, `t : M(Ψ, Ψ') → O'`,
  `u : O → M(Ψ, Ψ)`, `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` (vocabulary's `TransitionSet.src/tgt/unit/inv`)
  and `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`, `((o', φ', o''), (o, φ, o')) ↦ (o, φ' ∘ φ, o'')`
  (`TransitionSet.comp` on Part I's `MPolyfold.fibredProduct src tgt`; I did not use
  `F.FibProd`/`F.mulMap`).  "sc-smooth" = `MPolyfold.IsScSmoothMap` for `s, t, u, ι`; for `m` it
  is the project's `MPolyfold.IsScSmoothOnFibredProduct` (sc-smooth on the sub-M-polyfold
  fibred product of the product, Definition 17.1.8 (c)), which needs as arguments that `s` is a
  local sc-diffeomorphism and `t` sc-smooth; so B also asserts `s` is a local sc-diffeomorphism
  (stronger than "sc-smooth", but part of Theorem 19.5.1 for the natural structure).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_32
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

/-- A family of natural M-polyfold structures on the transition sets `(M(Ψ, Ψ'), T_{Ψ,Ψ'})`. -/
structure NatStr {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction}
    (F : U.TransitionData) where
  t2 : ∀ Ψ Ψ' : U.Unif, T2Space (F.Tr Ψ Ψ')
  pc : ∀ Ψ Ψ' : U.Unif, ParacompactSpace (F.Tr Ψ Ψ')
  P : ∀ Ψ Ψ' : U.Unif, @MPolyfold (F.Tr Ψ Ψ') _ (t2 Ψ Ψ') (pc Ψ Ψ')
  natural : ∀ Ψ Ψ' : U.Unif, @IsNatural C U F Ψ Ψ' (t2 Ψ Ψ') (pc Ψ Ψ') (P Ψ Ψ')

variable {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction} {F : U.TransitionData}

/-- `M(Ψ, Ψ')` with the structure `N`. -/
def NTN (_N : NatStr F) (Ψ Ψ' : U.Unif) : Type := F.Tr Ψ Ψ'

instance (N : NatStr F) (Ψ Ψ' : U.Unif) : TopologicalSpace (NTN N Ψ Ψ') :=
  inferInstanceAs (TopologicalSpace (F.Tr Ψ Ψ'))
instance (N : NatStr F) (Ψ Ψ' : U.Unif) : T2Space (NTN N Ψ Ψ') := N.t2 Ψ Ψ'
instance (N : NatStr F) (Ψ Ψ' : U.Unif) : ParacompactSpace (NTN N Ψ Ψ') := N.pc Ψ Ψ'

/-- The M-polyfold `M(Ψ, Ψ')` of `N`. -/
def NatStr.M (N : NatStr F) (Ψ Ψ' : U.Unif) : MPolyfold (NTN N Ψ Ψ') := N.P Ψ Ψ'

/-- `s`. -/
def sN (N : NatStr F) (Ψ Ψ' : U.Unif) (h : NTN N Ψ Ψ') : (Ψ : C.Uniformizer).O :=
  GroupoidStr.TransitionSet.src (h : (Ψ : C.Uniformizer).Trans Ψ')

/-- `t`. -/
def tN (N : NatStr F) (Ψ Ψ' : U.Unif) (h : NTN N Ψ Ψ') : (Ψ' : C.Uniformizer).O :=
  GroupoidStr.TransitionSet.tgt (h : (Ψ : C.Uniformizer).Trans Ψ')

/-- `ι(o, φ, o') = (o', φ⁻¹, o)`. -/
def iN (N : NatStr F) (Ψ Ψ' : U.Unif) (h : NTN N Ψ Ψ') : NTN N Ψ' Ψ :=
  GroupoidStr.TransitionSet.inv (h : (Ψ : C.Uniformizer).Trans Ψ')

/-- `u(o) = (o, 1, o)`. -/
def uN (N : NatStr F) (Ψ : U.Unif) (o : (Ψ : C.Uniformizer).O) : NTN N Ψ Ψ :=
  (GroupoidStr.TransitionSet.unit o : (Ψ : C.Uniformizer).Trans Ψ)

/-- `m` on the fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`. -/
def mN (N : NatStr F) (Ψ Ψ' Ψ'' : U.Unif)
    (p : ↑(MPolyfold.fibredProduct (sN N Ψ' Ψ'') (tN N Ψ Ψ'))) : NTN N Ψ Ψ'' :=
  GroupoidStr.TransitionSet.comp (p.1.1 : (Ψ' : C.Uniformizer).Trans Ψ'')
    (p.1.2 : (Ψ : C.Uniformizer).Trans Ψ') (by
    obtain ⟨⟨⟨s₁, m₁, t₁, hs₁, ht₁⟩, ⟨s₂, m₂, t₂, hs₂, ht₂⟩⟩, h⟩ := p
    change s₁ = t₂ at h
    subst h
    exact hs₁.trans ht₂.symm)

/-- Corollary 19.5.2: for the natural M-polyfold structures, all structure maps `s, t, u, ι, m`
are sc-smooth. -/
def B : Prop :=
  ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData),
    B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    @TopologicalSpace.MetrizableSpace C.OrbitSpace (natT B.U) →
    ∀ N : NatStr F,
      (∀ Ψ Ψ' : B.U.Unif, (N.M Ψ Ψ').IsScSmoothMap (Ψ : C.Uniformizer).P (sN N Ψ Ψ')) ∧
      (∀ Ψ Ψ' : B.U.Unif, (N.M Ψ Ψ').IsScSmoothMap (Ψ' : C.Uniformizer).P (tN N Ψ Ψ')) ∧
      (∀ Ψ : B.U.Unif, (Ψ : C.Uniformizer).P.IsScSmoothMap (N.M Ψ Ψ) (uN N Ψ)) ∧
      (∀ Ψ Ψ' : B.U.Unif, (N.M Ψ Ψ').IsScSmoothMap (N.M Ψ' Ψ) (iN N Ψ Ψ')) ∧
      ∃ hs : ∀ Ψ Ψ' : B.U.Unif,
          (N.M Ψ Ψ').IsLocalScDiffeo (Ψ : C.Uniformizer).P (sN N Ψ Ψ'),
        ∀ Ψ Ψ' Ψ'' : B.U.Unif,
          ∃ hts : (N.M Ψ Ψ').IsScSmoothMap (Ψ' : C.Uniformizer).P (tN N Ψ Ψ'),
            MPolyfold.IsScSmoothOnFibredProduct (N.M Ψ' Ψ'') (N.M Ψ Ψ') (N.M Ψ Ψ'')
              (hs Ψ' Ψ'') hts (mN N Ψ Ψ' Ψ'')

end RoundTrip.V19_32
