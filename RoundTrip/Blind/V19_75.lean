import Polyfold
/-! Blind formalization of V19_75 (the text's §19.7, Proposition 19.7.13, p. 913 of the Springer
2021 book; new in the 2021 edition).

Text: `M(Ψ̂, Ψ̂')` has a natural regular Hausdorff, locally metrizable topology, uniquely
characterized by the canonical map to `M(Ψ, Ψ') ₛ×_τ̂ E` being a homeomorphism.

Choices:
- Setting: universe `0`: groupoidal categories `A`, `B`, a functor `P : A → B`
  (`GroupoidFunctor`) which is a finite-to-one covering functor (Definition 19.7.1, the standing
  assumption of §19.7; vocabulary `IsFiniteToOneCovering`, checked by `#print`), and a basic
  construction for `P` (Definition 19.7.11; vocabulary `CoveringBasicConstruction P`: a proper
  covering uniformizer construction `F̂` and a transition construction `𝓕` of the induced `F`).
  `Ψ̂ ∈ F̂(β)`, `Ψ̂' ∈ F̂(β')` range over `Bh.hatU.Unif`; `Ψ, Ψ'` are their underlying uniformizers.
  No `HasClassUniformizers`, no metrizability, no compatibility hypothesis is assumed (none is
  quoted, and none is needed to state the claim).  I did not use the vocabulary's
  `IsCompatible` (an added hypothesis of the project).
- `M(Ψ̂, Ψ̂')` = the vocabulary's `MHat` (triples `(e, φ̂, e')`); I wrap it in a type synonym `MT`
  so that the project's own topology instance on `MHat` is not used.
- `M(Ψ, Ψ')` carries `T_{Ψ,Ψ'}` (the vocabulary's `MB`, i.e. `M(Ψ, Ψ')` of the underlying basic
  construction `(F, 𝓕)`, with the instance of the transition data); `E` is the object space of
  `Ψ̂`; `M(Ψ, Ψ') ₛ×_τ̂ E` = the vocabulary's `Fib` (`{(h, e) | s(h) = τ̂(e)}`, subspace of the
  product).  The canonical map is the vocabulary's `toFib`, `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)`.
- "has a topology, uniquely characterized by the canonical map being a homeomorphism, which is
  regular Hausdorff and locally metrizable": there is a topology `t` on `M(Ψ̂, Ψ̂')` for which
  `toFib` is (the underlying map of) a homeomorphism, every topology with this property equals
  `t`, and `t` is `RegularSpace`, `T2Space` and locally metrizable (every point has an open
  neighbourhood metrizable in the subspace topology).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_75
open Polyfold
open GroupoidalCategory

/-- `M(Ψ̂, Ψ̂')` as a bare type (no topology instance). -/
def MT {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : Type :=
  Bh.MHat x y

/-- The canonical map `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is a homeomorphism for the topology `t`. -/
def IsCanonHomeo {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) (t : TopologicalSpace (MT Bh x y)) :
    Prop :=
  ∃ e : @Homeomorph (MT Bh x y) (Bh.Fib x y) t _, ∀ h : MT Bh x y, e h = Bh.toFib x y h

/-- Proposition 19.7.13: the natural topology on `M(Ψ̂, Ψ̂')`. -/
def B : Prop :=
  ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif),
      ∃ t : TopologicalSpace (MT Bh x y),
        IsCanonHomeo Bh x y t ∧
        (∀ t' : TopologicalSpace (MT Bh x y), IsCanonHomeo Bh x y t' → t' = t) ∧
        @RegularSpace (MT Bh x y) t ∧ @T2Space (MT Bh x y) t ∧
        ∀ h : MT Bh x y, ∃ W : Set (MT Bh x y), @IsOpen _ t W ∧ h ∈ W ∧
          @TopologicalSpace.MetrizableSpace W (@instTopologicalSpaceSubtype _ _ t)

end RoundTrip.V19_75
