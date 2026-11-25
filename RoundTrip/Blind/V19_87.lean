import Polyfold
/-! Blind formalization of V19_87 (the text's §19.7, Proposition 19.7.26, p. 926 of the Springer
2021 book; 2017: Proposition 19.8).

Text: if `|ℬ|` is metrizable, `M(Ψ̂, Ψ̂')` has a natural M-polyfold structure for which `p` is a
local sc-diffeomorphism.

Choices:
- Setting (as in the blind V19_75–V19_77): universe `0`: groupoidal categories `A`, `B`, a
  finite-to-one covering functor `P : A → B` (Definition 19.7.1; vocabulary
  `IsFiniteToOneCovering`) and a basic construction `Bh` for `P` (Definition 19.7.11; vocabulary
  `CoveringBasicConstruction P`, underlying basic construction `Bh.toBasic` for `B`).
- Hypotheses: `Bh.toBasic.U.HasClassUniformizers` (the standing assumption under which `T_{|B|}`
  is a topology, Theorem 19.2.2; presupposed by "`|ℬ|` is metrizable") and `T_{|B|}` (vocabulary
  `Bh.toBasic.natTop hB`) metrizable (Mathlib's `MetrizableSpace`).  No compatibility hypothesis
  (the vocabulary's `IsCompatible`) is assumed.
- `M(Ψ, Ψ')` carries the M-polyfold structure of Theorem 19.5.1 for the underlying basic
  construction (the vocabulary's `Bh.basePolyfold`, i.e. `Bh.toBasic.transPolyfold`).
- `M(Ψ̂, Ψ̂')` (vocabulary `MHat`, wrapped in the synonym `MT` to avoid the project's instance)
  carries the topology of Proposition 19.7.13 (induced by the canonical bijection
  `toFib : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`).  An M-polyfold structure must live on this topology;
  since an M-polyfold is Hausdorff and paracompact (`MPolyfold` takes these instances), these two
  properties of the topology are part of the claim (existentially quantified instances).
- "a natural M-polyfold structure for which `p` is a local sc-diffeomorphism": there is an
  M-polyfold structure `S` on `M(Ψ̂, Ψ̂')` with `p` (vocabulary `pB`) a local sc-diffeomorphism
  `S → M(Ψ, Ψ')` (`MPolyfold.IsLocalScDiffeo`).  I do not pin "natural" further: since `p` is a
  local homeomorphism (Proposition 19.7.14), a structure for which `p` is a local
  sc-diffeomorphism is determined (charts are pulled back along `p`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_87
open Polyfold
open GroupoidalCategory

/-- `M(Ψ̂, Ψ̂')` as a bare type. -/
def MT {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : Type :=
  Bh.MHat x y

/-- The topology of Proposition 19.7.13: induced by `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`. -/
noncomputable instance {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : TopologicalSpace (MT Bh x y) :=
  TopologicalSpace.induced (Bh.toFib x y) inferInstance

/-- Proposition 19.7.26: the M-polyfold structure of `M(Ψ̂, Ψ̂')`. -/
def B : Prop :=
  ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ (Bh : CoveringBasicConstruction P) (hB : Bh.toBasic.U.HasClassUniformizers),
      @TopologicalSpace.MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hB) →
      ∀ x y : Bh.hatU.Unif,
        ∃ (_ : T2Space (MT Bh x y)) (_ : ParacompactSpace (MT Bh x y)) (S : MPolyfold (MT Bh x y)),
          S.IsLocalScDiffeo (Bh.basePolyfold x y) (fun h : MT Bh x y => Bh.pB x y h)

end RoundTrip.V19_87
