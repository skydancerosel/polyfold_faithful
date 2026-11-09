import Polyfold
/-! Blind formalization of V8_45 (the 2021 book, Part II, §8.1, Proposition 8.1.17, p. 371).

Text: (1) If `X¹` has the local unique continuation property, so has `TX`, and
`(T𝐗)^T = p⁻¹((𝐗¹)^T)`.  (2) If `X` has (SLUC), so has `TX`.

Choices:
- Setting for (1) as in the Chapter 7 blind files: `Obj Mor : Type` (universe 0) with the
  instances of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (Definition 7.3, read with
  `#print`).  For (2) the text's iterated lifts `Xⁱ` are only defined in the project for bundled
  ep-groupoids, so (2) quantifies over `A : EP.{0}` (the bundled ep-groupoid: types, their
  topologies and the ep-groupoid `A.X`).
- `X¹`: the project's `X.liftOne` (index lift, 2021 Proposition 7.3.9 / 2017 Proposition 7.11).
  `TX`: the project's `X.tangentEpGroupoid` (objects `TX`, morphisms `T𝐗`).  For bundled
  `A`, `TX` is `A.tangentEP` (same ep-groupoid `A.X.tangentEpGroupoid`, read with `#print`) and
  `Xⁱ` is `A.lift i` (`X⁰ = X`, `X^{i+1} = (Xⁱ)¹`, read with `#print`).
- (LUC): the project's `EpGroupoid.IsLUC` (2021 Definition 7.2.18), read with `#print`: every
  object `x` has a natural representation `U(x)` such that `Φ(g) = id` on a nonempty open
  subset of `U(x)` forces `Φ(g) = id` on `U(x)`.  This is the text's definition as I know it.
- (SLUC): written out from 2021 Definition 7.4.12 as "(LUC) for every `Xⁱ`", my `SLUC`
  (identical to the project's `EP.IsSLUC`, which I did not need).
- `𝐗^T`: the project's `nonEffectivePart` (2017 Definition 7.12): the morphisms `φ ∈ T_x` for
  some object `x` (read with `#print`).  `(T𝐗)^T` is that of `TX`, `(𝐗¹)^T` that of `X¹`.
- `p : T𝐗 → 𝐗¹`: the tangent-bundle projection of the morphism M-polyfold, the project's
  `X.PMor.tangentProj` (Part I's `p : TX → X¹`, `[(x, φ, h)] ↦ x`, applied to `𝐗`); it is the
  morphism part of the projection functor `TX → X¹` of Theorem 8.1.
- Reading of (1): both the (LUC) of `TX` and the identity `(T𝐗)^T = p⁻¹((𝐗¹)^T)` are under the
  hypothesis that `X¹` has (LUC) (the sentence "If …, so has `TX`, and …").  This is the weaker
  reading; the identity might be meant unconditionally.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_45
open Polyfold

/-- (SLUC), 2021 Definition 7.4.12: (LUC) for every `Xⁱ`. -/
def SLUC (A : EP) : Prop := ∀ i : ℕ, (A.lift i).X.IsLUC

/-- Proposition 8.1.17: (1) (LUC) of `X¹` gives (LUC) of `TX` and `(T𝐗)^T = p⁻¹((𝐗¹)^T)`;
(2) (SLUC) passes from `X` to `TX`. -/
def B : Prop :=
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    X.liftOne.IsLUC →
      X.tangentEpGroupoid.IsLUC ∧
        X.tangentEpGroupoid.nonEffectivePart =
          X.PMor.tangentProj ⁻¹' X.liftOne.nonEffectivePart) ∧
  (∀ A : EP.{0}, SLUC A → SLUC A.tangentEP)

end RoundTrip.V8_45
