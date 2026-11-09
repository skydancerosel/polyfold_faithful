import Polyfold
/-! Blind formalization of V8_44 (the 2021 book, Part II, §8.1, Proposition 8.1.16, p. 369).

Text: if the ep-groupoid `X` satisfies the Zhou condition (Definition 7.4.5), so does its tangent
`TX`.  (The rest of the quoted paragraph describes the proof: write an isotropy element of a
smooth `b ∈ TX` over `x` as `(g, h)`, differentiate (8.16), use that `Tτ` is onto.)

Choices:
- Setting as in the Chapter 7 blind files (e.g. `RoundTrip/Blind/V7_53.lean`): `Obj Mor : Type`
  (universe 0) with the instances of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the
  project's Definition 7.3, fields read with `#print`).
- `TX`: the project's `X.tangentEpGroupoid` (2017 Theorem 8.1 / 2021 Theorem 8.1.1: objects `TX`,
  morphisms `T𝐗`, structure maps the tangent maps), an ep-groupoid with object and morphism
  types in `Type 1` (the tangent space of a type in `Type` lives in `Type 1`, vocab).
- "the Zhou condition": the project's `EpGroupoid.IsZhou` (2021 Definition 7.4.5), read with
  `#print`: for every smooth object `x` and `g ∈ G_x`, if `Tg` is the identity on `T_xX` then
  `g ∈ T_x`, where `T_x` (`trivialSubgroup`) is the set of `g` with `Φ(g) = id` on the
  neighbourhood of some natural representation (`ActsTrivially`).  This is the text's notion as
  I understand Definition 7.4.5; I use it for both `X` and `TX`.
- The proof's ingredients ("`Tτ` is onto", (8.16)) are not hypotheses of the proposition; no
  further hypothesis is added.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_44
open Polyfold

/-- Proposition 8.1.16: the Zhou condition passes from `X` to its tangent `TX`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    X.IsZhou → X.tangentEpGroupoid.IsZhou

end RoundTrip.V8_44
