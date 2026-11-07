import Polyfold
/-! Blind formalization of V7_40 (the text's §7.2, p. 243, and Proposition 7.10, p. 244; the
2017 book, arXiv 1707.08941, Part II).

Text: the reduced ep-groupoid `X_R` has the objects `X` and as morphism M-polyfold `𝐗^R`, with
`s([φ]) = s_X(φ)`, `t([φ]) = t_X(φ)` (and the other structure maps descended); Proposition 7.10:
every ep-groupoid `X` possesses an associated reduced ep-groupoid `X_R`, and `X_R` is effective.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (the vocabulary's Definition 7.3),
  `Obj Mor : Type` (universe 0), with the Hausdorff/paracompact instances that the vocabulary's
  M-polyfolds carry.
- `𝐗^R`: the vocabulary's `X.ReducedMor` (`Quot X.ReducedRel`, Definition 7.12).  Its topology is
  the instance found by Lean; I checked by `rfl` (not kept in this file) that it is the quotient
  topology `coinduced X.reducedπ`.  I read the text's `𝐗^R` as carrying the quotient topology.
- The groupoid structure of `X_R`: `X.reducedGroupoidStr` (objects `Obj`, `s[φ] = s φ`,
  `t[φ] = t φ`, `u(x) = [1_x]`, `ι[φ] = [φ⁻¹]`, `m([φ],[ψ]) = [φ ∘ ψ]`; checked by `#print`/`rfl`).
- "as morphism M-polyfold one takes `𝐗^R`": the M-polyfold structure of Proposition 7.9, i.e.
  the vocabulary's `X.reducedPolyfold` (the atlas `reducedAtlas` of the charts `Ψ_φ`), trusted from
  its docstring and `#print`.  "On the object level `X_R = X`": object M-polyfold `X.PObj`.
  B asks for equality with this particular atlas (the text's structure is the class of atlases
  equivalent to it; B is the claim for the text's own atlas).
- That `X_R` is an ep-groupoid includes that `𝐗^R` is an M-polyfold, hence (as the vocabulary's
  M-polyfolds) a Hausdorff paracompact space.  The vocabulary's `reducedPolyfold` takes these two
  properties as instance arguments; the text claims them for every ep-groupoid, so B asserts them
  (existentially, as Props) instead of assuming them.
- "X_R possesses ... is an ep-groupoid": there is an `EpGroupoid` structure on `(Obj, 𝐗^R)` whose
  groupoid data, object M-polyfold and morphism M-polyfold are exactly the above (all remaining
  fields of `EpGroupoid` are Props: local sc-diffeomorphic `s, t`, sc-smooth `u, ι, m`,
  properness).  "Effective": the vocabulary's `EpGroupoid.IsEffective` (Definition 7.11).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_40
open Polyfold

/-- Proposition 7.10: for every ep-groupoid `X`, `(X, 𝐗^R)` with the descended structure maps,
object M-polyfold `X` and morphism M-polyfold `𝐗^R` (Proposition 7.9) is an ep-groupoid (in
particular `𝐗^R` is Hausdorff and paracompact), and it is effective. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (_ : T2Space X.ReducedMor) (_ : ParacompactSpace X.ReducedMor),
      ∃ Y : EpGroupoid Obj X.ReducedMor,
        Y.toGroupoidStr = X.reducedGroupoidStr ∧ Y.PObj = X.PObj ∧
          Y.PMor = X.reducedPolyfold ∧ Y.IsEffective

end RoundTrip.V7_40
