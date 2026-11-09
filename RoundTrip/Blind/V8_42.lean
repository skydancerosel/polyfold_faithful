import Polyfold
/-! Blind formalization of V8_42 (the 2017 book, arXiv 1707.08941, Part II, §8.5.1, Proposition 8.4
and the paragraph before it, p. 288; 2021: Proposition 8.6.4).

Text: let `F : Y → X` be an sc-smooth proper covering functor.  Then for every connected component
`c` of the orbit space `|X|` there is a constant `k_c` with `#F⁻¹(x) = k_c` whenever `π(x) ∈ c`.  In
other words, viewing `ℕ = {1, 2, …}` as an ep-groupoid with the identities as the morphisms, the map
`X → ℕ`, `x ↦ #F⁻¹(x)`, is an sc-smooth functor.  (Before: the structure of the isomorphism
classes of `F⁻¹(x)` stays the same if `x` is perturbed, which with Lemma 8.6.3 gives the result.)

Choices:
- Setting as in my `RoundTrip/Blind/V8_38.lean`: spaces in `Type`, Hausdorff paracompact, the
  project's `EpGroupoid`, `EpFunctor` (sc-smooth functors by definition), and
  `EpFunctor.IsProperCovering` (= Definition 8.5.1, checked with `#print`).
- `|X|`: the project's `X.OrbitSpace` (`Quotient` of the relation "joined by a morphism", read
  with `#print`), with its topology, which I checked (`rfl`) to be the quotient topology
  `coinduced π`; `π` is `X.π` (`x ↦ ⟦x⟧`).  "Connected component `c`": `c = connectedComponent p`
  for some `p ∈ |X|`.  `#` is `Set.ncard` (fibres are finite by Definition 8.5.1 (2)).
- "`ℕ` as an ep-groupoid with the identities as the morphisms": the project's
  `EpGroupoid.trivial` (`#print`ed: morphisms = objects, all structure maps the identity) of
  `discretePolyfold ℕ` (the discrete M-polyfold, charts `{n} → ℝ⁰`).  The text's `ℕ = {1, 2, …}`:
  I use Mathlib's `ℕ` (with `0`) as the target and assert separately that every `#F⁻¹(x) ≥ 1`, so
  the functor takes values in `{1, 2, …}`; for maps into a discrete space this is the same claim.
- "`x ↦ #F⁻¹(x)` is an sc-smooth functor": some project `EpFunctor E : X → ℕ` (a functor of the
  groupoids, sc-smooth on objects and morphisms) with `E.obj x = #F⁻¹(x)`; its morphism map is
  forced (`E.mor φ` is the identity `E.obj (s φ)` of the trivial groupoid).
- The sentence before the proposition ("the structure … stays the same if `x` is perturbed") is
  a heuristic for the proof and too vague to formalize; not included.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_42
open Polyfold

/-- Proposition 8.6.4: `x ↦ #F⁻¹(x)` is constant on the preimage of every connected component of
`|X|`; it is an sc-smooth functor from `X` to the discrete ep-groupoid `ℕ`, with values `≥ 1`. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering →
      -- constancy on connected components of `|X|`
      (∀ c : Set X.OrbitSpace, (∃ p : X.OrbitSpace, c = connectedComponent p) →
        ∃ k : ℕ, ∀ x : ObjX, X.π x ∈ c → (F.obj ⁻¹' {x}).ncard = k) ∧
      -- "in other words": an sc-smooth functor `X → ℕ`
      (∃ E : EpFunctor X (EpGroupoid.trivial (discretePolyfold ℕ)),
        ∀ x : ObjX, E.obj x = (F.obj ⁻¹' {x}).ncard) ∧
      -- with values in `{1, 2, …}`
      (∀ x : ObjX, 1 ≤ (F.obj ⁻¹' {x}).ncard)

end RoundTrip.V8_42
