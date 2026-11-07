import Polyfold
/-! Blind formalization of V7_7 (the text's Part II, §7.1, Definition 7.5, p. 228 of the 2017
book).

Text: the induced degeneracy index `d_{|X|} : |X| → ℕ` is defined by `d_{|X|}(|x|) = d_X(x)`.

Choices:
- This item is a definition.  Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact,
  `X : EpGroupoid Obj Mor` (`RoundTrip/Blind/V7_3.lean`).  `|X|` and `|x| = π(x)` are the
  project's `OrbitSpace` and `π` (characterized in `RoundTrip/Blind/V7_1.lean`); `d_X` is the
  project's `MPolyfold.degIndex` of the object M-polyfold (Definition 2.22,
  `RoundTrip/Blind/V2_26.lean`).
- B: (a) the presupposition that makes the definition meaningful: `d_X(x) = d_X(x')` whenever
  `x ∼ x'` (stated just before the definition); (b) the project's `degIndexOrbit` satisfies
  `d_{|X|}(|x|) = d_X(x)` for every `x` (as `π` is onto, this determines it).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_7
open Polyfold

/-- Definition 7.5: `d_{|X|}(|x|) = d_X(x)` is well defined, and it is the project's
`degIndexOrbit`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ x x' : Obj, X.Isomorphic x x' → X.PObj.degIndex x = X.PObj.degIndex x') ∧
    (∀ x : Obj, X.degIndexOrbit (X.π x) = X.PObj.degIndex x)

end RoundTrip.V7_7
