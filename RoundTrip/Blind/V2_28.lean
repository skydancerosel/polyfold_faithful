import Polyfold
/-! Blind formalization of V2_28 (the text's §2.3, Proposition 2.24, p. 31).

Text: if `f : (U, x) → (V, f(x))` is a germ of sc-diffeomorphisms between M-polyfolds (`X` and
`Y`), then `d_X(x) = d_Y(f(x))`.

Choices:
- Setting: `X Y : Type` (spaces put in `Type`, universe instances `u = v = 0`), both Hausdorff and
  paracompact, with M-polyfold structures `P`, `Q` (Definition 2.13).
- "Germ of sc-diffeomorphisms `f : (U, x) → (V, f(x))`": open `U ∋ x` in `X`, open `V` in `Y`, and
  `f : U → V` an sc-diffeomorphism, i.e. sc-smooth with an sc-smooth inverse `g : V → U`.  This
  is the project's `P.IsScDiffeoOn Q f g U V` (checked with `#print`: `P.IsScSmoothOn Q f U`
  (which includes `U` open), `Q.IsScSmoothOn P g V` (`V` open), `f(U) ⊆ V`, `g(V) ⊆ U`,
  `g ∘ f = id` on `U`, `f ∘ g = id` on `V`; `IsScSmoothOn` is Definition 2.14, see
  `RoundTrip/Blind/V2_24.lean`), plus `x ∈ U` (then `f(x) ∈ V`).  `f`, `g` are total maps whose
  values off `U`, `V` are irrelevant.
- `d_X`, `d_Y`: the project's `MPolyfold.degIndex` (Definition 2.22, checked; see
  `RoundTrip/Blind/V2_26.lean`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_28
open Polyfold

/-- Proposition 2.24: the degeneracy index is invariant under germs of sc-diffeomorphisms. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (Q : MPolyfold Y)
    (f : X → Y) (g : Y → X) (U : Set X) (V : Set Y) (x : X),
    x ∈ U → P.IsScDiffeoOn Q f g U V → P.degIndex x = Q.degIndex (f x)

end RoundTrip.V2_28
