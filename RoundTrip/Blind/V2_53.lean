import Polyfold
/-! Blind formalization of V2_53 (the text's §2.4, Proposition 2.46, pp. 46–47).

Text: for a local sc-diffeomorphism `f : X → Z` and an sc-smooth `g : Y → Z`, the fibred product
`X ₓ×_g Y` is a sub-M-polyfold of `X × Y`; if `Y` is tame, so is the fibred product, with
`d(x, y) = d_Y(y)`; with both maps local sc-diffeomorphisms and both spaces tame,
`d = ½ d_{X×Y} = d_X(x) = d_Y(y)`.

Choices:
- Setting: `X Y Z : Type` (universe 0, as asked), each Hausdorff paracompact, with M-polyfold
  structures `P`, `Q`, `S` (the project's `MPolyfold`, Definition 2.13).  The product M-polyfold
  `X × Y` is the project's `P.prod Q` (checked with `#print`: the atlas of product charts
  `φ × ψ` with models `(O × O', C × C', E ⊕ E')`); it needs `X × Y` paracompact as an instance,
  which is a hypothesis of B (true: M-polyfolds are metrizable, Theorem 2.16).
- "local sc-diffeomorphism": `P.IsLocalScDiffeo S f` (checked: every `x` has an open `U ∋ x`, an
  open `V ⊆ Z` and `h : Z → X` with `f : U → V`, `h : V → U` mutually inverse and sc-smooth,
  `IsScDiffeoOn`).  "sc-smooth": `Q.IsScSmoothMap S g` (Definition 2.14, checked: sc-smooth on
  `univ`, in all pairs of charts).
- The fibred product: the project's `MPolyfold.fibredProduct f g` (checked:
  `{(x, y) | f x = g y} ⊆ X × Y`).  "sub-M-polyfold": `IsSubMPolyfold` (Definition 2.20,
  checked: every point has an open `V` in `X × Y` and an sc-smooth `r : V → V`, `r ∘ r = r`, with
  `r(V) = A ∩ V`).
- "the fibred product is tame", `d`: the fibred product with its induced M-polyfold structure,
  the project's `subPolyfold` (Proposition 2.21, sub-charts `φ|_{W ∩ A}`); it needs the subtype
  paracompact as an instance, which B asserts (true: it is closed in a metrizable space).  Tame is
  `MPolyfold.IsTame` (Definition 2.37, checked: an equivalent atlas of charts on tame retracts — a
  property of the given structure).  `d`, `d_X`, `d_Y`, `d_{X×Y}` are `MPolyfold.degIndex`
  (Definition 2.22, checked: the minimum of `d_C(φ(x))` over the compatible charts around the
  point) of the respective M-polyfolds.
- I attach `d(x, y) = d_Y(y)` to the tame case, as the item groups it ("if `Y` is tame, so is the
  fibred product, with `d(x, y) = d_Y(y)`").
- "`d = ½ d_{X×Y}`" is written `2 * d = d_{X×Y}` in `ℕ`.  The last claim assumes: `f` and `g`
  local sc-diffeomorphisms, `X` and `Y` tame.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_53
open Polyfold

/-- Proposition 2.46: fibred products along a local sc-diffeomorphism are sub-M-polyfolds; tame
when `Y` is, with `d = d_Y`; and `d = ½ d_{X×Y} = d_X = d_Y` when both maps are local
sc-diffeomorphisms and both spaces are tame. -/
def B : Prop :=
  ∀ (X Y Z : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] [ParacompactSpace (X × Y)]
    (P : MPolyfold X) (Q : MPolyfold Y) (S : MPolyfold Z) (f : X → Z) (g : Y → Z),
    P.IsLocalScDiffeo S f → Q.IsScSmoothMap S g →
      -- the fibred product is a sub-M-polyfold of `X × Y`
      (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g) ∧
      -- `Y` tame: the fibred product is tame, with `d(x, y) = d_Y(y)`
      (Q.IsTame →
        ∃ (hA : (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g))
          (_ : ParacompactSpace (MPolyfold.fibredProduct f g)),
          ((P.prod Q).subPolyfold hA).IsTame ∧
          ∀ p : MPolyfold.fibredProduct f g,
            ((P.prod Q).subPolyfold hA).degIndex p = Q.degIndex p.1.2) ∧
      -- both maps local sc-diffeomorphisms, both spaces tame: `d = ½ d_{X×Y} = d_X = d_Y`
      (Q.IsLocalScDiffeo S g → P.IsTame → Q.IsTame →
        ∃ (hA : (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g))
          (_ : ParacompactSpace (MPolyfold.fibredProduct f g)),
          ∀ p : MPolyfold.fibredProduct f g,
            2 * ((P.prod Q).subPolyfold hA).degIndex p = (P.prod Q).degIndex p.1 ∧
            ((P.prod Q).subPolyfold hA).degIndex p = P.degIndex p.1.1 ∧
            ((P.prod Q).subPolyfold hA).degIndex p = Q.degIndex p.1.2)

end RoundTrip.V2_53
