import Polyfold
/-! Blind formalization of V11_2 (the text's Part II, §11.1, Proposition 11.1.2, p. 522 of the
Springer 2021 book; 2017: Proposition 11.1, p. 376).

Text: if `f : X → Y` is a generalized isomorphism and `|f|(|x|) = |y|`, then
`d_X(x₀) = d_Y(y₀)` for all representatives `x₀` of `|x|` and `y₀` of `|y|`.

Choices:
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`), `f` a
  morphism `X → Y` of the project's `EP(E⁻¹)` (`EPLocalization.EPLoc`, Definition 10.3.12).
- "generalized isomorphism" (Definition 10.3.9: some `g` with `g ∘ f = 1_X`, `f ∘ g = 1_Y`):
  Mathlib's `IsIso f` in `EP(E⁻¹)`.
- `|x|`: the class of `x` in the project's orbit space `X.OrbitSpace` (`#print`ed: the quotient
  of the objects by "there is a morphism `x → y`").  `|f| : |X| → |Y|` is the project's
  `EPLoc.orbitMap f` (`#print`ed: on a representative `X ←F A →Φ Y`, `|Φ| ∘ |F|⁻¹` with `|F|⁻¹`
  the inverse of the homeomorphism `|F|`; Definition 10.3.7).
- `d_X`, `d_Y`: the degeneracy indices of the object M-polyfolds, the project's
  `MPolyfold.degIndex` (Part I's Definition, `#print`ed: `sInf` of the chart degeneracy indices).
- "for all representatives": B quantifies over all objects `x₀`, `y₀` with `|f|(|x₀|) = |y₀|`,
  which is the same as all representatives of `|x|` and `|y|`.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_2
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- `|x| ∈ |X|`, the orbit of `x`. -/
abbrev piB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj) : X.OrbitSpace :=
  Quotient.mk _ x

/-- Proposition 11.1.2: a generalized isomorphism preserves the degeneracy index. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), IsIso f →
    ∀ (x₀ : X.Obj) (y₀ : Y.Obj), EPLoc.orbitMap f (piB X.X x₀) = piB Y.X y₀ →
      X.X.PObj.degIndex x₀ = Y.X.PObj.degIndex y₀

end RoundTrip.V11_2
