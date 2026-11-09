import Polyfold
/-! Blind formalization of V11_1 (the text's Part II, §11.1, Theorem 11.1.1, p. 521 of the
Springer 2021 book; 2017: Theorem 11.1, p. 375).

Text: the tangent functor `T : EP → EP` induces a functor `T : EP(E⁻¹) → EP(E⁻¹)` by
`[X ←F A →Φ Y] ↦ [TX ←TF TA →TΦ TY]`, compatible with `i : EP → EP(E⁻¹)`.

Choices:
- Setting: universe `1`, i.e. `EP.{1}` and `EPLoc.{1}` (all spaces in `Type 1`), not `Type`.
  The project's tangent `EP.tangent` and its tangent functor `tangentFunctor` (2021 Theorem 8.1.3)
  live on `EP.{max u 1}` (the tangent space of a type in `Type u` is in `Type (max u 1)`), so an
  endofunctor `T` needs universe `max u 1`; I take `u = 0`.
- `EP(E⁻¹)`: the project's category `EPLocalization.EPLoc` (Definition 10.3.12: bundled
  ep-groupoids, morphisms the classes of diagrams); `[d]` is `EPLoc.homMk d` for a diagram
  `d : X ←F A →Φ Y` (the project's `Diagram`: an `EP` `A`, an equivalence `F`, a functor `Φ`).
- `i`: the project's `EPLoc.localizationFunctor` (read with `#print`: identity on objects,
  `Φ ↦ [X ←1 X →Φ Y]`, the text's `i` of Theorem 10.3.14).
- `T : EP → EP`: the project's `tangentFunctor.{0}` (checked by `rfl`: `obj X = EP.tangent X`,
  `map Φ` is `EpFunctor.tangent Φ`, Chapter 8's `TΦ`).
- `[TX ←TF TA →TΦ TY]`: the project's `Diagram.tangent d` (`#print`ed and checked by `rfl`: its
  middle groupoid is `EP.tangent A`, its legs are `EpFunctor.tangent F` and `EpFunctor.tangent Φ`;
  it carries the proof that `TF` is an equivalence, Theorem 10.1.7).
- Reading of "induces a functor": there is a functor `T'` of `EP(E⁻¹)` with `T'(X) = TX` on
  every object and `T'[d] = [Td]` for every diagram `d`.  Since `T'(X) = TX` is only a
  propositional equation, the morphism equation is stated with the `eqToHom` transports along it.
  Every morphism of `EP(E⁻¹)` is some `[d]`, so this determines `T'` on morphisms (and contains the
  well-definedness of `[d] ↦ [Td]` and functoriality).
- "compatible with `i`": the square commutes, `i ∘ T = T' ∘ i` as functors `EP → EP(E⁻¹)`
  (Mathlib's equality of functors, `i ⋙ T' = T ⋙ i`).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_1
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- Theorem 11.1.1: `T` descends to a functor of `EP(E⁻¹)`, `X ↦ TX`, `[d] ↦ [Td]`, commuting
with `i`. -/
def B : Prop :=
  ∃ (T : EPLoc.{1} ⥤ EPLoc.{1})
    (hobj : ∀ X : EPLoc.{1}, T.obj X = EPLoc.of (EP.tangent.{0} X.toEP)),
    (∀ (X Y : EP.{1}) (d : Diagram X Y),
      T.map (EPLoc.homMk d) =
        eqToHom (hobj (EPLoc.of X)) ≫ EPLoc.homMk (Diagram.tangent.{0} d) ≫
          eqToHom (hobj (EPLoc.of Y)).symm) ∧
    EPLoc.localizationFunctor.{1} ⋙ T = tangentFunctor.{0} ⋙ EPLoc.localizationFunctor.{1}

end RoundTrip.V11_1
