import Polyfold
/-! Blind formalization of V10_45 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.14,
p. 491; 2017: Theorem 10.5, p. 354): the localization functor.

Text: a functor `i : EP → EP(E⁻¹)`, identity on objects, `i(Φ) = [X ←1 X →Φ Y]`, with `i(F)`
invertible for `F ∈ E`.

Choices:
- `EP(E⁻¹)` is the project's category `EPLoc` (compared with Definition 10.3.12 in
  `RoundTrip/Blind/V10_44.lean`: objects the ep-groupoids, morphisms the classes `EPLoc.homMk d`,
  composition of Theorem 10.3.8, units `[1_X]`); "invertible" is Mathlib's `IsIso` there (a
  generalized isomorphism).  `EP` is the project's `EP.{u}` (any universe `u`), whose identities
  and composition are `EpFunctor.id`, `EpFunctor.comp` (vocabulary docstrings: "the identity /
  the composition of `EP`").
- `[X ←1 X →Φ Y]`: `EPLoc.homMk` of the project's `Diagram.ofFunctor Φ` (docstring: the diagram
  `d_Φ = X ←1 X →Φ Y`).  I trust this construction (building it myself needs a proof that the
  identity functor is an equivalence, which is a project lemma).
- "A functor, identity on objects, with `i(Φ) = …`": the assignment `X ↦ X` (as an object
  `EPLoc.of X`), `Φ ↦ [X ←1 X →Φ Y]` preserves identities and composition (that is exactly the
  existence of a functor with these values; stated elementarily to avoid casts along
  `i.obj X = EPLoc.of X`).
- `F ∈ E`: `F` is an equivalence, the project's `EpFunctor.IsEquivalence` (Definition 10.1.1;
  the project's `EP.equivalences` is the same class as a `MorphismProperty`, not used).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_45
open Polyfold Polyfold.EPLocalization CategoryTheory

universe u

/-- `i(Φ) = [X ←1 X →Φ Y]`. -/
noncomputable def iB {X Y : EP.{u}} (Φ : EpFunctor X.X Y.X) : EPLoc.of X ⟶ EPLoc.of Y :=
  EPLoc.homMk (Diagram.ofFunctor (X := X) (Y := Y) Φ)

/-- `Φ ↦ [X ←1 X →Φ Y]` is a functor `EP → EP(E⁻¹)` (identity on objects) inverting the
equivalences. -/
def B : Prop :=
  (∀ X : EP.{u}, iB (EpFunctor.id X.X) = 𝟙 (EPLoc.of X)) ∧
  (∀ (X Y Z : EP.{u}) (Φ : EpFunctor X.X Y.X) (Ψ : EpFunctor Y.X Z.X),
      iB (Ψ.comp Φ) = iB Φ ≫ iB Ψ) ∧
  (∀ (X Y : EP.{u}) (F : EpFunctor X.X Y.X), F.IsEquivalence → IsIso (iB F))

end RoundTrip.V10_45
