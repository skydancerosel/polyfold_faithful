import Polyfold
/-! Blind formalization of V10_31 (the text's Part II, §10.4, Definition 10.4.11, p. 503 of the
Springer 2021 book; 2017: Definition 10.13, p. 364).

Text: `𝓢𝓔𝓟` is the category whose objects are the strong bundles over ep-groupoids and whose
morphisms are the strong bundle functors; `F` is the class of strong bundle equivalences.

Choices:
- This item is a definition.  Setting: the project's bundled `SEP` in universe 0 (`SEP.{0}`; fields
  read with `#print`: the base spaces, an `EpGroupoid` `X`, the total space `W`, `P : W → X`, the
  fibre structures, a strong bundle `B` and an `EpStrongBundle X B`), i.e. exactly a strong bundle
  over an ep-groupoid (Definition 8.3.1, V8_20); nothing about objects is claimed beyond this
  bundling.
- Morphisms `(P, μ) → (P', μ')` (my `HomB`): pairs `(ϕ, Φ)` of sc-smooth functors `ϕ : X → X'`,
  `Φ : (W, 𝐖) → (W', 𝐖')` with `Φ` a strong bundle functor covering `ϕ` (the project's
  `IsStrongBundleFunctor`, Definition 8.3.3, V8_24); `(W, 𝐖)` is the project's `E.toEpGroupoid`.
- "is the category": B asserts a family of bijections `e` between the project's morphisms
  `A ⟶ A'` (of its `Category SEP` instance) and `HomB A A'`, taking identities to the pairs of
  identity functors and composition to componentwise composition of functors (written on object
  and morphism maps, so the project's `EpFunctor.id`, `EpFunctor.comp` are not used).  This says
  that the project's `SEP` is (isomorphic, identically on objects, to) the text's category.
- "`F` is the class of strong bundle equivalences": the project's `SEP.equivalences` (a
  `MorphismProperty`) holds for `f` iff the pair `e f` is a strong bundle equivalence (Definition
  10.4.1, the project's `IsStrongBundleEquivalence`, trusted; see my V10_25).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_31
open Polyfold CategoryTheory

/-- A morphism of `𝓢𝓔𝓟`: a strong bundle functor `Φ` covering `ϕ`. -/
def HomB (A A' : SEP.{0}) : Type :=
  {p : EpFunctor A.X A'.X × EpFunctor A.E.toEpGroupoid A'.E.toEpGroupoid //
    A.E.IsStrongBundleFunctor A'.E p.1 p.2}

/-- **Definition 10.4.11**: the project's `SEP` has the strong bundle functors as morphisms, with
the composition and identities of functors, and its class `F` is that of the strong bundle
equivalences. -/
def B : Prop :=
  ∃ e : ∀ A A' : SEP.{0}, (A ⟶ A') ≃ HomB A A',
    -- identities are the pairs of identity functors
    (∀ A : SEP.{0},
      (∀ x : A.Obj, (e A A (𝟙 A)).1.1.obj x = x) ∧ (∀ φ : A.Mor, (e A A (𝟙 A)).1.1.mor φ = φ) ∧
      (∀ w : A.W, (e A A (𝟙 A)).1.2.obj w = w) ∧
      (∀ q : pullbackSpace A.P A.X.src, (e A A (𝟙 A)).1.2.mor q = q)) ∧
    -- composition is componentwise composition of functors
    (∀ (A A' A'' : SEP.{0}) (f : A ⟶ A') (g : A' ⟶ A''),
      (∀ x : A.Obj, (e A A'' (f ≫ g)).1.1.obj x = (e A' A'' g).1.1.obj ((e A A' f).1.1.obj x)) ∧
      (∀ φ : A.Mor, (e A A'' (f ≫ g)).1.1.mor φ = (e A' A'' g).1.1.mor ((e A A' f).1.1.mor φ)) ∧
      (∀ w : A.W, (e A A'' (f ≫ g)).1.2.obj w = (e A' A'' g).1.2.obj ((e A A' f).1.2.obj w)) ∧
      (∀ q : pullbackSpace A.P A.X.src,
        (e A A'' (f ≫ g)).1.2.mor q = (e A' A'' g).1.2.mor ((e A A' f).1.2.mor q))) ∧
    -- `F` is the class of strong bundle equivalences
    (∀ (A A' : SEP.{0}) (f : A ⟶ A'),
      SEP.equivalences f ↔ A.E.IsStrongBundleEquivalence A'.E (e A A' f).1.1 (e A A' f).1.2)

end RoundTrip.V10_31
