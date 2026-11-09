import Polyfold
/-! Blind formalization of V8_32 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Definition 8.9
and the category `Diff_sc` before it, pp. 279–280; 2021: Definition 8.5.5, pp. 387–389).

Text: `Diff_sc` is the category whose objects are M-polyfolds and whose morphisms are sc-smooth
diffeomorphisms.  Let `D`, `C` be categories with finitely many objects and morphisms, all
morphisms isomorphisms, `C` with one object `x`.  A covering functor `f : D → C` is a functor with
`𝐃 → 𝐂 ₛ×_f D`, `ψ ↦ (f(ψ), s(ψ))`, a bijection.  A geometric lift of a covering functor `f`
consists of functors `L_D : D → Diff_sc`, `L_C : C → Diff_sc` and a natural transformation
`τ : L_D → L_C ∘ f` of functors `D → Diff_sc`.

Choices:
- This item is a definition; B states that the project's notions are the text's.
- `Diff_sc`: the project's `MPolyfoldCat` (`#print`ed: a type in universe 0 here, with a topology,
  Hausdorff, paracompact, and an `MPolyfold` structure — the project's M-polyfolds) with its
  `Category` instance (`instCategoryMPolyfoldCat`).  An sc-smooth diffeomorphism `A → B` (my
  `IsScDiffeoB`): a map with a two-sided inverse, both sc-smooth (`MPolyfold.IsScSmoothMap`,
  Definition 2.14).  B (i): every morphism `m : A ⟶ B` has an underlying map (`ScDiffeo.toFun`,
  `A ⟶ B` being `ScDiffeo A B` by `rfl`) which is an sc-diffeomorphism, every sc-diffeomorphism is
  the map of a morphism, identities are identity maps and composition is composition of maps.
- `D`: a Mathlib `Groupoid` (all morphisms isomorphisms) with finitely many objects and morphisms
  (`Fintype` instances); `C`: a one-object groupoid, encoded as Mathlib's `SingleObj G` for a
  finite group `G` (its automorphism group; morphisms compose by `g ∘ h = g * h`, Mathlib's
  `comp_as_mul`).  The finiteness hypotheses are the text's setting; the notions do not use them.
- Covering functor (my `IsCoveringB`): the fibred product `𝐂 ₛ×_f D` written for a general target
  category, `{(φ, y) | s(φ) = f(y)} = Σ (y : D) (c : C), (f(y) ⟶ c)`, and the map
  `ψ ↦ (f(ψ), s(ψ))` from `𝐃 = Σ (a b : D), (a ⟶ b)` to it a bijection.  B (ii): for
  `C = SingleObj G` this is the project's `IsCoveringFunctor` (`#print`ed: bijectivity of
  `ψ ↦ (f(ψ), s(ψ))` into
  `G × D`), a nontrivial identification of `𝐂 ₛ×_f D` with `G × D`.
- Geometric lift: the project's structure `GeometricLift f` (`#print`ed: fields `LD`, `LC`,
  `τ : LD ⟶ f ⋙ LC`).  B (iii): for a covering functor `f`, every triple `(L_D, L_C, τ)` with
  `τ : L_D ⟶ f ⋙ L_C` (`L_C ∘ f` is `f ⋙ L_C`) is a geometric lift with these components.  (That
  every geometric lift has such components is its typing.)
- Nothing looks false to me.
-/
namespace RoundTrip.V8_32
open Polyfold CategoryTheory

/-- An sc-smooth diffeomorphism `f : A → B` between M-polyfolds. -/
def IsScDiffeoB (A B : MPolyfoldCat.{0}) (f : A.carrier → B.carrier) : Prop :=
  ∃ g : B.carrier → A.carrier, A.P.IsScSmoothMap B.P f ∧ B.P.IsScSmoothMap A.P g ∧
    (∀ a, g (f a) = a) ∧ ∀ b, f (g b) = b

/-- **Covering functor**: `ψ ↦ (f(ψ), s(ψ))` is a bijection `𝐃 → 𝐂 ₛ×_f D`, where
`𝐂 ₛ×_f D = {(φ, y) | s(φ) = f(y)}` is written `Σ (y : D) (c : C), (f(y) ⟶ c)`. -/
def IsCoveringB {D : Type} [Groupoid D] {C : Type} [Groupoid C] (f : D ⥤ C) : Prop :=
  Function.Bijective (fun ψ : (Σ (a : D) (b : D), (a ⟶ b)) =>
    (⟨ψ.1, f.obj ψ.2.1, f.map ψ.2.2⟩ : Σ (y : D) (c : C), (f.obj y ⟶ c)))

/-- Definition 8.5.5: the project's `Diff_sc`, covering functors and geometric lifts are the
text's. -/
def B : Prop :=
  -- (i) `Diff_sc`: morphisms are the sc-diffeomorphisms, composed as maps
  (∀ A B : MPolyfoldCat.{0},
    (∀ m : A ⟶ B, IsScDiffeoB A B m.toFun) ∧
    (∀ f : A.carrier → B.carrier, IsScDiffeoB A B f → ∃ m : A ⟶ B, m.toFun = f)) ∧
  (∀ A : MPolyfoldCat.{0}, (𝟙 A : A ⟶ A).toFun = id) ∧
  (∀ (A B C : MPolyfoldCat.{0}) (m : A ⟶ B) (n : B ⟶ C), (m ≫ n).toFun = n.toFun ∘ m.toFun) ∧
  -- (ii), (iii): covering functors and geometric lifts
  ∀ (D : Type) [Groupoid D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
    (G : Type) [Group G] [Fintype G] (f : D ⥤ SingleObj G),
    (IsCoveringFunctor f ↔ IsCoveringB f) ∧
    (IsCoveringFunctor f →
      ∀ (LD : D ⥤ MPolyfoldCat.{0}) (LC : SingleObj G ⥤ MPolyfoldCat.{0}) (τ : LD ⟶ f ⋙ LC),
        ∃ L : GeometricLift.{0} f, L.LD = LD ∧ L.LC = LC ∧ HEq L.τ τ)

end RoundTrip.V8_32
