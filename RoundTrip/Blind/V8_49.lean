import Polyfold
/-! Blind formalization of V8_49 (the 2021 book, Part II, §8.5, the remark after Definition 8.5.5
and Example 8.5.6, p. 388).

Text: for a covering functor `f : D → C` and `d ∈ D` with `f(d) = x`, the map `f : G_d → G_x` is
injective, but it need not be surjective.  Example 8.5.6: `D` with two objects `a`, `b` and
exactly one morphism between any two objects, `C` with one object `x` and `G_x = {1_x, ε}`,
`f(φ) = f(φ⁻¹) = ε` for the morphism `φ : a → b`.

Choices:
- The text of Definition 8.5.5 is not quoted in the item.  I read "covering functor" as in the
  project's vocabulary docstring of 2017 Definition 8.9: a functor `f : D → C` of groupoids such
  that `ψ ↦ (f(ψ), s(ψ))` is a bijection from the morphisms of `D` onto
  `C ₛ×_f D = {(φ, d) | s(φ) = f(d)}` (unique lifting of morphisms of `C` starting at `f(d)`).
  The project's `IsCoveringFunctor` is only stated for one-object `C = SingleObj G`; since the
  remark speaks of a general `x = f(d)`, I define my own `IsCoveringB` for arbitrary groupoids
  `C` (Mathlib categories with `Groupoid` instances, objects and morphisms in `Type`).  I do not
  assume `D`, `C` finite (the text may; injectivity does not need it).
- `C ₛ×_f D` is the type of triples `⟨d, c, φ : f(d) ⟶ c⟩`, and `ψ : a ⟶ b` goes to
  `⟨a, f(b), f(ψ)⟩`.
- `G_d` is the hom type `d ⟶ d` (all endomorphisms are isomorphisms in a groupoid); the map
  `G_d → G_x` is `g ↦ f.map g`.
- Example 8.5.6: `D` is my `DB` (objects `Bool`, `a = false`, `b = true`, exactly one morphism
  `()` between any two objects); `C` is Mathlib's `SingleObj ℤˣ` (one object, `G_x = ℤˣ =
  {1, -1}`, `ε = -1`); `f` is `fB`, sending a morphism `a' → b'` to `1` if `a' = b'` and to
  `ε` otherwise (so `f(1_a) = f(1_b) = 1_x`, `f(φ) = f(φ⁻¹) = ε`; the identities are forced by
  functoriality).  The claim of the example: `fB` is a covering functor and `G_a → G_x` is not
  surjective.
- B is the conjunction of the injectivity statement (for all covering functors and all `d`) and
  the example.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_49
open CategoryTheory

/-- A covering functor of groupoids: `ψ ↦ (f(ψ), s(ψ))` is a bijection from the morphisms of
`D` onto `C ₛ×_f D`. -/
def IsCoveringB {D C : Type} [Groupoid.{0} D] [Groupoid.{0} C] (f : D ⥤ C) : Prop :=
  Function.Bijective
    (fun p : (Σ (a : D) (b : D), a ⟶ b) =>
      (⟨p.1, f.obj p.2.1, f.map p.2.2⟩ : Σ (a : D) (c : C), f.obj a ⟶ c))

/-- The groupoid `D` of Example 8.5.6: two objects, exactly one morphism between any two. -/
def DB : Type := Bool

instance : Groupoid.{0} DB where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv _ := ()
  inv_comp _ := rfl
  comp_inv _ := rfl

instance : DecidableEq DB := inferInstanceAs (DecidableEq Bool)

/-- The object `a` of `D`. -/
def aB : DB := false

/-- The value of `f` on the morphism `a' → b'`: `1` if `a' = b'`, else `ε = -1`. -/
def fBmap (a b : DB) : ℤˣ := if a = b then 1 else -1

/-- The functor `f : D → C = SingleObj ℤˣ` of Example 8.5.6: `1` on identities, `ε = -1` on
`φ : a → b` and `φ⁻¹ : b → a`. -/
def fB : DB ⥤ SingleObj ℤˣ where
  obj _ := SingleObj.star ℤˣ
  map {a b} _ := (fBmap a b : ℤˣ)
  map_id a := by
    change fBmap a a = 1
    exact if_pos rfl
  map_comp {a b c} _ _ := by
    change fBmap a c = fBmap b c * fBmap a b
    cases a <;> cases b <;> cases c <;> decide

/-- The remark after Definition 8.5.5 and Example 8.5.6: a covering functor is injective on
isotropy groups, and (Example 8.5.6) need not be surjective on them. -/
def B : Prop :=
  (∀ (D C : Type) [Groupoid.{0} D] [Groupoid.{0} C] (f : D ⥤ C), IsCoveringB f →
    ∀ d : D, Function.Injective (fun g : d ⟶ d => f.map g)) ∧
  (IsCoveringB fB ∧ ¬ Function.Surjective (fun g : aB ⟶ aB => fB.map g))

end RoundTrip.V8_49
