import Polyfold
/-! Blind formalization of V8_33 (the 2017 book, arXiv 1707.08941, Part II, §8.4, after
Definition 8.9, pp. 280–281; 2021: after Definition 8.5.5, pp. 388–390).

Text: for a covering functor `f : D → C` with a geometric lift `τ : L_D → L_C ∘ f`:
`U(x) := L_C(x)`, `U(y) := L_D(y)` for `y ∈ D = f⁻¹(x)`; `τ(y) : U(y) → U(x)` is an
sc-diffeomorphism; for `ψ : y → y'`, `φ_{yy'}(ψ) := L_D(ψ) : U(y) → U(y')` is an
sc-diffeomorphism, and `φ_{yy''}(ψ ∘ γ) = φ_{y'y''}(ψ) ∘ φ_{yy'}(γ)`.  `G_y` acts on `U(y)` by
`h ∗ z := L_D(h)(z)` and `G_x` on `U(x)` by `g ∗ z = L_C(g)(z)`, and since `τ` is natural,
`τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)`: the `τ(y)` are equivariant with respect to `f : G_y → G_x`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_32.lean`: `D` a finite Mathlib groupoid, `C = SingleObj G`
  for a finite group `G` (one object `x = star`, `G_x = G`, `g ∘ h = g * h`), `f : D ⥤ SingleObj G`
  a covering functor (the project's `IsCoveringFunctor`, `#print`ed: bijectivity of
  `ψ ↦ (f(ψ), s(ψ))` into `G × D`, the text's definition, see V8_32), and `L : GeometricLift f`
  (the project's structure, `#print`ed: `L_D`, `L_C`, `τ : L_D ⟶ f ⋙ L_C`) with values in the
  project's `Diff_sc = MPolyfoldCat` (universe 0; `A ⟶ B` is `ScDiffeo A B`, composition is
  composition of maps, checked by `rfl`).
- `U(x) = (L_C x).carrier`, `U(y) = (L_D y).carrier`; `τ(y)` is the map `(L.τ.app y).toFun`
  (its type `U(y) → U(f(y))` is `U(y) → U(x)` definitionally, `SingleObj G` having one object).
- "sc-diffeomorphism": a map with an inverse such that the project's `MPolyfold.IsScDiffeoOn`
  holds on the whole spaces (as for the project's morphisms of `Diff_sc`).
- `ψ ∘ γ` is Mathlib's `γ ≫ ψ`.  `G_y` is `y ⟶ y` with `h ∘ k = k ≫ h`; "acts" means the action
  laws `1 ∗ z = z`, `(h ∘ k) ∗ z = h ∗ (k ∗ z)` for the formula `h ∗ z = L_D(h)(z)`, and likewise
  for `g ∗ z = L_C(g)(z)` on `U(x)` with the product of `G`.  Equivariance: `f(h) ∈ G` is `f.map h`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_33
open Polyfold CategoryTheory

/-- After Definition 8.5.5: `τ(y)` and `φ_{yy'}(ψ) = L_D(ψ)` are sc-diffeomorphisms, `φ` is
compatible with composition, `h ∗ z = L_D(h)(z)` and `g ∗ z = L_C(g)(z)` are actions of `G_y` on
`U(y)` and of `G_x` on `U(x)`, and `τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)`. -/
def B : Prop :=
  ∀ (D : Type) [Groupoid D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
    (G : Type) [Group G] [Fintype G] (f : D ⥤ SingleObj G),
    IsCoveringFunctor f → ∀ L : GeometricLift.{0} f,
      -- `τ(y) : U(y) → U(x)` is an sc-diffeomorphism
      (∀ y : D, ∃ g : (L.LC.obj (SingleObj.star G)).carrier → (L.LD.obj y).carrier,
        (L.LD.obj y).P.IsScDiffeoOn (L.LC.obj (SingleObj.star G)).P (L.τ.app y).toFun g
          Set.univ Set.univ) ∧
      -- `φ_{yy'}(ψ) = L_D(ψ) : U(y) → U(y')` is an sc-diffeomorphism
      (∀ (y y' : D) (ψ : y ⟶ y'), ∃ g : (L.LD.obj y').carrier → (L.LD.obj y).carrier,
        (L.LD.obj y).P.IsScDiffeoOn (L.LD.obj y').P (L.LD.map ψ).toFun g Set.univ Set.univ) ∧
      -- `φ_{yy''}(ψ ∘ γ) = φ_{y'y''}(ψ) ∘ φ_{yy'}(γ)`
      (∀ (y y' y'' : D) (γ : y ⟶ y') (ψ : y' ⟶ y''),
        (L.LD.map (γ ≫ ψ)).toFun = (L.LD.map ψ).toFun ∘ (L.LD.map γ).toFun) ∧
      -- `G_y` acts on `U(y)` by `h ∗ z = L_D(h)(z)`
      (∀ (y : D) (z : (L.LD.obj y).carrier), (L.LD.map (𝟙 y)).toFun z = z) ∧
      (∀ (y : D) (h k : y ⟶ y) (z : (L.LD.obj y).carrier),
        (L.LD.map (k ≫ h)).toFun z = (L.LD.map h).toFun ((L.LD.map k).toFun z)) ∧
      -- `G_x` acts on `U(x)` by `g ∗ z = L_C(g)(z)`
      (∀ z : (L.LC.obj (SingleObj.star G)).carrier,
        (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from (1 : G))).toFun z = z) ∧
      (∀ (g h : G) (z : (L.LC.obj (SingleObj.star G)).carrier),
        (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from g * h)).toFun z =
          (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from g)).toFun
            ((L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from h)).toFun z)) ∧
      -- equivariance: `τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)`
      (∀ (y : D) (h : y ⟶ y) (z : (L.LD.obj y).carrier),
        (L.τ.app y).toFun ((L.LD.map h).toFun z) =
          (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from (f.map h : G))).toFun
            ((L.τ.app y).toFun z))

end RoundTrip.V8_33
