import Polyfold
/-! Blind formalization of V11_34 (the text's Part II, §11.6, Lemma 11.6.2, p. 551 of the
Springer 2021 book, and the action (11.15), p. 550; 2017: Lemma 11.8, p. 402).

Text: `G_x` acts on `Y_x = F⁻¹(x)` by `g * y = t(α⁻¹(g, y))`, and the full subcategory `Y(x)` is
naturally identified with `G_x ⋉ Y_x`.

Choices:
- Setting as in `RoundTrip/Blind/V8_27.lean`: ep-groupoids `Y`, `X` (all four spaces in `Type`,
  universe 0), `F : EpFunctor Y X` a proper covering functor (the project's
  `EpFunctor.IsProperCovering`, Definition 8.5.1, characterized in V8_27).
- `α` is (my reading) the map `𝐘 → 𝐗 ₛ×_F Y`, `ψ ↦ (F(ψ), s(ψ))` of condition (3) of
  Definition 8.5.1, a bijection for a proper covering.  `α⁻¹(φ, y)` is my `alphaInvB`: a chosen
  `ψ` with `F(ψ) = φ`, `s(ψ) = y` (junk `1_y` when there is none).  Since this uses choice, B
  also asserts (conjunct (0)) that `α` is a bijection onto `{(φ, y) | s(φ) = F(y)}`, i.e. that
  such a `ψ` exists and is unique; this is presupposed by the text's `α⁻¹`.
- `G_x` is the set of morphisms `g` of `X` with `s(g) = t(g) = x`, with the multiplication
  `X.comp g h = g ∘ h` and unit `1_x` (Definition 7.2); `Y_x = F.obj ⁻¹' {x}`.  I do not use the
  project's `Isotropy`, `Fiber`, `fiberSMul`, `Translation`, `toTranslation`.
- "acts": a left action, `g * y ∈ Y_x`, `1_x * y = y`, `(g ∘ h) * y = g * (h * y)` for
  `g, h ∈ G_x`, `y ∈ Y_x` (conjunct (1)).
- `G_x ⋉ Y_x` (as I read the translation groupoid): objects `Y_x`, morphisms the pairs
  `(g, y) ∈ G_x × Y_x` with source `y`, target `g * y`, unit `(1_x, y)`, composition
  `(g', g * y) ∘ (g, y) = (g' ∘ g, y)`.  `Y(x)`: objects `Y_x`, morphisms the `ψ ∈ 𝐘` with
  `s(ψ), t(ψ) ∈ Y_x`.  "naturally identified" (my reading): the functor which is the identity on
  objects and `ψ ↦ α(ψ) = (F(ψ), s(ψ))` on morphisms is an isomorphism of categories
  (conjunct (2)): it lands in the morphisms of `G_x ⋉ Y_x` and preserves targets (source is
  automatic), it is a bijection on morphisms, and it preserves units and composition.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_34
open Polyfold

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

open Classical in
/-- `α⁻¹(φ, y)`: a morphism `ψ` of `Y` with `F(ψ) = φ` and `s(ψ) = y` (junk `1_y` if none). -/
noncomputable def alphaInvB (F : EpFunctor Y X) (φ : MorX) (y : ObjY) : MorY :=
  if h : ∃ ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y then Classical.choose h else Y.unit y

/-- (11.15): `g * y = t(α⁻¹(g, y))`. -/
noncomputable def smulB (F : EpFunctor Y X) (g : MorX) (y : ObjY) : ObjY :=
  Y.tgt (alphaInvB F g y)

/-- The isotropy group `G_x` as a set of morphisms of `X`. -/
def isoB (X : EpGroupoid ObjX MorX) (x : ObjX) : Set MorX :=
  {g | X.src g = x ∧ X.tgt g = x}

end

/-- Lemma 11.6.2: `g * y = t(α⁻¹(g, y))` is an action of `G_x` on `Y_x`, and `Y(x) ≅ G_x ⋉ Y_x`
via `ψ ↦ (F(ψ), s(ψ))`. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering →
    -- (0) `α⁻¹` is well defined: `α` is a bijection onto `𝐗 ₛ×_F Y`
    (∀ (φ : MorX) (y : ObjY), X.src φ = F.obj y →
      ∃! ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y) ∧
    ∀ x : ObjX,
      -- (1) `G_x` acts on `Y_x` (on the left) by `g * y = t(α⁻¹(g, y))`
      (∀ g ∈ isoB X x, ∀ y ∈ F.obj ⁻¹' {x}, F.obj (smulB F g y) = x) ∧
      (∀ y ∈ F.obj ⁻¹' {x}, smulB F (X.unit x) y = y) ∧
      (∀ g ∈ isoB X x, ∀ h ∈ isoB X x, ∀ y ∈ F.obj ⁻¹' {x},
        smulB F (X.comp g h) y = smulB F g (smulB F h y)) ∧
      -- (2) `Y(x) → G_x ⋉ Y_x`, identity on objects, `ψ ↦ (F(ψ), s(ψ))`, is an isomorphism:
      -- it maps a morphism `ψ : y → y'` of `Y(x)` to a morphism `(F ψ, y) : y → F(ψ) * y = y'`,
      (∀ ψ : MorY, F.obj (Y.src ψ) = x → F.obj (Y.tgt ψ) = x →
        F.mor ψ ∈ isoB X x ∧ Y.tgt ψ = smulB F (F.mor ψ) (Y.src ψ)) ∧
      -- it is injective on morphisms,
      (∀ ψ ψ' : MorY, F.obj (Y.src ψ) = x → F.obj (Y.tgt ψ) = x →
        F.obj (Y.src ψ') = x → F.obj (Y.tgt ψ') = x →
        F.mor ψ = F.mor ψ' → Y.src ψ = Y.src ψ' → ψ = ψ') ∧
      -- surjective on morphisms,
      (∀ g ∈ isoB X x, ∀ y ∈ F.obj ⁻¹' {x}, ∃ ψ : MorY,
        F.obj (Y.tgt ψ) = x ∧ Y.src ψ = y ∧ F.mor ψ = g) ∧
      -- and preserves units and composition
      (∀ y ∈ F.obj ⁻¹' {x}, F.mor (Y.unit y) = X.unit x) ∧
      (∀ ψ ψ' : MorY, F.obj (Y.src ψ) = x → F.obj (Y.tgt ψ) = x →
        Y.src ψ' = Y.tgt ψ → F.obj (Y.tgt ψ') = x →
        F.mor (Y.comp ψ' ψ) = X.comp (F.mor ψ') (F.mor ψ) ∧ Y.src (Y.comp ψ' ψ) = Y.src ψ)

end RoundTrip.V11_34
