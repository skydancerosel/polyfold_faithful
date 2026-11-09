import Polyfold
/-! Blind formalization of V11_35 (the text's Part II, §11.6, Lemma 11.6.3, pp. 551–552 of the
Springer 2021 book; 2017: Lemma 11.9, p. 403).

Text: a morphism `φ : x → x'` gives an equivariant bijection `B_φ : Y_x → Y_{x'}` ((11.16)) and an
isomorphism `φ̃ : G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`.

Choices:
- Setting, `α⁻¹` (`alphaInvB`), the action `g * y = t(α⁻¹(g, y))` (`smulB`, (11.15)), `G_x`
  (`isoB`) and `Y_x = F.obj ⁻¹' {x}` exactly as in my `RoundTrip/Blind/V11_34.lean` (copied):
  ep-groupoids in `Type`, `F` a proper covering functor (the project's
  `EpFunctor.IsProperCovering`).  None of the project's `transportFiber`, `translationMap`,
  `Fiber`, `Translation` is used.
- (11.16) is not quoted; I read it as `B_φ(y) = t(α⁻¹(φ, y))` (the target of the unique lift of
  `φ` with source `y`), my `transportB`.  `φ : x → x'` is a morphism with `s(φ) = x`,
  `t(φ) = x'`.
- "equivariant": with respect to the conjugation `c_φ : G_x → G_{x'}`, `g ↦ φ ∘ g ∘ φ⁻¹` (my
  reading; `φ⁻¹ = X.inv φ`): `B_φ(g * y) = c_φ(g) * B_φ(y)`.
- `φ̃` (my reading of the unquoted definition): `y ↦ B_φ(y)` on objects and
  `(g, y) ↦ (φ ∘ g ∘ φ⁻¹, B_φ(y))` on morphisms, with `G_x ⋉ Y_x` as in V11_34 (morphisms
  `(g, y) ∈ G_x × Y_x : y → g * y`, unit `(1_x, y)`, composition
  `(g', g * y) ∘ (g, y) = (g' ∘ g, y)`).  "isomorphism": bijective on objects (the bijection
  `B_φ`) and on morphisms (`G_x × Y_x → G_{x'} × Y_{x'}`), and a functor: sources are preserved
  by construction, targets by the equivariance, units iff `c_φ(1_x) = 1_{x'}`, composition iff
  `c_φ(g' ∘ g) = c_φ(g') ∘ c_φ(g)`.  B lists these, together with `c_φ` being a bijection
  `G_x → G_{x'}` (so a group isomorphism, presupposed by "equivariant").
- B is the conjunction of all the claims.  Nothing looks false to me.
-/
namespace RoundTrip.V11_35
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

/-- (11.16), as I read it: `B_φ(y) = t(α⁻¹(φ, y))`. -/
noncomputable def transportB (F : EpFunctor Y X) (φ : MorX) (y : ObjY) : ObjY :=
  Y.tgt (alphaInvB F φ y)

/-- The isotropy group `G_x` as a set of morphisms of `X`. -/
def isoB (X : EpGroupoid ObjX MorX) (x : ObjX) : Set MorX :=
  {g | X.src g = x ∧ X.tgt g = x}

/-- The conjugation `c_φ(g) = φ ∘ g ∘ φ⁻¹`. -/
def conjB (X : EpGroupoid ObjX MorX) (φ g : MorX) : MorX :=
  X.comp φ (X.comp g (X.inv φ))

end

/-- Lemma 11.6.3: `B_φ : Y_x → Y_{x'}` is a bijection, equivariant along `g ↦ φ ∘ g ∘ φ⁻¹`, and
`φ̃(g, y) = (φ ∘ g ∘ φ⁻¹, B_φ(y))` is an isomorphism `G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering →
    ∀ (φ : MorX) (x x' : ObjX), X.src φ = x → X.tgt φ = x' →
      -- `B_φ : Y_x → Y_{x'}` is a bijection
      Set.BijOn (transportB F φ) (F.obj ⁻¹' {x}) (F.obj ⁻¹' {x'}) ∧
      -- `c_φ : G_x → G_{x'}` is a bijection preserving units and composition
      Set.BijOn (conjB X φ) (isoB X x) (isoB X x') ∧
      conjB X φ (X.unit x) = X.unit x' ∧
      (∀ g ∈ isoB X x, ∀ g' ∈ isoB X x,
        conjB X φ (X.comp g' g) = X.comp (conjB X φ g') (conjB X φ g)) ∧
      -- `B_φ` is equivariant: `B_φ(g * y) = (φ ∘ g ∘ φ⁻¹) * B_φ(y)`
      (∀ g ∈ isoB X x, ∀ y ∈ F.obj ⁻¹' {x},
        transportB F φ (smulB F g y) = smulB F (conjB X φ g) (transportB F φ y)) ∧
      -- `φ̃` is a bijection on morphisms `G_x × Y_x → G_{x'} × Y_{x'}`
      Set.BijOn (fun p : MorX × ObjY => (conjB X φ p.1, transportB F φ p.2))
        (isoB X x ×ˢ (F.obj ⁻¹' {x})) (isoB X x' ×ˢ (F.obj ⁻¹' {x'}))

end RoundTrip.V11_35
