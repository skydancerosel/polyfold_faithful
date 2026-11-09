import Polyfold
/-! Blind formalization of V11_38 (the text's Part II, §11.6, Theorem 11.6.6 (1), p. 555 of the
Springer 2021 book, and its proof, steps (A)–(C), pp. 556–560; 2017: Theorem 11.10, p. 405).

Text: for an equivalence `(Ψ, Φ) : F → F'` and a functor `(ζ, ξ) : F'' → F'`, the functor `H` of
(11.18), (11.19) between the weak fibred products is a proper covering functor; steps (A)–(C).

Choices:
- Setting: proper covering functors `F : Y → X`, `F' : Y' → X'`, `F'' : Y'' → X''` between
  ep-groupoids (the project's `EpFunctor.IsProperCovering`, Definition 8.5.1, checked in
  `RoundTrip/Blind/V8_27.lean`), all twelve spaces in `Type` (universe 0).  `(Ψ, Φ) : F → F'` an
  element `Γ` of the project's `ProperCoveringHom F F'` with `Γ.IsEquivalence`, `(ζ, ξ) : F'' → F'`
  an element `Λ` of `ProperCoveringHom F'' F'` (both characterized as Definition 11.6.4 in my
  `RoundTrip/Blind/V11_36.lean`).
- The weak fibred products `P = Y ×_{Y'} Y''` (of `Ψ` and `ζ`) and `Q = X ×_{X'} X''` (of `Φ` and
  `ξ`) as ep-groupoids: the project's `WeakFibredProduct.epGroupoid` (Definition 10.2.1 with the
  structure of Theorem 10.2.2; checked in `RoundTrip/Blind/V10_17.lean` and following), whose
  admissibility hypothesis ("one of the two functors is a local sc-diffeomorphism on objects")
  is supplied by `Ψ` resp. `Φ` being equivalences (field `isLocalScDiffeo_obj` of
  `EpFunctor.IsEquivalence`).
- (11.18), (11.19), as I read them: `H(y, ψ', y'') = (F(y), F'(ψ'), F''(y''))` on objects and
  `H(h, ψ', h'') = (F(h), F'(ψ'), F''(h''))` on morphisms.  Since the project's objects and
  morphisms of a weak fibred product are determined by their three entries (V10_17), I describe
  `H` through the entries `x, φ, z` resp. `h, φ, k` of its values.
- "the functor `H` is a proper covering functor": there is an sc-smooth functor
  (`EpFunctor`) `P → Q` with these object and morphism maps, and it is a proper covering
  functor.  Steps (A)–(C) are steps of the proof; B is the claim (1) only.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_38
open Polyfold

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}

/-- The ep-groupoid `P = Y ×_{Y'} Y''` (weak fibred product of `Ψ` and `ζ`). -/
noncomputable def PB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom F'' F') :
    EpGroupoid (WeakFibredProduct.Obj Γ.Ψ Λ.Ψ) (WeakFibredProduct.Mor Γ.Ψ Λ.Ψ) :=
  WeakFibredProduct.epGroupoid Γ.Ψ Λ.Ψ (Or.inl hΓ.isEquivalence_Ψ.isLocalScDiffeo_obj)

/-- The ep-groupoid `Q = X ×_{X'} X''` (weak fibred product of `Φ` and `ξ`). -/
noncomputable def QB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom F'' F') :
    EpGroupoid (WeakFibredProduct.Obj Γ.Φ Λ.Φ) (WeakFibredProduct.Mor Γ.Φ Λ.Φ) :=
  WeakFibredProduct.epGroupoid Γ.Φ Λ.Φ (Or.inl hΓ.isEquivalence_Φ.isLocalScDiffeo_obj)

/-- `H` is given by (11.18) on objects and (11.19) on morphisms. -/
def IsHB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence) (Λ : ProperCoveringHom F'' F')
    (H : EpFunctor (PB Γ hΓ Λ) (QB Γ hΓ Λ)) : Prop :=
  (∀ o : WeakFibredProduct.Obj Γ.Ψ Λ.Ψ,
    (H.obj o).x = F.obj o.x ∧ (H.obj o).φ = F'.mor o.φ ∧ (H.obj o).z = F''.obj o.z) ∧
  (∀ m : WeakFibredProduct.Mor Γ.Ψ Λ.Ψ,
    (H.mor m).h = F.mor m.h ∧ (H.mor m).φ = F'.mor m.φ ∧ (H.mor m).k = F''.mor m.k)

end

/-- Theorem 11.6.6 (1): the functor `H : Y ×_{Y'} Y'' → X ×_{X'} X''` of (11.18), (11.19) is an
sc-smooth functor and a proper covering functor. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (ObjY' MorY' : Type) [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
    [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
    (ObjX' MorX' : Type) [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
    [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
    (ObjY'' MorY'' : Type) [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
    [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
    (ObjX'' MorX'' : Type) [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
    [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX)
    (Y' : EpGroupoid ObjY' MorY') (X' : EpGroupoid ObjX' MorX')
    (Y'' : EpGroupoid ObjY'' MorY'') (X'' : EpGroupoid ObjX'' MorX'')
    (F : EpFunctor Y X) (F' : EpFunctor Y' X') (F'' : EpFunctor Y'' X''),
    F.IsProperCovering → F'.IsProperCovering → F''.IsProperCovering →
    ∀ (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence) (Λ : ProperCoveringHom F'' F'),
      ∃ H : EpFunctor (PB Γ hΓ Λ) (QB Γ hΓ Λ), IsHB Γ hΓ Λ H ∧ H.IsProperCovering

end RoundTrip.V11_38
